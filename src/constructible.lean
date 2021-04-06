import data.real.sqrt

inductive constructible : ℝ → Prop
| one : constructible 1
| add : ∀ ⦃x y⦄, constructible x → constructible y → constructible (x + y)
| neg : ∀ ⦃x⦄, constructible x → constructible (-x)
| mul : ∀ ⦃x y⦄, constructible x → constructible y → constructible (x * y)
| inv : ∀ ⦃x⦄, constructible x → constructible (x⁻¹)
| sqrt : ∀ ⦃x⦄, constructible x → constructible (real.sqrt x)

@[user_attribute]
meta def constructibility : user_attribute :=
{ name := `constructibility,
  descr := "lemmas used to prove constructibility" }

attribute [constructibility] constructible.one constructible.add constructible.neg constructible.mul 
  constructible.inv constructible.sqrt

namespace tactic

meta def constructibility_core : tactic unit := apply_rules [``(constructibility)] 50 {}

namespace interactive

meta def constructibility : tactic unit := tactic.constructibility_core

end interactive

end tactic

-- meta def constructibility : tactic unit :=
-- `[ apply_rules [constructible.one, constructible.add, constructible.neg, constructible.mul, 
--                 constructible.inv, constructible.sqrt] ]

@[constructibility]
lemma constructible_zero : constructible 0 :=
begin
  rw ←add_neg_self (1 : ℝ),
  constructibility,
end

def constructible_number := {x // constructible x}

namespace constructible_number

local notation `C` := constructible_number

def zero : C := ⟨0, by constructibility⟩

instance : has_zero C := ⟨zero⟩

def one : C := ⟨1, by constructibility⟩

instance : has_one C := ⟨one⟩

def add : C → C → C
| ⟨a, ha⟩ ⟨b, hb⟩ := ⟨a + b, by constructibility⟩

instance : has_add C := ⟨add⟩

def neg : C → C
| ⟨a, ha⟩ := ⟨-a, by constructibility⟩

instance : has_neg C := ⟨neg⟩

instance : add_comm_group C :=
{ add_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, subtype.ext $ add_assoc a b c,
  zero_add := λ ⟨a, ha⟩, subtype.ext $ zero_add a,
  add_zero := λ ⟨a, ha⟩, subtype.ext $ add_zero a,
  add_comm := λ ⟨a, ha⟩ ⟨b, hb⟩, subtype.ext $ add_comm a b,
  add_left_neg := λ ⟨a, ha⟩, subtype.ext $ add_left_neg a,
  sub := λ a b, a + - b,
  sub_eq_add_neg := λ ⟨a, ha⟩ ⟨b, hb⟩, rfl,
  ..constructible_number.has_add, ..constructible_number.has_zero, ..constructible_number.has_neg }

def mul : C → C → C
| ⟨a, ha⟩ ⟨b, hb⟩ := ⟨a * b, by constructibility⟩

instance : has_mul C := ⟨mul⟩

instance : comm_ring C :=
{ mul_assoc := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, subtype.ext $ mul_assoc a b c,
  one_mul := λ ⟨a, ha⟩, subtype.ext $ one_mul a,
  mul_one := λ ⟨a, ha⟩, subtype.ext $ mul_one a,
  left_distrib := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, subtype.ext $ left_distrib a b c,
  right_distrib := λ ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩, subtype.ext $ right_distrib a b c,
  mul_comm := λ ⟨a, ha⟩ ⟨b, hb⟩, subtype.ext $ mul_comm a b,
  ..constructible_number.add_comm_group, ..constructible_number.has_mul, ..constructible_number.has_one }

noncomputable def inv : C → C
| ⟨a, ha⟩ := ⟨a⁻¹, by constructibility⟩

noncomputable instance : has_inv C := ⟨inv⟩

example {α β : Type} (f : α → β) (hf : function.injective f) (a b : α) (hab : a ≠ b) : f a ≠ f b :=
begin
  exact function.injective.ne hf hab
end

noncomputable instance : field C :=
{ exists_pair_ne := ⟨0, 1, subtype.ne_of_val_ne zero_ne_one⟩,
  mul_inv_cancel := λ ⟨a, ha⟩ h, subtype.ext $ mul_inv_cancel $ subtype.val_injective.ne h,
  inv_zero := subtype.ext inv_zero,
  ..constructible_number.comm_ring, ..constructible_number.has_inv }

end constructible_number
