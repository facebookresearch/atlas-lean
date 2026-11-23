/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Bioinformatics.CRNDirect
public meta import CSLibExt.Bioinformatics.CRNDirect


namespace Cslib.Bioinformatics.CRN

/-! ## Computed examples: birth reaction over `Fin 2` -/

/-- Birth reaction ∅ → A over two species (`Fin 2`, species `0` is `A`),
with rate constant `2`. -/
def birthReaction : Reaction (Fin 2) :=
  { reactants := fun _ => 0
    products := fun s => if s = 0 then 1 else 0
    k := 2
    k_nonneg := by norm_num }

/-- Empty initial state. -/
def initState : Fin 2 → ℕ := fun _ => 0

theorem birth_k : birthReaction.k = 2 := rfl

theorem birth_reactants (s : Fin 2) : birthReaction.reactants s = 0 := rfl

theorem birth_products (s : Fin 2) :
    birthReaction.products s = (if s = 0 then 1 else 0) := rfl

/-- A birth reaction fires at its rate constant regardless of state. -/
theorem birth_propensity (x : Fin 2 → ℕ) :
    propensity birthReaction x = 2 := by
  unfold propensity combFactor
  simp [birth_k, birth_reactants, Nat.descFactorial_zero, Nat.factorial_zero,
    Finset.prod_const_one]

/-- Firing the birth reaction from the empty state produces one `A`. -/
theorem birth_fire_empty :
    fire birthReaction initState
      = fun s => if s = (0 : Fin 2) then 1 else 0 := by
  funext s
  simp [fire, initState, birth_reactants, birth_products]

theorem birth_fire_zero : fire birthReaction initState 0 = 1 := by
  simp [fire, initState, birth_reactants, birth_products]

theorem birth_fire_ne (s : Fin 2) (hs : s ≠ 0) :
    fire birthReaction initState s = 0 := by
  simp [fire, initState, birth_reactants, birth_products, hs]

/-- Single-reaction selection: the birth reaction is selected and the new
state has one `A`; the waiting time stays symbolic. -/
theorem birth_step_some :
    step [birthReaction] initState (1 / 2) (1 / 2) =
      some (Real.log (1 / (1 / 2)) / 2, birthReaction,
        fire birthReaction initState) := by
  have ha0 : totalPropensity [birthReaction] initState = 2 := by
    simp [totalPropensity, birth_propensity]
  have hlt2 : (1 / 2 : ℝ) * 2 < propensity birthReaction initState := by
    rw [birth_propensity]
    norm_num
  have hsel2 : selectAux [birthReaction] initState ((1 / 2 : ℝ) * 2) =
      some birthReaction := by
    rw [selectAux_cons, ite_eq_left hlt2]
  rw [step_eq, ha0, ite_eq_right (by norm_num : (2 : ℝ) ≠ 0), hsel2]

/-- Absorbing example: the empty list never fires. -/
theorem empty_step_none (u1 u2 : ℝ) :
    step ([] : List (Reaction (Fin 2))) initState u1 u2 = none :=
  step_none_of_empty initState u1 u2

/-- The waiting time from the birth example is nonnegative (via soundness). -/
theorem birth_tau_nonneg : 0 ≤ Real.log (1 / (1 / 2 : ℝ)) / 2 := by
  have h := step_some_sound [birthReaction] initState (1 / 2) (1 / 2) _ _ _
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) birth_step_some
  exact h.1

#print axioms birth_propensity
#print axioms birth_fire_empty
#print axioms birth_fire_zero
#print axioms birth_fire_ne
#print axioms birth_step_some
#print axioms empty_step_none
#print axioms birth_tau_nonneg

end Cslib.Bioinformatics.CRN
