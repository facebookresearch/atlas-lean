/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.ComplexBalanced

/-! Tests for complex-balanced mass-action systems: a non-vacuity witness (the dimerization
`2A ⇌ B` with rate constants `1` and `4`, complex balanced at `(2, 1)`), the Horn–Jackson
theorems applied to it, a second positive equilibrium on the curve `c_B = c_A² / 4`, a
network whose positive equilibria are not complex balanced (so the complex-balanced
hypothesis cannot be dropped), and boundary values of the pseudo-Helmholtz function. -/

open Real

namespace MathlibExtTest.Biology.Dynamics.ComplexBalanced

open MathlibExt.Biology.Dynamics.ComplexBalanced ReactionNetwork

/-- The dimerization `2A ⇌ B` on species `Fin 2` (`0 = A`, `1 = B`): reaction `0` is
`2A → B`, reaction `1` is `B → 2A`. -/
def dimer : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![2, 0], ![0, 1]]
  prod := ![![0, 1], ![2, 0]]

/-- Rate constants `k₀ = 1`, `k₁ = 4`. -/
noncomputable def kDimer : Fin 2 → ℝ := ![1, 4]

/-- The reference concentrations `c* = (2, 1)`. -/
noncomputable def cDimer : Fin 2 → ℝ := ![2, 1]

theorem kDimer_pos : ∀ r, 0 < kDimer r := by
  intro r; fin_cases r <;> simp [kDimer]

theorem cDimer_pos : ∀ s, 0 < cDimer s := by
  intro s; fin_cases s <;> simp [cDimer]

/-- Both reactions run at rate `4` at `c* = (2, 1)`: `1 · 2² = 4 · 1`. -/
theorem rate_dimer (r : Fin 2) : dimer.rate kDimer cDimer r = 4 := by
  fin_cases r <;> norm_num [rate, dimer, kDimer, cDimer, Fin.prod_univ_two]

/-- **Non-vacuity witness.** The dimerization is complex balanced at `(2, 1)` for the rate
constants `(1, 4)`, so every hypothesis of the Horn–Jackson theorems is satisfiable. -/
theorem isComplexBalanced_dimer : dimer.IsComplexBalanced kDimer cDimer := by
  intro z
  simp only [Finset.sum_filter, Fin.sum_univ_two, rate_dimer]
  simp only [dimer, Matrix.cons_val_zero, Matrix.cons_val_one]
  exact add_comm _ _

/-- Complex balance makes `(2, 1)` an equilibrium. -/
example : dimer.massActionField kDimer cDimer = 0 :=
  dimer.massActionField_eq_zero_of_isComplexBalanced isComplexBalanced_dimer

/-- `(4, 4)` is another positive equilibrium (on the curve `c_B = c_A² / 4`): both reactions
run at rate `16`. -/
theorem massActionField_dimer_four : dimer.massActionField kDimer ![4, 4] = 0 := by
  funext s
  fin_cases s <;>
    simp [massActionField, dimer, kDimer, Fin.sum_univ_two, Fin.prod_univ_two] <;> norm_num

/-- By Horn–Jackson, the equilibrium `(4, 4)` is complex balanced. -/
example : dimer.IsComplexBalanced kDimer ![4, 4] :=
  dimer.isComplexBalanced_of_massActionField_eq_zero kDimer_pos cDimer_pos
    isComplexBalanced_dimer (by intro s; fin_cases s <;> simp) massActionField_dimer_four

/-- Exactly one positive equilibrium in the compatibility class of `(1, 1)`. -/
example : ∃! x : Fin 2 → ℝ, (∀ s, 0 < x s) ∧
    x - ![1, 1] ∈ dimer.stoichiometricSubspace ∧ dimer.massActionField kDimer x = 0 :=
  dimer.existsUnique_equilibrium_of_isComplexBalanced kDimer_pos cDimer_pos
    isComplexBalanced_dimer (by intro s; fin_cases s <;> simp)

/-- The Horn–Jackson inequality at the positive non-equilibrium state `(1, 1)`. -/
example : dimer.helmholtzRate kDimer cDimer ![1, 1] ≤ 0 :=
  dimer.helmholtzRate_nonpos kDimer_pos cDimer_pos isComplexBalanced_dimer
    (by intro s; fin_cases s <;> simp)

/-- The rate of change of `G` vanishes at the equilibrium `(4, 4)`. -/
example : dimer.helmholtzRate kDimer cDimer ![4, 4] = 0 :=
  (dimer.helmholtzRate_eq_zero_iff kDimer_pos cDimer_pos isComplexBalanced_dimer
    (by intro s; fin_cases s <;> simp)).2 massActionField_dimer_four

/-- The pseudo-Helmholtz function at the reference point is `-∑ c*_s = -3`. -/
example : pseudoHelmholtz cDimer cDimer = -3 := by
  simp [pseudoHelmholtz, cDimer, Fin.sum_univ_two]; norm_num

/-- Boundary value: at `c = 0` the pseudo-Helmholtz function is `0`, which agrees with the
continuous extension `c log c → 0`. -/
example : pseudoHelmholtz cDimer 0 = 0 := by
  simp [pseudoHelmholtz]

/-- Junk value outside the domain: Lean's `Real.log (-1) = 0` gives `G(-1, -1) = 2 + log 2`,
which has no chemical meaning; the theorems assume positive concentrations. -/
example : pseudoHelmholtz cDimer (fun _ => -1) = 2 + Real.log 2 := by
  simp [pseudoHelmholtz, cDimer, Fin.sum_univ_two]; ring

/-- The network `A → 2A`, `A → 0` on one species (birth and death at equal rates `1`). -/
def birthDeath : ReactionNetwork (Fin 1) (Fin 2) where
  src := ![![1], ![1]]
  prod := ![![2], ![0]]

/-- Every concentration is an equilibrium of `birthDeath` with rate constants `(1, 1)`. -/
theorem massActionField_birthDeath (c : Fin 1 → ℝ) :
    birthDeath.massActionField 1 c = 0 := by
  funext s
  fin_cases s
  simp [massActionField, birthDeath, Fin.sum_univ_two]
  ring

/-- No positive state of `birthDeath` is complex balanced: the complex `2A` receives flux `c`
and emits none. So the positive equilibria of a mass-action system need not be complex
balanced; the hypothesis of `isComplexBalanced_of_massActionField_eq_zero` that some positive
complex-balanced equilibrium exists cannot be dropped. -/
theorem not_isComplexBalanced_birthDeath {c : Fin 1 → ℝ} (hc : 0 < c 0) :
    ¬ birthDeath.IsComplexBalanced 1 c := by
  intro h
  have h2 := h ![2]
  rw [Finset.sum_filter, Finset.sum_filter] at h2
  simp [Fin.sum_univ_two, birthDeath, rate] at h2
  exact hc.ne h2

#print axioms isComplexBalanced_dimer
#print axioms ReactionNetwork.existsUnique_equilibrium_of_isComplexBalanced
#print axioms ReactionNetwork.antitoneOn_pseudoHelmholtz
#print axioms exists_pos_sub_mem_log_orthogonal

end MathlibExtTest.Biology.Dynamics.ComplexBalanced
