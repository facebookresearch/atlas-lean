/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.DeficiencyZero.Integration

/-! Tests for the deficiency-zero integration: the reversible isomerization `A ⇌ B` has
`deficiency = 0` (obtained from the linear form through `deficiency_eq_zero_iff`) and is weakly
reversible, so the deficiency-zero theorem in its `N.deficiency = 0` form gives a positive
complex-balanced equilibrium and exactly one equilibrium per compatibility class. The network
`0 → A`, `2A → 3A` (deficiency one) violates the linear form, so `deficiency_eq_zero_iff`
detects that its deficiency is nonzero. -/

namespace MathlibExtTest.Biology.Dynamics.DeficiencyZero.Integration

open MathlibExt.Biology.Dynamics.ComplexBalanced ReactionNetwork

/-- The reversible isomerization `A ⇌ B` on species `Fin 2` (`0 = A`, `1 = B`). -/
def revAB : ReactionNetwork (Fin 2) (Fin 2) where
  src := ![![1, 0], ![0, 1]]
  prod := ![![0, 1], ![1, 0]]

/-- `A ⇌ B` has deficiency zero, from the linear form `ker Y ∩ im ∂ = 0`. -/
theorem revAB_deficiency : revAB.deficiency = 0 := by
  refine revAB.deficiency_eq_zero_iff.2 fun α hα η => ?_
  have h0 := congrFun hα 0
  simp [revAB, Fin.sum_univ_two] at h0
  simp only [revAB, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have : α 1 = α 0 := by linarith
  rw [this]
  ring

theorem revAB_isWeaklyReversible : revAB.IsWeaklyReversible :=
  isWeaklyReversible_of_reversible fun r => by
    fin_cases r
    · exact ⟨1, rfl, rfl⟩
    · exact ⟨0, rfl, rfl⟩

/-- **Non-vacuity.** `A ⇌ B` has a positive complex-balanced equilibrium for every choice of
positive rate constants. -/
example {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) :
    ∃ c : Fin 2 → ℝ, (∀ s, 0 < c s) ∧ revAB.IsComplexBalanced k c :=
  revAB.exists_pos_isComplexBalanced revAB_deficiency revAB_isWeaklyReversible hk

/-- Exactly one positive equilibrium of `A ⇌ B` in the compatibility class of `(1, 2)`. -/
example {k : Fin 2 → ℝ} (hk : ∀ r, 0 < k r) : ∃! x : Fin 2 → ℝ, (∀ s, 0 < x s) ∧
    x - ![1, 2] ∈ revAB.stoichiometricSubspace ∧ revAB.massActionField k x = 0 :=
  revAB.existsUnique_equilibrium revAB_deficiency revAB_isWeaklyReversible hk
    (by intro s; fin_cases s <;> simp)

/-- The network `0 → A`, `2A → 3A` on one species: two linkage classes, deficiency one. -/
def disconnNet : ReactionNetwork (Fin 1) (Fin 2) where
  src := ![![0], ![2]]
  prod := ![![1], ![3]]

/-- **Boundary.** The weighting `α = (1, -1)` has zero net stoichiometric change but nonzero
net change against the indicator of the complex `A`, so the forward direction of
`deficiency_eq_zero_iff` rules out deficiency zero. -/
example : disconnNet.deficiency ≠ 0 := by
  intro h
  have := disconnNet.deficiency_eq_zero_iff.1 h ![1, -1] (by
    funext s
    fin_cases s
    simp [disconnNet, Fin.sum_univ_two]
    norm_num) fun y => if y = ![1] then 1 else 0
  simp [disconnNet, Fin.sum_univ_two] at this

#print axioms ReactionNetwork.deficiency_eq_zero_iff
#print axioms ReactionNetwork.exists_pos_isComplexBalanced
#print axioms ReactionNetwork.existsUnique_equilibrium

end MathlibExtTest.Biology.Dynamics.DeficiencyZero.Integration
