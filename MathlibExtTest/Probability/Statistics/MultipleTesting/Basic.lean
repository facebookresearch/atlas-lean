/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MultipleTesting.Basic

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.MultipleTesting

namespace MathlibExtTest.Probability.Statistics.MultipleTesting.Basic

/-- Three p-values `0.01, 0.02, 0.5`. -/
noncomputable def p3 : Fin 3 → ℝ := ![1 / 100, 2 / 100, 1 / 2]

/-- Two of the three p-values are at most `0.025`. -/
theorem numBelow_p3 : numBelow p3 (1 / 40) = 2 := by
  rw [numBelow, show (Finset.univ.filter fun i => p3 i ≤ 1 / 40) = {0, 1} by
    ext i; fin_cases i <;> norm_num [p3]]
  rfl

/-- Boundary: a threshold below every p-value counts nothing; `1` counts everything. -/
example : numBelow p3 0 = 0 := by
  rw [numBelow, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro i _
  fin_cases i <;> norm_num [p3]

example : numBelow p3 1 = 3 := by
  rw [numBelow, Finset.filter_true_of_mem fun i _ => by fin_cases i <;> norm_num [p3]]
  rfl

/-- Non-vacuity of `IsValidPValue`: the identity on `[0, 1]` under Lebesgue measure is a
uniform, hence valid, p-value. -/
example : IsValidPValue (volume.restrict (Set.Icc (0 : ℝ) 1)) id :=
  isValidPValue_of_hasLaw_uniform HasLaw.id

/-- A constant p-value `1` is valid (it is conservative), under a Dirac measure. -/
example : IsValidPValue (Measure.dirac ()) fun _ : Unit => (1 : ℝ) := by
  intro t ht
  rcases eq_or_lt_of_le ht.2 with rfl | hlt
  · simp
  · simp [not_le.2 hlt]

/-- False discovery proportion: rejecting `{0, 1}` with `H0 = {1, 2}` gives `1 / 2`; rejecting
nothing gives `0`. -/
example : falseDiscoveryProportion ({1, 2} : Finset (Fin 3)) {0, 1} = 1 / 2 := by
  norm_num [falseDiscoveryProportion]

example (H0 : Finset (Fin 3)) : falseDiscoveryProportion H0 ∅ = 0 := by
  simp [falseDiscoveryProportion]

example (H0 R : Finset (Fin 3)) :
    0 ≤ falseDiscoveryProportion H0 R ∧ falseDiscoveryProportion H0 R ≤ 1 :=
  ⟨falseDiscoveryProportion_nonneg H0 R, falseDiscoveryProportion_le_one H0 R⟩

end MathlibExtTest.Probability.Statistics.MultipleTesting.Basic
