/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic

import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.ExactTests MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic

namespace MathlibExtTest.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic

/-! ### Smoke test: the exact test is valid for every sample size -/

/-- The exact HWE test is valid for the sparse model `N = 10`, `n_A = 2`. -/
example : IsValidPValue (uniformArrangements 10 2) fun s => hweExactPValue 10 2 (hetCount s) :=
  isValidPValue_hweExactPValue 10 2 (by norm_num)

/-- The heterozygote-deficit test is valid too, including in the degenerate model `N = 0`. -/
example : IsValidPValue (uniformArrangements 0 0) fun s => hweDeficitPValue 0 0 (hetCount s) :=
  isValidPValue_hweDeficitPValue 0 0 (by norm_num)

/-- The uniform-placement model is a probability measure for feasible allele counts. -/
example : IsProbabilityMeasure (uniformArrangements 10 2) := by
  have : Fact (2 ≤ 2 * 10) := ⟨by norm_num⟩
  infer_instance

/-- Any extremeness key works, e.g. ranking by excess heterozygosity (`g j = -j`). -/
example (N nA : ℕ) :
    IsValidPValue (uniformArrangements N nA)
      fun s => orderedPValue (leveneProb N nA) (fun j => -(j : ℝ)) (nA + 1) (hetCount s) :=
  isValidPValue_orderedPValue (hasLaw_hetCount N nA) _

/-! ### The sparse case: exact values -/

/-- Null law of `n_AB` for `N = 10`, `n_A = 2`: no heterozygote with probability `1/19`, two
heterozygotes with probability `18/19`. -/
example : leveneProb 10 2 0 + leveneProb 10 2 2 = 1 := by
  rw [leveneProb_sparse_zero, leveneProb_sparse_two]
  norm_num

/-- The observation "one `AA`, no `AB`, nine `BB`": exact p-value `1/19 > 0.05`. -/
example : 1 / 20 < hweExactPValue 10 2 0 := by
  rw [hweExactPValue_sparse]
  norm_num

/-- The one-sided deficit p-value of the same observation is also `P(n_AB ≤ 0) = 1/19`. -/
example : hweDeficitPValue 10 2 0 = 1 / 19 := by
  simp only [hweDeficitPValue, orderedPValue, sum_filter, sum_range_succ, range_zero, sum_empty,
    leveneProb_sparse_zero, leveneProb_sparse_one, leveneProb_sparse_two]
  norm_num

/-- The observed heterozygote count with the largest null probability has exact p-value `1`. -/
example : hweExactPValue 10 2 2 = 1 := by
  simp only [hweExactPValue, orderedPValue, sum_filter, sum_range_succ, range_zero, sum_empty,
    leveneProb_sparse_zero, leveneProb_sparse_one, leveneProb_sparse_two]
  norm_num

/-- Pearson's statistic takes only two values in the sparse model. -/
example : hweChiSqOfHet 10 2 0 = 10 ∧ hweChiSqOfHet 10 2 2 = 10 / 81 :=
  ⟨hweChiSqOfHet_sparse_zero, hweChiSqOfHet_sparse_two⟩

/-- The asymptotic p-value of the sparse observation is at most `0.05` (it rejects), while the
exact p-value is `1/19` (it does not). -/
example : asymptoticHWEPValue 10 2 0 ≤ 1 / 20 ∧ 1 / 20 < hweExactPValue 10 2 0 := by
  refine ⟨asymptoticHWEPValue_sparse_le, ?_⟩
  rw [hweExactPValue_sparse]
  norm_num

/-- The asymptotic p-value is anti-conservative in the sparse model. -/
example : ¬ IsValidPValue (uniformArrangements 10 2)
    fun s => asymptoticHWEPValue 10 2 (hetCount s) :=
  not_isValidPValue_asymptoticHWEPValue_sparse

/-- The statistic grows with `N`: with one `AA` homozygote among `100` individuals, `X² = 100`. -/
example : hweChiSq 1 0 99 = 100 := by
  have := hweChiSq_one_zero (m := 99) (by norm_num)
  norm_num at this
  exact this

/-! ### Regime boundaries -/

/-- The sparse case is outside Cochran's rule. -/
example : ¬ InChiSqRegime 5 1 0 9 := not_inChiSqRegime_sparse

/-- A balanced sample at HWE proportions is inside it: `(25, 50, 25)` has expected counts
`(25, 50, 25)`, and Pearson's statistic is `0`. -/
example : InChiSqRegime 5 25 50 25 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [expectedAA, expectedAB, expectedBB, freqA]

example : hweChiSq 25 50 25 = 0 := by
  norm_num [hweChiSq, expectedAA, expectedAB, expectedBB, freqA]

/-! ### Genomic control -/

/-- Under the multiplicative-inflation model genomic control is valid. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {Z : Ω → ℝ}
    (hZ : HasLaw Z (gaussianReal 0 1) μ) :
    IsValidPValue μ fun ω => gcPValue 2 (2 * Z ω ^ 2) :=
  isValidPValue_gcPValue (by norm_num) ⟨Z, hZ, fun _ => rfl⟩

/-- No inflation factor repairs the sparse case: `λ = 1` (the clipping floor), `λ = 1/2`
(below the clipping floor, inflating the statistic), and `λ = 100` (heavy deflation) all fail. -/
example : ¬ IsValidPValue (uniformArrangements 10 2)
    fun s => gcPValue 1 (hweChiSqOfHet 10 2 (hetCount s)) :=
  not_isValidPValue_gcPValue_sparse one_pos

example : ¬ IsValidPValue (uniformArrangements 10 2)
    fun s => gcPValue (1 / 2) (hweChiSqOfHet 10 2 (hetCount s)) :=
  not_isValidPValue_gcPValue_sparse (by norm_num)

example : ¬ IsValidPValue (uniformArrangements 10 2)
    fun s => gcPValue 100 (hweChiSqOfHet 10 2 (hetCount s)) :=
  not_isValidPValue_gcPValue_sparse (by norm_num)

/-- With `λ = 1` the level-`0.05` genomic-control test still rejects with null probability at
least `1/19`. -/
example : ENNReal.ofReal (1 / 19) ≤ uniformArrangements 10 2
    {s | gcPValue 1 (hweChiSqOfHet 10 2 (hetCount s)) ≤ 1 / 20} :=
  gcPValue_sparse_rejection_ge one_pos le_rfl

example (x : ℝ) : chiSqOneSurvival x = (chiSquareMeasure 1).real (Set.Ici x) := rfl

example (x : ℝ) : chiSqOneSurvival x = (gaussianReal 0 1).real {z | x ≤ z ^ 2} := by
  rw [chiSqOneSurvival, ← gaussianReal_map_sq, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Ici]
  rfl

example : chiSqOneSurvival 0 = 1 := by
  rw [chiSqOneSurvival, ← gaussianReal_map_sq, measureReal_def,
    Measure.map_apply (by fun_prop) measurableSet_Ici]
  simp [Set.preimage, sq_nonneg]

example : orderedPValue (fun _ => 1 / 3) (fun _ => 0) 3 1 = 1 := by
  norm_num [orderedPValue, sum_range_succ]

example (f g : ℕ → ℝ) : orderedPValue f g 0 0 = 0 := by
  simp [orderedPValue]

/-- `χ²₁` tail bounds used above. -/
example : chiSqOneSurvival 10 ≤ 1 / 20 := chiSqOneSurvival_ten_le

example : chiSqOneSurvival 1 < 1 := chiSqOneSurvival_lt_one one_pos

end MathlibExtTest.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic
