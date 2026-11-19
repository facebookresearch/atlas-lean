/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic
public import MathlibExtTest.Biology.StatisticalGenetics.AssociationTests.PearsonLimit

import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Filter
open MathlibExt.Probability.Statistics.ExactTests MathlibExt.Probability.Statistics.MultipleTesting
open MathlibExt.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic
open MathlibExt.Biology.StatisticalGenetics.RareVariantInference.GenomicControl
open MathlibExt.Biology.StatisticalGenetics.PearsonLimit
open MathlibExtTest.Biology.StatisticalGenetics.PearsonLimit (X4 μH μH_real_singleton
  hasLaw_sq_chiSquare)

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

/-- Any extremeness key works, e.g. ranking by excess heterozygosity (`g j = -j`). The
feasible allele count is required: without it the arrangement measure can be the zero
measure and validity would hold vacuously. -/
example (N nA : ℕ) (hnA : nA ≤ 2 * N) :
    IsValidPValue (uniformArrangements N nA)
      fun s => orderedPValue (leveneProb N nA) (fun j => -(j : ℝ)) (nA + 1) (hetCount s) :=
  isValidPValue_orderedPValue hnA (hasLaw_hetCount N nA) _

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
example : hweStat 100 ![99, 0, 1] = 100 := by
  have := hweStat_one_homozygote (m := 99) (by norm_num)
  norm_num at this
  exact this

/-! ### Regime boundaries -/

/-- The sparse case is outside Cochran's rule. -/
example : ¬ InChiSqRegime 5 10 ![9, 0, 1] := not_inChiSqRegime_sparse

/-- A balanced sample at HWE proportions is inside it: `(25, 50, 25)` has expected counts
`(25, 50, 25)`, and Pearson's statistic is `0`. -/
example : InChiSqRegime 5 100 ![25, 50, 25] := by
  intro i
  fin_cases i <;> norm_num [hweProb, alleleFreqHat, Fin.sum_univ_three]

example : hweStat 100 ![25, 50, 25] = 0 := by
  norm_num [hweStat, pearsonStatistic, hweProb, alleleFreqHat, Fin.sum_univ_three]

/-! ### Genomic control -/

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

example : orderedPValue (fun _ => 1 / 3) (fun _ => 0) 3 1 = 1 := by
  norm_num [orderedPValue, sum_range_succ]

example (f g : ℕ → ℝ) : orderedPValue f g 0 0 = 0 := by
  simp [orderedPValue]

/-! ### Connection to Pearson's limit theorem -/

/-- The sparse observation, computed from the definitions on both sides: the heterozygote-count
statistic at `(N, n_A, n_AB) = (10, 2, 0)` and `hweStat` of the table `(9, 0, 1)` are both `10`. -/
example : hweChiSqOfHet 10 2 0 = 10 ∧ hweStat 10 ![9, 0, 1] = 10 := by
  constructor
  · norm_num [hweChiSqOfHet, hweStat, pearsonStatistic, hweProb, alleleFreqHat,
      Fin.sum_univ_three]
  · norm_num [hweStat, pearsonStatistic, hweProb, alleleFreqHat, Fin.sum_univ_three]

/-- The table identity at `(9, 0, 1)` states exactly the equality of those two numbers. -/
example : hweChiSqOfHet 10 2 0 = hweStat 10 ![9, 0, 1] := by
  simpa using hweChiSqOfHet_eq_hweStat 9 0 1

/-- A table with every cell nonzero, `(2, 3, 5)`: `N = 10`, `n_A = 13`, `n_AB = 3`. Both sides,
computed from the definitions, equal `X² = N F̂² = 10 (31/91)² = 9610/8281`. -/
example : hweChiSqOfHet 10 13 3 = 9610 / 8281 ∧ hweStat 10 ![2, 3, 5] = 9610 / 8281 := by
  constructor
  · norm_num [hweChiSqOfHet, hweStat, pearsonStatistic, hweProb, alleleFreqHat,
      Fin.sum_univ_three]
  · norm_num [hweStat, pearsonStatistic, hweProb, alleleFreqHat, Fin.sum_univ_three]

example : hweChiSqOfHet 10 13 3 = hweStat 10 ![2, 3, 5] := by
  simpa using hweChiSqOfHet_eq_hweStat 2 3 5

/-- An infeasible input is outside the identity: `(N, n_A, n_AB) = (1, 1, 0)` has `n_A - n_AB`
odd, so no genotype table realizes it, and the floor divisions collapse every cell to `0`. -/
example : hweChiSqOfHet 1 1 0 = hweStat 1 ![0, 0, 0] := by
  norm_num [hweChiSqOfHet]

/-- The concrete sample `0, 1, 2, 2` of `PearsonLimit`'s tests: allele count `5`, one
heterozygote, and `hweChiSqOfHet 4 5 1 = 196/225`, computed from the definition. -/
example : ∑ m ∈ range 4, (X4 m () : ℕ) = 5 ∧
    #{m ∈ range 4 | X4 m () = 1} = 1 ∧
    hweChiSqOfHet 4 5 1 = 196 / 225 := by
  refine ⟨by decide, by decide, ?_⟩
  norm_num [hweChiSqOfHet, hweStat, pearsonStatistic, hweProb, alleleFreqHat, Fin.sum_univ_three]

/-- The sample form on that sample. -/
example : hweChiSqOfHet 4
      (∑ m ∈ range 4, (X4 m () : ℕ))
      #{m ∈ range 4 | X4 m () = 1} =
    hweStat 4 (cellCount X4 4 ()) :=
  hweChiSqOfHet_eq_hweStat_cellCount _ 4 ()

/-- **Non-vacuity of `tendstoInDistribution_hweChiSqOfHet`.** For an i.i.d. sample from the
Hardy–Weinberg population at `p = 1/2` (two fair alleles), the heterozygote-count statistic at
the observed counts converges in distribution to `x ↦ x²` under `N(0, 1)`, i.e. to `χ²₁`. -/
theorem exists_hweChiSqOfHet_tendsto_chiSquare :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (X : ℕ → Ω → Fin 3),
      (∀ m, HasLaw (X m) μH P) ∧
        iIndepFun X P ∧
        TendstoInDistribution
          (fun N ω => hweChiSqOfHet N (∑ m ∈ range N, (X m ω : ℕ)) #{m ∈ range N | X m ω = 1})
          atTop (fun x : ℝ => x ^ 2) (fun _ => P) (gaussianReal 0 1) := by
  obtain ⟨Ω, _, P, X, hmeas, hlaw, hindep, hP⟩ :=
    exists_iid ℕ μH
  refine ⟨Ω, _, P, hP, X, hlaw, hindep, ?_⟩
  have hident : ∀ m, IdentDistrib (X m) (X 0) P P := fun m =>
    ⟨(hmeas m).aemeasurable, (hmeas 0).aemeasurable, (hlaw m).map_eq.trans (hlaw 0).map_eq.symm⟩
  have hX0 : ∀ i, P.real (X 0 ⁻¹' {i}) = hweProb (1 / 2) i := fun i => by
    rw [← map_measureReal_apply (hmeas 0) (measurableSet_singleton i), (hlaw 0).map_eq,
      μH_real_singleton]
  exact tendstoInDistribution_hweChiSqOfHet hX0 (by norm_num) (by norm_num) hindep hident
    hasLaw_sq_chiSquare

end MathlibExtTest.Biology.StatisticalGenetics.AssociationTests.ExactVsAsymptotic
