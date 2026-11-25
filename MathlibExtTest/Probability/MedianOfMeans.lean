/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MedianOfMeans

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability.MedianOfMeans

namespace MathlibExtTest.Probability.MedianOfMeans

-- Three values `0, 1, 100`: only one lies outside `[0, 2]`, so the median lies in `[0, 2]`.
set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
example : sampleMedian ![(0 : ℝ), 1, 100] ∈ Set.Icc (0 : ℝ) 2 := by
  apply sampleMedian_mem_Icc
  have : (Finset.univ.filter fun i : Fin 3 => ![(0 : ℝ), 1, 100] i ∉ Set.Icc (0 : ℝ) 2) =
      {2} := by
    ext i; fin_cases i <;> simp <;> norm_num
  rw [this]; simp

-- The amplification bound with `s = 32` repetitions is `exp (-9) < 1.3 · 10⁻⁴`.
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Fin 32 → Ω → ℝ} (h : iIndepFun Y μ) (hm : ∀ i, Measurable (Y i)) {a b : ℝ}
    (hbad : ∀ i, μ.real {ω | Y i ω ∉ Set.Icc a b} ≤ 1 / 8) :
    μ.real {ω | sampleMedian (fun i => Y i ω) ∉ Set.Icc a b} ≤ Real.exp (-9) := by
  have := measureReal_sampleMedian_notMem_Icc_le h hm hbad
  have h9 : (-9 * ((32 : ℕ) : ℝ) / 32) = -9 := by norm_num
  rwa [h9] at this

end MathlibExtTest.Probability.MedianOfMeans
