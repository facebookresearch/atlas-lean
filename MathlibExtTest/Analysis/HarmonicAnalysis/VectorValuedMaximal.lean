/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.HarmonicAnalysis.VectorValuedMaximal

/-!
# Tests for the vector-valued dyadic maximal inequality

The indicators of disjoint measurable subsets of the unit interval have mixed input norm at
most one, even for infinitely many nonempty sets.
-/

open MeasureTheory Set
open scoped ENNReal

namespace MathlibExtTest.Analysis.HarmonicAnalysis.VectorValuedMaximal

open MathlibExt.Analysis.HarmonicAnalysis.DyadicMaximal
open MathlibExt.Analysis.HarmonicAnalysis.VectorValuedMaximalWanted

example {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (s : ℕ → Set ℝ) (hs : ∀ i, MeasurableSet (s i))
    (hd : Pairwise (Function.onFun Disjoint s)) (hsub : ∀ i, s i ⊆ Ico 0 1) :
    (∫⁻ x, (∑' i, dyadicMaximalFunction ((s i).indicator fun _ => (1 : ℝ)) x ^ q) ^ (p / q)) <
      ∞ := by
  classical
  let f := fun i => (s i).indicator fun _ => (1 : ℝ)
  have hq₀ := zero_lt_one.trans hq
  have hr := div_pos (zero_lt_one.trans hp) hq₀
  have hin (x) : (∑' i, ‖f i x‖ₑ ^ q) ^ (p / q) ≤
      (Ico (0 : ℝ) 1).indicator (fun _ => (1 : ℝ≥0∞)) x := by
    by_cases hx : ∃ i, x ∈ s i
    · obtain ⟨i, hi⟩ := hx
      rw [tsum_eq_single i, indicator_of_mem (hsub i hi)]
      · simp [f, indicator_of_mem hi]
      · intro j hj
        have hj' : x ∉ s j := fun h => disjoint_left.mp (hd hj) h hi
        simp [f, indicator_of_notMem hj', ENNReal.zero_rpow_of_pos hq₀]
    · have hnone (i) : x ∉ s i := fun h => hx ⟨i, h⟩
      simp [f, indicator_of_notMem (hnone _), ENNReal.zero_rpow_of_pos hq₀,
        ENNReal.zero_rpow_of_pos hr]
  obtain ⟨C, hC, h⟩ := exists_lintegral_tsum_rpow_dyadicMaximalFunction_le hp hq
  refine (h f (fun i => measurable_const.indicator (hs i))).trans_lt
    (ENNReal.mul_lt_top hC.lt_top ((lintegral_mono hin).trans_lt ?_))
  rw [lintegral_indicator measurableSet_Ico, setLIntegral_const, one_mul, Real.volume_Ico]
  exact ENNReal.ofReal_lt_top

end MathlibExtTest.Analysis.HarmonicAnalysis.VectorValuedMaximal
