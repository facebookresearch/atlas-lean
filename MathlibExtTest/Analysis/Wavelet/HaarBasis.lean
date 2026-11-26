/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Wavelet.HaarBasis

open MeasureTheory Set
open MathlibExt.Analysis.Wavelet.Haar
open MathlibExt.Analysis.Wavelet.HaarBasisWanted

-- Completeness in integral form: a function in `L²(ℝ)` whose integral against every Haar
-- function vanishes is zero.
example (f : Lp ℝ 2 (volume : Measure ℝ)) (hf : ∀ j k : ℤ, ∫ x, haarSystem j k x * f x = 0) :
    f = 0 := by
  obtain ⟨b, hb⟩ := exists_hilbertBasis_haarSystem
  have hcoef (jk : ℤ × ℤ) : b.repr f jk = 0 := by
    rw [HilbertBasis.repr_apply_apply, L2.inner_def, ← hf jk.1 jk.2]
    apply integral_congr_ae
    filter_upwards [hb jk] with x hx
    simp [hx, RCLike.inner_apply, mul_comm]
  have hsum := b.hasSum_repr f
  simp only [hcoef, zero_smul] at hsum
  exact hsum.unique hasSum_zero

-- A coarse scale, which replaces the constant function of the unit-interval basis: the element
-- of index `(-1, 0)` is `2^{-1/2} (1_{[0,1)} - 1_{[1,2)})`.
example : ∃ b : HilbertBasis (ℤ × ℤ) ℝ (Lp ℝ 2 (volume : Measure ℝ)),
    b (-1, 0) = (2 : ℝ) ^ ((-1 : ℝ) / 2) •
      (indicatorConstLp 2 (measurableSet_Ico (a := (0 : ℝ)) (b := 1)) measure_Ico_lt_top.ne
          (1 : ℝ) -
        indicatorConstLp 2 (measurableSet_Ico (a := (1 : ℝ)) (b := 2)) measure_Ico_lt_top.ne
          (1 : ℝ)) := by
  obtain ⟨b, hb⟩ := exists_hilbertBasis_haarSystem
  refine ⟨b, Lp.ext ?_⟩
  filter_upwards [hb (-1, 0), Lp.coeFn_smul ((2 : ℝ) ^ ((-1 : ℝ) / 2))
      (indicatorConstLp 2 (measurableSet_Ico (a := (0 : ℝ)) (b := 1)) measure_Ico_lt_top.ne
          (1 : ℝ) -
        indicatorConstLp 2 (measurableSet_Ico (a := (1 : ℝ)) (b := 2)) measure_Ico_lt_top.ne
          (1 : ℝ)),
    Lp.coeFn_sub
      (indicatorConstLp 2 (measurableSet_Ico (a := (0 : ℝ)) (b := 1)) measure_Ico_lt_top.ne
        (1 : ℝ))
      (indicatorConstLp 2 (measurableSet_Ico (a := (1 : ℝ)) (b := 2)) measure_Ico_lt_top.ne
        (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (μ := volume) (s := Ico (0 : ℝ) 1)
      (hs := measurableSet_Ico) (hμs := measure_Ico_lt_top.ne) (c := (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (μ := volume) (s := Ico (1 : ℝ) 2)
      (hs := measurableSet_Ico) (hμs := measure_Ico_lt_top.ne) (c := (1 : ℝ))]
    with x hx hsmul hsub h1 h2
  rw [hx, hsmul, Pi.smul_apply, hsub, Pi.sub_apply, h1, h2, smul_eq_mul, haarSystem]
  have hy : (2 : ℝ) ^ (-1 : ℤ) * x - ((0 : ℤ) : ℝ) = x / 2 := by
    rw [zpow_neg_one, Int.cast_zero, sub_zero, inv_mul_eq_div]
  rw [hy, show (((-1 : ℤ) : ℝ) / 2) = (-1 : ℝ) / 2 by push_cast; ring]
  congr 1
  by_cases h0 : x ∈ Ico (0 : ℝ) 1
  · have h1' : x ∉ Ico (1 : ℝ) 2 := fun h => by linarith [h.1, h0.2]
    rw [indicator_of_mem h0, indicator_of_notMem h1',
      haarFunction_eq_one ⟨by linarith [h0.1], by linarith [h0.2]⟩]
    norm_num
  · by_cases h1' : x ∈ Ico (1 : ℝ) 2
    · rw [indicator_of_notMem h0, indicator_of_mem h1',
        haarFunction_eq_neg_one ⟨by linarith [h1'.1], by linarith [h1'.2]⟩]
      norm_num
    · have hout : x / 2 ∉ Ico (0 : ℝ) 1 := by
        rintro ⟨hl, hr⟩
        rcases lt_or_ge x 1 with hx1 | hx1
        · exact h0 ⟨by linarith, hx1⟩
        · exact h1' ⟨hx1, by linarith⟩
      rw [indicator_of_notMem h0, indicator_of_notMem h1', haarFunction_eq_zero hout]
      norm_num
