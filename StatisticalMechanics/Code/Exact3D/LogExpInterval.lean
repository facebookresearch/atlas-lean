/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Exact3D.LogExpBounds
import Code.Exact3D.Intervals








namespace StatMech
namespace Exact3D
namespace RatInterval


def Positive (I : RatInterval) : Prop :=
  0 < I.lower


theorem point_positive {q : ℚ} (hq : 0 < q) : (point q).Positive := by
  simpa [Positive, point] using hq

theorem lower_pos_real_of_positive {I : RatInterval} (hI : I.Positive) :
    (0 : ℝ) < (I.lower : ℝ) := by
  exact_mod_cast hI


theorem pos_of_positive_memR {I : RatInterval} {x : ℝ}
    (hI : I.Positive) (hx : I.MemR x) :
    0 < x :=
  lt_of_lt_of_le (lower_pos_real_of_positive hI) hx.1


def invPositive (I : RatInterval) (hI : I.Positive) : RatInterval where
  lower := 1 / I.upper
  upper := 1 / I.lower
  lower_le_upper := by
    have hl : (0 : ℚ) < I.lower := hI
    exact one_div_le_one_div_of_le hl I.lower_le_upper


theorem invPositive_positive {I : RatInterval} (hI : I.Positive) :
    (invPositive I hI).Positive := by
  have hupper : (0 : ℚ) < I.upper := lt_of_lt_of_le hI I.lower_le_upper
  exact one_div_pos.mpr hupper


theorem invPositive_nonnegative {I : RatInterval} (hI : I.Positive) :
    (invPositive I hI).Nonnegative :=
  (invPositive_positive hI).le


theorem invPositive_memR {I : RatInterval} (hI : I.Positive)
    {x : ℝ} (hx : I.MemR x) :
    (invPositive I hI).MemR x⁻¹ := by
  have hIl : (0 : ℝ) < (I.lower : ℝ) := lower_pos_real_of_positive hI
  have hxpos : 0 < x := pos_of_positive_memR hI hx
  constructor
  · have hxu : x ≤ (I.upper : ℝ) := hx.2
    have h := one_div_le_one_div_of_le hxpos hxu
    simpa [invPositive, one_div] using h
  · have hxl : (I.lower : ℝ) ≤ x := hx.1
    have h := one_div_le_one_div_of_le hIl hxl
    simpa [invPositive, one_div] using h


def divPositive (I J : RatInterval) (hJ : J.Positive) : RatInterval :=
  mul I (invPositive J hJ)



theorem divPositive_memR {I J : RatInterval} (hJ : J.Positive)
    {x y : ℝ} (hx : I.MemR x) (hy : J.MemR y) :
    (divPositive I J hJ).MemR (x / y) := by
  simpa [divPositive, div_eq_mul_inv] using mul_memR hx (invPositive_memR hJ hy)



def divNonnegPositive (I J : RatInterval)
    (hI : I.Nonnegative) (hJ : J.Positive) : RatInterval :=
  mulNonneg I (invPositive J hJ) hI (invPositive_nonnegative hJ)



theorem divNonnegPositive_memR {I J : RatInterval}
    (hI : I.Nonnegative) (hJ : J.Positive)
    {x y : ℝ} (hx : I.MemR x) (hy : J.MemR y) :
    (divNonnegPositive I J hI hJ).MemR (x / y) := by
  simpa [divNonnegPositive, div_eq_mul_inv] using
    mulNonneg_memR hI (invPositive_nonnegative hJ) hx (invPositive_memR hJ hy)



theorem log_le_of_memR_upper_le_logUpperBound {I : RatInterval} {x u v : ℝ}
    (hx : I.MemR x) (hx_pos : 0 < x) (hIu : (I.upper : ℝ) ≤ u)
    (huv : LogUpperBound u v) :
    Real.log x ≤ v :=
  log_le_of_le_of_log_le hx_pos (le_trans hx.2 hIu) huv.bound



theorem log_le_of_positive_memR_upper_le_logUpperBound
    {I : RatInterval} {x u v : ℝ}
    (hI : I.Positive) (hx : I.MemR x) (hIu : (I.upper : ℝ) ≤ u)
    (huv : LogUpperBound u v) :
    Real.log x ≤ v :=
  log_le_of_memR_upper_le_logUpperBound hx (pos_of_positive_memR hI hx) hIu huv


theorem log_le_of_memR_upper_le_ratLogUpperBound
    {I : RatInterval} {x : ℝ} {u v : ℚ}
    (hx : I.MemR x) (hx_pos : 0 < x) (hIu : I.upper ≤ u)
    (huv : RatLogUpperBound u v) :
    Real.log x ≤ (v : ℝ) :=
  log_le_of_memR_upper_le_logUpperBound hx hx_pos (by exact_mod_cast hIu) huv



theorem log_le_of_positive_memR_upper_le_ratLogUpperBound
    {I : RatInterval} {x : ℝ} {u v : ℚ}
    (hI : I.Positive) (hx : I.MemR x) (hIu : I.upper ≤ u)
    (huv : RatLogUpperBound u v) :
    Real.log x ≤ (v : ℝ) :=
  log_le_of_memR_upper_le_ratLogUpperBound hx (pos_of_positive_memR hI hx) hIu huv



theorem le_log_of_logLowerBound_le_lower_memR
    {I : RatInterval} {x l a : ℝ}
    (hla : LogLowerBound l a) (haI : a ≤ (I.lower : ℝ)) (hx : I.MemR x) :
    l ≤ Real.log x :=
  le_log_of_le_of_le_log hla.x_pos (le_trans haI hx.1) hla.bound


theorem le_log_of_ratLogLowerBound_le_lower_memR
    {I : RatInterval} {x : ℝ} {l a : ℚ}
    (hla : RatLogLowerBound l a) (haI : a ≤ I.lower) (hx : I.MemR x) :
    (l : ℝ) ≤ Real.log x :=
  le_log_of_logLowerBound_le_lower_memR hla (by exact_mod_cast haI) hx



theorem exp_le_of_memR_upper_le_expUpperBound
    {I : RatInterval} {x u r : ℝ}
    (hx : I.MemR x) (hIu : (I.upper : ℝ) ≤ u)
    (hur : ExpUpperBound u r) :
    Real.exp x ≤ r :=
  le_trans (Real.exp_le_exp.mpr (le_trans hx.2 hIu)) hur.bound


theorem exp_le_of_memR_upper_le_ratExpUpperBound
    {I : RatInterval} {x : ℝ} {u r : ℚ}
    (hx : I.MemR x) (hIu : I.upper ≤ u)
    (hur : RatExpUpperBound u r) :
    Real.exp x ≤ (r : ℝ) :=
  exp_le_of_memR_upper_le_expUpperBound hx (by exact_mod_cast hIu) hur



theorem exp_lower_le_exp_of_lower_le_memR
    {I : RatInterval} {x l : ℝ}
    (hlI : l ≤ (I.lower : ℝ)) (hx : I.MemR x) :
    Real.exp l ≤ Real.exp x :=
  Real.exp_le_exp.mpr (le_trans hlI hx.1)


theorem rat_exp_lower_le_exp_of_lower_le_memR
    {I : RatInterval} {x : ℝ} {l : ℚ}
    (hlI : l ≤ I.lower) (hx : I.MemR x) :
    Real.exp (l : ℝ) ≤ Real.exp x :=
  exp_lower_le_exp_of_lower_le_memR (by exact_mod_cast hlI) hx

end RatInterval
end Exact3D
end StatMech
