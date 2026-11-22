/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.AlexandrovGeometry.ModelTrig

/- Tests for model trigonometry derivatives via the production lemmas. -/

namespace AlexandrovGeometry

/-- `cs` at zero is one, via the production lemma. -/
theorem test_modelCos_zero (κ : ℝ) : modelCos κ 0 = 1 :=
  modelCos_zero_right κ

/-- `sn` at zero is zero, via the production lemma. -/
theorem test_modelSin_zero (κ : ℝ) : modelSin κ 0 = 0 :=
  modelSin_zero_right κ

/-- `sn` derivative for `κ = 1`. -/
example (t : ℝ) : HasDerivAt (modelSin 1) (modelCos 1 t) t :=
  hasDerivAt_modelSin 1 t

/-- `sn` derivative for `κ = 0`. -/
example (t : ℝ) : HasDerivAt (modelSin 0) (modelCos 0 t) t :=
  hasDerivAt_modelSin 0 t

/-- `sn` derivative for `κ = -1`. -/
example (t : ℝ) : HasDerivAt (modelSin (-1)) (modelCos (-1) t) t :=
  hasDerivAt_modelSin (-1) t

/-- `cs` derivative for `κ = 1`. -/
example (t : ℝ) : HasDerivAt (modelCos 1) (-1 * modelSin 1 t) t :=
  hasDerivAt_modelCos 1 t

/-- `cs` derivative for `κ = 0`. -/
example (t : ℝ) : HasDerivAt (modelCos 0) (-0 * modelSin 0 t) t :=
  hasDerivAt_modelCos 0 t

/-- `cs` derivative for `κ = -1`. -/
example (t : ℝ) :
    HasDerivAt (modelCos (-1)) (-(-1) * modelSin (-1) t) t :=
  hasDerivAt_modelCos (-1) t

/-- `sn` derivative at `0` is `1` for `κ = 1`. -/
example : HasDerivAt (modelSin 1) 1 0 := by
  have h : HasDerivAt (modelSin 1) (modelCos 1 0) 0 :=
    hasDerivAt_modelSin 1 0
  rw [modelCos_zero_right] at h
  exact h

/-- `sn` derivative at `0` is `1` for `κ = 0`. -/
example : HasDerivAt (modelSin 0) 1 0 := by
  have h : HasDerivAt (modelSin 0) (modelCos 0 0) 0 :=
    hasDerivAt_modelSin 0 0
  rw [modelCos_zero_right] at h
  exact h

/-- `sn` derivative at `0` is `1` for `κ = -1`. -/
example : HasDerivAt (modelSin (-1)) 1 0 := by
  have h : HasDerivAt (modelSin (-1)) (modelCos (-1) 0) 0 :=
    hasDerivAt_modelSin (-1) 0
  rw [modelCos_zero_right] at h
  exact h

/-- `cs` derivative at `0` is `0` for `κ = 1`. -/
example : HasDerivAt (modelCos 1) 0 0 := by
  have h : HasDerivAt (modelCos 1) (-1 * modelSin 1 0) 0 :=
    hasDerivAt_modelCos 1 0
  rw [modelSin_zero_right, mul_zero] at h
  exact h

/-- `cs` derivative at `0` is `0` for `κ = 0`. -/
example : HasDerivAt (modelCos 0) 0 0 := by
  have h : HasDerivAt (modelCos 0) (-0 * modelSin 0 0) 0 :=
    hasDerivAt_modelCos 0 0
  rw [modelSin_zero_right, mul_zero] at h
  exact h

/-- `cs` derivative at `0` is `0` for `κ = -1`. -/
example : HasDerivAt (modelCos (-1)) 0 0 := by
  have h : HasDerivAt (modelCos (-1)) (-(-1) * modelSin (-1) 0) 0 :=
    hasDerivAt_modelCos (-1) 0
  rw [modelSin_zero_right, mul_zero] at h
  exact h

/-- `cs` for `κ = 4` via the positive branch lemma. -/
example (t : ℝ) : modelCos 4 t = Real.cos (2 * t) := by
  have hκ : (0 : ℝ) < 4 := by norm_num
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  have h := modelCos_of_pos hκ t
  rw [hsqrt4] at h
  exact h

/-- `sn` for `κ = 4` via the positive branch lemma. -/
example (t : ℝ) : modelSin 4 t = Real.sin (2 * t) / 2 := by
  have hκ : (0 : ℝ) < 4 := by norm_num
  have hsqrt4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  have h := modelSin_of_pos hκ t
  rw [hsqrt4] at h
  exact h

/-- `cs` for `κ = -4` via the negative branch lemma. -/
example (t : ℝ) : modelCos (-4) t = Real.cosh (2 * t) := by
  have hκ : (-4 : ℝ) < 0 := by norm_num
  have hsqrt : √(-(-4 : ℝ)) = 2 := by
    rw [show -(-4 : ℝ) = 4 by norm_num,
      show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  have h := modelCos_of_neg hκ t
  rw [hsqrt] at h
  exact h

/-- `sn` for `κ = -4` via the negative branch lemma. -/
example (t : ℝ) : modelSin (-4) t = Real.sinh (2 * t) / 2 := by
  have hκ : (-4 : ℝ) < 0 := by norm_num
  have hsqrt : √(-(-4 : ℝ)) = 2 := by
    rw [show -(-4 : ℝ) = 4 by norm_num,
      show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
  have h := modelSin_of_neg hκ t
  rw [hsqrt] at h
  exact h

/-- `cs` for `κ = 0` via the zero lemma. -/
example (t : ℝ) : modelCos 0 t = 1 :=
  modelCos_zero_left t

/-- `sn` for `κ = 0` via the zero lemma. -/
example (t : ℝ) : modelSin 0 t = t :=
  modelSin_zero_left t

/-- Wrong-branch control: `cs` for `κ = -1` is not `cos`. -/
example : modelCos (-1) 1 ≠ Real.cos (√(-1) * 1) := by
  intro hcon
  have hκ : (-1 : ℝ) < 0 := by norm_num
  have hsqrt1 : √(-(-1 : ℝ)) = 1 := by
    rw [show -(-1 : ℝ) = 1 by norm_num, Real.sqrt_one]
  have hl : modelCos (-1) 1 = Real.cosh 1 := by
    have h := modelCos_of_neg hκ 1
    rw [hsqrt1, one_mul] at h
    exact h
  have hsqrt_neg : √(-1 : ℝ) = 0 :=
    Real.sqrt_eq_zero'.mpr (by norm_num)
  have hr : Real.cos (√(-1 : ℝ) * 1) = 1 := by
    rw [hsqrt_neg, zero_mul, Real.cos_zero]
  have heq : Real.cosh (1 : ℝ) = 1 := hl.symm.trans (hcon.trans hr)
  have hlt : (1 : ℝ) < Real.cosh 1 :=
    Real.one_lt_cosh.mpr (by norm_num)
  rw [heq] at hlt
  exact absurd hlt (lt_irrefl 1)

/-- Wrong-branch control: `sn` for `κ = -1` is not `sin`. -/
example : modelSin (-1) 1 ≠ Real.sin (√(-1) * 1) / √(-1) := by
  intro hcon
  have hκ : (-1 : ℝ) < 0 := by norm_num
  have hsqrt1 : √(-(-1 : ℝ)) = 1 := by
    rw [show -(-1 : ℝ) = 1 by norm_num, Real.sqrt_one]
  have hl : modelSin (-1) 1 = Real.sinh 1 := by
    have h := modelSin_of_neg hκ 1
    rw [hsqrt1, one_mul, div_one] at h
    exact h
  have hsqrt_neg : √(-1 : ℝ) = 0 :=
    Real.sqrt_eq_zero'.mpr (by norm_num)
  have hr : Real.sin (√(-1 : ℝ) * 1) / √(-1 : ℝ) = 0 := by
    rw [hsqrt_neg, zero_mul, Real.sin_zero, zero_div]
  have heq : Real.sinh (1 : ℝ) = 0 := hl.symm.trans (hcon.trans hr)
  have hpos : (0 : ℝ) < Real.sinh 1 :=
    Real.sinh_pos_iff.mpr (by norm_num)
  rw [heq] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- Wrong-branch control: `cs` for `κ = 1` is not `cosh`. -/
example : modelCos 1 Real.pi ≠ Real.cosh (√(-1) * Real.pi) := by
  intro hcon
  have hκ : (0 : ℝ) < 1 := by norm_num
  have hl : modelCos 1 Real.pi = -1 := by
    have h := modelCos_of_pos hκ Real.pi
    rw [Real.sqrt_one, one_mul, Real.cos_pi] at h
    exact h
  have hsqrt_neg : √(-1 : ℝ) = 0 :=
    Real.sqrt_eq_zero'.mpr (by norm_num)
  have hr : Real.cosh (√(-1 : ℝ) * Real.pi) = 1 := by
    rw [hsqrt_neg, zero_mul, Real.cosh_zero]
  rw [hl, hr] at hcon
  have hlt : (-1 : ℝ) < 1 := by norm_num
  rw [hcon] at hlt
  exact absurd hlt (lt_irrefl 1)

/-- Wrong-branch control: `sn` for `κ = 1` is not `sinh`. -/
example : modelSin 1 (Real.pi / 2) ≠
    Real.sinh (√(-1) * (Real.pi / 2)) / √(-1) := by
  intro hcon
  have hκ : (0 : ℝ) < 1 := by norm_num
  have hl : modelSin 1 (Real.pi / 2) = 1 := by
    have h := modelSin_of_pos hκ (Real.pi / 2)
    rw [Real.sqrt_one, one_mul, div_one, Real.sin_pi_div_two] at h
    exact h
  have hsqrt_neg : √(-1 : ℝ) = 0 :=
    Real.sqrt_eq_zero'.mpr (by norm_num)
  have hr : Real.sinh (√(-1 : ℝ) * (Real.pi / 2)) / √(-1 : ℝ) = 0 := by
    rw [hsqrt_neg, zero_mul, Real.sinh_zero, zero_div]
  rw [hl, hr] at hcon
  exact absurd hcon (by norm_num)

/-- Derivative control: `sn` for `κ = 1` has derivative `1`, not `0`, at `0`. -/
example : ¬ HasDerivAt (modelSin 1) 0 0 := by
  intro hcon
  have h1 : HasDerivAt (modelSin 1) 1 0 := by
    have h : HasDerivAt (modelSin 1) (modelCos 1 0) 0 :=
      hasDerivAt_modelSin 1 0
    rw [modelCos_zero_right] at h
    exact h
  have heq : (0 : ℝ) = 1 := hcon.unique h1
  have hlt : (0 : ℝ) < 1 := Real.zero_lt_one
  rw [heq] at hlt
  exact absurd hlt (lt_irrefl 1)

/-- Derivative control: `cs` for `κ = -1` has derivative `sn`, not `-sn`. -/
example : ¬ HasDerivAt (modelCos (-1)) (-(modelSin (-1) 1)) 1 := by
  intro hcon
  have htrue : HasDerivAt (modelCos (-1)) (modelSin (-1) 1) 1 := by
    have h := hasDerivAt_modelCos (-1) 1
    simp only [neg_neg, one_mul] at h
    exact h
  have heq : -(modelSin (-1) 1) = modelSin (-1) 1 :=
    hcon.unique htrue
  have hκ : (-1 : ℝ) < 0 := by norm_num
  have hsqrt1 : √(-(-1 : ℝ)) = 1 := by
    rw [show -(-1 : ℝ) = 1 by norm_num, Real.sqrt_one]
  have hl : modelSin (-1) 1 = Real.sinh 1 := by
    have h := modelSin_of_neg hκ 1
    rw [hsqrt1, one_mul, div_one] at h
    exact h
  have hpos : (0 : ℝ) < Real.sinh 1 :=
    Real.sinh_pos_iff.mpr (by norm_num)
  rw [hl] at heq
  have hneg_pos : (0 : ℝ) < -(Real.sinh 1) := by
    rw [heq]
    exact hpos
  have hlt : Real.sinh (1 : ℝ) < 0 := neg_pos.mp hneg_pos
  have h0lt0 : (0 : ℝ) < 0 := lt_trans hpos hlt
  exact absurd h0lt0 (lt_irrefl 0)

/-- Derivative control: `cs` for `κ = 0` never has derivative `1`. -/
example (t : ℝ) : ¬ HasDerivAt (modelCos 0) 1 t := by
  intro hcon
  have htrue : HasDerivAt (modelCos 0) 0 t := by
    have h := hasDerivAt_modelCos 0 t
    simp only [neg_zero, zero_mul] at h
    exact h
  have heq : (1 : ℝ) = 0 := hcon.unique htrue
  have hlt : (0 : ℝ) < 1 := Real.zero_lt_one
  rw [heq] at hlt
  exact absurd hlt (lt_irrefl 0)

end AlexandrovGeometry
