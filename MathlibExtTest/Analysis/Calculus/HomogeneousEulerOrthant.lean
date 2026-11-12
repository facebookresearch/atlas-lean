/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Calculus.HomogeneousEulerOrthant

/-!
# Tests for Euler's identity on the positive orthant

The Cobb–Douglas function `x₀ ^ (1/2) * x₁ ^ (1/4)` is homogeneous of degree `3/4` and its Euler sum
at `(4, 16)` is `3`; the ratio `x₀ / x₁` is homogeneous of degree `0` and its Euler sum is `0`.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Calculus.HomogeneousEulerOrthant

open _root_.MetaMathlibExt

noncomputable def cobbDouglas : (Fin 2 → ℝ) → ℝ :=
  fun x => x 0 ^ (1/2 : ℝ) * x 1 ^ (1/4 : ℝ)

theorem differentiableAt_proj (x : Fin 2 → ℝ) (i : Fin 2) :
    DifferentiableAt ℝ (fun x : Fin 2 → ℝ => x i) x := by
  have hfun : (fun x : Fin 2 → ℝ => x i)
      = ⇑(ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i) := by
    funext y
    simp
  rw [hfun]
  exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).differentiableAt

theorem cobbDouglas_homogeneous : IsHomogeneousOnPosOrthant (3/4 : ℝ) cobbDouglas := by
  intro x hx t ht
  simp only [cobbDouglas, Pi.smul_apply, smul_eq_mul]
  rw [Real.mul_rpow (le_of_lt ht) (le_of_lt (hx 0)),
    Real.mul_rpow (le_of_lt ht) (le_of_lt (hx 1))]
  have hr : (1/2 : ℝ) + 1/4 = 3/4 := by norm_num
  have h := Real.rpow_add ht (1/2 : ℝ) (1/4 : ℝ)
  rw [hr] at h
  rw [h]
  ring

theorem rpow_half_four : (4 : ℝ) ^ (1/2 : ℝ) = 2 := by
  have e : ((2 : ℕ) : ℝ) * (1/2) = 1 := by norm_num
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), e, Real.rpow_one]

theorem rpow_quarter_sixteen : (16 : ℝ) ^ (1/4 : ℝ) = 2 := by
  have e : ((4 : ℕ) : ℝ) * (1/4) = 1 := by norm_num
  rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), e, Real.rpow_one]

theorem cobbDouglas_at : cobbDouglas ![4, 16] = 4 := by
  have v0 : (![4, 16] : Fin 2 → ℝ) 0 = 4 := by simp
  have v1 : (![4, 16] : Fin 2 → ℝ) 1 = 16 := by simp
  simp only [cobbDouglas, v0, v1, rpow_half_four, rpow_quarter_sixteen]
  norm_num

theorem cobbDouglas_pos : ∀ i, 0 < (![4, 16] : Fin 2 → ℝ) i := by
  intro i
  fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem cobbDouglas_differentiable : DifferentiableAt ℝ cobbDouglas ![4, 16] := by
  have v0 : (![4, 16] : Fin 2 → ℝ) 0 = 4 := by simp
  have v1 : (![4, 16] : Fin 2 → ℝ) 1 = 16 := by simp
  have h4ne : (![4, 16] : Fin 2 → ℝ) 0 ≠ 0 := by rw [v0]; norm_num
  have h16ne : (![4, 16] : Fin 2 → ℝ) 1 ≠ 0 := by rw [v1]; norm_num
  have hrpow0 :
      DifferentiableAt ℝ (fun y : ℝ => y ^ (1/2 : ℝ)) ((![4, 16] : Fin 2 → ℝ) 0) :=
    (Real.hasDerivAt_rpow_const (x := ((![4, 16] : Fin 2 → ℝ) 0)) (p := (1/2 : ℝ))
      (Or.inl h4ne)).differentiableAt
  have hrpow1 :
      DifferentiableAt ℝ (fun y : ℝ => y ^ (1/4 : ℝ)) ((![4, 16] : Fin 2 → ℝ) 1) :=
    (Real.hasDerivAt_rpow_const (x := ((![4, 16] : Fin 2 → ℝ) 1)) (p := (1/4 : ℝ))
      (Or.inl h16ne)).differentiableAt
  have hd0 : DifferentiableAt ℝ (fun x : Fin 2 → ℝ => x 0 ^ (1/2 : ℝ)) ![4, 16] :=
    DifferentiableAt.comp (x := ((![4, 16] : Fin 2 → ℝ))) (f := (fun x : Fin 2 → ℝ => x 0))
      (g := (fun y : ℝ => y ^ (1/2 : ℝ))) hrpow0 (differentiableAt_proj _ 0)
  have hd1 : DifferentiableAt ℝ (fun x : Fin 2 → ℝ => x 1 ^ (1/4 : ℝ)) ![4, 16] :=
    DifferentiableAt.comp (x := ((![4, 16] : Fin 2 → ℝ))) (f := (fun x : Fin 2 → ℝ => x 1))
      (g := (fun y : ℝ => y ^ (1/4 : ℝ))) hrpow1 (differentiableAt_proj _ 1)
  have h :
      DifferentiableAt ℝ (fun x : Fin 2 → ℝ => x 0 ^ (1/2 : ℝ) * x 1 ^ (1/4 : ℝ))
        ![4, 16] :=
    hd0.mul hd1
  exact h

theorem cobbDouglas_euler_sum :
    ∑ i, (![4, 16] : Fin 2 → ℝ) i * fderiv ℝ cobbDouglas ![4, 16] (Pi.single i 1)
      = 3 := by
  have hsum :=
    cobbDouglas_homogeneous.sum_mul_fderiv_single (x := ![4, 16]) cobbDouglas_pos
      cobbDouglas_differentiable
  rw [cobbDouglas_at, show (3/4 : ℝ) * 4 = 3 by norm_num] at hsum
  exact hsum

noncomputable def ratioFunc : (Fin 2 → ℝ) → ℝ := fun x => x 0 / x 1

theorem ratioFunc_homogeneous : IsHomogeneousOnPosOrthant (0 : ℝ) ratioFunc := by
  intro x hx t ht
  simp only [ratioFunc, Pi.smul_apply, smul_eq_mul]
  rw [Real.rpow_zero, one_mul]
  exact mul_div_mul_left _ _ (ne_of_gt ht)

theorem ratioFunc_pos : ∀ i, 0 < (![1, 2] : Fin 2 → ℝ) i := by
  intro i
  fin_cases i <;> norm_num [Matrix.cons_val_zero, Matrix.cons_val_one]

theorem ratioFunc_differentiable : DifferentiableAt ℝ ratioFunc ![1, 2] := by
  have v1 : (![1, 2] : Fin 2 → ℝ) 1 = 2 := by simp
  have h1ne : (![1, 2] : Fin 2 → ℝ) 1 ≠ 0 := by rw [v1]; norm_num
  have h : DifferentiableAt ℝ (fun x : Fin 2 → ℝ => x 0 * (x 1)⁻¹) ![1, 2] :=
    (differentiableAt_proj _ 0).mul ((differentiableAt_proj _ 1).inv h1ne)
  show DifferentiableAt ℝ (fun x : Fin 2 → ℝ => x 0 / x 1) ![1, 2]
  simpa [div_eq_mul_inv] using h

theorem ratioFunc_euler_sum :
    ∑ i, (![1, 2] : Fin 2 → ℝ) i * fderiv ℝ ratioFunc ![1, 2] (Pi.single i 1)
      = 0 := by
  have hsum :=
    ratioFunc_homogeneous.sum_mul_fderiv_single (x := ![1, 2]) ratioFunc_pos
      ratioFunc_differentiable
  rw [zero_mul] at hsum
  exact hsum

end MathlibExtTest.Analysis.Calculus.HomogeneousEulerOrthant
