/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.SupportingGradient
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Convex.Mul

/-!
# Tests for supporting-gradient optimality certificates

`y ^ 2` on `[1, 3]` has a boundary minimum at `1` where the derivative is `2`, not `0`; for the
nonconvex `y ^ 3` on `[-1, 1]` the derivative at `0` is nonnegative in every feasible direction
but `0` is not a minimizer.
-/

@[expose] public section

namespace MathlibExtTest.Analysis.Convex.SupportingGradient

theorem sq_isMinOn : IsMinOn (fun y : ℝ => y ^ 2) (Set.Icc (1 : ℝ) 3) 1 := by
  have hconv : ConvexOn ℝ Set.univ (fun y : ℝ => y ^ 2) := Even.convexOn_pow even_two
  have hf : ConvexOn ℝ (Set.Icc (1 : ℝ) 3) (fun y : ℝ => y ^ 2) :=
    hconv.subset (Set.subset_univ _) (convex_Icc 1 3)
  have hx : (1 : ℝ) ∈ Set.Icc (1 : ℝ) 3 := by norm_num [Set.mem_Icc]
  have hd : DifferentiableAt ℝ (fun y : ℝ => y ^ 2) 1 :=
    (hasDerivAt_pow 2 (1 : ℝ)).differentiableAt
  have h2val : ((2 : ℕ) : ℝ) * (1 : ℝ) ^ ((2 : ℕ) - 1) = 2 := by simp
  have hderiv : HasDerivAt (fun y : ℝ => y ^ 2) 2 (1 : ℝ) := by
    have h := hasDerivAt_pow 2 (1 : ℝ)
    rw [h2val] at h
    exact h
  have hfderiv : fderiv ℝ (fun y : ℝ => y ^ 2) 1 =
      ContinuousLinearMap.toSpanSingleton ℝ 2 :=
    hderiv.hasFDerivAt.fderiv
  have hdir : ∀ y ∈ Set.Icc (1 : ℝ) 3, 0 ≤ fderiv ℝ (fun y : ℝ => y ^ 2) 1 (y - 1) := by
    intro y hy
    rw [hfderiv, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    have hy1 : (1 : ℝ) ≤ y := (Set.mem_Icc.mp hy).1
    exact mul_nonneg (sub_nonneg.mpr hy1) zero_le_two
  exact MathlibExt.SupportingGradient.isMinOn_of_convexOn_of_fderiv_nonneg hf hx hd hdir

theorem cube_directional_nonneg :
    ∀ y ∈ Set.Icc (-1 : ℝ) 1, 0 ≤ fderiv ℝ (fun y : ℝ => y ^ 3) 0 (y - 0) := by
  have h3val : ((3 : ℕ) : ℝ) * (0 : ℝ) ^ ((3 : ℕ) - 1) = 0 := by simp
  have h0 : HasDerivAt (fun y : ℝ => y ^ 3) 0 (0 : ℝ) := by
    have h := hasDerivAt_pow 3 (0 : ℝ)
    rw [h3val] at h
    exact h
  have hf0 : fderiv ℝ (fun y : ℝ => y ^ 3) 0 =
      ContinuousLinearMap.toSpanSingleton ℝ 0 :=
    h0.hasFDerivAt.fderiv
  intro y _
  simp [hf0]

theorem cube_not_min : ¬ IsMinOn (fun y : ℝ => y ^ 3) (Set.Icc (-1 : ℝ) 1) 0 := by
  intro hmin
  rw [isMinOn_iff] at hmin
  have hmem : (-1 / 2 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by norm_num [Set.mem_Icc]
  have hle := hmin _ hmem
  norm_num at hle

end MathlibExtTest.Analysis.Convex.SupportingGradient
