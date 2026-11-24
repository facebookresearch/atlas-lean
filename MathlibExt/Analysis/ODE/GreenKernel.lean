/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section

/-!
# Two-solution Green kernels on the line

This file packages the elementary two-solution formula for a one-dimensional
Green kernel. Given a left solution `u`, a right solution `v`, and a
left-branch coefficient `C`, the kernel is

`G(x, y) = C y * u x` for `x ≤ y`, and
`G(x, y) = C y * (u y / v y) * v x` for `y < x`.

The coefficient is left abstract: `C y` is the entire left-branch coefficient.
In Sturm-Liouville examples it may absorb `v y`, the Wronskian, and the
operator's leading coefficient; it is not by itself a reciprocal Wronskian.
The point of the file is the reusable analytic bookkeeping that follows from
the formula alone: branch values, agreement of the right branch on the
diagonal, positivity, continuity across the diagonal, one-sided derivatives,
and the derivative jump in Wronskian form.

For the Dirichlet Laplacian on `[0, 1]`, taking `u x = x`, `v x = 1 - x`, and
`C y = 1 - y` gives `min x y * (1 - max x y)`. The same shape also covers the
neutral Wright-Fisher sojourn kernel and Patterson's killed Wright-Fisher
kernel in `Domains.Biology.PopulationGenetics.Diffusion`.

## Main results

* `GreenKernel.kernel_of_le`, `GreenKernel.kernel_of_lt`: the two branches.
* `GreenKernel.kernel_self_eq_right`: the right branch has the diagonal value.
* `GreenKernel.continuousAt_kernel_diagonal`: continuity in the first variable
  across `x = y`.
* `GreenKernel.hasDerivWithinAt_kernel_Iic`,
  `GreenKernel.hasDerivWithinAt_kernel_Ici`: one-sided derivatives at the
  diagonal.
* `GreenKernel.derivWithin_kernel_jump_wronskian`: the derivative jump is
  `C y * wronskian u v y / v y`.
-/

open Filter Set
open scoped Topology

namespace GreenKernel

/-- The two-solution Green kernel with left solution `u`, right solution `v`,
and left-branch coefficient `C`: for `x ≤ y` it is `C y * u x`, and for `y < x` it is
`C y * (u y / v y) * v x`. The right branch is normalized so that it agrees with
the left branch at `x = y` whenever `v y ≠ 0`. -/
noncomputable def kernel (u v C : ℝ → ℝ) (x y : ℝ) : ℝ :=
  if x ≤ y then C y * u x else C y * (u y / v y) * v x

/-- The Wronskian `u v' - u' v` of two real functions, matching the determinant
convention `det [[u, v], [u', v']]`. -/
noncomputable def wronskian (u v : ℝ → ℝ) (x : ℝ) : ℝ :=
  u x * deriv v x - deriv u x * v x

/-- The left branch of the two-solution Green kernel. -/
theorem kernel_of_le {u v C : ℝ → ℝ} {x y : ℝ} (hxy : x ≤ y) :
    kernel u v C x y = C y * u x := by
  unfold kernel
  rw [ite_eq_left hxy]

/-- The right branch of the two-solution Green kernel. -/
theorem kernel_of_lt {u v C : ℝ → ℝ} {x y : ℝ} (hxy : y < x) :
    kernel u v C x y = C y * (u y / v y) * v x := by
  unfold kernel
  rw [ite_eq_right (not_le.mpr hxy)]

/-- The diagonal value is given by the left branch. -/
theorem kernel_self {u v C : ℝ → ℝ} {y : ℝ} :
    kernel u v C y y = C y * u y :=
  kernel_of_le le_rfl

/-- The right-branch expression also gives the diagonal value when `v y ≠ 0`. -/
theorem kernel_self_eq_right {u v C : ℝ → ℝ} {y : ℝ} (hv : v y ≠ 0) :
    kernel u v C y y = C y * (u y / v y) * v y := by
  rw [kernel_self]
  field_simp

/-- Positivity of the kernel from positivity of the normalization and the two
solutions at the relevant points. -/
theorem kernel_pos {u v C : ℝ → ℝ} {x y : ℝ} (hC : 0 < C y) (hux : 0 < u x)
    (huy : 0 < u y) (hvy : 0 < v y) (hvx : 0 < v x) :
    0 < kernel u v C x y := by
  by_cases h : x ≤ y
  · rw [kernel_of_le h]
    exact mul_pos hC hux
  · rw [kernel_of_lt (not_le.mp h)]
    exact mul_pos (mul_pos hC (div_pos huy hvy)) hvx

private theorem eventuallyEq_kernel_left {u v C : ℝ → ℝ} {y : ℝ} :
    (fun x => kernel u v C x y) =ᶠ[𝓝[Iic y] y] fun x => C y * u x := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  exact kernel_of_le hz

private theorem eventuallyEq_kernel_right {u v C : ℝ → ℝ} {y : ℝ} (hv : v y ≠ 0) :
    (fun x => kernel u v C x y) =ᶠ[𝓝[Ici y] y]
      fun x => C y * (u y / v y) * v x := by
  filter_upwards [self_mem_nhdsWithin] with z hz
  rcases hz.eq_or_lt with rfl | h
  · exact kernel_self_eq_right hv
  · exact kernel_of_lt h

/-- Left derivative of the Green kernel at the diagonal. -/
theorem hasDerivWithinAt_kernel_Iic {u v C : ℝ → ℝ} {y u' : ℝ}
    (hu : HasDerivAt u u' y) :
    HasDerivWithinAt (fun x => kernel u v C x y) (C y * u') (Iic y) y := by
  have hbr := (hu.const_mul (C y)).hasDerivWithinAt (s := Iic y)
  exact hbr.congr_of_eventuallyEq_of_mem eventuallyEq_kernel_left
    (mem_Iic.mpr le_rfl)

/-- Right derivative of the Green kernel at the diagonal. -/
theorem hasDerivWithinAt_kernel_Ici {u v C : ℝ → ℝ} {y v' : ℝ}
    (hv : HasDerivAt v v' y) (hvy : v y ≠ 0) :
    HasDerivWithinAt (fun x => kernel u v C x y)
      (C y * (u y / v y) * v') (Ici y) y := by
  have hbr := (hv.const_mul (C y * (u y / v y))).hasDerivWithinAt (s := Ici y)
  exact hbr.congr_of_eventuallyEq_of_mem (eventuallyEq_kernel_right hvy)
    (mem_Ici.mpr le_rfl)

/-- The Green kernel is continuous in its first variable across the diagonal. -/
theorem continuousAt_kernel_diagonal {u v C : ℝ → ℝ} {y : ℝ}
    (hu : ContinuousAt u y) (hv : ContinuousAt v y) (hvy : v y ≠ 0) :
    ContinuousAt (fun x => kernel u v C x y) y := by
  have hL : ContinuousWithinAt (fun x => kernel u v C x y) (Iic y) y := by
    have hT : Tendsto (fun x => kernel u v C x y) (𝓝[Iic y] y)
        (𝓝 (C y * u y)) :=
      (hu.const_mul (C y)).continuousWithinAt.congr' eventuallyEq_kernel_left.symm
    rwa [← kernel_self] at hT
  have hR : ContinuousWithinAt (fun x => kernel u v C x y) (Ici y) y := by
    have hT : Tendsto (fun x => kernel u v C x y) (𝓝[Ici y] y)
        (𝓝 (C y * (u y / v y) * v y)) :=
      (hv.const_mul (C y * (u y / v y))).continuousWithinAt.congr'
        (eventuallyEq_kernel_right hvy).symm
    rwa [← kernel_self_eq_right hvy] at hT
  have h := hL.union hR
  rwa [Set.Iic_union_Ici, continuousWithinAt_univ] at h

/-- Derivative jump of the Green kernel at the diagonal, in unfolded form. -/
theorem derivWithin_kernel_jump {u v C : ℝ → ℝ} {y : ℝ}
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) (hvy : v y ≠ 0) :
    derivWithin (fun x => kernel u v C x y) (Ici y) y -
        derivWithin (fun x => kernel u v C x y) (Iic y) y =
      C y * (u y / v y * deriv v y - deriv u y) := by
  rw [(hasDerivWithinAt_kernel_Ici hv.hasDerivAt hvy).derivWithin
      (uniqueDiffWithinAt_Ici y),
    (hasDerivWithinAt_kernel_Iic hu.hasDerivAt).derivWithin
      (uniqueDiffWithinAt_Iic y)]
  ring

/-- Derivative jump of the Green kernel at the diagonal, in Wronskian form. -/
theorem derivWithin_kernel_jump_wronskian {u v C : ℝ → ℝ} {y : ℝ}
    (hu : DifferentiableAt ℝ u y) (hv : DifferentiableAt ℝ v y) (hvy : v y ≠ 0) :
    derivWithin (fun x => kernel u v C x y) (Ici y) y -
        derivWithin (fun x => kernel u v C x y) (Iic y) y =
      C y * wronskian u v y / v y := by
  rw [derivWithin_kernel_jump hu hv hvy]
  unfold wronskian
  field_simp

end GreenKernel
