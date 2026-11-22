/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.RCLike.Lemmas

/-!
# Backward error and distance to singularity in the 2-norm

Two rank-one perturbation results of the perturbation theory of linear systems, both stated for
the operator norm induced by an inner product (the matrix 2-norm), from J. W. Demmel's Math 221
course (UC Berkeley, Lecture 3 notes of 10 September 2024,
https://people.eecs.berkeley.edu/~demmel/ma221_Fall24/Lectures/Lecture_03.txt):

* `isLeast_norm_backward_error`: **backward error of an approximate solution.** For `x̂ ≠ 0`
  with residual `r = A x̂ - b`, the smallest `‖E‖` such that `(A + E) x̂ = b` is `‖r‖ / ‖x̂‖`.
  So a small residual means that `x̂` exactly solves a nearby system; the lower bound
  `‖r‖ ≤ ‖E‖ ‖x̂‖` holds in every norm, and the 2-norm attains it with
  `E = -r x̂* / ‖x̂‖²` (J. L. Rigal and J. Gaches, J. ACM 14 (1967), 543–548).
* `isLeast_norm_of_not_isUnit_sub`: **distance to the nearest singular operator.** On a nonzero
  finite-dimensional inner product space, the smallest `‖E‖` such that `A - E` is singular is
  `1 / ‖A⁻¹‖`; dividing by `‖A‖`, the relative distance from `A` to the singular matrices is
  `1 / κ(A)` with `κ(A) = ‖A‖ ‖A⁻¹‖`.
-/

@[expose] public section

namespace MathlibExt.Analysis.InnerProductSpace.LinearSystemBackwardError

open MathlibExt.Analysis.Normed.Operator.LinearSystemPerturbation

variable {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- The rank-one operator `v ↦ ‖x‖⁻² ⟪x, v⟫ y`, written with Mathlib's
`InnerProductSpace.rankOne`; it maps `x` to `y` and has norm `‖y‖ / ‖x‖`. -/
private noncomputable abbrev rankOneTo (x y : F) : F →L[𝕜] F :=
  (((‖x‖ ^ 2 : ℝ) : 𝕜)⁻¹) • InnerProductSpace.rankOne 𝕜 y x

private theorem rankOneTo_apply_self {x : F} (hx : x ≠ 0) (y : F) :
    rankOneTo (𝕜 := 𝕜) x y x = y := by
  have hx' : ((‖x‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    have : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
    exact_mod_cast this.ne'
  simp only [rankOneTo, smul_apply, InnerProductSpace.rankOne_apply,
    inner_self_eq_norm_sq_to_K, smul_smul]
  rw [show ((‖x‖ : 𝕜) ^ 2) = ((‖x‖ ^ 2 : ℝ) : 𝕜) by push_cast; rfl, inv_mul_cancel₀ hx', one_smul]

private theorem norm_rankOneTo {x : F} (hx : x ≠ 0) (y : F) :
    ‖rankOneTo (𝕜 := 𝕜) x y‖ = ‖y‖ / ‖x‖ := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  rw [rankOneTo, norm_smul, InnerProductSpace.norm_rankOne, norm_inv, RCLike.norm_ofReal,
    abs_of_pos (by positivity)]
  field_simp

/-- **Backward error of an approximate solution.** For an operator `A` on an inner product
space, `b`, and `x̂ ≠ 0` with residual `r = A x̂ - b`, the least `‖E‖` over all `E` with
`(A + E) x̂ = b` is `‖r‖ / ‖x̂‖` (Demmel, Math 221 Lecture 3 notes, 2024: "The smallest `E` such
that `(A+E)x' = b` has `norm(E) = norm(r)/norm(x')`", in the 2-norm; Rigal and Gaches 1967). -/
theorem isLeast_norm_backward_error (A : F →L[𝕜] F) (b : F) {x : F} (hx : x ≠ 0) :
    IsLeast {t : ℝ | ∃ E : F →L[𝕜] F, (A + E) x = b ∧ ‖E‖ = t} (‖A x - b‖ / ‖x‖) := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  refine ⟨⟨rankOneTo x (-(A x - b)), ?_, ?_⟩, ?_⟩
  · rw [add_apply, rankOneTo_apply_self hx]
    abel
  · rw [norm_rankOneTo hx, norm_neg]
  · rintro t ⟨E, hE, rfl⟩
    rw [div_le_iff₀ hxpos]
    have hr : A x - b = -(E x) := by
      rw [add_apply] at hE
      rw [← hE]
      abel
    rw [hr, norm_neg]
    exact E.le_opNorm x

/-- **Distance to the nearest singular operator.** On a nonzero finite-dimensional inner
product space, for invertible `A` the least `‖E‖` such that `A - E` is not invertible is
`‖A⁻¹‖⁻¹` (Demmel, Math 221 Lecture 3 notes, 2024: "`min{norm(E)/norm(A): A-E singular} =
1/kappa(A)`", proved there in the 2-norm). The space must be nonzero: on the zero space every
operator is invertible. -/
theorem isLeast_norm_of_not_isUnit_sub [FiniteDimensional 𝕜 F] [Nontrivial F]
    (A : (F →L[𝕜] F)ˣ) :
    IsLeast {t : ℝ | ∃ E : F →L[𝕜] F, ¬ IsUnit ((A : F →L[𝕜] F) - E) ∧ ‖E‖ = t}
      ‖(↑A⁻¹ : F →L[𝕜] F)‖⁻¹ := by
  have : ProperSpace F := FiniteDimensional.proper_rclike 𝕜 F
  have : CompleteSpace F := FiniteDimensional.complete 𝕜 F
  set Z : F →L[𝕜] F := ↑A⁻¹
  have hZpos : 0 < ‖Z‖ := Units.norm_pos A⁻¹
  refine ⟨?_, ?_⟩
  · -- a unit vector `y` at which `‖Z y‖ = ‖Z‖`
    have hsph : (Metric.sphere (0 : F) 1).Nonempty :=
      Set.nonempty_coe_sort.1 (NormedSpace.sphere_nonempty_rclike 𝕜 zero_le_one)
    obtain ⟨y, hy, hmax⟩ := (isCompact_sphere (0 : F) 1).exists_isMaxOn hsph
      (continuous_norm.comp Z.continuous).continuousOn
    have hy1 : ‖y‖ = 1 := by simpa using hy
    have hZy : ‖Z y‖ = ‖Z‖ := by
      refine le_antisymm ?_ ?_
      · simpa [hy1] using Z.le_opNorm y
      · refine ContinuousLinearMap.opNorm_le_of_unit_norm (norm_nonneg _) fun v hv => ?_
        exact hmax (by simpa using hv)
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
    set x := Z y
    have hx0 : x ≠ 0 := by
      intro h
      apply hZpos.ne'
      rw [← hZy, h, norm_zero]
    have hAx : (A : F →L[𝕜] F) x = y := by
      change ((A : F →L[𝕜] F) * Z) y = y
      rw [Units.mul_inv]
      rfl
    refine ⟨rankOneTo x y, ?_, ?_⟩
    · rintro ⟨U, hU⟩
      apply hx0
      have h0 : (U : F →L[𝕜] F) x = 0 := by
        rw [hU, sub_apply, hAx, rankOneTo_apply_self hx0, sub_self]
      have : ((↑U⁻¹ : F →L[𝕜] F) * U) x = 0 := by
        change (↑U⁻¹ : F →L[𝕜] F) ((U : F →L[𝕜] F) x) = 0
        rw [h0, map_zero]
      rwa [Units.inv_mul] at this
    · rw [norm_rankOneTo hx0, hy1, hZy, one_div]
  · rintro t ⟨E, hE, rfl⟩
    by_contra hlt
    push Not at hlt
    apply hE
    refine isUnit_sub A E ?_
    calc ‖E‖ * ‖Z‖ < ‖Z‖⁻¹ * ‖Z‖ := by gcongr
      _ = 1 := inv_mul_cancel₀ hZpos.ne'

end MathlibExt.Analysis.InnerProductSpace.LinearSystemBackwardError
