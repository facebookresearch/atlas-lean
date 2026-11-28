/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Normed.Operator.Compact.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

import Mathlib.Tactic.Positivity

/-!
# Compact operators between Hilbert spaces

Compact continuous linear maps between complete real or complex Hilbert spaces
admit arbitrarily close finite-range approximants obtained by projecting their
ranges onto finite-dimensional subspaces. The projection factor also shows
directly that the adjoints of the approximants have finite range. It follows
that the adjoint of a compact operator is compact.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace Topology

universe u𝕜 uE uF

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- Let `𝕜` be a real or complex scalar field and let both `E` and `F` be complete inner-product
spaces over `𝕜`. The operator is continuous and `𝕜`-linear from `E` to `F`. The approximation
error `ε` is strictly positive.

A compact map between Hilbert spaces can be approximated by a map that factors through a
finite-dimensional orthogonal projection. Both the approximant and its adjoint have finite
range. -/
theorem IsCompactOperator.exists_projectionFactor_hasFiniteRange_adjoint_norm_sub_lt
    {K : E →L[𝕜] F} (hK : IsCompactOperator K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (U : Submodule 𝕜 F) (hU : FiniteDimensional 𝕜 U),
      letI : FiniteDimensional 𝕜 U := hU
      ∃ A : E →L[𝕜] F,
        A = U.starProjection ∘L K ∧
        A.toLinearMap.HasFiniteRange ∧
        (ContinuousLinearMap.adjoint A).toLinearMap.HasFiniteRange ∧
        ‖K - A‖ < ε := by
  have hImage : IsCompact (closure (K '' Metric.closedBall (0 : E) 1)) :=
    hK.isCompact_closure_image_closedBall 1
  obtain ⟨t, _htSub, htFinite, htCover⟩ :=
    exists_finite_cover_balls_of_isCompact_closure hImage (half_pos hε)
  let U : Submodule 𝕜 F := Submodule.span 𝕜 t
  have hU : FiniteDimensional 𝕜 U := by
    dsimp only [U]
    exact FiniteDimensional.span_of_finite 𝕜 htFinite
  let _ : FiniteDimensional 𝕜 U := hU
  let P : F →L[𝕜] F := U.starProjection
  let A : E →L[𝕜] F := P ∘L K
  have hApprox : ‖K - A‖ ≤ ε / 2 := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
    intro x hx
    have hxBall : x ∈ Metric.closedBall (0 : E) 1 :=
      mem_closedBall_zero_iff.mpr hx.le
    have hKx : K x ∈ K '' Metric.closedBall (0 : E) 1 :=
      ⟨x, hxBall, rfl⟩
    have hcover := htCover hKx
    rw [Set.mem_iUnion] at hcover
    obtain ⟨z, hcover⟩ := hcover
    rw [Set.mem_iUnion] at hcover
    obtain ⟨hzt, hzball⟩ := hcover
    have hzU : z ∈ U := by
      dsimp only [U]
      exact Submodule.subset_span hzt
    have hproj : ‖K x - U.starProjection (K x)‖ ≤ ‖K x - z‖ := by
      rw [U.starProjection_minimal]
      exact ciInf_le
        ⟨0, Set.forall_mem_range.mpr fun _ => norm_nonneg _⟩
        (⟨z, hzU⟩ : U)
    have happly : (K - A) x = K x - U.starProjection (K x) := by
      simp only [A, P, ContinuousLinearMap.comp_apply, sub_apply]
    rw [happly]
    exact hproj.trans (by
      simpa only [dist_eq_norm] using (Metric.mem_ball.mp hzball).le)
  have hPRange : P.range = U := by
    simpa only [P] using Submodule.range_starProjection U
  have hUfg : U.FG :=
    (Submodule.fg_iff_finiteDimensional U).mpr inferInstance
  have hPfinite : P.toLinearMap.HasFiniteRange := by
    change P.range.FG
    rw [hPRange]
    exact hUfg
  have hAeq : A = U.starProjection ∘L K := by
    rfl
  have hAfinite : A.toLinearMap.HasFiniteRange := by
    rw [show A = P ∘L K by rfl]
    simpa only [ContinuousLinearMap.toLinearMap_comp] using
      hPfinite.comp_right K.toLinearMap
  have hPadjoint : ContinuousLinearMap.adjoint P = P := by
    rw [← ContinuousLinearMap.star_eq_adjoint]
    exact (isSelfAdjoint_starProjection U).star_eq
  have hAadjoint :
      ContinuousLinearMap.adjoint A =
        ContinuousLinearMap.adjoint K ∘L P := by
    rw [show A = P ∘L K by rfl, ContinuousLinearMap.adjoint_comp,
      hPadjoint]
  have hAadjointFinite :
      (ContinuousLinearMap.adjoint A).toLinearMap.HasFiniteRange := by
    rw [hAadjoint]
    simpa only [ContinuousLinearMap.toLinearMap_comp] using
      hPfinite.comp_left (ContinuousLinearMap.adjoint K).toLinearMap
  refine ⟨U, hU, ?_⟩
  change ∃ A : E →L[𝕜] F,
    A = U.starProjection ∘L K ∧
      A.toLinearMap.HasFiniteRange ∧
      (ContinuousLinearMap.adjoint A).toLinearMap.HasFiniteRange ∧
      ‖K - A‖ < ε
  exact ⟨A, hAeq, hAfinite, hAadjointFinite,
    hApprox.trans_lt (half_lt_self hε)⟩

/-- Let `𝕜` be a real or complex scalar field and let both `E` and `F` be complete inner-product
spaces over `𝕜`. The operator is continuous and `𝕜`-linear from `E` to `F`.

The adjoint of a compact continuous linear map between complete real or complex Hilbert spaces
is compact. -/
theorem IsCompactOperator.adjoint {K : E →L[𝕜] F}
    (hK : IsCompactOperator K) :
    IsCompactOperator (ContinuousLinearMap.adjoint K) := by
  have hmem : ContinuousLinearMap.adjoint K ∈
      closure {A : F →L[𝕜] E | IsCompactOperator A} := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨U, hU, h⟩ :=
      hK.exists_projectionFactor_hasFiniteRange_adjoint_norm_sub_lt hε
    let _ : FiniteDimensional 𝕜 U := hU
    obtain ⟨A, _hFactor, _hFinite, hAdjointFinite, hNorm⟩ := h
    refine ⟨ContinuousLinearMap.adjoint A,
      hAdjointFinite.isCompactOperator, ?_⟩
    calc
      dist (ContinuousLinearMap.adjoint K)
          (ContinuousLinearMap.adjoint A) = dist K A :=
        ContinuousLinearMap.adjoint.isometry.dist_eq K A
      _ = ‖K - A‖ := dist_eq_norm K A
      _ < ε := hNorm
  rw [isClosed_setOfPred_isCompactOperator.closure_eq] at hmem
  exact hmem
