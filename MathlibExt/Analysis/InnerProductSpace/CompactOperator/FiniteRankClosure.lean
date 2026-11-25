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

public import MathlibExt.Analysis.InnerProductSpace.CompactOperator

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Compact Hilbert-space operators as the closure of finite-rank operators

For complete real or complex Hilbert spaces, compact continuous linear maps
are exactly the operator-norm closure of the span of rank-one maps.  The hard
direction uses the existing finite-dimensional orthogonal-projection
approximant, expands that projection in an orthonormal basis, and composes each
rank-one summand with the original operator.
-/

@[expose] public section

noncomputable section

open Set
open scoped InnerProductSpace Topology

namespace InnerProductSpace

universe u𝕜 uE uF

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/-- Let `𝕜` be a real or complex scalar field and let `E` and `F` be normed
inner-product spaces over `𝕜`. The finite-rank submodule of `E →L[𝕜] F` is
the `𝕜`-linear span of the maps `z ↦ ⟪y, z⟫_𝕜 • x`, with `x : F` and `y : E`. -/
def finiteRankSubmodule : Submodule 𝕜 (E →L[𝕜] F) :=
  Submodule.span 𝕜
    (Set.range fun p : F × E => rankOne 𝕜 p.1 p.2)

/-- Let `𝕜` be a real or complex scalar field, let `E` and `F` be normed
inner-product spaces over `𝕜`, and let `x : F` and `y : E`. The rank-one map
`z ↦ ⟪y, z⟫_𝕜 • x` belongs to the finite-rank submodule of `E →L[𝕜] F`. -/
theorem rankOne_mem_finiteRankSubmodule (x : F) (y : E) :
    rankOne 𝕜 x y ∈ finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F) :=
  Submodule.subset_span ⟨(x, y), rfl⟩

/-- Let `𝕜` be a real or complex scalar field and let `E` and `F` be normed
inner-product spaces over `𝕜`. Every continuous `𝕜`-linear map `T : E →L[𝕜] F`
in the linear span of Hilbert-space rank-one maps is a compact operator. -/
theorem finiteRankSubmodule_isCompactOperator
    {T : E →L[𝕜] F}
    (hT : T ∈ finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F)) :
    IsCompactOperator T := by
  change T ∈ Submodule.span 𝕜
    (Set.range fun p : F × E => rankOne 𝕜 p.1 p.2) at hT
  refine Submodule.span_induction
    (p := fun (S : E →L[𝕜] F) _ => IsCompactOperator S)
    ?_ (isCompactOperator_zero : IsCompactOperator (0 : E →L[𝕜] F))
    ?_ ?_ hT
  · rintro _ ⟨⟨x, y⟩, rfl⟩
    have hSpan :
        (ContinuousLinearMap.toSpanSingleton 𝕜 x).toLinearMap.HasFiniteRange :=
      LinearMap.HasFiniteRange.of_finite_dom
    have hRange : (rankOne 𝕜 x y).toLinearMap.HasFiniteRange := by
      rw [rankOne_def', ContinuousLinearMap.toLinearMap_comp]
      exact hSpan.comp_right (innerSL 𝕜 y).toLinearMap
    exact hRange.isCompactOperator
  · intro S T _ _ hS hT
    exact hS.add hT
  · intro c T _ hT
    exact hT.smul c

/-- Let `𝕜` be a real or complex scalar field, let `E` be a normed
inner-product space over `𝕜`, and let `F` be a complete inner-product space
over `𝕜`. If `T : E →L[𝕜] F` belongs to the operator-norm closure of the
linear span of rank-one maps, then `T` is a compact operator. -/
theorem topologicalClosure_finiteRankSubmodule_isCompactOperator
    [CompleteSpace F] {T : E →L[𝕜] F}
    (hT : T ∈
      (finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F)).topologicalClosure) :
    IsCompactOperator T := by
  change T ∈ closure
    (finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F) :
      Set (E →L[𝕜] F)) at hT
  have hsubset :
      closure
          (finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F) :
            Set (E →L[𝕜] F)) ⊆
        {S : E →L[𝕜] F | IsCompactOperator S} :=
    closure_minimal
      (fun _ h => finiteRankSubmodule_isCompactOperator h)
      isClosed_setOfPred_isCompactOperator
  exact hsubset hT

/-- Let `𝕜` be a real or complex scalar field and let both `E` and `F` be
complete inner-product spaces over `𝕜`. Every compact continuous linear map
`T : E →L[𝕜] F` lies in the operator-norm closure of the `𝕜`-linear span of
Hilbert-space rank-one maps from `E` to `F`. -/
theorem _root_.IsCompactOperator.mem_topologicalClosure_finiteRankSubmodule
    [CompleteSpace E] [CompleteSpace F]
    {T : E →L[𝕜] F} (hT : IsCompactOperator T) :
    T ∈ (finiteRankSubmodule
      (𝕜 := 𝕜) (E := E) (F := F)).topologicalClosure := by
  change T ∈ closure
    (finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F) :
      Set (E →L[𝕜] F))
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨U, hU, hApprox⟩ :=
    hT.exists_projectionFactor_hasFiniteRange_adjoint_norm_sub_lt hε
  let _ : FiniteDimensional 𝕜 U := hU
  obtain ⟨A, hFactor, _hFinite, _hAdjointFinite, hNorm⟩ := hApprox
  let b : OrthonormalBasis (Fin (Module.finrank 𝕜 U)) 𝕜 U :=
    stdOrthonormalBasis 𝕜 U
  have hProjection :
      U.starProjection = ∑ i, rankOne 𝕜 (b i : F) (b i : F) :=
    b.starProjection_eq_sum_rankOne
  have hA_sum :
      A = ∑ i, rankOne 𝕜 (b i : F)
        (ContinuousLinearMap.adjoint T (b i : F)) := by
    calc
      A = U.starProjection ∘L T := hFactor
      _ = (∑ i, rankOne 𝕜 (b i : F) (b i : F)) ∘L T := by
        exact congrArg (fun P : F →L[𝕜] F => P.comp T) hProjection
      _ = ∑ i, (rankOne 𝕜 (b i : F) (b i : F) ∘L T) := by
        ext x
        simp
      _ = ∑ i, rankOne 𝕜 (b i : F)
          (ContinuousLinearMap.adjoint T (b i : F)) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact InnerProductSpace.rankOne_comp (b i : F) (b i : F) T
  have hA_mem :
      A ∈ finiteRankSubmodule (𝕜 := 𝕜) (E := E) (F := F) := by
    rw [hA_sum]
    exact Submodule.sum_mem _ fun i _ =>
      rankOne_mem_finiteRankSubmodule (b i : F)
        (ContinuousLinearMap.adjoint T (b i : F))
  refine ⟨A, hA_mem, ?_⟩
  simpa only [dist_eq_norm] using hNorm

/-- Let `𝕜` be a real or complex scalar field and let both `E` and `F` be
complete inner-product spaces over `𝕜`. A continuous linear map
`T : E →L[𝕜] F` is compact if and only if it belongs to the operator-norm
closure of the `𝕜`-linear span of Hilbert-space rank-one maps. -/
theorem isCompactOperator_iff_mem_topologicalClosure_finiteRankSubmodule
    [CompleteSpace E] [CompleteSpace F] (T : E →L[𝕜] F) :
    IsCompactOperator T ↔
      T ∈ (finiteRankSubmodule
        (𝕜 := 𝕜) (E := E) (F := F)).topologicalClosure :=
  ⟨IsCompactOperator.mem_topologicalClosure_finiteRankSubmodule,
    topologicalClosure_finiteRankSubmodule_isCompactOperator⟩

/-- Let `𝕜` be a real or complex scalar field and let both `E` and `F` be
complete inner-product spaces over `𝕜`. In the operator-norm space
`E →L[𝕜] F`, the submodule of compact operators equals the closure of the
`𝕜`-linear span of Hilbert-space rank-one maps from `E` to `F`. -/
theorem compactOperator_eq_topologicalClosure_finiteRankSubmodule
    [CompleteSpace E] [CompleteSpace F] :
    compactOperator (RingHom.id 𝕜) E F =
      (finiteRankSubmodule
        (𝕜 := 𝕜) (E := E) (F := F)).topologicalClosure := by
  ext T
  exact isCompactOperator_iff_mem_topologicalClosure_finiteRankSubmodule T

end InnerProductSpace
