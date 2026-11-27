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

public import MathlibExt.Analysis.Normed.Operator.Compact.LeftRegularizer
public import MathlibExt.Analysis.Normed.Operator.Compact.OpenMap
public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Group.Quotient

import Mathlib.Tactic.Abel

/-!
# Two-sided compact parametrices imply Fredholmness

Let `𝕜` be a normed field with a compatible real-like or complex-like structure, and `E,F`
normed `𝕜`-spaces. For bounded maps `T : E → F` and `U : F → E`, assume both `UT-I_E` and
`TU-I_F` are compact.

Then `T` is strict, has closed range of finite codimension, and has a finite-dimensional kernel
with a closed topological complement. These are the five conditions of the Fredholm predicate.
No completeness or inner product on `E,F`, and no approximation property, is required.
-/

namespace ContinuousLinearMap.IsFredholm

universe u𝕜 uE uF

section FiniteKernel

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

private theorem finiteDimensional_ker_of_compact_left_error
    (T : E →L[𝕜] F) (U : F →L[𝕜] E)
    (hUT : IsCompactOperator (U.comp T - (1 : E →L[𝕜] E))) :
    FiniteDimensional 𝕜 T.ker := by
  let K : E →L[𝕜] E := U.comp T - 1
  have hK : IsCompactOperator K.toLinearMap := hUT
  have hPreserves : ∀ x ∈ T.ker, K.toLinearMap x ∈ T.ker := by
    intro x hx
    have hxT : T x = 0 := hx
    change T (U (T x) - x) = 0
    simp only [hxT, map_zero, map_sub, sub_self]
  have hRestricted : IsCompactOperator (K.toLinearMap.restrict hPreserves) :=
    hK.restrict hPreserves T.isClosed_ker
  have hNeg := hRestricted.neg
  change IsCompactOperator
    (fun x : T.ker => -(K.toLinearMap.restrict hPreserves x)) at hNeg
  have hIdentity :
      (fun x : T.ker => -(K.toLinearMap.restrict hPreserves x)) = id := by
    funext x
    apply Subtype.ext
    change -(U (T (x : E)) - (x : E)) = (x : E)
    rw [show T (x : E) = 0 from x.property, map_zero, zero_sub, neg_neg]
  have hId : IsCompactOperator (id : T.ker → T.ker) := hIdentity ▸ hNeg
  exact FiniteDimensional.of_isCompactOperator_id hId

end FiniteKernel

@[expose] public section

variable {𝕜 : Type u𝕜} [NormedField 𝕜] [IsRCLikeNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type uF} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Fredholm operator from a two-sided compact parametrix.** Let `𝕜` be a normed field with
compatible real-like or complex-like normed-field structure, and `E,F` normed `𝕜`-spaces,
possibly incomplete. If bounded `T : E → F` and `U : F → E` have compact errors `UT-I_E`
and `TU-I_F`, then `T` is Fredholm: strict, with closed finite-codimension range and
finite-dimensional, topologically complemented kernel. No inner product is required. -/
theorem of_compactParametrix (T : E →L[𝕜] F) (U : F →L[𝕜] E)
    (hUT : IsCompactOperator (U.comp T - (1 : E →L[𝕜] E)))
    (hTU : IsCompactOperator (T.comp U - (1 : F →L[𝕜] F))) :
    letI : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜;
    T.IsFredholm := by
  let : RCLike 𝕜 := IsRCLikeNormedField.rclike 𝕜
  change T.IsFredholm
  have hFinite : FiniteDimensional 𝕜 T.ker :=
    finiteDimensional_ker_of_compact_left_error T U hUT
  let : FiniteDimensional 𝕜 T.ker := hFinite
  have hComplement : T.ker.ClosedComplemented :=
    Submodule.ClosedComplemented.of_finiteDimensional T.ker
  obtain ⟨H, hNH⟩ := hComplement.exists_isTopCompl
  let i : H →L[𝕜] E := H.subtypeL
  let r : E →L[𝕜] H := H.projectionOntoL T.ker hNH.symm
  let S : H →L[𝕜] F := T.domRestrict H
  let V : F →L[𝕜] H := r.comp U
  have hFix (x : H) : r (x : E) = x :=
    Submodule.projectionOntoL_apply_left hNH.symm x
  have hInjective : Function.Injective S := by
    intro x y hxy
    apply Subtype.ext
    have hTxy : T (x : E) = T (y : E) := hxy
    have hKer : (x : E) - (y : E) ∈ T.ker := by
      change T ((x : E) - (y : E)) = 0
      rw [map_sub, hTxy, sub_self]
    have hH : (x : E) - (y : E) ∈ H := H.sub_mem x.property y.property
    exact sub_eq_zero.mp
      ((Submodule.disjoint_def.mp hNH.isCompl.disjoint) _ hKer hH)
  have hError : V.comp S - (1 : H →L[𝕜] H) =
      r.comp ((U.comp T - (1 : E →L[𝕜] E)).comp i) := by
    apply ContinuousLinearMap.ext
    intro x
    change r (U (T (x : E))) - x = r (U (T (x : E)) - (x : E))
    rw [map_sub, hFix x]
  have hKi : IsCompactOperator ((U.comp T - (1 : E →L[𝕜] E)).comp i) := by
    simpa only [ContinuousLinearMap.coe_comp] using hUT.comp_clm i
  have hVCompact : IsCompactOperator (V.comp S - (1 : H →L[𝕜] H)) := by
    rw [hError]
    simpa only [ContinuousLinearMap.coe_comp] using hKi.clm_comp r
  have hEmbedding : Topology.IsClosedEmbedding S :=
    ContinuousLinearMap.isClosedEmbedding_of_injective_compact_left_parametrix
      S V hInjective hVCompact
  have hFactor : S.comp r = T := by
    apply ContinuousLinearMap.ext
    intro x
    have hProjection : i (r x) = H.projection T.ker hNH.symm.isCompl x := rfl
    have hResidual : x - i (r x) ∈ T.ker := by
      rw [hProjection]
      exact Submodule.sub_projection_mem hNH.symm.isCompl x
    have hTResidual : T (x - i (r x)) = 0 := hResidual
    rw [map_sub] at hTResidual
    change T (i (r x)) = T x
    exact (sub_eq_zero.mp hTResidual).symm
  have hQuotient : Topology.IsQuotientMap r :=
    Submodule.isQuotientMap_projectionOntoL hNH.symm
  have hStrictComp : Topology.IsStrictMap (S.comp r) := by
    change Topology.IsStrictMap ((S : H → F) ∘ (r : E → H))
    exact hQuotient.isStrictMap_iff.mp hEmbedding.isEmbedding.isStrictMap
  have hStrict : Topology.IsStrictMap T := by
    simpa only [hFactor] using hStrictComp
  have hRanges : Set.range (T : E → F) = Set.range (S : H → F) :=
    (congrArg (fun f : E →L[𝕜] F => Set.range (f : E → F)) hFactor).symm.trans
      (hQuotient.surjective.range_comp (S : H → F))
  have hClosed : IsClosed (T.range : Set F) := by
    change IsClosed (Set.range (T : E → F))
    rw [hRanges]
    exact hEmbedding.isClosed_range
  let : IsClosed (T.range : Set F) := hClosed
  let q : F →L[𝕜] (F ⧸ T.range) := T.range.mkQL
  have hqT : q.comp T = (0 : E →L[𝕜] (F ⧸ T.range)) := by
    apply ContinuousLinearMap.ext
    intro x
    change T.range.mkQ (T x) = 0
    have hMember : T x ∈ (T.range.mkQ).ker := by
      rw [Submodule.ker_mkQ]
      exact LinearMap.mem_range_self T.toLinearMap x
    exact hMember
  have hqError : q.comp (T.comp U - (1 : F →L[𝕜] F)) = -q := by
    apply ContinuousLinearMap.ext
    intro x
    change q (T (U x) - x) = -q x
    have hZero : q (T (U x)) = 0 := DFunLike.congr_fun hqT (U x)
    rw [map_sub, hZero, zero_sub]
  have hqErrorCompact :
      IsCompactOperator (q.comp (T.comp U - (1 : F →L[𝕜] F))) := by
    simpa only [ContinuousLinearMap.coe_comp] using hTU.clm_comp q
  have hqCompact : IsCompactOperator q := by
    have hNegq : IsCompactOperator (-q : F →L[𝕜] (F ⧸ T.range)) :=
      hqError ▸ hqErrorCompact
    have hNegNeg := hNegq.neg
    change IsCompactOperator (fun x : F => -(-q x)) at hNegNeg
    simpa only [neg_neg] using hNegNeg
  have hqOpen : IsOpenMap q :=
    T.range.isOpenQuotientMap_mkQL.isOpenMap
  have hCoker : T.range.CoFG :=
    FiniteDimensional.of_isCompactOperator_of_isOpenMap q hqCompact hqOpen
  exact ⟨hStrict, hClosed, hFinite, hCoker, hComplement⟩

end

end ContinuousLinearMap.IsFredholm
