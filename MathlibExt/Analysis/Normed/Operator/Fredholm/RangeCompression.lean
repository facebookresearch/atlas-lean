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

public import MathlibExt.Analysis.Normed.Operator.Fredholm.CompactParametrix
public import MathlibExt.Analysis.Normed.Operator.Compact.FiniteRange
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent

import Mathlib.Tactic.Abel

/-!
# Fredholm compression between bounded idempotent ranges

Let `E,F` be complete real or complex Hilbert spaces, `T : E → F` a Fredholm operator, and `p :
E → E`, `q : F → F` bounded idempotents. If the intertwining defect `Tp-qT` is compact, the
compressed map `x ↦ q(Tx)` from `range p` to `range q` is Fredholm.

The ranges carry their inherited norms, topologies and inner products. The idempotents need not
be orthogonal or have cofinite ranges, and `T(range p) ⊆ range q` is not assumed. No equality of
ambient and compressed indices is asserted.
-/

namespace ContinuousLinearMap

universe u𝕜 uE uF

section DefectIdentities

variable {𝕜 : Type u𝕜} [Ring 𝕜]
variable {E : Type uE} [AddCommGroup E] [Module 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E]
variable {F : Type uF} [AddCommGroup F] [Module 𝕜 F]
  [TopologicalSpace F] [IsTopologicalAddGroup F]

private theorem range_compression_left_defect
    {p : E →L[𝕜] E} {q : F →L[𝕜] F} {T : E →L[𝕜] F} {U : F →L[𝕜] E}
    (hp : IsIdempotentElem p) :
    (p.rangeRestrict.comp (U.domRestrict q.range)).comp
        (q.rangeRestrict.comp (T.domRestrict p.range)) - (1 : p.range →L[𝕜] p.range) =
      p.rangeRestrict.comp
        (((U.comp T - 1) - U.comp (T.comp p - q.comp T)).domRestrict p.range) := by
  have hpFix (x : p.range) : p (x : E) = (x : E) :=
    (LinearMap.IsIdempotentElem.isProj_range p.toLinearMap
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp)).map_id (x : E) x.property
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  change p (U (q (T (x : E)))) - (x : E) =
    p ((U (T (x : E)) - (x : E)) - U (T (p (x : E)) - q (T (x : E))))
  rw [hpFix x, map_sub U]
  simp only [map_sub, hpFix x]
  abel

omit [IsTopologicalAddGroup E] in
private theorem range_compression_right_defect
    {p : E →L[𝕜] E} {q : F →L[𝕜] F} {T : E →L[𝕜] F} {U : F →L[𝕜] E}
    (hq : IsIdempotentElem q) :
    (q.rangeRestrict.comp (T.domRestrict p.range)).comp
        (p.rangeRestrict.comp (U.domRestrict q.range)) - (1 : q.range →L[𝕜] q.range) =
      q.rangeRestrict.comp
        (((T.comp U - 1) + (T.comp p - q.comp T).comp U).domRestrict q.range) := by
  have hqFix (y : q.range) : q (y : F) = (y : F) :=
    (LinearMap.IsIdempotentElem.isProj_range q.toLinearMap
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hq)).map_id (y : F) y.property
  have hqq (y : F) : q (q y) = q y :=
    hqFix (⟨q y, ⟨y, rfl⟩⟩ : q.range)
  apply ContinuousLinearMap.ext
  intro y
  apply Subtype.ext
  change q (T (p (U (y : F)))) - (y : F) =
    q ((T (U (y : F)) - (y : F)) + (T (p (U (y : F))) - q (T (U (y : F)))))
  simp only [map_add, map_sub, hqFix y, hqq]
  abel

end DefectIdentities

@[expose] public section

open scoped LinearMap.FiniteRangeSetoid

namespace IsFredholm

variable {𝕜 : Type u𝕜} [RCLike 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]
variable {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [CompleteSpace F]

/-- **Fredholm map compressed between idempotent ranges.** Let `𝕜` be real or complex, `E,F`
complete normed inner-product `𝕜`-spaces, `T : E →L[𝕜] F` Fredholm, and bounded
idempotents `p` on `E`, `q` on `F`. If `T∘p-q∘T` is compact, then `x ↦ q(Tx) : range p →
range q` is Fredholm with the inherited subspace structures. The idempotents need not be
self-adjoint or have cofinite ranges. -/
theorem range_compression {p : E →L[𝕜] E} {q : F →L[𝕜] F} {T : E →L[𝕜] F}
    (hT : T.IsFredholm) (hp : IsIdempotentElem p) (hq : IsIdempotentElem q)
    (hDelta : IsCompactOperator (T.comp p - q.comp T)) :
    (q.rangeRestrict.comp (T.domRestrict p.range)).IsFredholm := by
  obtain ⟨U, hU⟩ := hT.exists_isQuasiInverse
  let A : E →L[𝕜] E := U.comp T - 1
  let B : F →L[𝕜] F := T.comp U - 1
  have hAfin : A.toLinearMap.HasFiniteRange := by
    have hLeft : U.toLinearMap.IsLeftQuasiInverse T.toLinearMap := hU.1
    rw [LinearMap.IsLeftQuasiInverse,
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] at hLeft
    change A.toLinearMap.HasFiniteRange at hLeft
    exact hLeft
  have hBfin : B.toLinearMap.HasFiniteRange := by
    have hRight : U.toLinearMap.IsRightQuasiInverse T.toLinearMap := hU.2
    rw [LinearMap.IsRightQuasiInverse,
      LinearMap.FiniteRangeSetoid.equiv_iff_hasFiniteRange] at hRight
    change B.toLinearMap.HasFiniteRange at hRight
    exact hRight
  have hA : IsCompactOperator A :=
    LinearMap.HasFiniteRange.isCompactOperator (T := A) hAfin
  have hB : IsCompactOperator B :=
    LinearMap.HasFiniteRange.isCompactOperator (T := B) hBfin
  let D : E →L[𝕜] F := T.comp p - q.comp T
  have hD : IsCompactOperator D := hDelta
  have hUD : IsCompactOperator (U.comp D) := by
    simpa only [ContinuousLinearMap.coe_comp] using hD.clm_comp U
  have hDU : IsCompactOperator (D.comp U) := by
    simpa only [ContinuousLinearMap.coe_comp] using hD.comp_clm U
  let CE : E →L[𝕜] E := A - U.comp D
  let CF : F →L[𝕜] F := B + D.comp U
  have hCE : IsCompactOperator CE := by
    simpa only [CE, FunLike.coe_sub] using hA.sub hUD
  have hCF : IsCompactOperator CF := by
    simpa only [CF, FunLike.coe_add] using hB.add hDU
  let S : p.range →L[𝕜] q.range := q.rangeRestrict.comp (T.domRestrict p.range)
  let V : q.range →L[𝕜] p.range := p.rangeRestrict.comp (U.domRestrict q.range)
  have hLeftDefect : V.comp S - 1 =
      p.rangeRestrict.comp (CE.domRestrict p.range) :=
    range_compression_left_defect (p := p) (q := q) (T := T) (U := U) hp
  have hRightDefect : S.comp V - 1 =
      q.rangeRestrict.comp (CF.domRestrict q.range) :=
    range_compression_right_defect (p := p) (q := q) (T := T) (U := U) hq
  have hCEdom : IsCompactOperator (CE.domRestrict p.range) := by
    simpa only [ContinuousLinearMap.domRestrict, ContinuousLinearMap.coe_comp]
      using hCE.comp_clm p.range.subtypeL
  have hCFdom : IsCompactOperator (CF.domRestrict q.range) := by
    simpa only [ContinuousLinearMap.domRestrict, ContinuousLinearMap.coe_comp]
      using hCF.comp_clm q.range.subtypeL
  have hLeft : IsCompactOperator (V.comp S - (1 : p.range →L[𝕜] p.range)) := by
    rw [hLeftDefect]
    simpa only [ContinuousLinearMap.coe_comp] using hCEdom.clm_comp p.rangeRestrict
  have hRight : IsCompactOperator (S.comp V - (1 : q.range →L[𝕜] q.range)) := by
    rw [hRightDefect]
    simpa only [ContinuousLinearMap.coe_comp] using hCFdom.clm_comp q.rangeRestrict
  let : CompleteSpace p.range :=
    IsClosed.completeSpace_coe (s := (p.range : Set E))
      (hs := ContinuousLinearMap.IsIdempotentElem.isClosed_range hp)
  let : CompleteSpace q.range :=
    IsClosed.completeSpace_coe (s := (q.range : Set F))
      (hs := ContinuousLinearMap.IsIdempotentElem.isClosed_range hq)
  exact of_compactParametrix S V hLeft hRight

end IsFredholm

end

end ContinuousLinearMap
