/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.KTheory.Exact.Quillen.QuillenSpanFlagEndpointTransport
public import MathlibExt.KTheory.Exact.Quillen.SpanFlagStageShell

/-!
# Composition coherence for endpoint-compatible flagged Quillen spans

Compatible apex isomorphisms for two adjacent pairs of raw Quillen spans
induce the compatible isomorphism of their ordered pullback composites.  The
apex map is the pullback lift of the two component apex maps, so both hom and
inverse projection formulas are explicit.

Endpoint transport converts the resulting comparison into an ordinary span
isomorphism.  Existing flag transport and canonical uniqueness then give the
material kernel, pushout, and quotient comparison.  Fixed-endpoint rebasing
connects this binary construction to the long shell of an edgewise Stage.

This file constructs no Stage reconstruction, grid-fiber connectedness,
contractibility, realization weak equivalence, or Q/S comparison.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open SimplexCategory
open scoped Simplicial

universe v u

namespace AlgebraicKTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

namespace QuillenSpan.EndpointIso

variable {X0 X1 X2 Y0 Y1 Y2 : C}
variable {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
  {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
variable {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}

/-- Pullback-induced apex isomorphism for the ordered composite of two
adjacent endpoint-compatible comparisons. -/
noncomputable def compApexIso
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    (Span.comp S01 S12).apex ≅ (Span.comp T01 T12).apex := by
  let f : (Span.comp S01 S12).apex ⟶ (Span.comp T01 T12).apex :=
    pullback.lift
      (pullback.fst S01.r S12.l ≫ c01.1.hom)
      (pullback.snd S01.r S12.l ≫ c12.1.hom)
      (by
        simp only [Category.assoc, c01.hom_r, c12.hom_l]
        rw [← Category.assoc, pullback.condition, Category.assoc])
  let g : (Span.comp T01 T12).apex ⟶ (Span.comp S01 S12).apex :=
    pullback.lift
      (pullback.fst T01.r T12.l ≫ c01.1.inv)
      (pullback.snd T01.r T12.l ≫ c12.1.inv)
      (by
        simp only [Category.assoc, c01.inv_r, c12.inv_l]
        rw [← Category.assoc, pullback.condition, Category.assoc])
  refine
    { hom := f
      inv := g
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · apply pullback.hom_ext
    · dsimp only [f, g]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback.lift_fst, Category.assoc, c01.1.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · dsimp only [f, g]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
        pullback.lift_snd, Category.assoc, c12.1.hom_inv_id,
        Category.comp_id, Category.id_comp]
  · apply pullback.hom_ext
    · dsimp only [f, g]
      rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
        pullback.lift_fst, Category.assoc, c01.1.inv_hom_id,
        Category.comp_id, Category.id_comp]
    · dsimp only [f, g]
      rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
        pullback.lift_snd, Category.assoc, c12.1.inv_hom_id,
        Category.comp_id, Category.id_comp]

/-- Compose two adjacent endpoint-compatible raw-span comparisons in the
ordered `Span.comp S01 S12` direction. -/
noncomputable def comp
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    QuillenSpan.EndpointIso
      (Span.comp S01 S12) (Span.comp T01 T12) e0 e2 := by
  refine ⟨compApexIso c01 c12, ?_, ?_⟩
  · change (compApexIso c01 c12).hom ≫
        (pullback.fst T01.r T12.l ≫ T01.l) =
      (pullback.fst S01.r S12.l ≫ S01.l) ≫ e0.hom
    rw [← Category.assoc]
    unfold compApexIso
    dsimp only
    rw [pullback.lift_fst, Category.assoc, c01.hom_l,
      ← Category.assoc]
  · change (compApexIso c01 c12).hom ≫
        (pullback.snd T01.r T12.l ≫ T12.r) =
      (pullback.snd S01.r S12.l ≫ S12.r) ≫ e2.hom
    rw [← Category.assoc]
    unfold compApexIso
    dsimp only
    rw [pullback.lift_snd, Category.assoc, c12.hom_r,
      ← Category.assoc]

/-- The composite apex hom commutes with the first pullback projection. -/
@[reassoc]
theorem comp_hom_fst
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    (c01.comp c12).1.hom ≫ pullback.fst T01.r T12.l =
      pullback.fst S01.r S12.l ≫ c01.1.hom := by
  change (compApexIso c01 c12).hom ≫ pullback.fst T01.r T12.l = _
  unfold compApexIso
  dsimp only
  apply pullback.lift_fst

/-- The composite apex hom commutes with the second pullback projection. -/
@[reassoc]
theorem comp_hom_snd
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    (c01.comp c12).1.hom ≫ pullback.snd T01.r T12.l =
      pullback.snd S01.r S12.l ≫ c12.1.hom := by
  change (compApexIso c01 c12).hom ≫ pullback.snd T01.r T12.l = _
  unfold compApexIso
  dsimp only
  apply pullback.lift_snd

/-- The composite apex inverse commutes with the first pullback projection. -/
@[reassoc]
theorem comp_inv_fst
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    (c01.comp c12).1.inv ≫ pullback.fst S01.r S12.l =
      pullback.fst T01.r T12.l ≫ c01.1.inv := by
  change (compApexIso c01 c12).inv ≫ pullback.fst S01.r S12.l = _
  unfold compApexIso
  dsimp only
  apply pullback.lift_fst

/-- The composite apex inverse commutes with the second pullback projection. -/
@[reassoc]
theorem comp_inv_snd
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    (c01.comp c12).1.inv ≫ pullback.snd S01.r S12.l =
      pullback.snd T01.r T12.l ≫ c12.1.inv := by
  change (compApexIso c01 c12).inv ≫ pullback.snd S01.r S12.l = _
  unfold compApexIso
  dsimp only
  apply pullback.lift_snd

/-- Binary endpoint comparison composition preserves reflexive comparisons. -/
theorem comp_refl :
    (QuillenSpan.EndpointIso.refl S01).comp
        (QuillenSpan.EndpointIso.refl S12) =
      QuillenSpan.EndpointIso.refl (Span.comp S01 S12) :=
  Subsingleton.elim _ _

/-- Symmetry commutes with binary endpoint comparison composition. -/
theorem comp_symm
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2) :
    (c01.comp c12).symm = c01.symm.comp c12.symm :=
  Subsingleton.elim _ _

/-- Comparison transitivity commutes with binary span composition. -/
theorem comp_trans
    {Z0 Z1 Z2 : C} {U01 : QuillenSpan Z0 Z1}
    {U12 : QuillenSpan Z1 Z2}
    {f0 : Y0 ≅ Z0} {f1 : Y1 ≅ Z1} {f2 : Y2 ≅ Z2}
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2)
    (d01 : QuillenSpan.EndpointIso T01 U01 f0 f1)
    (d12 : QuillenSpan.EndpointIso T12 U12 f1 f2) :
    (c01.trans d01).comp (c12.trans d12) =
      (c01.comp c12).trans (d01.comp d12) :=
  Subsingleton.elim _ _

/-- Rebase an endpoint-compatible comparison along fixed-endpoint raw-span
isomorphisms on its source and target. -/
noncomputable def rebase
    {X X' Y Y' : C}
    {S' S : QuillenSpan X Y} {T T' : QuillenSpan X' Y'}
    {eX : X ≅ X'} {eY : Y ≅ Y'}
    (e : QuillenSpan.EndpointIso S T eX eY)
    (s : S' ≅ S) (t : T ≅ T') :
    QuillenSpan.EndpointIso S' T' eX eY := by
  let sA := Span.SpanBicat.apexIso s
  let tA := Span.SpanBicat.apexIso t
  refine ⟨sA.trans (e.1.trans tA), ?_, ?_⟩
  · change (s.hom.hom ≫ (e.1.hom ≫ t.hom.hom)) ≫ T'.l =
      S'.l ≫ eX.hom
    calc
      _ = s.hom.hom ≫ (e.1.hom ≫ (t.hom.hom ≫ T'.l)) := by
        simp only [Category.assoc]
      _ = s.hom.hom ≫ (e.1.hom ≫ T.l) :=
        congrArg (fun f => s.hom.hom ≫ (e.1.hom ≫ f)) t.hom.hom_l
      _ = s.hom.hom ≫ (S.l ≫ eX.hom) :=
        congrArg (fun f => s.hom.hom ≫ f) e.hom_l
      _ = (s.hom.hom ≫ S.l) ≫ eX.hom := (Category.assoc _ _ _).symm
      _ = S'.l ≫ eX.hom :=
        congrArg (fun f => f ≫ eX.hom) s.hom.hom_l
  · change (s.hom.hom ≫ (e.1.hom ≫ t.hom.hom)) ≫ T'.r =
      S'.r ≫ eY.hom
    calc
      _ = s.hom.hom ≫ (e.1.hom ≫ (t.hom.hom ≫ T'.r)) := by
        simp only [Category.assoc]
      _ = s.hom.hom ≫ (e.1.hom ≫ T.r) :=
        congrArg (fun f => s.hom.hom ≫ (e.1.hom ≫ f)) t.hom.hom_r
      _ = s.hom.hom ≫ (S.r ≫ eY.hom) :=
        congrArg (fun f => s.hom.hom ≫ f) e.hom_r
      _ = (s.hom.hom ≫ S.r) ≫ eY.hom := (Category.assoc _ _ _).symm
      _ = S'.r ≫ eY.hom :=
        congrArg (fun f => f ≫ eY.hom) s.hom.hom_r

@[simp]
theorem rebase_hom_hom
    {X X' Y Y' : C}
    {S' S : QuillenSpan X Y} {T T' : QuillenSpan X' Y'}
    {eX : X ≅ X'} {eY : Y ≅ Y'}
    (e : QuillenSpan.EndpointIso S T eX eY)
    (s : S' ≅ S) (t : T ≅ T') :
    (e.rebase s t).1.hom =
      s.hom.hom ≫ (e.1.hom ≫ t.hom.hom) :=
  rfl

end QuillenSpan.EndpointIso

namespace QuillenSpan

/-- Standard associator isomorphism for three ordered Quillen spans. -/
noncomputable def associator
    {X0 X1 X2 X3 : C}
    (S01 : QuillenSpan X0 X1) (S12 : QuillenSpan X1 X2)
    (S23 : QuillenSpan X2 X3) :
    Span.comp (Span.comp S01 S12) S23 ≅
      Span.comp S01 (Span.comp S12 S23) :=
  Span.SpanBicat.associator
    (c₁ := ⟨X0⟩) (c₂ := ⟨X1⟩) (c₃ := ⟨X2⟩) (c₄ := ⟨X3⟩)
    S01 S12 S23

/-- Transport a fixed-endpoint raw-span isomorphism along endpoint
isomorphisms. -/
noncomputable def endpointTransportIsoMap
    {X X' Y Y' : C} {S T : QuillenSpan X Y}
    (i : S ≅ T) (eX : X ≅ X') (eY : Y ≅ Y') :
    endpointTransport S eX eY ≅ endpointTransport T eX eY := by
  refine Span.mkIso ?_ ?_ ?_
  · change S.apex ≅ T.apex
    exact Span.SpanBicat.apexIso i
  · change i.hom.hom ≫ (T.l ≫ eX.hom) = S.l ≫ eX.hom
    rw [← Category.assoc, i.hom.hom_l]
  · change i.hom.hom ≫ (T.r ≫ eY.hom) = S.r ≫ eY.hom
    rw [← Category.assoc, i.hom.hom_r]

@[simp]
theorem endpointTransportIsoMap_apex
    {X X' Y Y' : C} {S T : QuillenSpan X Y}
    (i : S ≅ T) (eX : X ≅ X') (eY : Y ≅ Y') :
    Span.SpanBicat.apexIso (endpointTransportIsoMap i eX eY) =
      Span.SpanBicat.apexIso i :=
  rfl

end QuillenSpan

namespace QuillenSpan.EndpointIso

/-- Binary endpoint comparison composition is associative after conjugating
by the standard source and target Span associators. -/
theorem comp_assoc
    {X0 X1 X2 X3 Y0 Y1 Y2 Y3 : C}
    {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
    {S23 : QuillenSpan X2 X3}
    {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
    {T23 : QuillenSpan Y2 Y3}
    {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
    {e3 : X3 ≅ Y3}
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2)
    (c23 : QuillenSpan.EndpointIso S23 T23 e2 e3) :
    ((c01.comp c12).comp c23).rebase
        (QuillenSpan.associator S01 S12 S23).symm
        (QuillenSpan.associator T01 T12 T23) =
      c01.comp (c12.comp c23) :=
  Subsingleton.elim _ _

end QuillenSpan.EndpointIso

private theorem endpointCompositionFlagData_ext
    {X Y : C} {S : QuillenSpan X Y}
    (A B : QuillenSpanFlagData S)
    (hKernelObj : A.kernelObj = B.kernelObj)
    (hPushoutObj : A.pushoutObj = B.pushoutObj)
    (hQuotientObj : A.quotientObj = B.quotientObj)
    (hKernelι : HEq A.kernelι B.kernelι)
    (hQuotientπ : HEq A.quotientπ B.quotientπ)
    (hSourceToPushout : HEq A.sourceToPushout B.sourceToPushout)
    (hTargetToPushout : HEq A.targetToPushout B.targetToPushout)
    (hPushoutToQuotient : HEq A.pushoutToQuotient B.pushoutToQuotient) :
    A = B := by
  cases A
  cases B
  simp_all only [QuillenSpanFlagData.mk.injEq, true_and]

/-- Endpoint transport commutes with fixed-endpoint raw-span flag transport. -/
theorem QuillenSpanFlagData.endpointTransport_transport
    {X X' Y Y' : C} {S T : QuillenSpan X Y}
    (i : S ≅ T) (eX : X ≅ X') (eY : Y ≅ Y')
    (A : QuillenSpanFlagData S) :
    (QuillenSpanFlagData.transport i A).endpointTransport eX eY =
      QuillenSpanFlagData.transport
        (QuillenSpan.endpointTransportIsoMap i eX eY)
        (A.endpointTransport eX eY) := by
  apply endpointCompositionFlagData_ext <;>
    simp [QuillenSpan.endpointTransportIsoMap, Span.mkIso]

/-- Canonical material flag comparison for the ordered binary composite of
two adjacent endpoint-compatible span comparisons. -/
noncomputable def QuillenSpanFlagHom.endpointCompCanonical
    {X0 X1 X2 Y0 Y1 Y2 : C}
    {S01 : QuillenSpan X0 X1} {S12 : QuillenSpan X1 X2}
    {T01 : QuillenSpan Y0 Y1} {T12 : QuillenSpan Y1 Y2}
    {e0 : X0 ≅ Y0} {e1 : X1 ≅ Y1} {e2 : X2 ≅ Y2}
    (c01 : QuillenSpan.EndpointIso S01 T01 e0 e1)
    (c12 : QuillenSpan.EndpointIso S12 T12 e1 e2)
    (A : QuillenSpanFlagData (Span.comp S01 S12))
    (B : QuillenSpanFlagData (Span.comp T01 T12)) :
    QuillenSpanFlagData.transport (c01.comp c12).endpointTransportIso
        (A.endpointTransport e0 e2) ⟶ B :=
  QuillenSpanFlagHom.endpointCanonical (c01.comp c12) A B

local instance endpointCompositionWaldhausenCategory : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

noncomputable local instance endpointCompositionShellHasPullback
    {a : SimplexCategory} (A : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r) :
    HasPullback
      (edgewiseStageShellPacket A k l hkl).span.r
      (edgewiseStageShellPacket A l r hlr).span.l :=
  (edgewiseStageShell_isPullback A hkl hlr).hasPullback

/-- The comparisons of two adjacent edgewise Stage shells induce the endpoint
comparison of the long shell, in the ordered `Span.comp` direction. -/
noncomputable def edgewiseStageShellEndpointIsoComp {a : SimplexCategory}
    (A B : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r)
    {eK : (edgewiseStageShellPacket A k l hkl).source ≅
      (edgewiseStageShellPacket B k l hkl).source}
    {eL : (edgewiseStageShellPacket A k l hkl).target ≅
      (edgewiseStageShellPacket B k l hkl).target}
    {eR : (edgewiseStageShellPacket A l r hlr).target ≅
      (edgewiseStageShellPacket B l r hlr).target}
    (cKL : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k l hkl).span
      (edgewiseStageShellPacket B k l hkl).span eK eL)
    (cLR : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A l r hlr).span
      (edgewiseStageShellPacket B l r hlr).span eL eR) :
    QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k r (hkl.trans hlr)).span
      (edgewiseStageShellPacket B k r (hkl.trans hlr)).span eK eR :=
  (cKL.comp cLR).rebase
    (edgewiseStageShellSpanCompIso A hkl hlr)
    (edgewiseStageShellSpanCompIso B hkl hlr).symm

set_option backward.isDefEq.respectTransparency false in
/-- The induced long-shell apex hom restricts to the first short-shell apex
comparison. -/
theorem edgewiseStageShellEndpointIsoComp_hom_left {a : SimplexCategory}
    (A B : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r)
    {eK : (edgewiseStageShellPacket A k l hkl).source ≅
      (edgewiseStageShellPacket B k l hkl).source}
    {eL : (edgewiseStageShellPacket A k l hkl).target ≅
      (edgewiseStageShellPacket B k l hkl).target}
    {eR : (edgewiseStageShellPacket A l r hlr).target ≅
      (edgewiseStageShellPacket B l r hlr).target}
    (cKL : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k l hkl).span
      (edgewiseStageShellPacket B k l hkl).span eK eL)
    (cLR : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A l r hlr).span
      (edgewiseStageShellPacket B l r hlr).span eL eR) :
    (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR).1.hom ≫
        edgewiseStageShellToLeft B hkl hlr =
      edgewiseStageShellToLeft A hkl hlr ≫ cKL.1.hom := by
  let iA := edgewiseStageShellSpanCompIso A hkl hlr
  let iB := edgewiseStageShellSpanCompIso B hkl hlr
  have hBInv :
      iB.inv.hom ≫ edgewiseStageShellToLeft B hkl hlr =
        pullback.fst
          (edgewiseStageShellPacket B k l hkl).span.r
          (edgewiseStageShellPacket B l r hlr).span.l := by
    rw [← edgewiseStageShellSpanCompIso_hom_fst B hkl hlr]
    simp [iB]
  have hComp := QuillenSpan.EndpointIso.comp_hom_fst cKL cLR
  have hA := edgewiseStageShellSpanCompIso_hom_fst A hkl hlr
  change (iA.hom.hom ≫
      ((cKL.comp cLR).1.hom ≫ iB.inv.hom)) ≫
        edgewiseStageShellToLeft B hkl hlr = _
  calc
    _ = iA.hom.hom ≫
        ((cKL.comp cLR).1.hom ≫
          (iB.inv.hom ≫ edgewiseStageShellToLeft B hkl hlr)) := by
      simp only [Category.assoc]
    _ = iA.hom.hom ≫
        ((cKL.comp cLR).1.hom ≫ pullback.fst _ _) := by rw [hBInv]
    _ = iA.hom.hom ≫
        (pullback.fst _ _ ≫ cKL.1.hom) :=
      congrArg (fun f => iA.hom.hom ≫ f) hComp
    _ = (iA.hom.hom ≫ pullback.fst _ _) ≫ cKL.1.hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ cKL.1.hom) hA

set_option backward.isDefEq.respectTransparency false in
/-- The induced long-shell apex hom restricts to the second short-shell apex
comparison. -/
theorem edgewiseStageShellEndpointIsoComp_hom_right {a : SimplexCategory}
    (A B : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r)
    {eK : (edgewiseStageShellPacket A k l hkl).source ≅
      (edgewiseStageShellPacket B k l hkl).source}
    {eL : (edgewiseStageShellPacket A k l hkl).target ≅
      (edgewiseStageShellPacket B k l hkl).target}
    {eR : (edgewiseStageShellPacket A l r hlr).target ≅
      (edgewiseStageShellPacket B l r hlr).target}
    (cKL : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k l hkl).span
      (edgewiseStageShellPacket B k l hkl).span eK eL)
    (cLR : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A l r hlr).span
      (edgewiseStageShellPacket B l r hlr).span eL eR) :
    (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR).1.hom ≫
        edgewiseStageShellToRight B hkl hlr =
      edgewiseStageShellToRight A hkl hlr ≫ cLR.1.hom := by
  let iA := edgewiseStageShellSpanCompIso A hkl hlr
  let iB := edgewiseStageShellSpanCompIso B hkl hlr
  have hBInv :
      iB.inv.hom ≫ edgewiseStageShellToRight B hkl hlr =
        pullback.snd
          (edgewiseStageShellPacket B k l hkl).span.r
          (edgewiseStageShellPacket B l r hlr).span.l := by
    rw [← edgewiseStageShellSpanCompIso_hom_snd B hkl hlr]
    simp [iB]
  have hComp := QuillenSpan.EndpointIso.comp_hom_snd cKL cLR
  have hA := edgewiseStageShellSpanCompIso_hom_snd A hkl hlr
  change (iA.hom.hom ≫
      ((cKL.comp cLR).1.hom ≫ iB.inv.hom)) ≫
        edgewiseStageShellToRight B hkl hlr = _
  calc
    _ = iA.hom.hom ≫
        ((cKL.comp cLR).1.hom ≫
          (iB.inv.hom ≫ edgewiseStageShellToRight B hkl hlr)) := by
      simp only [Category.assoc]
    _ = iA.hom.hom ≫
        ((cKL.comp cLR).1.hom ≫ pullback.snd _ _) := by rw [hBInv]
    _ = iA.hom.hom ≫
        (pullback.snd _ _ ≫ cLR.1.hom) :=
      congrArg (fun f => iA.hom.hom ≫ f) hComp
    _ = (iA.hom.hom ≫ pullback.snd _ _) ≫ cLR.1.hom :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun f => f ≫ cLR.1.hom) hA

/-- Canonical material comparison between the two long-shell flags induced by
the ordered pair of adjacent endpoint-compatible shell comparisons. -/
noncomputable def edgewiseStageShellFlagEndpointCompCanonical
    {a : SimplexCategory}
    (A B : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r)
    {eK : (edgewiseStageShellPacket A k l hkl).source ≅
      (edgewiseStageShellPacket B k l hkl).source}
    {eL : (edgewiseStageShellPacket A k l hkl).target ≅
      (edgewiseStageShellPacket B k l hkl).target}
    {eR : (edgewiseStageShellPacket A l r hlr).target ≅
      (edgewiseStageShellPacket B l r hlr).target}
    (cKL : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k l hkl).span
      (edgewiseStageShellPacket B k l hkl).span eK eL)
    (cLR : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A l r hlr).span
      (edgewiseStageShellPacket B l r hlr).span eL eR) :
    let cLong := edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR
    QuillenSpanFlagData.transport cLong.endpointTransportIso
        ((edgewiseStageShellPacket A k r (hkl.trans hlr)).flag.endpointTransport
          eK eR) ⟶
      (edgewiseStageShellPacket B k r (hkl.trans hlr)).flag :=
  QuillenSpanFlagHom.endpointCanonical
    (edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR)
    (edgewiseStageShellPacket A k r (hkl.trans hlr)).flag
    (edgewiseStageShellPacket B k r (hkl.trans hlr)).flag

set_option backward.isDefEq.respectTransparency false in
/-- Transporting the long-shell comparison to the chosen pullback composite
agrees with the source flag of the ordered binary composite comparison. -/
theorem edgewiseStageShellFlagEndpointComp_source {a : SimplexCategory}
    (A B : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r)
    {eK : (edgewiseStageShellPacket A k l hkl).source ≅
      (edgewiseStageShellPacket B k l hkl).source}
    {eL : (edgewiseStageShellPacket A k l hkl).target ≅
      (edgewiseStageShellPacket B k l hkl).target}
    {eR : (edgewiseStageShellPacket A l r hlr).target ≅
      (edgewiseStageShellPacket B l r hlr).target}
    (cKL : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k l hkl).span
      (edgewiseStageShellPacket B k l hkl).span eK eL)
    (cLR : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A l r hlr).span
      (edgewiseStageShellPacket B l r hlr).span eL eR) :
    let iA := edgewiseStageShellSpanCompIso A hkl hlr
    let iB := edgewiseStageShellSpanCompIso B hkl hlr
    let c := cKL.comp cLR
    let cLong := edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR
    let FA := (edgewiseStageShellPacket A k r (hkl.trans hlr)).flag
    QuillenSpanFlagData.transport iB
        (QuillenSpanFlagData.transport cLong.endpointTransportIso
          (FA.endpointTransport eK eR)) =
      QuillenSpanFlagData.transport c.endpointTransportIso
        ((QuillenSpanFlagData.transport iA FA).endpointTransport eK eR) := by
  dsimp only
  let iA := edgewiseStageShellSpanCompIso A hkl hlr
  let iB := edgewiseStageShellSpanCompIso B hkl hlr
  let c := cKL.comp cLR
  let cLong := edgewiseStageShellEndpointIsoComp A B hkl hlr cKL cLR
  let FA := (edgewiseStageShellPacket A k r (hkl.trans hlr)).flag
  let FAE := FA.endpointTransport eK eR
  let iAE := QuillenSpan.endpointTransportIsoMap iA eK eR
  have hiB : iB.inv.hom ≫ iB.hom.hom = 𝟙 _ := by
    change (Span.SpanBicat.apexIso iB).inv ≫
        (Span.SpanBicat.apexIso iB).hom = 𝟙 _
    exact (Span.SpanBicat.apexIso iB).inv_hom_id
  have hIso : cLong.endpointTransportIso ≪≫ iB =
      iAE ≪≫ c.endpointTransportIso := by
    apply Iso.ext
    apply Span.hom_ext
    change (cLong.1.hom ≫ iB.hom.hom) = iA.hom.hom ≫ c.1.hom
    change ((iA.hom.hom ≫ (c.1.hom ≫ iB.inv.hom)) ≫
      iB.hom.hom) = _
    calc
      _ = (iA.hom.hom ≫ c.1.hom) ≫
          (iB.inv.hom ≫ iB.hom.hom) := by
        simp only [Category.assoc]
      _ = (iA.hom.hom ≫ c.1.hom) ≫ 𝟙 _ :=
        congrArg (fun f => (iA.hom.hom ≫ c.1.hom) ≫ f) hiB
      _ = _ := Category.comp_id _
  calc
    QuillenSpanFlagData.transport iB
        (QuillenSpanFlagData.transport cLong.endpointTransportIso FAE) =
      QuillenSpanFlagData.transport
        (cLong.endpointTransportIso ≪≫ iB) FAE :=
      (QuillenSpanFlagData.transport_trans
        cLong.endpointTransportIso iB FAE).symm
    _ = QuillenSpanFlagData.transport
        (iAE ≪≫ c.endpointTransportIso) FAE := by rw [hIso]
    _ = QuillenSpanFlagData.transport c.endpointTransportIso
        (QuillenSpanFlagData.transport iAE FAE) :=
      QuillenSpanFlagData.transport_trans iAE c.endpointTransportIso FAE
    _ = QuillenSpanFlagData.transport c.endpointTransportIso
        ((QuillenSpanFlagData.transport iA FA).endpointTransport eK eR) := by
      rw [QuillenSpanFlagData.endpointTransport_transport]

set_option backward.isDefEq.respectTransparency false in
/-- After the long-shell source identification, the transported long canonical
flag map is the canonical flag map of the ordered binary composite. -/
theorem edgewiseStageShellFlagEndpointComp_map {a : SimplexCategory}
    (A B : Stage C (edgewiseQ.obj a).len)
    {k l r : Fin (a.len + 1)} (hkl : k ≤ l) (hlr : l ≤ r)
    {eK : (edgewiseStageShellPacket A k l hkl).source ≅
      (edgewiseStageShellPacket B k l hkl).source}
    {eL : (edgewiseStageShellPacket A k l hkl).target ≅
      (edgewiseStageShellPacket B k l hkl).target}
    {eR : (edgewiseStageShellPacket A l r hlr).target ≅
      (edgewiseStageShellPacket B l r hlr).target}
    (cKL : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A k l hkl).span
      (edgewiseStageShellPacket B k l hkl).span eK eL)
    (cLR : QuillenSpan.EndpointIso
      (edgewiseStageShellPacket A l r hlr).span
      (edgewiseStageShellPacket B l r hlr).span eL eR) :
    let iA := edgewiseStageShellSpanCompIso A hkl hlr
    let iB := edgewiseStageShellSpanCompIso B hkl hlr
    let FA := (edgewiseStageShellPacket A k r (hkl.trans hlr)).flag
    let FB := (edgewiseStageShellPacket B k r (hkl.trans hlr)).flag
    let hSource := edgewiseStageShellFlagEndpointComp_source
      A B hkl hlr cKL cLR
    eqToHom hSource ≫
        QuillenSpanFlagHom.endpointCompCanonical cKL cLR
          (QuillenSpanFlagData.transport iA FA)
          (QuillenSpanFlagData.transport iB FB) =
      (QuillenSpanFlagData.transportFunctor iB).map
        (edgewiseStageShellFlagEndpointCompCanonical
          A B hkl hlr cKL cLR) := by
  dsimp only
  apply Subsingleton.elim

end AlgebraicKTheory

end
