/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitGroupoidCloneDescReadback
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanRetracts

/-!
# The SAME original unit-groupoid point pushout and its actual weak map

The complete clone descender retains both original cocone functors,
including all original full Hom coefficients and inverse unit maps.
Actual whole coordinate readback proves uniqueness. Thus the original
unit-groupoid/point square is genuinely a global carrier pushout, and
its SAME original source map is DK weak without Kan premises.
-/

noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.UnitGroupoidClone

/-- Exact whole original clone triangles determine the SAME genuine enriched descender. -/
theorem cloneDesc_unique (C : Carrier.{u}) (x : C) {E : Type v} [EnrichedCategory SSet.{u} E]
    (F : EnrichedFunctor SSet.{u} C E) (y : E)
    (α : ForgetEnrichment.of SSet.{u} (F.obj x) ≅ ForgetEnrichment.of SSet.{u} y)
    (H : EnrichedFunctor SSet.{u} (object C x) E)
    (hF : (inclusion C x).comp SSet.{u} H = F)
    (hG : (unitMap C x).comp SSet.{u} H = OriginalTwoLabelUnitGroupoid.ofIso (F.obj x) y α) :
    H = cloneDesc C x F y α := by
  cases hF
  have hy := congrArg (fun G : EnrichedFunctor SSet.{u} unitDomain.{u} E =>
    G.obj OriginalTwoLabelUnitGroupoid.target) hG
  change H.obj (newObject C x) = y at hy
  cases hy
  have hi (G K : EnrichedFunctor SSet.{u} unitDomain.{u} E) (h : G = K) :
      HEq (OriginalTwoLabelUnitGroupoid.originalIso G) (OriginalTwoLabelUnitGroupoid.originalIso K) := by
    cases h
    rfl
  have hg := eq_of_heq (hi ((unitMap C x).comp SSet.{u} H)
    (OriginalTwoLabelUnitGroupoid.ofIso (((inclusion C x).comp SSet.{u} H).obj x)
      (H.obj (newObject C x)) α) hG)
  have hα : H.forget.mapIso (unitCoordinateIso C x) = α :=
    (unitCoordinateIso_map x H).trans
      (hg.trans
          (OriginalTwoLabelUnitGroupoid.originalIso_ofIso
            (((inclusion C x).comp SSet.{u} H).obj x) (H.obj (newObject C x)) α))
  cases hα
  exact (cloneDesc_readback C x H).symm

/-- The SAME original source-point map into the actual complete two-label unit groupoid. -/
abbrev unitPoint : BergnerObjects.point.{u} ⟶ unitDomain.{u} :=
  BergnerObjects.select (C := unitDomain.{u}) OriginalTwoLabelUnitGroupoid.source

variable (C : Carrier.{u}) (x : C)

/-- Both SAME original full point selections commute in the actual clone square. -/
theorem unitSquare_condition : unitPoint.{u} ≫ unitMap C x =
    BergnerObjects.select (C := C) x ≫ inclusion C x :=
  (unitMap_source C x).trans (BergnerObjects.select_comp (C := C) (D := object C x) x (inclusion C x)).symm

/-- The actual original complete unit-groupoid point pushout cocone. -/
def unitPushoutCocone : PushoutCocone unitPoint.{u} (BergnerObjects.select (C := C) x) :=
  PushoutCocone.mk (unitMap C x) (inclusion C x) (unitSquare_condition C x)

variable (s : PushoutCocone unitPoint.{u} (BergnerObjects.select (C := C) x))

/-- The SAME actual original cocone forces precisely its original source-object equality. -/
theorem unitCocone_source : s.inl.obj OriginalTwoLabelUnitGroupoid.source = s.inr.obj x :=
  congrArg (fun F : BergnerObjects.point.{u} ⟶ s.pt => F.obj PUnit.unit) s.condition

/-- The actual original cocone unit isomorphism retains both SAME original target objects. -/
def unitCoconeIso : ForgetEnrichment.of (C := s.pt) SSet.{u} (s.inr.obj x) ≅
    ForgetEnrichment.of (C := s.pt) SSet.{u} (s.inl.obj OriginalTwoLabelUnitGroupoid.target) :=
  eqToIso (congrArg (ForgetEnrichment.of (C := s.pt) SSet.{u}) (unitCocone_source C x s).symm) ≪≫
    OriginalTwoLabelUnitGroupoid.originalIso s.inl

/-- The SAME whole original unit-groupoid cocone evaluates every original full clone coefficient. -/
def unitPushoutDesc : object C x ⟶ s.pt :=
  cloneDesc C x s.inr (s.inl.obj OriginalTwoLabelUnitGroupoid.target) (unitCoconeIso C x s)

/-- The actual complete original unit-groupoid leg factors through the SAME descender. -/
theorem unitPushoutDesc_left : unitMap C x ≫ unitPushoutDesc C x s = s.inl :=
  (cloneDesc_unit C x s.inr (s.inl.obj OriginalTwoLabelUnitGroupoid.target) (unitCoconeIso C x s)).trans
    (OriginalTwoLabelUnitGroupoid.ofIso_readback_at_source s.inl (s.inr.obj x) (unitCocone_source C x s))

/-- The actual complete original old-source leg factors through the SAME descender. -/
theorem unitPushoutDesc_right : inclusion C x ≫ unitPushoutDesc C x s = s.inr :=
  cloneDesc_left C x s.inr (s.inl.obj OriginalTwoLabelUnitGroupoid.target) (unitCoconeIso C x s)

/-- The actual full original unit-groupoid point cocone has its genuine complete carrier universal property. -/
def unitPushoutIsColimit : IsColimit (unitPushoutCocone C x) :=
  PushoutCocone.IsColimit.mk (unitSquare_condition C x) (unitPushoutDesc C x)
    (unitPushoutDesc_left C x) (unitPushoutDesc_right C x)
    (fun s H hG hF => cloneDesc_unique C x s.inr
      (s.inl.obj OriginalTwoLabelUnitGroupoid.target) (unitCoconeIso C x s) H hF
        (hG.trans (OriginalTwoLabelUnitGroupoid.ofIso_readback_at_source s.inl (s.inr.obj x)
          (unitCocone_source C x s)).symm))

/-- The SAME original full unit-groupoid point square is genuinely a varying-object carrier pushout. -/
theorem unit_isPushout : IsPushout unitPoint.{u} (BergnerObjects.select (C := C) x) (unitMap C x) (inclusion C x) :=
  IsPushout.of_isColimit (unitPushoutIsColimit C x)

/-- Any actual original unit-groupoid point pushout retains the SAME original DK-weak source map. -/
theorem unit_pushout_weak {D : Carrier.{u}} (a : unitDomain.{u} ⟶ D) (b : C ⟶ D)
    (sq : IsPushout unitPoint.{u} (BergnerObjects.select (C := C) x) a b) :
    EnrichedDwyerKan.weakEquivalences b := by
  let e := (unit_isPushout C x).isoIsPushout _ _ sq
  have he : inclusion C x ≫ e.hom = b := (unit_isPushout C x).inr_isoIsPushout_hom _ _ sq
  have hw := EnrichedDwyerKan.weakEquivalences.comp_mem _ _ (inclusion_weak C x)
    (EnrichedDwyerKan.weakEquivalences.of_isIso e.hom)
  exact he ▸ hw

end CategoryTheory.SimplicialEnrichment.UnitGroupoidClone
