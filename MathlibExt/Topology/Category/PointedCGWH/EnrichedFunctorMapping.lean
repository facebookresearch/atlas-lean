/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Enriched.GradingConvention
public import MathlibExt.CategoryTheory.Enriched.MappingEndOrientation
public import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds
public import MathlibExt.CategoryTheory.Enriched.FunctorCategory
public import MathlibExt.CategoryTheory.Enriched.Limits.WeightedEnd
public import MathlibExt.Topology.Category.PointedCGWH.Closed
public import MathlibExt.Topology.Category.CGWH.Limits
public import Mathlib.CategoryTheory.Limits.Comma

/-!
# Full native represented graded transformations

The full weighted end on a genuine pointed CGWH functor carrier represents
the pinned positive graded-transformation presheaf. The native symmetry
supplies the positive/reverse grading equality. Native small limits supply
the actual particular end; no end-existence or model packet is an input.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped CGWH.limits MonoidalClosed

namespace PointedCGWH.EnrichedFunctorMapping

attribute [local instance] MonoidalClosed.enrichedCategorySelf

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The actual full native Hom naturality end on a small enriched source. -/
abbrev mappingObject : PointedCGWH.{u, v} :=
  Enriched.weightedEnd X.toEnrichedFunctor Y.toEnrichedFunctor

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- Every original enriched source object gives its complete native internal-Hom projection. -/
abbrev π (a : I) : mappingObject X Y ⟶
    (ihom (X.toEnrichedFunctor.obj a)).obj (Y.toEnrichedFunctor.obj a) :=
  Enriched.weightedEnd.π X.toEnrichedFunctor Y.toEnrichedFunctor a

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private def tautologicalGrade :
    GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (mappingObject X Y))
      X.toEnrichedFunctor Y.toEnrichedFunctor where
  app := π X Y
  naturality a b := by
    dsimp only [Center.ofBraided, Center.ofBraidedObj]
    apply (MappingEndOrientationProbe.canonicalNaturality_iff_endRelation
      (Wₛ := X.toEnrichedFunctor) (Fₛ := Y.toEnrichedFunctor) (π X Y) a b).2
    simpa only [MappingEndOrientationProbe.endLeft, MappingEndOrientationProbe.endRight] using
      Enriched.weightedEnd.condition X.toEnrichedFunctor Y.toEnrichedFunctor a b

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- An actual native end arrow gives the pinned positive graded transformation. -/
@[no_expose]
def toGrade (T : PointedCGWH.{u, v}) (f : T ⟶ mappingObject X Y) :
    GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor :=
  (enrichedNatTransYoneda X.toEnrichedFunctor Y.toEnrichedFunctor).map f.op
    (tautologicalGrade X Y)

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private theorem toGrade_app_private (T : PointedCGWH.{u, v})
    (f : T ⟶ mappingObject X Y) (a : I) :
    (toGrade X Y T f).app a = f ≫ π X Y a := rfl

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The full native conversion retains every actual original end projection. -/
theorem toGrade_app (T : PointedCGWH.{u, v}) (f : T ⟶ mappingObject X Y) (a : I) :
    (toGrade X Y T f).app a = f ≫ π X Y a :=
  toGrade_app_private X Y T f a

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private theorem gradeCondition {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) (a b : I) :
    MonoidalClosed.curry (MappingEndOrientationProbe.endLeft
      (W := X.toEnrichedFunctor) (F := Y.toEnrichedFunctor) (K := T) σ.app a b) =
      MonoidalClosed.curry (MappingEndOrientationProbe.endRight
        (W := X.toEnrichedFunctor) (F := Y.toEnrichedFunctor) (K := T) σ.app a b) := by
  have h := σ.naturality a b
  dsimp only [Center.ofBraided, Center.ofBraidedObj] at h
  exact (MappingEndOrientationProbe.canonicalNaturality_iff_endRelation
    (Wₛ := X.toEnrichedFunctor) (Fₛ := Y.toEnrichedFunctor) (M := T) σ.app a b).1 h

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The full pinned positive graded transformation lifts to the actual native end. -/
@[no_expose]
def ofGrade {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) : T ⟶ mappingObject X Y :=
  Enriched.weightedEnd.lift (X := T) X.toEnrichedFunctor Y.toEnrichedFunctor σ.app
    (fun a b => by
      simpa only [MappingEndOrientationProbe.endLeft, MappingEndOrientationProbe.endRight] using
        gradeCondition X Y σ a b)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private theorem ofGrade_π_private {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) (a : I) :
    ofGrade X Y σ ≫ π X Y a = σ.app a :=
  Enriched.weightedEnd.lift_π (X := T) X.toEnrichedFunctor Y.toEnrichedFunctor σ.app
    (fun a b => by
      simpa only [MappingEndOrientationProbe.endLeft, MappingEndOrientationProbe.endRight] using
        gradeCondition X Y σ a b) a

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The chosen inverse map retains the complete original graded component family. -/
@[reassoc]
theorem ofGrade_π {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) (a : I) :
    ofGrade X Y σ ≫ π X Y a = σ.app a :=
  ofGrade_π_private X Y σ a

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- Native end arrows and pinned positive graded transformations are equivalent
at every coefficient. -/
@[no_expose]
def gradeEquiv (T : PointedCGWH.{u, v}) :
    (T ⟶ mappingObject X Y) ≃
      GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
        X.toEnrichedFunctor Y.toEnrichedFunctor where
  toFun := toGrade X Y T
  invFun := ofGrade X Y
  left_inv f := by
    apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y.toEnrichedFunctor
    intro a
    rw [ofGrade_π, toGrade_app]
  right_inv σ := by
    apply GradedNatTrans.ext
    funext a
    rw [toGrade_app, ofGrade_π]

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private theorem gradeEquiv_apply_private (T : PointedCGWH.{u, v})
    (f : T ⟶ mappingObject X Y) : gradeEquiv X Y T f = toGrade X Y T f := rfl

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The coefficient equivalence uses the original chosen native conversion map. -/
theorem gradeEquiv_apply (T : PointedCGWH.{u, v}) (f : T ⟶ mappingObject X Y) :
    gradeEquiv X Y T f = toGrade X Y T f :=
  gradeEquiv_apply_private X Y T f

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private theorem gradeEquiv_symm_apply_private {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) :
    (gradeEquiv X Y T).symm σ = ofGrade X Y σ := rfl

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The coefficient equivalence uses the original chosen lift as its inverse. -/
theorem gradeEquiv_symm_apply {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) :
    (gradeEquiv X Y T).symm σ = ofGrade X Y σ :=
  gradeEquiv_symm_apply_private X Y σ

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- Every actual coefficient arrow commutes with the full forward conversion. -/
theorem toGrade_precomp {T T' : PointedCGWH.{u, v}} (f : T' ⟶ T)
    (g : T ⟶ mappingObject X Y) :
    (enrichedNatTransYoneda X.toEnrichedFunctor Y.toEnrichedFunctor).map f.op
        (toGrade X Y T g) = toGrade X Y T' (f ≫ g) := by
  apply GradedNatTrans.ext
  funext a
  change f ≫ (toGrade X Y T g).app a = (toGrade X Y T' (f ≫ g)).app a
  rw [toGrade_app, toGrade_app, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- Every actual coefficient arrow commutes with the full original native lift. -/
theorem ofGrade_precomp {T T' : PointedCGWH.{u, v}} (f : T' ⟶ T)
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) :
    ofGrade X Y
        ((enrichedNatTransYoneda X.toEnrichedFunctor Y.toEnrichedFunctor).map f.op σ) =
      f ≫ ofGrade X Y σ := by
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y.toEnrichedFunctor
  intro a
  rw [ofGrade_π, Category.assoc, ofGrade_π]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The actual native end represents the entire pinned positive graded-transformation presheaf. -/
@[no_expose]
def representedPresheafIso :
    yoneda.obj (mappingObject X Y) ≅
      enrichedNatTransYoneda X.toEnrichedFunctor Y.toEnrichedFunctor :=
  NatIso.ofComponents (fun T => (gradeEquiv X Y T.unop).toIso)
    (fun {A B} f => by
      refine ConcreteCategory.hom_ext _ _ (fun g => ?_)
      change gradeEquiv X Y B.unop (f.unop ≫ g) =
        (enrichedNatTransYoneda X.toEnrichedFunctor Y.toEnrichedFunctor).map f
          (gradeEquiv X Y A.unop g)
      rw [gradeEquiv_apply, gradeEquiv_apply]
      exact (toGrade_precomp X Y f.unop g).symm)

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private theorem representedPresheafIso_hom_app_private
    (T : PointedCGWH.{u, v}) (f : T ⟶ mappingObject X Y) :
    (representedPresheafIso X Y).hom.app (op T) f = toGrade X Y T f := rfl

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The whole presheaf isomorphism retains its chosen map at every native coefficient. -/
theorem representedPresheafIso_hom_app
    (T : PointedCGWH.{u, v}) (f : T ⟶ mappingObject X Y) :
    (representedPresheafIso X Y).hom.app (op T) f = toGrade X Y T f :=
  representedPresheafIso_hom_app_private X Y T f

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
private theorem representedPresheafIso_inv_app_private {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) :
    (representedPresheafIso X Y).inv.app (op T) σ = ofGrade X Y σ := rfl

set_option maxHeartbeats 200000 in
-- Preserve the original budget for the full native mapping or Kan construction.
/-- The whole presheaf isomorphism retains its chosen original lift at every native coefficient. -/
theorem representedPresheafIso_inv_app {T : PointedCGWH.{u, v}}
    (σ : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
      X.toEnrichedFunctor Y.toEnrichedFunctor) :
    (representedPresheafIso X Y).inv.app (op T) σ = ofGrade X Y σ :=
  representedPresheafIso_inv_app_private X Y σ



/-- The entire chosen native forward conversion is the canonical positive weighted-end function. -/
theorem toGrade_eq_endToPositive (T : PointedCGWH.{u, v}) :
    toGrade X Y T =
      GradingConvention.endToPositive X.toEnrichedFunctor Y.toEnrichedFunctor (K := T) := by
  funext f
  apply GradedNatTrans.ext
  funext a
  exact (toGrade_app X Y T f a).trans
    (GradingConvention.endToPositive_app_symmetric
      X.toEnrichedFunctor Y.toEnrichedFunctor f a).symm

/-- The entire chosen native inverse is the canonical positive weighted-end lift function. -/
theorem ofGrade_eq_endFromPositive (T : PointedCGWH.{u, v}) :
    (ofGrade X Y (T := T)) =
      GradingConvention.endFromPositive X.toEnrichedFunctor Y.toEnrichedFunctor (K := T) := by
  funext t
  apply Enriched.weightedEnd.hom_ext X.toEnrichedFunctor Y.toEnrichedFunctor
  intro a
  exact (ofGrade_π X Y t a).trans
    (GradingConvention.endFromPositive_symmetric_π
      X.toEnrichedFunctor Y.toEnrichedFunctor t a).symm

end PointedCGWH.EnrichedFunctorMapping
