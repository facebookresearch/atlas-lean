/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.PointedCGWH.EnrichedFunctorMapping
public import MathlibExt.CategoryTheory.Enriched.GradedTensor

/-!
# Actual native scalar tensor and full mapping-end correspondence

The native end/positive-grade equivalence composes with the complete shared
central-grade/scalar tensor correspondence. Both original component maps
are retained, and native coefficient regrading is the actual shared scalar
transformation. No scalar-Hom equivalence or end witness is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section

universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace PointedCGWH.EnrichedFunctorMapping

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  (X Y : EnrichedFunctorCat PointedCGWH.{u, v} I)

set_option backward.isDefEq.respectTransparency false in
/-- The actual fixed-left native scalar functor is closed against the full original native end. -/
@[no_expose]
def tensorHomEquiv (T : PointedCGWH.{u, v}) :
    (T ⟶ mappingObject X Y) ≃ (EnrichedFunctorCat.tensorLeftObject T X ⟶ Y) :=
  (gradeEquiv X Y T).trans
    (EnrichedFunctorCat.gradedTensorHomEquiv
      ((Center.ofBraided PointedCGWH.{u, v}).obj T) X Y)

private theorem tensorHomEquiv_apply_private (T : PointedCGWH.{u, v})
    (f : T ⟶ mappingObject X Y) :
    tensorHomEquiv X Y T f = EnrichedFunctorCat.gradedTensorToUnit
      ((Center.ofBraided PointedCGWH.{u, v}).obj T) (toGrade X Y T f) := by
  change EnrichedFunctorCat.gradedTensorHomEquiv
    ((Center.ofBraided PointedCGWH.{u, v}).obj T) X Y (gradeEquiv X Y T f) = _
  rw [gradeEquiv_apply]
  rfl

/-- The native closed correspondence retains the actual chosen graded-to-scalar map. -/
theorem tensorHomEquiv_apply (T : PointedCGWH.{u, v}) (f : T ⟶ mappingObject X Y) :
    tensorHomEquiv X Y T f = EnrichedFunctorCat.gradedTensorToUnit
      ((Center.ofBraided PointedCGWH.{u, v}).obj T) (toGrade X Y T f) :=
  tensorHomEquiv_apply_private X Y T f

set_option backward.isDefEq.respectTransparency false in
private theorem tensorHomEquiv_symm_apply_private (T : PointedCGWH.{u, v})
    (f : EnrichedFunctorCat.tensorLeftObject T X ⟶ Y) :
    (tensorHomEquiv X Y T).symm f = ofGrade X Y
      (EnrichedFunctorCat.gradedTensorOfUnit
        ((Center.ofBraided PointedCGWH.{u, v}).obj T) f) := by
  change (gradeEquiv X Y T).symm
    ((EnrichedFunctorCat.gradedTensorHomEquiv
      ((Center.ofBraided PointedCGWH.{u, v}).obj T) X Y).symm f) = _
  rw [gradeEquiv_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native inverse retains the actual chosen scalar-to-grade map and original end lift. -/
theorem tensorHomEquiv_symm_apply (T : PointedCGWH.{u, v})
    (f : EnrichedFunctorCat.tensorLeftObject T X ⟶ Y) :
    (tensorHomEquiv X Y T).symm f = ofGrade X Y
      (EnrichedFunctorCat.gradedTensorOfUnit
        ((Center.ofBraided PointedCGWH.{u, v}).obj T) f) :=
  tensorHomEquiv_symm_apply_private X Y T f

set_option backward.isDefEq.respectTransparency false in
/-- Every native scalar component is the positive braid followed by full end evaluation. -/
theorem tensorHomEquiv_component (T : PointedCGWH.{u, v})
    (f : T ⟶ mappingObject X Y) (a : I) :
    EnrichedFunctorCat.component (tensorHomEquiv X Y T f) a =
      (β_ T (X.toEnrichedFunctor.obj a)).hom ≫ MonoidalClosed.uncurry (f ≫ π X Y a) := by
  rw [tensorHomEquiv_apply, EnrichedFunctorCat.gradedTensorToUnit_component]
  dsimp only [GradedNatTrans.gradeFirstComponent, Center.ofBraided, Center.ofBraidedObj]
  rw [toGrade_app]

set_option backward.isDefEq.respectTransparency false in
/-- Every original inverse projection retains the actual inverse braid and scalar component. -/
theorem tensorHomEquiv_symm_π (T : PointedCGWH.{u, v})
    (f : EnrichedFunctorCat.tensorLeftObject T X ⟶ Y) (a : I) :
    (tensorHomEquiv X Y T).symm f ≫ π X Y a =
      MonoidalClosed.curry
        ((β_ T (X.toEnrichedFunctor.obj a)).inv ≫ EnrichedFunctorCat.component f a) := by
  rw [tensorHomEquiv_symm_apply, ofGrade_π, EnrichedFunctorCat.gradedTensorOfUnit_app]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The native closed correspondence is natural in every actual scalar arrow. -/
theorem tensorHomEquiv_coefficient_naturality {T T' : PointedCGWH.{u, v}}
    (h : T' ⟶ T) (f : T ⟶ mappingObject X Y) :
    tensorHomEquiv X Y T' (h ≫ f) =
      EnrichedFunctorCat.scalarTensorMap h X ≫ tensorHomEquiv X Y T f := by
  rw [tensorHomEquiv_apply, tensorHomEquiv_apply, ← toGrade_precomp]
  have hRegrade :
      (enrichedNatTransYoneda X.toEnrichedFunctor Y.toEnrichedFunctor).map h.op
          (toGrade X Y T f) =
        GradedNatTrans.regrade ((Center.ofBraided PointedCGWH.{u, v}).map h)
          (toGrade X Y T f) := by
    apply GradedNatTrans.ext
    funext a
    rfl
  rw [hRegrade]
  exact EnrichedFunctorCat.gradedTensorToUnit_regrade
    ((Center.ofBraided PointedCGWH.{u, v}).map h) (toGrade X Y T f)



/-- The complete original native Hom record is the canonical end representation
followed by tensor conversion. -/
theorem tensorHomEquiv_eq_endHomEquiv (T : PointedCGWH.{u, v}) :
    tensorHomEquiv X Y T =
      (GradingConvention.endHomEquiv X.toEnrichedFunctor Y.toEnrichedFunctor T).trans
        (EnrichedFunctorCat.gradedTensorHomEquiv
          ((Center.ofBraided PointedCGWH.{u, v}).obj T) X Y) := by
  have hGrade : gradeEquiv X Y T =
      GradingConvention.endHomEquiv X.toEnrichedFunctor Y.toEnrichedFunctor T := by
    apply Equiv.ext
    intro f
    rw [gradeEquiv_apply, GradingConvention.endHomEquiv_apply]
    exact congrFun (toGrade_eq_endToPositive X Y T) f
  exact congrArg (fun e : (T ⟶ mappingObject X Y) ≃
      GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj T)
        X.toEnrichedFunctor Y.toEnrichedFunctor =>
    e.trans (EnrichedFunctorCat.gradedTensorHomEquiv
      ((Center.ofBraided PointedCGWH.{u, v}).obj T) X Y)) hGrade

end PointedCGWH.EnrichedFunctorMapping
