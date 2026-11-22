/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.StandardRightFreeEvaluation

/-!
# Whole original standard RIGHT free comparison on the actual full J source
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed
namespace PointedCGWH.OriginalStandardRightFreeLevels

attribute [local instance] originalSymmetricSequenceMonoidal
  originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal sphereSequenceMonObj
  sphereSequenceIsCommMonObj MonoidalLeftAction.monoidalOppositeLeftAction

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse-carrier free is compared on every full J Hom by the original counit. -/
@[no_expose]
def nativeOperatorFreeIso (e : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.nativeFreeFunctor.{u, v} e ⋙
      SymmetricRightModulePresentation.rightModuleToOperator.{u, v} ≅
        EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e) := by
  rw [SymmetricStandardRightFreeEvaluation.nativeFreeFunctor_eq]
  let E := SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}
  let L := EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
    (symmetricOperatorObj.{u, v} e)
  change (L ⋙ E.inverse) ⋙ E.functor ≅ L
  exact Functor.associator L E.inverse E.functor ≪≫
    Functor.isoWhiskerLeft L E.counitIso ≪≫ Functor.rightUnitor L

/-- The actual original standard right free carries its whole unchanged J-diagram comparison. -/
@[no_expose]
def originalOperatorFreeIso (e : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.originalFreeFunctor.{u, v} e ⋙
      SymmetricRightModulePresentation.rightModuleToOperator.{u, v} ≅
        EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e) :=
  Functor.isoWhiskerRight (SymmetricStandardRightFreeEvaluation.freeComparison e)
    SymmetricRightModulePresentation.rightModuleToOperator ≪≫ nativeOperatorFreeIso e

private theorem originalOperatorFreeIso_eq_proof (e : Operad.SmallFinBijGroupoid) :
    originalOperatorFreeIso.{u, v} e =
      Functor.isoWhiskerRight (SymmetricStandardRightFreeEvaluation.freeComparison e)
        SymmetricRightModulePresentation.rightModuleToOperator ≪≫ nativeOperatorFreeIso e := rfl

/-- The complete public initializer retains the same actual comparison and original counit. -/
theorem originalOperatorFreeIso_eq (e : Operad.SmallFinBijGroupoid) :
    originalOperatorFreeIso.{u, v} e =
      Functor.isoWhiskerRight (SymmetricStandardRightFreeEvaluation.freeComparison e)
        SymmetricRightModulePresentation.rightModuleToOperator ≪≫ nativeOperatorFreeIso e :=
  originalOperatorFreeIso_eq_proof e

/-- Both entire original coefficient maps satisfy naturality as full J morphisms. -/
theorem originalOperatorFreeIso_naturality (e : Operad.SmallFinBijGroupoid)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e ⋙
      SymmetricRightModulePresentation.rightModuleToOperator).map f ≫
        (originalOperatorFreeIso e).hom.app Y =
      (originalOperatorFreeIso e).hom.app X ≫
        (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e)).map f :=
  (originalOperatorFreeIso e).hom.naturality f

/-- The complete inverse comparison retains the same full J coefficient morphism. -/
theorem originalOperatorFreeIso_inv_naturality (e : Operad.SmallFinBijGroupoid)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
      (symmetricOperatorObj.{u, v} e)).map f ≫ (originalOperatorFreeIso e).inv.app Y =
      (originalOperatorFreeIso e).inv.app X ≫
        (SymmetricStandardRightFreeEvaluation.originalFreeFunctor e ⋙
          SymmetricRightModulePresentation.rightModuleToOperator).map f :=
  (originalOperatorFreeIso e).inv.naturality f

section CounitValues
universe uS vS uC vC uD vD
variable {S : Type uS} [Category.{vS} S] {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]

private def freeCounitIso (E : C ≌ D) (L : S ⥤ D) : (L ⋙ E.inverse) ⋙ E.functor ≅ L :=
  Functor.associator L E.inverse E.functor ≪≫
    Functor.isoWhiskerLeft L E.counitIso ≪≫ Functor.rightUnitor L

private theorem freeCounitIso_hom (E : C ≌ D) (L : S ⥤ D) (X : S) :
    (freeCounitIso E L).hom.app X = E.counitIso.hom.app (L.obj X) := by
  unfold freeCounitIso
  change 𝟙 _ ≫ E.counitIso.hom.app (L.obj X) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

private theorem freeCounitIso_inv (E : C ≌ D) (L : S ⥤ D) (X : S) :
    (freeCounitIso E L).inv.app X = E.counitIso.inv.app (L.obj X) := by
  unfold freeCounitIso
  change (𝟙 _ ≫ E.counitIso.inv.app (L.obj X)) ≫ 𝟙 _ = _
  rw [Category.id_comp, Category.comp_id]

private theorem isoHomApp_heq {F G H : S ⥤ D} (q : F ≅ H) (r : G ≅ H)
    (hFG : F = G) (h : HEq q r) (X : S) : HEq (q.hom.app X) (r.hom.app X) := by
  cases hFG
  cases (eq_of_heq h)
  rfl

private theorem isoInvApp_heq {F G H : S ⥤ D} (q : F ≅ H) (r : G ≅ H)
    (hFG : F = G) (h : HEq q r) (X : S) : HEq (q.inv.app X) (r.inv.app X) := by
  cases hFG
  cases (eq_of_heq h)
  rfl

end CounitValues

private theorem mprValue_heq {α β : Sort u} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by
  cases h
  rfl

/-- The whole native source is the literal inverse free functor on the same carrier. -/
theorem nativeOperatorFreeIso_source_eq (e : Operad.SmallFinBijGroupoid) :
    SymmetricStandardRightFreeEvaluation.nativeFreeFunctor.{u, v} e ⋙
      SymmetricRightModulePresentation.rightModuleToOperator.{u, v} =
        (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e) ⋙
            SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.inverse) ⋙
          SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor := by
  rw [SymmetricStandardRightFreeEvaluation.nativeFreeFunctor_eq]
  rfl

private theorem nativeOperatorFreeIso_initializer_proof (e : Operad.SmallFinBijGroupoid) :
    HEq (nativeOperatorFreeIso.{u, v} e)
      (freeCounitIso SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}
        (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e))) := by
  unfold nativeOperatorFreeIso freeCounitIso
  exact mprValue_heq _ _

/-- The complete opaque native Iso is characterized by its original associator and same counit. -/
theorem nativeOperatorFreeIso_initializer_heq (e : Operad.SmallFinBijGroupoid) :
    HEq (nativeOperatorFreeIso.{u, v} e)
      (Functor.associator
        (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e))
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.inverse
        SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor ≪≫
          Functor.isoWhiskerLeft
            (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
              (symmetricOperatorObj.{u, v} e))
            SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso ≪≫
              Functor.rightUnitor
                (EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
                  (symmetricOperatorObj.{u, v} e))) :=
  nativeOperatorFreeIso_initializer_proof e

/-- The entire native forward J morphism is the original actual carrier counit value. -/
theorem nativeOperatorFreeIso_hom_heq (e : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    HEq ((nativeOperatorFreeIso e).hom.app X)
      (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso.hom.app
        ((EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e)).obj X)) :=
  (isoHomApp_heq _ _ (nativeOperatorFreeIso_source_eq e)
    (nativeOperatorFreeIso_initializer_proof e) X).trans
      (heq_of_eq (freeCounitIso_hom _ _ X))

/-- The entire native inverse J morphism is the same original inverse carrier counit value. -/
theorem nativeOperatorFreeIso_inv_heq (e : Operad.SmallFinBijGroupoid)
    (X : PointedCGWH.{u, v}) :
    HEq ((nativeOperatorFreeIso e).inv.app X)
      (SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.counitIso.inv.app
        ((EnrichedFunctorCat.Free.functor (V := PointedCGWH.{u, v})
          (symmetricOperatorObj.{u, v} e)).obj X)) :=
  (isoInvApp_heq _ _ (nativeOperatorFreeIso_source_eq e)
    (nativeOperatorFreeIso_initializer_proof e) X).trans
      (heq_of_eq (freeCounitIso_inv _ _ X))

end PointedCGWH.OriginalStandardRightFreeLevels
