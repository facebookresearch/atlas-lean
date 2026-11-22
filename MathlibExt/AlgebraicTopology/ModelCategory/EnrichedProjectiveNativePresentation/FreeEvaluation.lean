/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation
import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# Actual source free/evaluation adjunction comparisons

The canonical native free adjunction is transported through the complete
existing carrier equivalence. Original source adjunctions are compared by
their actual common evaluation functor, preserving both Hom maps and units.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory Limits HomotopicalAlgebra MorphismProperty

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- The actual canonical free functor followed by the explicit original inverse. -/
def transportedFree (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A) :
    PointedCGWH.{u, v} ⥤ C :=
  EnrichedFunctorCat.Free.functor a ⋙ e.inverse

/-- Actual original-presentation evaluation through the forward carrier functor. -/
def transportedEvaluation (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A) :
    C ⥤ PointedCGWH.{u, v} :=
  e.functor ⋙ EnrichedFunctorCat.evaluation a

/-- Compose the REAL native free adjunction and actual inverse carrier adjunction. -/
def transportedAdjunction (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A) :
    transportedFree e a ⊣ transportedEvaluation e a :=
  (EnrichedFunctorCat.Free.adjunction a).comp e.symm.toAdjunction

/-- The complete transported Hom map uses both actual input correspondences. -/
theorem transportedAdjunction_homEquiv
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (X : PointedCGWH.{u, v}) (Y : C) :
    (transportedAdjunction e a).homEquiv X Y =
      (e.symm.toAdjunction.homEquiv ((EnrichedFunctorCat.Free.functor a).obj X) Y).trans
        ((EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)) :=
  congrFun (congrFun (Adjunction.comp_homEquiv _ _) X) Y

/-- The actual unit retains the native unit and full carrier counit inverse. -/
theorem transportedAdjunction_unit_app
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (X : PointedCGWH.{u, v}) :
    (transportedAdjunction e a).unit.app X =
      (EnrichedFunctorCat.Free.adjunction a).unit.app X ≫
        (EnrichedFunctorCat.evaluation a).map
          (e.counitIso.inv.app ((EnrichedFunctorCat.Free.functor a).obj X)) :=
  Adjunction.comp_unit_app _ _ X

/-- The actual counit uses the native counit and original carrier unit inverse. -/
theorem transportedAdjunction_counit_app
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A) (Y : C) :
    (transportedAdjunction e a).counit.app Y =
      e.inverse.map ((EnrichedFunctorCat.Free.adjunction a).counit.app (e.functor.obj Y)) ≫
        e.unitIso.inv.app Y :=
  Adjunction.comp_counit_app _ _ Y

/-- Compare with the ORIGINAL evaluation through its complete natural iso. -/
def originalEvaluationAdjunction
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (R : C ⥤ PointedCGWH.{u, v}) (hR : transportedEvaluation e a ≅ R) :
    transportedFree e a ⊣ R :=
  (transportedAdjunction e a).ofNatIsoRight hR

/-- The original-evaluation forward Hom map retains the entire natural evaluation comparison. -/
theorem originalEvaluationAdjunction_homEquiv
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (R : C ⥤ PointedCGWH.{u, v}) (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : C} (f : (transportedFree e a).obj X ⟶ Y) :
    (originalEvaluationAdjunction e a R hR).homEquiv X Y f =
      (transportedAdjunction e a).homEquiv X Y f ≫ hR.hom.app Y :=
  Adjunction.homEquiv_ofNatIsoRight_apply _ _ f

/-- The original-evaluation inverse Hom map retains the original inverse evaluation comparison. -/
theorem originalEvaluationAdjunction_homEquiv_symm
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (R : C ⥤ PointedCGWH.{u, v}) (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : C} (f : X ⟶ R.obj Y) :
    ((originalEvaluationAdjunction e a R hR).homEquiv X Y).symm f =
      ((transportedAdjunction e a).homEquiv X Y).symm (f ≫ hR.inv.app Y) :=
  Adjunction.homEquiv_ofNatIsoRight_symm_apply _ _ f

/-- The ORIGINAL source free functor is compared to the actual transported canonical free. -/
def originalFreeIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) :
    L ≅ transportedFree e a :=
  Adjunction.leftAdjointUniq adj (originalEvaluationAdjunction e a R hR)

/-- The full original unit is preserved through the actual free comparison. -/
theorem originalFreeIso_unit
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) (X : PointedCGWH.{u, v}) :
    adj.unit.app X ≫ R.map ((originalFreeIso e a L R adj hR).hom.app X) =
      (originalEvaluationAdjunction e a R hR).unit.app X :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ X

/-- The full original counit is preserved through the whole source free comparison. -/
theorem originalFreeIso_counit
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) (Y : C) :
    (originalFreeIso e a L R adj hR).hom.app (R.obj Y) ≫
        (originalEvaluationAdjunction e a R hR).counit.app Y =
      adj.counit.app Y :=
  Adjunction.leftAdjointUniq_hom_app_counit _ _ Y

/-- Every whole original free map has the same complete adjunct after migration. -/
theorem originalFreeIso_homEquiv_apply
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : C} (f : (transportedFree e a).obj X ⟶ Y) :
    adj.homEquiv X Y ((originalFreeIso e a L R adj hR).hom.app X ≫ f) =
      (originalEvaluationAdjunction e a R hR).homEquiv X Y f := by
  let q := originalFreeIso e a L R adj hR
  let newAdj := originalEvaluationAdjunction e a R hR
  have hStart := adj.homEquiv_naturality_right (q.hom.app X) f
  have hUnit : adj.homEquiv X ((transportedFree e a).obj X) (q.hom.app X) =
      newAdj.unit.app X :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  exact hStart.trans
    ((congrArg (fun z => z ≫ R.map f) hUnit).trans (newAdj.homEquiv_unit X Y f).symm)

/-- The full inverse adjunct is the ORIGINAL inverse source adjunct after migration. -/
theorem originalFreeIso_homEquiv_symm
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : C} (f : X ⟶ R.obj Y) :
    (originalFreeIso e a L R adj hR).hom.app X ≫
      ((originalEvaluationAdjunction e a R hR).homEquiv X Y).symm f =
        (adj.homEquiv X Y).symm f := by
  apply (adj.homEquiv X Y).injective
  exact (originalFreeIso_homEquiv_apply e a L R adj hR _).trans
    ((Equiv.apply_symm_apply _ f).trans (Equiv.apply_symm_apply _ f).symm)

/-- Map the original free comparison and the ACTUAL carrier counit into canonical enriched free. -/
def mappedOriginalFreeIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) :
    L ⋙ e.functor ≅ EnrichedFunctorCat.Free.functor a :=
  Functor.isoWhiskerRight (originalFreeIso e a L R adj hR) e.functor ≪≫
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft (EnrichedFunctorCat.Free.functor a) e.counitIso ≪≫
        Functor.rightUnitor _

/-- The complete original generator arrow maps to the full canonical enriched free arrow. -/
def originalFreeGeneratorArrowIso
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    CategoryTheory.Arrow.mk (e.functor.map (L.map f)) ≅
      CategoryTheory.Arrow.mk ((EnrichedFunctorCat.Free.functor a).map f) :=
  CategoryTheory.Arrow.isoOfNatIso (mappedOriginalFreeIso e a L R adj hR)
    (CategoryTheory.Arrow.mk f)

/-- Every canonical iso-invariant arrow class retains the actual original mapped free arrow. -/
theorem originalFreeGeneratorArrowClass_iff
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    (P : MorphismProperty (EnrichedFunctorCat PointedCGWH.{u, v} A)) [P.RespectsIso]
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    P (e.functor.map (L.map f)) ↔ P ((EnrichedFunctorCat.Free.functor a).map f) :=
  P.arrow_mk_iso_iff (originalFreeGeneratorArrowIso e a L R adj hR f)

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
