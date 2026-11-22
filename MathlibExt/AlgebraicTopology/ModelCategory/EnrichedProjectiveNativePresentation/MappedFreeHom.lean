/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.FreeEvaluation

/-!
# Original free adjuncts after the actual forward carrier functor

Compare both complete Hom maps directly with canonical native free/evaluation.
The original free comparison and the actual carrier counit determine the
mapped free isomorphism. These characteristics retain arbitrary whole maps.
-/

set_option autoImplicit false
noncomputable section
universe u v uC vC

open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.EnrichedProjective.NativePresentation

variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {C : Type uC} [Category.{vC} C]

/-- The mapped inverse free comparison is the actual counit inverse and mapped source inverse. -/
theorem mappedOriginalFreeIso_inv_app
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R) (X : PointedCGWH.{u, v}) :
    (mappedOriginalFreeIso e a L R adj hR).inv.app X =
      e.counitIso.inv.app ((EnrichedFunctorCat.Free.functor a).obj X) ≫
        e.functor.map ((originalFreeIso e a L R adj hR).inv.app X) := by
  simp only [mappedOriginalFreeIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app]
  apply congrArg (fun z => z ≫ e.functor.map ((originalFreeIso e a L R adj hR).inv.app X))
  change (𝟙 _ ≫ e.counitIso.inv.app _) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

/-- The actual transported free Hom map is native identity evaluation after the carrier Hom map. -/
theorem transportedAdjunction_homEquiv_apply
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    {X : PointedCGWH.{u, v}} {Y : C} (f : (transportedFree e a).obj X ⟶ Y) :
    (transportedAdjunction e a).homEquiv X Y f =
      (EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)
        (e.counitIso.inv.app ((EnrichedFunctorCat.Free.functor a).obj X) ≫ e.functor.map f) := by
  rw [transportedAdjunction_homEquiv]
  change (EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)
    (e.symm.toAdjunction.homEquiv _ Y f) = _
  exact congrArg ((EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y))
    (e.symm.toAdjunction.homEquiv_unit _ _ f)

/-- Every original source free map has the SAME complete native adjunct after mapping. -/
theorem mappedOriginalFreeIso_homEquiv_apply
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : C} (f : L.obj X ⟶ Y) :
    (EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)
      ((mappedOriginalFreeIso e a L R adj hR).inv.app X ≫ e.functor.map f) =
        adj.homEquiv X Y f ≫ hR.inv.app Y := by
  let q := originalFreeIso e a L R adj hR
  have hs := originalFreeIso_homEquiv_apply e a L R adj hR (q.inv.app X ≫ f)
  change adj.homEquiv X Y (q.hom.app X ≫ (q.inv.app X ≫ f)) = _ at hs
  rw [← Category.assoc, q.hom_inv_id_app, Category.id_comp] at hs
  have hEval := originalEvaluationAdjunction_homEquiv e a R hR (q.inv.app X ≫ f)
  have hBoth := hs.trans hEval
  have hCancel := congrArg (fun z => z ≫ hR.inv.app Y) hBoth
  rw [Category.assoc, hR.hom_inv_id_app, Category.comp_id] at hCancel
  have hMapped :
      (EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)
        ((mappedOriginalFreeIso e a L R adj hR).inv.app X ≫ e.functor.map f) =
          (transportedAdjunction e a).homEquiv X Y (q.inv.app X ≫ f) := by
    rw [mappedOriginalFreeIso_inv_app]
    have hMap := e.functor.map_comp (q.inv.app X) f
    change (EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)
      ((e.counitIso.inv.app _ ≫ e.functor.map (q.inv.app X)) ≫ e.functor.map f) = _
    rw [Category.assoc]
    have hUnder : e.functor.map (q.inv.app X) ≫ e.functor.map f =
      e.functor.map (q.inv.app X ≫ f) := hMap.symm
    exact (congrArg ((EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y))
      (congrArg (fun z => e.counitIso.inv.app _ ≫ z) hUnder)).trans
        (transportedAdjunction_homEquiv_apply e a (q.inv.app X ≫ f)).symm
  exact hMapped.trans hCancel.symm

/-- The actual mapped ORIGINAL inverse adjunct is the full native inverse after free comparison. -/
theorem mappedOriginalFreeIso_homEquiv_symm
    (e : C ≌ EnrichedFunctorCat PointedCGWH.{u, v} A) (a : A)
    (L : PointedCGWH.{u, v} ⥤ C) (R : C ⥤ PointedCGWH.{u, v}) (adj : L ⊣ R)
    (hR : transportedEvaluation e a ≅ R)
    {X : PointedCGWH.{u, v}} {Y : C} (f : X ⟶ R.obj Y) :
    e.functor.map ((adj.homEquiv X Y).symm f) =
      (mappedOriginalFreeIso e a L R adj hR).hom.app X ≫
        ((EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)).symm
          (f ≫ hR.inv.app Y) := by
  let q := mappedOriginalFreeIso e a L R adj hR
  have h : q.inv.app X ≫ e.functor.map ((adj.homEquiv X Y).symm f) =
      ((EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)).symm
        (f ≫ hR.inv.app Y) := by
    apply ((EnrichedFunctorCat.Free.adjunction a).homEquiv X (e.functor.obj Y)).injective
    exact (mappedOriginalFreeIso_homEquiv_apply e a L R adj hR _).trans
      (by simp only [Equiv.apply_symm_apply]; rfl)
  have hPost := congrArg (fun z => q.hom.app X ≫ z) h
  rw [← Category.assoc, q.hom_inv_id_app, Category.id_comp] at hPost
  exact hPost

end HomotopicalAlgebra.EnrichedProjective.NativePresentation
