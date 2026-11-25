/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Enriched.FreeYoneda
public import Mathlib.CategoryTheory.Adjunction.Unique

@[expose] public section
set_option autoImplicit false
noncomputable section
universe uV vV uJ uC vC
open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.EnrichedFunctorCat.FreeAdjunctionSource

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {J : Type uJ} [EnrichedCategory V J]
  {C : Type uC} [Category.{vC} C]
  (E : C ≌ EnrichedFunctorCat V J) (a : J)
  (L : V ⥤ C) (R : C ⥤ V) (adj : L ⊣ R)
  (r : E.functor ⋙ EnrichedFunctorCat.evaluation a ≅ R)

/-- The actual free adjunction is composed with the original inverse carrier adjunction. -/
@[no_expose]
def transported : Free.functor (V := V) a ⋙ E.inverse ⊣
    E.functor ⋙ EnrichedFunctorCat.evaluation a :=
  (Free.adjunction a).comp E.symm.toAdjunction

/-- The actual complete evaluation comparison fixes the original endpoint. -/
@[no_expose]
def migrated : Free.functor (V := V) a ⋙ E.inverse ⊣ R :=
  (transported E a).ofNatIsoRight r

/-- The whole original free comparison is derived from the actual chosen adjunctions. -/
@[no_expose]
def comparison : L ≅ Free.functor (V := V) a ⋙ E.inverse :=
  Adjunction.leftAdjointUniq adj (migrated E a R r)

/-- The original inverse-carrier free uses the same actual carrier counit. -/
@[no_expose]
def nativeIso : (Free.functor (V := V) a ⋙ E.inverse) ⋙ E.functor ≅
    Free.functor (V := V) a :=
  Functor.associator (Free.functor a) E.inverse E.functor ≪≫
    Functor.isoWhiskerLeft (Free.functor a) E.counitIso ≪≫
      Functor.rightUnitor (Free.functor a)

/-- The complete operator free comparison keeps the original chosen unit and counit. -/
@[no_expose]
def operatorIso : L ⋙ E.functor ≅ Free.functor (V := V) a :=
  Functor.isoWhiskerRight (comparison E a L R adj r) E.functor ≪≫ nativeIso E a

private theorem transported_eq_proof : transported E a =
    (Free.adjunction a).comp E.symm.toAdjunction := rfl

/-- The entire actual transported adjunction initializer remains public. -/
theorem transported_eq : transported E a =
    (Free.adjunction a).comp E.symm.toAdjunction := transported_eq_proof E a

private theorem migrated_eq_proof : migrated E a R r =
    (transported E a).ofNatIsoRight r := rfl

/-- The whole actual right endpoint transport preserves the chosen evaluation isomorphism. -/
theorem migrated_eq : migrated E a R r =
    (transported E a).ofNatIsoRight r := migrated_eq_proof E a R r

private theorem comparison_eq_proof : comparison E a L R adj r =
    Adjunction.leftAdjointUniq adj (migrated E a R r) := rfl

/-- The actual whole left comparison retains the two complete original chosen adjunctions. -/
theorem comparison_eq : comparison E a L R adj r =
    Adjunction.leftAdjointUniq adj (migrated E a R r) := comparison_eq_proof E a L R adj r

private theorem operatorIso_eq_proof : operatorIso E a L R adj r =
    Functor.isoWhiskerRight (comparison E a L R adj r) E.functor ≪≫ nativeIso E a := rfl

/-- The entire original operator comparison initializer preserves the same counit. -/
theorem operatorIso_eq : operatorIso E a L R adj r =
    Functor.isoWhiskerRight (comparison E a L R adj r) E.functor ≪≫ nativeIso E a :=
  operatorIso_eq_proof E a L R adj r

/-- The entire inverse-carrier component is exactly the actual original counit. -/
theorem nativeIso_hom_app (X : V) :
    (nativeIso E a).hom.app X = E.counitIso.hom.app ((Free.functor a).obj X) := by
  simp only [nativeIso, Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    Category.id_comp]
  exact Category.comp_id _

/-- Its complete inverse component is exactly the inverse of that same counit. -/
theorem nativeIso_inv_app (X : V) :
    (nativeIso E a).inv.app X = E.counitIso.inv.app ((Free.functor a).obj X) := by
  simp only [nativeIso, Iso.trans_inv, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.comp_id]

/-- Both full inverse factors retain the original free comparison and carrier counit. -/
theorem operatorIso_inv_app (X : V) :
    (operatorIso E a L R adj r).inv.app X =
      E.counitIso.inv.app ((Free.functor a).obj X) ≫
        E.functor.map ((comparison E a L R adj r).inv.app X) := by
  simp only [operatorIso, Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app, nativeIso_inv_app]

/-- The original adjunct retains the complete actual free comparison component. -/
theorem comparison_homEquiv {X : V} {M : C}
    (f : E.inverse.obj ((Free.functor a).obj X) ⟶ M) :
    adj.homEquiv X M ((comparison E a L R adj r).hom.app X ≫ f) =
      (migrated E a R r).homEquiv X M f := by
  have h := adj.homEquiv_naturality_right
    ((comparison E a L R adj r).hom.app X) f
  have hu : adj.homEquiv X _ ((comparison E a L R adj r).hom.app X) =
      (migrated E a R r).unit.app X :=
    Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ X
  exact h.trans ((congrArg (fun z => z ≫ R.map f) hu).trans
    ((migrated E a R r).homEquiv_unit X M f).symm)

/-- Whole composed adjuncts retain the same full free evaluation and inverse carrier unit. -/
theorem transported_homEquiv {X : V} {M : C}
    (f : E.inverse.obj ((Free.functor a).obj X) ⟶ M) :
    (transported E a).homEquiv X M f =
      (Free.adjunction a).homEquiv X (E.functor.obj M)
        (E.counitIso.inv.app ((Free.functor a).obj X) ≫ E.functor.map f) := by
  unfold transported
  rw [Adjunction.comp_homEquiv]
  change (Free.adjunction a).homEquiv X (E.functor.obj M)
    (E.symm.toAdjunction.homEquiv ((Free.functor a).obj X) M f) = _
  rw [Adjunction.homEquiv_unit]
  rfl

/-- Every original adjunct point is the actual full free evaluation after carrier transport. -/
theorem point {X : V} {M : C} (f : L.obj X ⟶ M) :
    adj.homEquiv X M f ≫ r.inv.app M =
      Free.evaluate a X (E.functor.obj M)
        ((operatorIso E a L R adj r).inv.app X ≫ E.functor.map f) := by
  let q := comparison E a L R adj r
  have hq : q.hom.app X ≫ q.inv.app X ≫ f = f := by
    rw [← Category.assoc, q.hom_inv_id_app, Category.id_comp]
  have hcmp := comparison_homEquiv E a L R adj r (q.inv.app X ≫ f)
  rw [hq] at hcmp
  rw [hcmp]
  rw [migrated, Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [Category.assoc, r.hom_inv_id_app, Category.comp_id, transported_homEquiv]
  rw [operatorIso_inv_app, E.functor.map_comp]
  simp only [Category.assoc]
  rw [Free.adjunction_homEquiv]
  rfl

end CategoryTheory.EnrichedFunctorCat.FreeAdjunctionSource
