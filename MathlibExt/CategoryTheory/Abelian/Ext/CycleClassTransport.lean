/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.Abelian.Ext.DerivedCoyoneda
public import MathlibExt.CategoryTheory.Abelian.RightDerived.CycleClassTransport

/-!
# Resolution representatives and derived cycle classes

An natural transformation from Coyoneda to a lifted additive functor carries each resolution
representative to the class of its literal image cycle. The comparison uses the existing Ext and
right-derived functor constructions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

universe u s t

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{max t s} C] [Abelian C]
  [HasInjectiveResolutions C] [HasExt.{max t s} C]

/--
The Ext-to-derived-functor comparison preserves every original resolution representative under a
specified literal cycle-value equation.
-/
theorem rightDerivedCoyonedaCompIso_inv_extMk_cycleClass
    (F : C ⥤ AddCommGrpCat.{s}) [F.Additive] (Z Y : C) (q : ℕ)
    (α : preadditiveCoyoneda.obj (op Z) ⟶ F ⋙ AddCommGrpCat.uliftFunctor.{t, s})
    (f : Z ⟶ (injectiveResolution Y).cocomplex.X q)
    (hf : f ≫ (injectiveResolution Y).cocomplex.d q (q + 1) = 0)
    (z : (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution Y).cocomplex).sc q).g.hom.ker)
    (hval : (α.app ((injectiveResolution Y).cocomplex.X q)) f = ULift.up z.val) :
    let R := injectiveResolution Y
    let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
    let U := AddCommGrpCat.uliftFunctor.{t, s}
    ((F.rightDerivedCompIsoOfPreservesHomology U q).app Y).inv
        ((NatTrans.rightDerived α q).app Y
          (((rightDerivedCoyonedaIsoExtFunctorObj Z q).app Y).inv
            (R.extMk f (q + 1) rfl hf))) =
      U.map (R.isoRightDerivedObj F q).inv
        (ULift.up ((K.sc q).homologyπ ((K.sc q).abCyclesIso.inv z))) := by
  let R := injectiveResolution Y
  let P := preadditiveCoyoneda.obj (op Z)
  let U := AddCommGrpCat.uliftFunctor.{t, s}
  let hE := DerivedCoyoneda.homologyDataExt Z R q
  let c : hE.K := ⟨f, hf⟩
  have hmiddle : (α.app (R.cocomplex.X q)) (hE.i c) = ULift.up z.val := hval
  have hTransport :=
    Functor.rightDerivedCompIsoOfPreservesHomology_inv_cycleClass.{u, max t s, s, t}
      F P α Y q hE c z hmiddle
  have hExt := rightDerivedCoyonedaIsoExtFunctorObj_inv_extMk.{max t s, u} Z Y q f hf
  exact (congrArg (fun x : (P.rightDerived q).obj Y =>
    ((F.rightDerivedCompIsoOfPreservesHomology U q).app Y).inv
      ((NatTrans.rightDerived α q).app Y x)) hExt).trans hTransport

end CategoryTheory.Abelian
