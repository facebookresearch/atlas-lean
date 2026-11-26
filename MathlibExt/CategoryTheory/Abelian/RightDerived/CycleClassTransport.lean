/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ShortComplex.Ab
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison

/-!
# Cycle classes under lifted right-derived coefficient maps

Let `C` be abelian with injective resolutions, `F : C → Ab_s`,
`P : C → Ab_max(t,s)` additive, and `U_t` the universe-lift functor.
For a transformation `α : P → F ⋙ U_t`, a specified value on a cycle
of the chosen resolution complex determines the same value on its
class in `U_t(R^qF(Y))`, after the derived postcomposition and
resolution comparisons.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u v s t

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]

/-- Let `C` be abelian with injective resolutions, `F : C → Ab_s`,
`P : C → Ab_max(t,s)` additive, `U_t : Ab_s → Ab_max(t,s)` the
universe-lift functor, and `α : P → F ⋙ U_t`. On the chosen resolution
`I` of `Y`, choose degree-`q` left-homology data for `P(I)` and a
cycle-carrier element `c`. If `α_(I^q)(i(c))` is the lifted cycle
`z` of `F(I)`, the derived map to `U_t(R^qF(Y))` sends the class of
`c` to the lifted class of `z` under the resolution comparisons. -/
theorem rightDerivedCompIsoOfPreservesHomology_inv_cycleClass
    (F : C ⥤ AddCommGrpCat.{s}) [F.Additive]
    (P : C ⥤ AddCommGrpCat.{max t s}) [P.Additive]
    (α : P ⟶ F ⋙ AddCommGrpCat.uliftFunctor.{t, s}) (Y : C) (q : ℕ)
    (hP : (((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution Y).cocomplex).sc q).LeftHomologyData)
    (c : hP.K)
    (z : (((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (injectiveResolution Y).cocomplex).sc q).g.hom.ker)
    (hval : (α.app ((injectiveResolution Y).cocomplex.X q)) (hP.i c) = ULift.up z.val) :
    let R := injectiveResolution Y
    let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
    let T := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
    let U := AddCommGrpCat.uliftFunctor.{t, s}
    ((F.rightDerivedCompIsoOfPreservesHomology U q).app Y).inv
        ((NatTrans.rightDerived α q).app Y
          ((R.isoRightDerivedObj P q).inv ((T.sc q).homologyπ (hP.cyclesIso.inv c)))) =
      U.map (R.isoRightDerivedObj F q).inv
        (ULift.up ((K.sc q).homologyπ ((K.sc q).abCyclesIso.inv z))) := by
  let R := injectiveResolution Y
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let T := (P.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let U := AddCommGrpCat.uliftFunctor.{t, s}
  let β := (NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex
  let φ : T.sc q ⟶ (K.sc q).map U :=
    (HomologicalComplex.shortComplexFunctor AddCommGrpCat.{max t s}
      (ComplexShape.up ℕ) q).map β
  let a := (T.sc q).homologyπ (hP.cyclesIso.inv c)
  let M := (K.sc q).mapHomologyIso U
  have hmiddle : φ.τ₂ (hP.i c) = ULift.up z.val := hval
  have hH : M.hom (HomologicalComplex.homologyMap β q a) =
      (ULift.up ((K.sc q).homologyπ ((K.sc q).abCyclesIso.inv z)) :
        U.obj (K.sc q).homology) :=
    ShortComplex.ulift_homologyMap_eq_of_middle_eq.{s, t} (K.sc q) (T.sc q) hP φ c z hmiddle
  have hComp : ((F.rightDerivedCompIsoOfPreservesHomology U q).app Y).inv
        ((NatTrans.rightDerived α q).app Y ((R.isoRightDerivedObj P q).inv a)) =
      U.map (R.isoRightDerivedObj F q).inv
        (M.hom (HomologicalComplex.homologyMap β q a)) :=
    ConcreteCategory.congr_hom
      (rightDerivedCompIsoOfPreservesHomology_inv_naturality_functor F U P α Y q) a
  exact hComp.trans (congrArg (U.map (R.isoRightDerivedObj F q).inv) hH)

end CategoryTheory.Functor
