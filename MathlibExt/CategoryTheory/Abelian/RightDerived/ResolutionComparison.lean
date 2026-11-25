/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import MathlibExt.Algebra.Homology.Functor
public import MathlibExt.Algebra.Homology.HomologyMapSquare
public import MathlibExt.CategoryTheory.Abelian.Injective.ResolutionComparison

/-!
# Comparisons between right-derived cohomology calculations

Let `C`, `D` be abelian categories, with injective resolutions in `C`,
and let `F : C → D` be additive. Two injective resolutions of an object
compute canonically isomorphic cohomology through `R^nF`.
The comparisons commute with lifts of maps of resolved objects and
with natural transformations of additive functors. An additive
homology-preserving target functor also commutes with right derivation.
-/

/-
Attribution for the adapted naturality declarations:
> Copyright (c) 2026 @junekim623, Muse. All rights reserved.
> Released under Apache 2.0 license as described in the file LICENSE.
> Authors: @junekim623, Muse.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v v' v'' u u' u''

namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable [HasInjectiveResolutions C]

/-- Let `C`, `D` be abelian, with injective resolutions in `C`,
`F : C → D` additive and `I,J` injective resolutions of `X`.
The canonical comparison `Hⁿ(F(I)) ≅ Hⁿ(F(J))` is obtained by
passing through `R^nF(X)`. -/
noncomputable def cohomologyComparisonIso {X : C}
    (I J : InjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ≅
      (HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj J.cocomplex) :=
  (I.isoRightDerivedObj F n).symm.trans (J.isoRightDerivedObj F n)

@[simp]
theorem cohomologyComparisonIso_refl {X : C} (I : InjectiveResolution X)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    cohomologyComparisonIso I I F n = Iso.refl _ := by
  apply Iso.ext
  exact Iso.inv_hom_id _

theorem cohomologyComparisonIso_symm {X : C}
    (I J : InjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    cohomologyComparisonIso J I F n =
      (cohomologyComparisonIso I J F n).symm :=
  rfl

@[simp]
theorem cohomologyComparisonIso_trans {X : C}
    (I J K : InjectiveResolution X) (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (cohomologyComparisonIso I J F n).trans
        (cohomologyComparisonIso J K F n) =
      cohomologyComparisonIso I K F n := by
  apply Iso.ext
  simp only [cohomologyComparisonIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.hom_inv_id_assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Let `C`, `D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. Given pairs `I_X,J_X` and `I_Y,J_Y`
of injective resolutions and lifts of the same map `f : X → Y`,
the degree-`n` cohomology maps commute with the canonical comparisons
between resolution choices. -/
theorem cohomologyComparisonIso_naturality
    {X Y : C} {IX JX : InjectiveResolution X}
    {IY JY : InjectiveResolution Y} {f : X ⟶ Y}
    (φI : InjectiveResolution.Hom IX IY f)
    (φJ : InjectiveResolution.Hom JX JY f)
    (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (cohomologyComparisonIso IX JX F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map φJ.hom =
      (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map φI.hom ≫
        (cohomologyComparisonIso IY JY F n).hom := by
  have hJ : (F.rightDerived n).map f ≫ (JY.isoRightDerivedObj F n).hom =
      (JX.isoRightDerivedObj F n).hom ≫
        (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map φJ.hom := by
    rw [F.rightDerived_map_eq n f φJ.hom φJ.ι_comp_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hI : (IX.isoRightDerivedObj F n).inv ≫ (F.rightDerived n).map f =
      (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
          HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map φI.hom ≫
        (IY.isoRightDerivedObj F n).inv := by
    rw [F.rightDerived_map_eq n f φI.hom φI.ι_comp_hom]
    simp only [Iso.inv_hom_id_assoc]
  change ((IX.isoRightDerivedObj F n).inv ≫ (JX.isoRightDerivedObj F n).hom) ≫
      (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map φJ.hom =
      (F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n).map φI.hom ≫
        ((IY.isoRightDerivedObj F n).inv ≫ (JY.isoRightDerivedObj F n).hom)
  simp only [Category.assoc]
  rw [← hJ, ← Category.assoc, hI, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C`, `D` be abelian, with injective resolutions in `C`,
`F,G : C → D` additive and `α : F → G`. For an injective resolution
`I` of `X`, the map `Hⁿ(F(I)) → Hⁿ(G(I))` commutes with the inverse
comparisons to `R^nF(X)` and `R^nG(X)`. -/
@[reassoc]
lemma isoRightDerivedObj_inv_naturality_functor
    {F G : C ⥤ D} [F.Additive] [G.Additive] {X : C}
    (I : InjectiveResolution X) (α : F ⟶ G) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app I.cocomplex) n ≫
        (I.isoRightDerivedObj G n).inv =
      (I.isoRightDerivedObj F n).inv ≫ (NatTrans.rightDerived α n).app X := by
  rw [InjectiveResolution.rightDerived_app_eq α I n,
    HomologicalComplex.homologyFunctor_map]
  simp only [Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Let `C`, `D` be abelian, with injective resolutions in `C`,
`F,G : C → D` additive and `α : F → G`. For an injective resolution
`I` of `X`, the forward comparisons from `R^nF(X)` and `R^nG(X)`
to resolution cohomology commute with `R^nα` and `Hⁿ(α_I)`. -/
@[reassoc]
lemma isoRightDerivedObj_hom_naturality_functor
    {F G : C ⥤ D} [F.Additive] [G.Additive] {X : C}
    (I : InjectiveResolution X) (α : F ⟶ G) (n : ℕ) :
    (NatTrans.rightDerived α n).app X ≫ (I.isoRightDerivedObj G n).hom =
      (I.isoRightDerivedObj F n).hom ≫ HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app I.cocomplex) n := by
  rw [InjectiveResolution.rightDerived_app_eq α I n,
    HomologicalComplex.homologyFunctor_map]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end CategoryTheory.InjectiveResolution

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]
variable {E : Type u''} [Category.{v''} E] [Abelian E]
variable [HasInjectiveResolutions C]

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`.
For additive `F : C → D` and additive homology-preserving `U : D → E`,
there is a natural isomorphism `R^nF ⋙ U ≅ R^n(F ⋙ U)`. -/
noncomputable def rightDerivedCompIsoOfPreservesHomology
    (F : C ⥤ D) [F.Additive] (U : D ⥤ E) [U.Additive]
    [U.PreservesHomology] (n : ℕ) :
    F.rightDerived n ⋙ U ≅ (F ⋙ U).rightDerived n := by
  let eMap (I : CochainComplex C ℕ) :=
    (HomologicalComplex.mapHomologyFunctorIso
      (c := ComplexShape.up ℕ) n U).symm.app
        ((F.mapHomologicalComplex _).obj I)
  refine NatIso.ofComponents (fun X =>
    U.mapIso ((injectiveResolution X).isoRightDerivedObj F n) ≪≫
      eMap (injectiveResolution X).cocomplex ≪≫
      ((injectiveResolution X).isoRightDerivedObj (F ⋙ U) n).symm) (fun {X Y} f => ?_)
  let φ := InjectiveResolution.desc f (injectiveResolution Y)
    (injectiveResolution X)
  have hφ := InjectiveResolution.desc_commutes_zero f
    (injectiveResolution Y) (injectiveResolution X)
  have hF := InjectiveResolution.isoRightDerivedObj_hom_naturality f
    (injectiveResolution X) (injectiveResolution Y) φ hφ F n
  have hFU := InjectiveResolution.isoRightDerivedObj_inv_naturality f
    (injectiveResolution X) (injectiveResolution Y) φ hφ (F ⋙ U) n
  have hmid : U.map ((F.mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n).map φ) ≫
      (eMap (injectiveResolution Y).cocomplex).hom =
    (eMap (injectiveResolution X).cocomplex).hom ≫
      (((F ⋙ U).mapHomologicalComplex _ ⋙
          HomologicalComplex.homologyFunctor _ _ n).map φ) :=
    ShortComplex.mapHomologyIso_inv_naturality
      ((HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℕ) n).map
        ((F.mapHomologicalComplex _).map φ)) U
  simp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  conv_lhs => rw [← Category.assoc, ← U.map_comp, hF, U.map_comp, Category.assoc]
  congr 1
  conv_lhs => rw [← Category.assoc, hmid, Category.assoc]
  congr 1
  exact hFU.symm

end CategoryTheory.Functor

end


/-
Authors of the representative calculation: @toskua and Avocado.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite

universe c d e vc vd ve
namespace CategoryTheory.Functor
variable {C : Type c} {D : Type d} {E : Type e}
  [Category.{vc} C] [Category.{vd} D] [Category.{ve} E]
  [Abelian C] [Abelian D] [Abelian E] [HasInjectiveResolutions C]

/-- Let `C`, `D`, `E` be abelian, with injective resolutions in `C`,
`F : C → D` and `P : C → E` additive, and `U : D → E` additive
and preserving homology. For `α : P → F ⋙ U` and the chosen resolution
`I` of `Y`, transporting `R^qα_Y` by the inverse postcomposition
comparison equals `H^q(α_I)` followed by the homology-preservation map
and the inverse comparison to `U(R^qF(Y))`. -/
theorem rightDerivedCompIsoOfPreservesHomology_inv_naturality_functor
    (F : C ⥤ D) [F.Additive] (U : D ⥤ E) [U.Additive] [U.PreservesHomology]
    (P : C ⥤ E) [P.Additive] (α : P ⟶ F ⋙ U) (Y : C) (q : ℕ) :
    let R := injectiveResolution Y
    let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
    let B := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) q U).app K
    (R.isoRightDerivedObj P q).inv ≫ (NatTrans.rightDerived α q).app Y ≫
        ((F.rightDerivedCompIsoOfPreservesHomology U q).app Y).inv =
      HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex) q ≫
        B.hom ≫ U.map (R.isoRightDerivedObj F q).inv := by
  let R := injectiveResolution Y
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex
  let B := (HomologicalComplex.mapHomologyFunctorIso (c := ComplexShape.up ℕ) q U).app K
  let H := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex α (ComplexShape.up ℕ)).app R.cocomplex) q
  let J := R.isoRightDerivedObj (F ⋙ U) q
  let V := ((F.rightDerivedCompIsoOfPreservesHomology U q).app Y).inv
  have hNat : H ≫ J.inv = (R.isoRightDerivedObj P q).inv ≫
      (NatTrans.rightDerived α q).app Y :=
    R.isoRightDerivedObj_inv_naturality_functor α q
  have hComp : V = J.hom ≫ B.hom ≫ U.map (R.isoRightDerivedObj F q).inv := by
    change (J.hom ≫ B.hom) ≫ U.map (R.isoRightDerivedObj F q).inv = _
    exact Category.assoc _ _ _
  have hCancel : J.inv ≫ V = B.hom ≫ U.map (R.isoRightDerivedObj F q).inv :=
    (congrArg (fun k => J.inv ≫ k) hComp).trans
      (Iso.inv_hom_id_assoc J (B.hom ≫ U.map (R.isoRightDerivedObj F q).inv))
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ V) hNat.symm).trans
      ((Category.assoc _ _ _).trans (congrArg (fun k => H ≫ k) hCancel)))

end CategoryTheory.Functor

end
