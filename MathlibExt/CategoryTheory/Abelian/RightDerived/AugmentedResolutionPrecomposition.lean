/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionNaturality
public import MathlibExt.CategoryTheory.Abelian.RightDerived.Precomposition

/-!
# Augmented comparisons under injective-preserving source change

Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology, and
`B : D → A` additive. Mapping a coaugmentation-preserving comparison
into an injective resolution preserves its augmentation equation.
For additive `P : C → A` with `P ≅ J ⋙ B`, the cohomology-to-derived
map then commutes with right-derived precomposition.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
variable {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable (J : C ⥤ D) [J.Additive] [J.PreservesInjectiveObjects] [J.PreservesHomology]
variable (B : D ⥤ A) [B.Additive]
variable {P : C ⥤ A} [P.Additive]

omit [HasInjectiveResolutions C] [HasInjectiveResolutions D] in
/-- Let `C,D` be abelian and `J : C → D` additive and preserving
injectives and homology. For `ι : X[0] → I`, an injective resolution
`R` of `X`, and `a : I → R` satisfying `ι ≫ a = ι_R`, mapping by
`J` gives a comparison `J(I) → J(R)` preserving the full
coaugmentation of the mapped injective resolution. -/
theorem map_augmentedResolutionComparison
    {X : C} (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (R : InjectiveResolution X) (a : I ⟶ R.cocomplex) (ha : ι ≫ a = R.ι) :
    ((HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app X ≫
      (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι) ≫
      (J.mapHomologicalComplex (ComplexShape.up ℕ)).map a = (J.mapInjectiveResolution R).ι := by
  change (_ ≫ (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι) ≫
    (J.mapHomologicalComplex (ComplexShape.up ℕ)).map a =
      _ ≫ (J.mapHomologicalComplex (ComplexShape.up ℕ)).map R.ι
  rw [Category.assoc, ← Functor.map_comp, ha]

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. For a coaugmentation quasi-isomorphism `ι : X[0] → I`,
the map `Hⁿ(P(I)) → R^nP(X)` followed by precomposition equals
transport along `α_I` to `Hⁿ((J ⋙ B)(I))`, identification with
`Hⁿ(B(J(I)))`, and the augmented comparison to `R^nB(J(X))`. -/
theorem augmentedResolutionToRightDerivedHom_precomposition
    (α : P ≅ J ⋙ B) {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι] (n : ℕ) :
    P.augmentedResolutionToRightDerivedHom I ι n ≫
      (rightDerivedPrecompIsoOfIso J B α n).hom.app X =
      HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I) n ≫
      HomologicalComplex.homologyMap
        (((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B)) (ComplexShape.up ℕ)).app I).inv) n ≫
      B.augmentedResolutionToRightDerivedHom
        ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I)
        ((HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app X ≫
          (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι) n := by
  let R := injectiveResolution X
  let a := augmentedResolutionComparison I ι
  let aJ := (J.mapHomologicalComplex (ComplexShape.up ℕ)).map a.val
  have hJ := map_augmentedResolutionComparison J I ι R a.val a.property
  have hm := B.augmentedResolutionToRightDerivedHom_eq_of_injectiveTarget
    ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I)
    ((HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app X ≫
      (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι)
    (J.mapInjectiveResolution R) aJ hJ n
  have hP := P.augmentedResolutionToRightDerivedHom_eq_of_injectiveTarget I ι R a.val a.property n
  have hr := rightDerivedPrecompIsoOfIso_resolution_formula J B α n R
  let HP := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n
  have hα := (NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).naturality a.val
  have hc := ((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B))
    (ComplexShape.up ℕ)).inv).naturality a.val
  rw [hP, hr, hm]
  change (HP.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map a.val) ≫
      (R.isoRightDerivedObj P n).inv) ≫
    ((R.isoRightDerivedObj P n).hom ≫ HP.map
      ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app R.cocomplex) ≫
      (rightDerivedPrecompHomologyIso J B n R).hom ≫ _) =
    HP.map ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I) ≫
      HP.map (((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B))
        (ComplexShape.up ℕ)).app I).inv) ≫
      (HP.map ((B.mapHomologicalComplex (ComplexShape.up ℕ)).map aJ) ≫ _)
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change HP.map ((P.mapHomologicalComplex (ComplexShape.up ℕ)).map a.val) ≫
      HP.map ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app R.cocomplex) ≫
      HP.map (((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B))
        (ComplexShape.up ℕ)).app R.cocomplex).inv) ≫ _ = _
  let r : HP.obj ((J.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      B.mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex) ⟶
      (B.rightDerived n).obj (J.obj X) := ((J.mapInjectiveResolution R).isoRightDerivedObj B n).inv
  let m := (P.mapHomologicalComplex (ComplexShape.up ℕ)).map a.val
  let t := (NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app R.cocomplex
  let t₀ := (NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I
  let c := ((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B)) (ComplexShape.up ℕ)).app R.cocomplex).inv
  let c₀ := ((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B)) (ComplexShape.up ℕ)).app I).inv
  let m' := ((J ⋙ B).mapHomologicalComplex (ComplexShape.up ℕ)).map a.val
  let m'' := (B.mapHomologicalComplex (ComplexShape.up ℕ)).map aJ
  have h₁ : HP.map m ≫ HP.map t = HP.map t₀ ≫ HP.map m' :=
    (HP.map_comp _ _).symm.trans ((congrArg HP.map hα).trans (HP.map_comp _ _))
  have h₂ : HP.map m' ≫ HP.map c = HP.map c₀ ≫ HP.map m'' :=
    (HP.map_comp _ _).symm.trans ((congrArg HP.map hc).trans (HP.map_comp _ _))
  change HP.map m ≫ HP.map t ≫ HP.map c ≫ r = HP.map t₀ ≫ HP.map c₀ ≫ HP.map m'' ≫ r
  calc
    _ = (HP.map m ≫ HP.map t) ≫ HP.map c ≫ r := (Category.assoc _ _ _).symm
    _ = (HP.map t₀ ≫ HP.map m') ≫ HP.map c ≫ r := congrArg (fun q => q ≫ HP.map c ≫ r) h₁
    _ = HP.map t₀ ≫ (HP.map m' ≫ HP.map c) ≫ r := by simp only [Category.assoc]
    _ = HP.map t₀ ≫ (HP.map c₀ ≫ HP.map m'') ≫ r := congrArg (fun q => HP.map t₀ ≫ q ≫ r) h₂
    _ = _ := by simp only [Category.assoc]

end CategoryTheory.Functor
