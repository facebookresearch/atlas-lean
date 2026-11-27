/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionPrecomposition
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionIso
public import MathlibExt.AlgebraicTopology.SimplicialObject.CofacePrecomposition

/-!
# Augmented cohomology comparison after complex precomposition

For abelian `C,D,A`, an additive injective- and homology-preserving
`J : C → D`, additive `P : C → A`, `B : D → A`, and `P ≅ J ⋙ B`,
an isomorphism between `J(I)` and a coaugmented complex `K` gives a
comparison square from `Hⁿ(P(I))` to `R^nB(J(X))`. Preserving the
coaugmentation proves this square commutes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits AlgebraicTopology
namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
  {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable (J : C ⥤ D) [J.Additive] [J.PreservesInjectiveObjects] [J.PreservesHomology]
  (B : D ⥤ A) [B.Additive] {P : C ⥤ A} [P.Additive]

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. For quasi-isomorphisms `ι : X[0] → I`, `κ : J(X)[0] → K`
and `e : J(I) ≅ K`, the complex-precomposition property says that
transport to `Hⁿ(B(K))` followed by its augmented comparison equals
the augmented comparison for `I` followed by derived precomposition. -/
def augmentedComplexPrecompositionProperty (α : P ≅ J ⋙ B) {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι)
    (K : CochainComplex D ℕ) (κ : (CochainComplex.single₀ D).obj (J.obj X) ⟶ K) (hκ : QuasiIso κ)
    (e : (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ≅ K) (n : ℕ) : Prop :=
  let : QuasiIso ι := hι
  let : QuasiIso κ := hκ
  HomologicalComplex.homologyMap
      (CosimplicialCup.complexPrecompositionIso J P B α I ≪≫
        (B.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso e).hom n ≫
      B.augmentedResolutionToRightDerivedHom K κ n =
    P.augmentedResolutionToRightDerivedHom I ι n ≫
      (rightDerivedPrecompIsoOfIso J B α n).hom.app X

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. For coaugmentation quasi-isomorphisms `ι : X[0] → I`,
`κ : J(X)[0] → K`, if `e : J(I) ≅ K` carries the mapped `ι` to `κ`,
then the augmented complex-precomposition property holds in every
degree `n`. -/
theorem augmentedComplexPrecompositionProperty_of_augmentation (α : P ≅ J ⋙ B) {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι)
    (K : CochainComplex D ℕ) (κ : (CochainComplex.single₀ D).obj (J.obj X) ⟶ K) (hκ : QuasiIso κ)
    (e : (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ≅ K)
    (h : ((HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app X ≫
        (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι) ≫ e.hom = κ) (n : ℕ) :
    augmentedComplexPrecompositionProperty J B α I ι hι K κ hκ e n := by
  let : QuasiIso ι := hι
  let : QuasiIso κ := hκ
  let ρ := (HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app X ≫
    (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι
  have hi := B.augmentedResolutionToRightDerivedHom_iso ρ κ e h n
  have hp := J.augmentedResolutionToRightDerivedHom_precomposition B α I ι n
  let H := HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) n
  let a := (NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I
  let b := (((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B))
    (ComplexShape.up ℕ)).app I).inv)
  let c := (B.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom
  let d : H.obj ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj K) ⟶
      (B.rightDerived n).obj (J.obj X) := B.augmentedResolutionToRightDerivedHom K κ n
  let r : H.obj ((B.mapHomologicalComplex (ComplexShape.up ℕ)).obj
      ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I)) ⟶
      (B.rightDerived n).obj (J.obj X) := B.augmentedResolutionToRightDerivedHom
    ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I) ρ n
  change H.map c ≫ d = r at hi
  change P.augmentedResolutionToRightDerivedHom I ι n ≫
    (rightDerivedPrecompIsoOfIso J B α n).hom.app X = H.map a ≫ H.map b ≫ r at hp
  change H.map ((a ≫ b) ≫ c) ≫ d = P.augmentedResolutionToRightDerivedHom I ι n ≫
    (rightDerivedPrecompIsoOfIso J B α n).hom.app X
  have hz : H.map ((a ≫ b) ≫ c) ≫ d = H.map a ≫ H.map b ≫ r := by
    rw [H.map_comp, H.map_comp]
    simp only [Category.assoc]
    rw [hi]
  exact hz.trans hp.symm

end CategoryTheory.Functor
