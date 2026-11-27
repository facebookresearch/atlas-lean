/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionPrecomposition

/-!
# The two augmented right-derived precomposition maps

For abelian `C,D,A`, injective resolutions in `C,D`, additive
injective- and homology-preserving `J : C → D`, and additive
`P : C → A`, `B : D → A` with `P ≅ J ⋙ B`, an exact coaugmented
complex `X[0] → I` gives two equal maps
`Hⁿ(P(I)) → R^nB(J(X))`: compare to derived cohomology first, or
first identify the mapped coefficient complex.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ v₁ v₂ v₃
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
  {A : Type u₃} [Category.{v₃} A] [Abelian A]
variable (J : C ⥤ D) [J.Additive] [J.PreservesInjectiveObjects] [J.PreservesHomology]
  (B : D ⥤ A) [B.Additive] {P : C ⥤ A} [P.Additive]

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. For a coaugmentation quasi-isomorphism `ι : X[0] → I`,
the left route `Hⁿ(P(I)) → R^nB(J(X))` is the augmented comparison
to `R^nP(X)` followed by the derived precomposition isomorphism. -/
def augmentedDerivedPrecompLeft (α : P ≅ J ⋙ B) {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι) (n : ℕ) :
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n ⟶
      (B.rightDerived n).obj (J.obj X) := by
  letI : QuasiIso ι := hι
  exact P.augmentedResolutionToRightDerivedHom I ι n ≫
    (rightDerivedPrecompIsoOfIso J B α n).hom.app X

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. For a coaugmentation quasi-isomorphism `ι : X[0] → I`,
the right route `Hⁿ(P(I)) → R^nB(J(X))` transports cohomology by
`α_I` and complex composition to `Hⁿ(B(J(I)))`, then applies the
augmented comparison for `J(I)`. -/
def augmentedDerivedPrecompRight (α : P ≅ J ⋙ B) {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι) (n : ℕ) :
    ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n ⟶
      (B.rightDerived n).obj (J.obj X) := by
  letI : QuasiIso ι := hι
  exact HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex α.hom (ComplexShape.up ℕ)).app I) n ≫
    HomologicalComplex.homologyMap
      (((Functor.mapHomologicalComplexCompIso (Iso.refl (J ⋙ B)) (ComplexShape.up ℕ)).app I).inv) n ≫
    B.augmentedResolutionToRightDerivedHom
      ((J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I)
      ((HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app X ≫
        (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι) n

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. For a coaugmentation quasi-isomorphism `ι : X[0] → I`,
the left and right augmented precomposition maps
`Hⁿ(P(I)) → R^nB(J(X))` are equal. -/
theorem augmentedDerivedPrecompLeft_eq_right (α : P ≅ J ⋙ B) {X : C} (I : CochainComplex C ℕ)
    (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι) (n : ℕ) :
    augmentedDerivedPrecompLeft J B α I ι hι n = augmentedDerivedPrecompRight J B α I ι hι n := by
  let : QuasiIso ι := hι
  exact J.augmentedResolutionToRightDerivedHom_precomposition B α I ι n

end CategoryTheory.Functor
