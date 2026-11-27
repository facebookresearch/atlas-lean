/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionComplexPrecomposition
public import MathlibExt.CategoryTheory.ComparisonArrows

/-!
# Two comparisons from augmented cohomology after source change

For abelian `C,D,A`, an additive injective- and homology-preserving
`J : C → D`, additive `P : C → A`, `B : D → A`, and `P ≅ J ⋙ B`,
coaugmented complexes resolving `X` and `J(X)` give two maps
`Hⁿ(P(I)) → R^nB(J(X))`. They agree when the identification of the
mapped complex with the second complex preserves its coaugmentation.
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
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. Suppose `ι : X[0] → I`, `κ : J(X)[0] → K` are quasi-isomorphisms
and `e : J(I) ≅ K`. The two maps `Hⁿ(P(I)) → R^nB(J(X))` are:
transport cohomology along `α_I` and `B(e)` then use the comparison
for `K`; or use the comparison for `I` then right-derived precomposition. -/
def augmentedComplexComparisonArrows (α : P ≅ J ⋙ B) {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι)
    (K : CochainComplex D ℕ) (κ : (CochainComplex.single₀ D).obj (J.obj X) ⟶ K) (hκ : QuasiIso κ)
    (e : (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ≅ K) (n : ℕ) :=
  let : QuasiIso ι := hι
  let : QuasiIso κ := hκ
  comparisonArrowsOfMaps
    (HomologicalComplex.homologyMap
      (CosimplicialCup.complexPrecompositionIso J P B α I ≪≫
        (B.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso e).hom n ≫
      B.augmentedResolutionToRightDerivedHom K κ n)
    (P.augmentedResolutionToRightDerivedHom I ι n ≫
      (rightDerivedPrecompIsoOfIso J B α n).hom.app X)

/-- Let `C,D,A` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → A`, `P : C → A` additive, and `α : P ≅ J ⋙ B`. For coaugmentation quasi-isomorphisms `ι : X[0] → I`,
`κ : J(X)[0] → K`, if `e : J(I) ≅ K` carries the mapped `ι` to `κ`,
the two comparison maps `Hⁿ(P(I)) → R^nB(J(X))` are equal. -/
theorem augmentedComplexComparisonArrows_eq (α : P ≅ J ⋙ B) {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι)
    (K : CochainComplex D ℕ) (κ : (CochainComplex.single₀ D).obj (J.obj X) ⟶ K) (hκ : QuasiIso κ)
    (e : (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ≅ K)
    (h : ((HomologicalComplex.singleMapHomologicalComplex J (ComplexShape.up ℕ) 0).inv.app X ≫
        (J.mapHomologicalComplex (ComplexShape.up ℕ)).map ι) ≫ e.hom = κ) (n : ℕ) :
    (augmentedComplexComparisonArrows J B α I ι hι K κ hκ e n).left =
      (augmentedComplexComparisonArrows J B α I ι hι K κ hκ e n).right :=
  J.augmentedComplexPrecompositionProperty_of_augmentation B α I ι hι K κ hκ e h n

end CategoryTheory.Functor
