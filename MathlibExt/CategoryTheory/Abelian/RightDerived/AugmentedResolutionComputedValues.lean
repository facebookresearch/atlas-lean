/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionComparisonArrows

/-!
# Values of augmented cohomology comparisons

For an additive-group-valued derived functor, a value of the comparison
on `Hⁿ(P(I))` is also the value obtained by transporting that cohomology
class to `Hⁿ(B(K))` and applying the augmented comparison for `K`.
The derived coefficient group and the class maps are fixed throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ v₁ v₂
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace CategoryTheory.Functor

/-- Let `C,D` be abelian, with injective resolutions in `C,D`,
`J : C → D` additive and preserving injectives and homology,
`B : D → Ab`, `P : C → Ab` additive, and `α : P ≅ J ⋙ B`.
Let `ι : X[0] → I`, `κ : J(X)[0] → K` be quasi-isomorphisms and
`e : J(I) ≅ K`. If the comparison via `α_I` and `B(e)` sends
`z ∈ Hⁿ(P(I))` to `v ∈ R^nB(J(X))`, then the augmented comparison
for `K` takes the transported class to that same `v`. -/
def augmentedComparisonComputedValue
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasInjectiveResolutions C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasInjectiveResolutions D]
    (J : C ⥤ D) [J.Additive] [J.PreservesInjectiveObjects] [J.PreservesHomology]
    (B : D ⥤ AddCommGrpCat.{u₃}) [B.Additive]
    {P : C ⥤ AddCommGrpCat.{u₃}} [P.Additive]
    (α : P ≅ J ⋙ B) {X : C}
    (I : CochainComplex C ℕ) (ι : (CochainComplex.single₀ C).obj X ⟶ I) (hι : QuasiIso ι)
    (K : CochainComplex D ℕ) (κ : (CochainComplex.single₀ D).obj (J.obj X) ⟶ K) (hκ : QuasiIso κ)
    (e : (J.mapHomologicalComplex (ComplexShape.up ℕ)).obj I ≅ K) (n : ℕ)
    (z : ((P.mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n)
    (v : (B.rightDerived n).obj (J.obj X))
    (h : (augmentedComplexComparisonArrows J B α I ι hι K κ hκ e n).left z = v) :
    letI : QuasiIso κ := hκ
    PLift ((B.augmentedResolutionToRightDerivedHom K κ n)
      (HomologicalComplex.homologyMap
        (CosimplicialCup.complexPrecompositionIso J P B α I ≪≫
          (B.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso e).hom n z) = v) := by
  letI : QuasiIso κ := hκ
  have hv : (augmentedComplexComparisonArrows J B α I ι hι K κ hκ e n).left z =
      (B.augmentedResolutionToRightDerivedHom K κ n)
        (HomologicalComplex.homologyMap
          (CosimplicialCup.complexPrecompositionIso J P B α I ≪≫
            (B.mapHomologicalComplex (ComplexShape.up ℕ)).mapIso e).hom n z) := rfl
  exact PLift.up (hv.symm.trans h)

end CategoryTheory.Functor
