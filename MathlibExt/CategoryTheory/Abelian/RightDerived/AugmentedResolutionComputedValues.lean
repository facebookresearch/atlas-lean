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
# Augmented comparison values with the derived target fixed

The output group is the original derived object. A value equality for the augmentation-comparison
arrow is transported through its literal homology and computed target maps.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u₁ u₂ u₃ v₁ v₂
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace CategoryTheory.Functor

/-- Evaluate the computed target map using a proved value of the augmented comparison. -/
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
