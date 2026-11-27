/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module
public import MathlibExt.CategoryTheory.Abelian.RightDerived.AugmentedResolutionNaturality

/-!
# Functorial coaugmented complexes and right derivation

In abelian categories `C,D`, with injective resolutions in `C`, an
additive `F : C → D` sends a functorial family of coaugmentation
quasi-isomorphisms `X[0] → R(X)` to a natural map from the cohomology
of `F(R(X))` to `R^nF(X)`.
-/


/-!
## Naturality in the resolved object

The family of coaugmentations is required to commute with each map
`f : X → Y`: `ι_X ≫ R(f) = f[0] ≫ ι_Y`. The cohomology-to-derived
comparisons then form a natural transformation in `X`.
-/
@[expose] public section
section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. Let `R : C → CochainComplex C ℕ` have coaugmentation
quasi-isomorphisms `ι_X : X[0] → R(X)` satisfying
`ι_X ≫ R(f) = f[0] ≫ ι_Y`. The maps `Hⁿ(F(R(X))) → R^nF(X)`
form a natural transformation from mapped family cohomology to `R^nF`. -/
def augmentedResolutionToRightDerivedNatTrans
    (F : C ⥤ D) [F.Additive] (R : C ⥤ CochainComplex C ℕ)
    (ι : ∀ X : C, (CochainComplex.single₀ C).obj X ⟶ R.obj X)
    (hι : ∀ X : C, QuasiIso (ι X))
    (hmap : ∀ {X Y : C} (f : X ⟶ Y), ι X ≫ R.map f = (CochainComplex.single₀ C).map f ≫ ι Y)
    (n : ℕ) :
    R ⋙ F.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
      HomologicalComplex.homologyFunctor D (ComplexShape.up ℕ) n ⟶ F.rightDerived n where
  app X := let := hι X; F.augmentedResolutionToRightDerivedHom (R.obj X) (ι X) n
  naturality X Y f := by
    let := hι X
    let := hι Y
    exact F.augmentedResolutionToRightDerivedHom_naturality (ι X) (ι Y) f (R.map f) (hmap f) n

end CategoryTheory.Functor
end
