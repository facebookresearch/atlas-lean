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
## Functorial augmented comparisons in arbitrary abelian categories
-/


/-!
## Functorial augmented exact resolutions give the cohomology-to-derived natural map
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

/--
The augmented injective comparison on a functorial complex is natural. The premises are the
coaugmentation maps and their functorial square.
-/
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
