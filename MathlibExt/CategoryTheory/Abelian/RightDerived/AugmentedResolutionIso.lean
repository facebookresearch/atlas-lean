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
# Augmented comparisons under coaugmentation-preserving isomorphisms

Let `C,D` be abelian, with injective resolutions in `C`, and
`F : C → D` additive. An isomorphism between nonnegative cochain
complexes resolving `X` that preserves their coaugmentations makes
their maps `Hⁿ(F(I)) → R^nF(X)` agree after cohomology transport.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For quasi-isomorphisms `ι : X[0] → I`, `κ : X[0] → J` and
`e : I ≅ J` satisfying `ι ≫ e = κ`, the cohomology map of `F(e)`
followed by the augmented comparison for `J` equals the comparison
for `I`. -/
theorem augmentedResolutionToRightDerivedHom_iso
    (F : C ⥤ D) [F.Additive] {X : C} {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj X ⟶ J) [QuasiIso ι] [QuasiIso κ]
    (e : I ≅ J) (h : ι ≫ e.hom = κ) (n : ℕ) :
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom) n ≫
      F.augmentedResolutionToRightDerivedHom J κ n =
      F.augmentedResolutionToRightDerivedHom I ι n := by
  have ha : ι ≫ e.hom = (CochainComplex.single₀ C).map (𝟙 X) ≫ κ := by
    simpa only [Functor.map_id, Category.id_comp] using h
  have hn := F.augmentedResolutionToRightDerivedHom_naturality ι κ (𝟙 X) e.hom ha n
  simpa only [Functor.map_id, Category.comp_id] using hn

end CategoryTheory.Functor



namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. Given quasi-isomorphisms `ι : X[0] → I`, `κ : X[0] → J` and
an isomorphism `e : I ≅ J` carrying `ι` to `κ`, the equality
`Hⁿ(F(e)) ≫ comparison_J = comparison_I` holds for their augmented
cohomology-to-derived maps. -/
theorem augmentedResolutionToRightDerivedHom_iso_explicit
    (F : C ⥤ D) [F.Additive] {X : C} {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj X ⟶ J) (hι : QuasiIso ι) (hκ : QuasiIso κ)
    (e : I ≅ J) (h : ι ≫ e.hom = κ) (n : ℕ) :
    let : QuasiIso ι := hι
    let : QuasiIso κ := hκ
    HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom) n ≫
      F.augmentedResolutionToRightDerivedHom J κ n =
      F.augmentedResolutionToRightDerivedHom I ι n := by
  let : QuasiIso ι := hι
  let : QuasiIso κ := hκ
  exact F.augmentedResolutionToRightDerivedHom_iso ι κ e h n

end CategoryTheory.Functor

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For quasi-isomorphisms `ι : X[0] → I`, `κ : X[0] → J`
and `e : I ≅ J`, the comparison property in degree `n` is the equality
`Hⁿ(F(e)) ≫ comparison_J = comparison_I` of maps to `R^nF(X)`. -/
def augmentedResolutionIsoProperty (F : C ⥤ D) [F.Additive] {X : C}
    {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj X ⟶ J) (hι : QuasiIso ι) (hκ : QuasiIso κ)
    (e : I ≅ J) (n : ℕ) : Prop :=
  let : QuasiIso ι := hι
  let : QuasiIso κ := hκ
  HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom) n ≫
    F.augmentedResolutionToRightDerivedHom J κ n = F.augmentedResolutionToRightDerivedHom I ι n

/-- Let `C,D` be abelian, with injective resolutions in `C`,
and `F : C → D` additive. For coaugmentation quasi-isomorphisms `ι : X[0] → I`,
`κ : X[0] → J`, an isomorphism `e : I ≅ J` satisfying `ι ≫ e = κ`
has the degree-`n` augmented cohomology comparison property. -/
theorem augmentedResolutionIsoProperty_of_augmentation (F : C ⥤ D) [F.Additive] {X : C}
    {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj X ⟶ J) (hι : QuasiIso ι) (hκ : QuasiIso κ)
    (e : I ≅ J) (h : ι ≫ e.hom = κ) (n : ℕ) :
    augmentedResolutionIsoProperty F ι κ hι hκ e n :=
  F.augmentedResolutionToRightDerivedHom_iso_explicit ι κ hι hκ e h n

end CategoryTheory.Functor
