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
## Augmentation-computed comparison under a original complex isomorphism
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
universe u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor
variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
variable {D : Type u'} [Category.{v'} D] [Abelian D]

/--
An original complex isomorphism preserving the full coaugmentation identifies the SAME
augmentation-computed maps in every degree.
-/
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

/--
Full coaugmentation compatibility and the quasi-isomorphism proofs give the original comparison
square, with no implicit resolution choice.
-/
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

/-- The literal computed-comparison equation on the given augmented complex isomorphism. -/
def augmentedResolutionIsoProperty (F : C ⥤ D) [F.Additive] {X : C}
    {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj X ⟶ J) (hι : QuasiIso ι) (hκ : QuasiIso κ)
    (e : I ≅ J) (n : ℕ) : Prop :=
  let : QuasiIso ι := hι
  let : QuasiIso κ := hκ
  HomologicalComplex.homologyMap ((F.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom) n ≫
    F.augmentedResolutionToRightDerivedHom J κ n = F.augmentedResolutionToRightDerivedHom I ι n

/-- The original coaugmentation equation proves that literal computed-comparison property. -/
theorem augmentedResolutionIsoProperty_of_augmentation (F : C ⥤ D) [F.Additive] {X : C}
    {I J : CochainComplex C ℕ}
    (ι : (CochainComplex.single₀ C).obj X ⟶ I)
    (κ : (CochainComplex.single₀ C).obj X ⟶ J) (hι : QuasiIso ι) (hκ : QuasiIso κ)
    (e : I ≅ J) (h : ι ≫ e.hom = κ) (n : ℕ) :
    augmentedResolutionIsoProperty F ι κ hι hκ e n :=
  F.augmentedResolutionToRightDerivedHom_iso_explicit ι κ hι hκ e h n

end CategoryTheory.Functor
