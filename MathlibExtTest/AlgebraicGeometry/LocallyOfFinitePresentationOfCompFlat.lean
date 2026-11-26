/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.LocallyOfFinitePresentationOfCompFlat

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry

-- `exactSource` consumer with the original binders: the conclusion is
-- local finite presentation of `g`, from local finite presentation of
-- the composite `f ≫ g` along a flat surjective quasi-compact locally
-- finitely presented cover `f`.
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f] [QuasiCompact f]
    [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp_of_flat_of_surjective f g

-- The same consumer in a different universe.
example {X Y Z : Scheme.{v}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f] [QuasiCompact f]
    [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp_of_flat_of_surjective f g

-- Boundary consumer: when the cover is the identity, the hypothesis on
-- the composite is the conclusion itself, and no flatness argument is
-- needed beyond the identity cover being flat, surjective and
-- locally of finite presentation.
example {Y Z : Scheme.{u}} (g : Y ⟶ Z) [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp_of_flat_of_surjective (𝟙 Y) g

-- The cover need not be quasi-compact: the consumer above without `[QuasiCompact f]`.
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [Flat f]
    [LocallyOfFinitePresentation f] [Surjective f]
    [LocallyOfFinitePresentation (f ≫ g)] : LocallyOfFinitePresentation g :=
  LocallyOfFinitePresentation.of_comp_of_flat_of_surjective f g

-- A concrete cover: `Spec ℤ[X][Y] ⟶ Spec ℤ[X]` is flat, surjective and of finite
-- presentation, and its composite with `Spec ℤ[X] ⟶ Spec ℤ` is of finite presentation.
example : LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ)))) := by
  let φ := CommRingCat.ofHom (algebraMap (Polynomial ℤ) (Polynomial (Polynomial ℤ)))
  have : Flat (Spec.map φ) := (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : LocallyOfFinitePresentation (Spec.map φ) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  have : Surjective (Spec.map φ) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := Polynomial ℤ)
      (B := Polynomial (Polynomial ℤ))⟩
  have : LocallyOfFinitePresentation
      (Spec.map φ ≫ Spec.map (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)).mpr
      (RingHom.finitePresentation_algebraMap.mpr inferInstance)
  exact LocallyOfFinitePresentation.of_comp_of_flat_of_surjective (Spec.map φ) _
