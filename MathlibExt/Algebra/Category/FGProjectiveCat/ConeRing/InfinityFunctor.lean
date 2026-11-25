/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionIntertwiner
public import MathlibExt.Algebra.Category.FGProjectiveCat.ScalarExtensionFunctorCoherence
public import MathlibExt.RingTheory.ConeRing.InfiniteSum

/-!
# The actual projective cone infinity functor and its original maps

Scalar extension along the original countable repeat acts on the original
finite-projective category of the cone. Its finite/projective preservation
and exactness come from the existing Ring-only scalar-extension supplier.
The frozen original projection/inclusion matrices give its four original
coefficient transformations and their exact matrix inverse relations.
-/

public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open ModuleCat.RingHomScalarExtension

universe uR uM

namespace FGProjectiveCat.ConeRing

variable (R : Type uR) [Ring R]

local notation "C" => _root_.ConeRing R

/-- The original ring-universe finite-projective category of the original cone ring. -/
abbrev category := FGProjectiveCat.{uR} C

local notation "P" => category R
local notation "φ" => _root_.ConeRing.infinityHom R
local notation "p₀" => _root_.ConeRing.firstProjection R
local notation "p₁" => _root_.ConeRing.tailProjection R
local notation "u₀" => _root_.ConeRing.firstInclusion R
local notation "u₁" => _root_.ConeRing.tailInclusion R

/-- The actual unresized extension on a module universe large enough for the original cone. -/
abbrev rawInfinityFunctor :
    FGProjectiveCat.{max uR uM} C ⥤ FGProjectiveCat.{max uR uM} C :=
  scalarExtension φ

/-- The original ring-universe scalar extension used by the native projective K-model. -/
abbrev infinityFunctor : P ⥤ P := ringScalarExtension φ

instance infinityFunctorAdditive : (infinityFunctor R).Additive := inferInstance

instance infinityFunctorExact : (infinityFunctor R).IsExact := inferInstance

instance rawInfinityFunctorAdditive : (rawInfinityFunctor.{uR,uM} R).Additive := inferInstance

instance rawInfinityFunctorExact : (rawInfinityFunctor.{uR,uM} R).IsExact := inferInstance

/-- The actual identity scalar functor before its original categorical identity unitor. -/
abbrev identityScalarFunctor : P ⥤ P := ringScalarExtension (RingHom.id C)

/-- The first projection has precisely the original identity-to-infinity balance relation. -/
theorem firstProjection_intertwines : Intertwines (RingHom.id C) φ p₀ := by
  intro a
  exact (_root_.ConeRing.firstProjection_mul_infinity a).symm

/-- The original tail projection commutes with the original infinity action. -/
theorem tailProjection_intertwines : Intertwines φ φ p₁ := by
  intro a
  exact (_root_.ConeRing.tailProjection_mul_infinity a).symm

/-- The first inclusion has precisely the original infinity-to-identity balance relation. -/
theorem firstInclusion_intertwines : Intertwines φ (RingHom.id C) u₀ := by
  intro a
  exact _root_.ConeRing.infinity_mul_firstInclusion a

/-- The original tail inclusion commutes with the original infinity action. -/
theorem tailInclusion_intertwines : Intertwines φ φ u₁ := by
  intro a
  exact _root_.ConeRing.infinity_mul_tailInclusion a

/-- The actual first projection coefficient transformation of the original scalar functors. -/
abbrev firstProjectionMap : identityScalarFunctor R ⟶ infinityFunctor R :=
  ringScalarExtensionIntertwiner (RingHom.id C) φ p₀ (firstProjection_intertwines R)

/-- The actual tail projection coefficient transformation of the original infinity functor. -/
abbrev tailProjectionMap : infinityFunctor R ⟶ infinityFunctor R :=
  ringScalarExtensionIntertwiner φ φ p₁ (tailProjection_intertwines R)

/-- The original first inclusion coefficient map to the actual identity scalar functor. -/
abbrev firstInclusionMap : infinityFunctor R ⟶ identityScalarFunctor R :=
  ringScalarExtensionIntertwiner φ (RingHom.id C) u₀ (firstInclusion_intertwines R)

/-- The actual tail inclusion coefficient transformation of the original infinity functor. -/
abbrev tailInclusionMap : infinityFunctor R ⟶ infinityFunctor R :=
  ringScalarExtensionIntertwiner φ φ u₁ (tailInclusion_intertwines R)

/-- The original first projection then inclusion is the identity scalar transformation. -/
theorem firstProjectionMap_firstInclusionMap :
    firstProjectionMap R ≫ firstInclusionMap R = 𝟙 (identityScalarFunctor R) := by
  rw [ringScalarExtensionIntertwiner_comp]
  simpa only [_root_.ConeRing.firstProjection_mul_firstInclusion] using
    ringScalarExtensionIntertwiner_one (RingHom.id C)

/-- The original tail projection then first inclusion is the actual zero transformation. -/
theorem tailProjectionMap_firstInclusionMap :
    tailProjectionMap R ≫ firstInclusionMap R = 0 := by
  rw [ringScalarExtensionIntertwiner_comp]
  simpa only [_root_.ConeRing.tailProjection_mul_firstInclusion] using
    ringScalarExtensionIntertwiner_zero φ (RingHom.id C)

/-- The original first projection then tail inclusion is the actual zero transformation. -/
theorem firstProjectionMap_tailInclusionMap :
    firstProjectionMap R ≫ tailInclusionMap R = 0 := by
  rw [ringScalarExtensionIntertwiner_comp]
  simpa only [_root_.ConeRing.firstProjection_mul_tailInclusion] using
    ringScalarExtensionIntertwiner_zero (RingHom.id C) φ

/-- The tail projection then inclusion is the identity of the original infinity functor. -/
theorem tailProjectionMap_tailInclusionMap :
    tailProjectionMap R ≫ tailInclusionMap R = 𝟙 (infinityFunctor R) := by
  rw [ringScalarExtensionIntertwiner_comp]
  simpa only [_root_.ConeRing.tailProjection_mul_tailInclusion] using
    ringScalarExtensionIntertwiner_one φ

/-- The two original inclusion/projection routes sum to the actual infinity identity. -/
theorem inclusion_projection_maps_sum :
    firstInclusionMap R ≫ firstProjectionMap R +
      tailInclusionMap R ≫ tailProjectionMap R = 𝟙 (infinityFunctor R) := by
  rw [ringScalarExtensionIntertwiner_comp, ringScalarExtensionIntertwiner_comp,
    ← ringScalarExtensionIntertwiner_add]
  simpa only [_root_.ConeRing.inclusion_projection_sum] using ringScalarExtensionIntertwiner_one φ

/-- Insert original modules through the original unit tensor into the infinity extension. -/
def insert : 𝟭 P ⟶ infinityFunctor R :=
  (ringScalarExtensionIdIso C).inv ≫ firstProjectionMap R

/-- Extract an original module from its actual infinity extension by the original unitor. -/
def extract : infinityFunctor R ⟶ 𝟭 P :=
  firstInclusionMap R ≫ (ringScalarExtensionIdIso C).hom

/-- The original first route gives the identity on every original finite projective. -/
theorem insert_extract : insert R ≫ extract R = 𝟙 (𝟭 P) := by
  calc
    insert R ≫ extract R = (ringScalarExtensionIdIso C).inv ≫
        (firstProjectionMap R ≫ firstInclusionMap R) ≫ (ringScalarExtensionIdIso C).hom := by
      simp only [insert, extract, Category.assoc]
    _ = 𝟙 (𝟭 P) := by rw [firstProjectionMap_firstInclusionMap]; simp

/-- The original tail projection followed by extraction is zero on the same carrier. -/
theorem tailProjectionMap_extract : tailProjectionMap R ≫ extract R = 0 := by
  rw [extract, ← Category.assoc, tailProjectionMap_firstInclusionMap]
  simp

/-- The original insertion followed by tail inclusion is zero on the same carrier. -/
theorem insert_tailInclusionMap : insert R ≫ tailInclusionMap R = 0 := by
  rw [insert, Category.assoc, firstProjectionMap_tailInclusionMap]
  simp

/-- The original inverse routes sum to the identity of the actual infinity functor. -/
theorem extract_insert_tail_maps :
    extract R ≫ insert R + tailInclusionMap R ≫ tailProjectionMap R = 𝟙 (infinityFunctor R) := by
  have hfirst : extract R ≫ insert R = firstInclusionMap R ≫ firstProjectionMap R := by
    simp only [extract, insert, Category.assoc, Iso.hom_inv_id_assoc]
  rw [hfirst]
  exact inclusion_projection_maps_sum R

/-- In original coordinates, insertion is the original first-projection pure tensor. -/
theorem insert_pure (X : P) (x : X) :
    ringScalarExtensionCoordinates φ X (((insert R).app X).hom.hom x) = pure φ X p₀ x := by
  change ringScalarExtensionCoordinates φ X
    (((firstProjectionMap R).app X).hom.hom
      (((ringScalarExtensionIdIso C).inv.app X).hom.hom x)) = _
  rw [ringScalarExtensionIdIso_inv_apply]
  exact (ringScalarExtensionIntertwiner_pure (RingHom.id C) φ p₀
    (firstProjection_intertwines R) X 1 x).trans
      (congrArg (fun c : C => pure φ X c x) (one_mul p₀))

/-- The original tail projection right-multiplies each original pure coefficient. -/
theorem tailProjectionMap_pure (X : P) (s : C) (x : X) :
    ringScalarExtensionCoordinates φ X
      (((tailProjectionMap R).app X).hom.hom
        ((ringScalarExtensionCoordinates φ X).symm (pure φ X s x))) = pure φ X (s * p₁) x :=
  ringScalarExtensionIntertwiner_pure φ φ p₁ (tailProjection_intertwines R) X s x

/-- The original tail inclusion right-multiplies each original pure coefficient. -/
theorem tailInclusionMap_pure (X : P) (s : C) (x : X) :
    ringScalarExtensionCoordinates φ X
      (((tailInclusionMap R).app X).hom.hom
        ((ringScalarExtensionCoordinates φ X).symm (pure φ X s x))) = pure φ X (s * u₁) x :=
  ringScalarExtensionIntertwiner_pure φ φ u₁ (tailInclusion_intertwines R) X s x

/-- The whole original extraction retains its first-inclusion coefficient and original unitor. -/
theorem extract_coordinates (X : P) (t : (infinityFunctor R).obj X) :
    (((extract R).app X).hom.hom t) = identityTensorLinearEquiv C X
      (coefficientIntertwiner φ (RingHom.id C) u₀ (firstInclusion_intertwines R) X
        (ringScalarExtensionCoordinates φ X t)) := by
  change (((ringScalarExtensionIdIso C).hom.app X).hom.hom
    (((firstInclusionMap R).app X).hom.hom t)) = _
  rw [ringScalarExtensionIdIso_hom_apply, ringScalarExtensionIntertwiner_coordinates]

/-- Every original pure tensor extracts to its original first-inclusion module action. -/
theorem extract_pure (X : P) (s : C) (x : X) :
    (((extract R).app X).hom.hom
      ((ringScalarExtensionCoordinates φ X).symm (pure φ X s x))) = (s * u₀) • x := by
  rw [extract_coordinates, LinearEquiv.apply_symm_apply, coefficientIntertwiner_pure,
    identityTensorLinearEquiv_pure]

end FGProjectiveCat.ConeRing

end
