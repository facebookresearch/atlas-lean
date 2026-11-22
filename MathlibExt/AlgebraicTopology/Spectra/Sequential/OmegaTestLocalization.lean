/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Sequential.NativeStableEquivalence
import MathlibExt.AlgebraicTopology.Spectra.Sequential.KLocalizationBridge
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ConstructionHomotopyComparison

/-!
# The original ordinary Omega tests and the original K-local reflection

The ordinary model's literal localization is compared with the native
caller-bottom localization through the complete existing model and Q data.
Every original Omega-target precomposition function and both Hom directions
are retained. The original K replacement, unit, and categorical reflector
therefore test this same original weak class. This identifies the categorical
localization; the arbitrary-target K-right intersection and stable model
axioms remain separate proofs.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v

open CategoryTheory HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum

open HomotopicalAlgebra.EnrichedProjective.Native
open PointedCGWH.SequentialSpectrum.StableK
open PointedCGWH.NativeOrderedMappingTelescope.NativeKLocalLiftingGeometry
open PointedCGWH.NativeOrderedMappingTelescope.NativeKStableAcyclicityGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

private abbrev actualIndex :=
  CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}

/-- The literal original ordinary localization carrier is the actual native carrier. -/
theorem levelHomotopyCategory_eq_native :
    LevelHomotopyCategory.{u, v} =
      Construction.nativeModelHomotopyCategory (A := actualIndex.{u, v}) :=
  Construction.fixedModelHomotopyCategory_eq_native

/-- Equality retains the complete actual original Q functor and all its map functions. -/
theorem toLevelHomotopyCategory_heq_native :
    HEq toLevelHomotopyCategory.{u, v}
      (Construction.nativeModelProjection (A := actualIndex.{u, v})) :=
  Construction.fixedModelProjection_heq_native

/-- All original Omega test maps commute through the actual full Hom correspondence. -/
theorem originalOmegaPrecomposition_conjugacy
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (E : PointedCGWH.SequentialSpectrum.{u, v})
    (g : toLevelHomotopyCategory.obj Y ⟶ toLevelHomotopyCategory.obj E) :
    Construction.fixedHoHomEquiv X E (toLevelHomotopyCategory.map f ≫ g) =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫
        Construction.fixedHoHomEquiv Y E g :=
  Construction.fixedHoHomEquiv_source f g

/-- This is equality of the two entire original precomposition functions. -/
theorem originalOmegaPrecomposition_wholeFunction
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (E : PointedCGWH.SequentialSpectrum.{u, v}) :
    (fun g : toLevelHomotopyCategory.obj Y ⟶ toLevelHomotopyCategory.obj E =>
      Construction.fixedHoHomEquiv X E (toLevelHomotopyCategory.map f ≫ g)) =
      (fun g : toLevelHomotopyCategory.obj Y ⟶ toLevelHomotopyCategory.obj E =>
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫
          Construction.fixedHoHomEquiv Y E g) := by
  funext g
  exact originalOmegaPrecomposition_conjugacy f E g

/-- The complete inverse Hom function retains the same original precomposition square. -/
theorem originalOmegaPrecomposition_conjugacy_symm
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (E : PointedCGWH.SequentialSpectrum.{u, v})
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Y ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj E) :
    (Construction.fixedHoHomEquiv X E).symm
        ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫ g) =
      toLevelHomotopyCategory.map f ≫ (Construction.fixedHoHomEquiv Y E).symm g :=
  Construction.fixedHoHomEquiv_source_symm f g

/-- The actual original Omega tests equal the complete original K-local Hom tests. -/
theorem omegaTestEquivalences_iff_originalLocalTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    omegaTestEquivalences f ↔ localTestEquivalences f := by
  have hB : B = Construction.generatorOrderBot.{v} := Subsingleton.elim _ _
  cases hB
  exact (originalLocalTestEquivalence_iff_omegaTests f).symm

/-- Equality concerns the entire actual original weak morphism property. -/
theorem omegaTestEquivalences_eq_originalLocalTests :
    omegaTestEquivalences.{u, v} = localTestEquivalences := by
  funext X Y f
  exact propext (omegaTestEquivalences_iff_originalLocalTests f)

/-- The same actual original bare K replacement detects precisely the original Omega tests. -/
theorem originalKDetectedWeak_eq_omegaTests :
    originalKDetectedWeakEquivalences.{u, v} = omegaTestEquivalences :=
  originalKDetectedWeak_eq_localTests.trans omegaTestEquivalences_eq_originalLocalTests.symm

/-- Every original arrow is tested using the same actual original K map, on all sources. -/
theorem originalKReplacementMap_weak_iff_omegaTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (localReplacement.map f) ↔
      omegaTestEquivalences f :=
  (originalKReplacementMap_weak_iff_localTests f).trans
    (omegaTestEquivalences_iff_originalLocalTests f).symm

/-- The original categorical reflector localizes the literal ordinary Omega-test class. -/
theorem localTestLocalization_isLocalization_omegaTests :
    localTestLocalization.{u, v}.IsLocalization omegaTestEquivalences := by
  rw [omegaTestEquivalences_eq_originalLocalTests]
  exact localTestLocalization_isLocalization

/-- The actual original K unit has the literal ordinary Omega tests at every source. -/
theorem originalKUnit_ordinaryOmegaTests (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    omegaTestEquivalences (localReplacementUnit.app X) :=
  (omegaTestEquivalences_iff_originalLocalTests _).mpr
    (originalKUnit_localTestEquivalence_allSource X)

/-- Every original K-left arrow has those same ordinary Omega tests on arbitrary endpoints. -/
theorem originalKLeft_ordinaryOmegaTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : generators.rlp.llp f) : omegaTestEquivalences f :=
  (omegaTestEquivalences_iff_originalLocalTests f).mpr (originalKLeft_localTests f hf)

/-- Both complete original unit Hom functions are transported to the ordinary source carrier. -/
def ordinaryKUnitHomEquiv (X Z : PointedCGWH.SequentialSpectrum.{u, v}) (hZ : Z.IsOmega) :
    (toLevelHomotopyCategory.obj (localReplacement.obj X) ⟶
        toLevelHomotopyCategory.obj Z) ≃
      (toLevelHomotopyCategory.obj X ⟶ toLevelHomotopyCategory.obj Z) :=
  (Construction.fixedHoHomEquiv (localReplacement.obj X) Z).trans
    ((originalKUnitHomEquiv X Z ((lifting_toZero_iff_isOmega Z).mpr hZ)).trans
      (Construction.fixedHoHomEquiv X Z).symm)

/-- The complete forward unit Hom function remains literal ordinary precomposition. -/
theorem ordinaryKUnitHomEquiv_apply (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega)
    (g : toLevelHomotopyCategory.obj (localReplacement.obj X) ⟶
      toLevelHomotopyCategory.obj Z) :
    ordinaryKUnitHomEquiv X Z hZ g =
      toLevelHomotopyCategory.map (localReplacementUnit.app X) ≫ g := by
  apply (Construction.fixedHoHomEquiv X Z).injective
  change Construction.fixedHoHomEquiv X Z
      ((Construction.fixedHoHomEquiv X Z).symm
        (originalKUnitHomEquiv X Z ((lifting_toZero_iff_isOmega Z).mpr hZ)
          (Construction.fixedHoHomEquiv (localReplacement.obj X) Z g))) = _
  rw [Equiv.apply_symm_apply, originalKUnitHomEquiv_apply]
  exact (originalOmegaPrecomposition_conjugacy (localReplacementUnit.app X) Z g).symm

/-- The whole inverse retains the original native inverse and both complete Hom transports. -/
theorem ordinaryKUnitHomEquiv_invFun (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega) :
    (ordinaryKUnitHomEquiv X Z hZ).invFun =
      (fun g => (Construction.fixedHoHomEquiv (localReplacement.obj X) Z).symm
        ((originalKUnitHomEquiv X Z ((lifting_toZero_iff_isOmega Z).mpr hZ)).symm
          (Construction.fixedHoHomEquiv X Z g))) := rfl

/-- Every ordinary input retains the complete original inverse section equation. -/
theorem ordinaryKUnitHomEquiv_symm_section (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega) (g : toLevelHomotopyCategory.obj X ⟶ toLevelHomotopyCategory.obj Z) :
    toLevelHomotopyCategory.map (localReplacementUnit.app X) ≫
      (ordinaryKUnitHomEquiv X Z hZ).symm g = g := by
  rw [← ordinaryKUnitHomEquiv_apply X Z hZ, Equiv.apply_symm_apply]

/-- Every actual source arrow retains the full ordinary forward unit naturality. -/
theorem ordinaryKUnitHomEquiv_source
    {X X' : PointedCGWH.SequentialSpectrum.{u, v}} (f : X' ⟶ X)
    (Z : PointedCGWH.SequentialSpectrum.{u, v}) (hZ : Z.IsOmega)
    (g : toLevelHomotopyCategory.obj (localReplacement.obj X) ⟶
      toLevelHomotopyCategory.obj Z) :
    ordinaryKUnitHomEquiv X' Z hZ (toLevelHomotopyCategory.map (localReplacement.map f) ≫ g) =
      toLevelHomotopyCategory.map f ≫ ordinaryKUnitHomEquiv X Z hZ g := by
  rw [ordinaryKUnitHomEquiv_apply, ordinaryKUnitHomEquiv_apply]
  let H := toLevelHomotopyCategory.{u, v}
  change H.map (localReplacementUnit.app X') ≫ (H.map (localReplacement.map f) ≫ g) =
    H.map f ≫ (H.map (localReplacementUnit.app X) ≫ g)
  rw [← Category.assoc, ← H.map_comp, localReplacementUnit_naturality, H.map_comp,
    Category.assoc]

/-- Every actual source arrow retains the complete original inverse naturality function. -/
theorem ordinaryKUnitHomEquiv_source_symm
    {X X' : PointedCGWH.SequentialSpectrum.{u, v}} (f : X' ⟶ X)
    (Z : PointedCGWH.SequentialSpectrum.{u, v}) (hZ : Z.IsOmega)
    (g : toLevelHomotopyCategory.obj X ⟶ toLevelHomotopyCategory.obj Z) :
    (ordinaryKUnitHomEquiv X' Z hZ).symm (toLevelHomotopyCategory.map f ≫ g) =
      toLevelHomotopyCategory.map (localReplacement.map f) ≫
        (ordinaryKUnitHomEquiv X Z hZ).symm g := by
  apply (ordinaryKUnitHomEquiv X' Z hZ).injective
  rw [Equiv.apply_symm_apply, ordinaryKUnitHomEquiv_source, Equiv.apply_symm_apply]

/-- Arbitrary original ordinary-Ho target maps retain the full forward unit function. -/
theorem ordinaryKUnitHomEquiv_target (X Z Z' : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega) (hZ' : Z'.IsOmega)
    (f : toLevelHomotopyCategory.obj Z ⟶ toLevelHomotopyCategory.obj Z')
    (g : toLevelHomotopyCategory.obj (localReplacement.obj X) ⟶
      toLevelHomotopyCategory.obj Z) :
    ordinaryKUnitHomEquiv X Z' hZ' (g ≫ f) = ordinaryKUnitHomEquiv X Z hZ g ≫ f := by
  rw [ordinaryKUnitHomEquiv_apply, ordinaryKUnitHomEquiv_apply]
  exact (Category.assoc _ _ _).symm

/-- Arbitrary ordinary-Ho target maps also retain the whole original inverse naturality. -/
theorem ordinaryKUnitHomEquiv_target_symm (X Z Z' : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega) (hZ' : Z'.IsOmega)
    (f : toLevelHomotopyCategory.obj Z ⟶ toLevelHomotopyCategory.obj Z')
    (g : toLevelHomotopyCategory.obj X ⟶ toLevelHomotopyCategory.obj Z) :
    (ordinaryKUnitHomEquiv X Z' hZ').symm (g ≫ f) =
      (ordinaryKUnitHomEquiv X Z hZ).symm g ≫ f := by
  apply (ordinaryKUnitHomEquiv X Z' hZ').injective
  rw [Equiv.apply_symm_apply, ordinaryKUnitHomEquiv_target X Z Z' hZ hZ',
    Equiv.apply_symm_apply]

end PointedCGWH.SequentialSpectrum
