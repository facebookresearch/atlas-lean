/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StabilizationKReflection
import MathlibExt.AlgebraicTopology.Spectra.Sequential.KLocalizationBridge
import MathlibExt.AlgebraicTopology.Spectra.Sequential.StabilizationKAdapter
import MathlibExt.AlgebraicTopology.Spectra.Sequential.KOmegaRecognition
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.CategoryTheory.HomCongr

import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerOmegaRecognition
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.IntegerUnit
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.RTelescopeOmega
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OmegaTestLocalization
import MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization

/-!
# The original R after the original telescope gives actual Omega-test recognition

The auxiliary functor uses the original T followed by the original R. Its
unit is the original T-unit followed by the original R-unit at T(X).
The genuine original integer-pi comparison Isos identify this whole unit
map. The actual R(T(X)) Omega theorem and Omega-input diagonal recognition
prove level-weak preservation and both iterated unit weak statements.
The ordinary level localization then gives the full original Omega Hom
tests. No claim that T itself is Omega and no stable model is assumed.
All original R/T/MC/unit choices and original I/K data remain unchanged.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry

open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.StageIntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerUnitGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerOmegaRecognitionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTelescopeOmegaGeometry
open PointedCGWH.SequentialSpectrum.StableK
open PointedCGWH.NativeOrderedMappingTelescope.NativeKLocalLiftingGeometry
open PointedCGWH.NativeOrderedMappingTelescope.NativeKStableAcyclicityGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

/-- The auxiliary functor retains the original telescope followed by the original R. -/
def reflectionFunctor : PointedCGWH.SequentialSpectrum.{u, v} ⥤
    PointedCGWH.SequentialSpectrum.{u, v} :=
  telescopeFunctor ⋙ PointedCGWH.SequentialSpectrum.OrderedLoop.functor

/-- The complete auxiliary unit retains both actual original unit maps. -/
def reflectionUnit : 𝟭 PointedCGWH.SequentialSpectrum.{u, v} ⟶ reflectionFunctor where
  app X := PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X ≫
    PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X)
  naturality {X Y} f := by
    change f ≫ (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app Y ≫
      PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope Y)) =
      (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X ≫
        PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X)) ≫
          PointedCGWH.SequentialSpectrum.OrderedLoop.functor.map (telescopeFunctor.map f)
    have hT : f ≫ PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app Y =
        PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X ≫ telescopeFunctor.map f :=
      PointedCGWH.SequentialSpectrum.MappingTelescope.unit.naturality f
    have hR : telescopeFunctor.map f ≫
        PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope Y) =
        PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X) ≫
          PointedCGWH.SequentialSpectrum.OrderedLoop.functor.map (telescopeFunctor.map f) :=
      PointedCGWH.SequentialSpectrum.OrderedLoop.unit.naturality (telescopeFunctor.map f)
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫
        PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope Y)) hT).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun a =>
            PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X ≫ a) hR).trans
            (Category.assoc _ _ _).symm)))

/-- Every whole unit component is the actual original two-map composite. -/
theorem reflectionUnit_app (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    reflectionUnit.app X = PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X ≫
      PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X) := rfl

/-- Every original Arrow retains the literal original T-map followed by the original R-map. -/
theorem reflectionFunctor_map {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    reflectionFunctor.map f =
      PointedCGWH.SequentialSpectrum.OrderedLoop.functor.map (telescopeFunctor.map f) := rfl

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The actual original R after T has a genuine Omega image on every original input. -/
theorem reflection_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (reflectionFunctor.obj X).IsOmega := rTelescope_isOmega X

/-- Both unit integer-pi comparison directions retain the original T-Iso and R-Iso. -/
def reflectionUnitIntegerPiIso (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (integerStablePiFunctor q).obj X ≅ (integerStablePiFunctor q).obj (reflectionFunctor.obj X) :=
  telescopeUnitIntegerPiIso q X ≪≫ integerStablePiRUnitIso q (telescope X)

/-- The entire Iso hom is the actual integer-pi map of both original units. -/
theorem reflectionUnitIntegerPiIso_hom (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (reflectionUnitIntegerPiIso q X).hom = (integerStablePiFunctor q).map (reflectionUnit.app X) :=
  by
    change (telescopeUnitIntegerPiIso q X).hom ≫ (integerStablePiRUnitIso q (telescope X)).hom = _
    calc
      _ = (integerStablePiFunctor q).map
          (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X) ≫
          (integerStablePiFunctor q).map
            (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X)) :=
        congrArg₂ (fun a b => a ≫ b) (telescopeUnitIntegerPiIso_hom q X)
          (integerStablePiRUnitIso_hom q (telescope X))
      _ = (integerStablePiFunctor q).map
          (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X ≫
            PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X)) :=
        ((integerStablePiFunctor q).map_comp _ _).symm
      _ = _ := congrArg (fun f => (integerStablePiFunctor q).map f) (reflectionUnit_app X).symm

/-- The entire inverse retains the original R inverse followed by the original T inverse. -/
theorem reflectionUnitIntegerPiIso_inv (q : ℤ) (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    (reflectionUnitIntegerPiIso q X).inv =
      (integerStablePiRUnitIso q (telescope X)).inv ≫ (telescopeUnitIntegerPiIso q X).inv := rfl

/-- The whole unit integer-pi natural Iso retains every original input map. -/
def reflectionUnitIntegerPiNatIso (q : ℤ) : integerStablePiFunctor.{u, v} q ≅
    reflectionFunctor ⋙ integerStablePiFunctor q :=
  NatIso.ofComponents (fun X => reflectionUnitIntegerPiIso q X) (fun f => by
    rw [reflectionUnitIntegerPiIso_hom, reflectionUnitIntegerPiIso_hom]
    exact (Functor.whiskerRight reflectionUnit (integerStablePiFunctor q)).naturality f)

/-- The entire unit is a genuine pi-star equivalence in every original integer degree. -/
theorem reflectionUnit_integerPiStar (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    integerPiStarEquivalences (reflectionUnit.app X) := by
  apply (integerPiStarEquivalences_iff _).mpr
  intro q
  rw [← reflectionUnitIntegerPiIso_hom]
  exact (reflectionUnitIntegerPiIso q X).isIso_hom

/-- Both directions use the whole actual original unit natural Iso, on arbitrary endpoints. -/
theorem integerPiStar_iff_reflectionMap
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔ integerPiStarEquivalences (reflectionFunctor.map f) := by
  rw [integerPiStarEquivalences_iff, integerPiStarEquivalences_iff]
  exact forall_congr' (fun q => NatIso.isIso_map_iff (reflectionUnitIntegerPiNatIso q) f)

/-- Original integer tests detect level weakness of the actual original R-after-T map. -/
theorem integerPiStar_iff_reflectionLevelWeak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔
      weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (reflectionFunctor.map f) :=
  (integerPiStar_iff_reflectionMap f).trans
    (omegaMap_integerPiStar_iff_modelWeak (reflectionFunctor.map f)
      (reflection_isOmega X) (reflection_isOmega Y))

/-- The actual auxiliary functor preserves the same original native level weak class. -/
theorem reflection_preservesLevelWeak
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (reflectionFunctor.map f) :=
  (integerPiStar_iff_reflectionLevelWeak f).mp (levelWeak_le_integerPiStarEquivalences f hf)

/-- The original auxiliary unit is level weak on every actual original Omega input. -/
theorem reflectionUnit_levelWeak_of_isOmega (X : PointedCGWH.SequentialSpectrum.{u, v})
    (hX : X.IsOmega) : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
      (reflectionUnit.app X) :=
  (omegaMap_integerPiStar_iff_modelWeak (reflectionUnit.app X) hX (reflection_isOmega X)).mp
    (reflectionUnit_integerPiStar X)

/-- The actual unit at the original auxiliary image is level weak on every original input. -/
theorem reflectionUnit_atReflection_levelWeak (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
      (reflectionUnit.app (reflectionFunctor.obj X)) :=
  reflectionUnit_levelWeak_of_isOmega _ (reflection_isOmega X)

/-- The actual auxiliary image of its original unit is level weak on every original input. -/
theorem reflection_mapUnit_levelWeak (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}
      (reflectionFunctor.map (reflectionUnit.app X)) :=
  (integerPiStar_iff_reflectionLevelWeak _).mp (reflectionUnit_integerPiStar X)

/-- The original R/T unit has both full Hom functions in the original native level localization. -/
def reflectionUnitHoHomEquiv (X Z : PointedCGWH.SequentialSpectrum.{u, v}) (hZ : Z.IsOmega) :
    ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj (reflectionFunctor.obj X) ⟶
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) ≃
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X ⟶
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :=
  Functor.CoaugmentedLocalization.unitHomEquiv
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf =>
      reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflectionUnit_atReflection_levelWeak reflection_mapUnit_levelWeak
    X Z (reflectionUnit_levelWeak_of_isOmega Z hZ)

/-- The forward Hom function localizes both original unit maps. -/
theorem reflectionUnitHoHomEquiv_apply (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega)
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj
      (reflectionFunctor.obj X) ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    reflectionUnitHoHomEquiv X Z hZ g =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map (reflectionUnit.app X) ≫ g :=
  Functor.CoaugmentedLocalization.unitHomEquiv_apply
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf =>
      reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflectionUnit_atReflection_levelWeak reflection_mapUnit_levelWeak
    X Z (reflectionUnit_levelWeak_of_isOmega Z hZ) g

/-- Both actual image and iterated units give precisely the original Omega-target Hom tests. -/
theorem reflectionLevelWeak_iff_omegaHomTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} (reflectionFunctor.map f) ↔
      ∀ Z : PointedCGWH.SequentialSpectrum.{u, v}, Z.IsOmega → Function.Bijective
        (fun g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Y ⟶
            (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z =>
          (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫ g) :=
  (weakEquivalence_iff_isIso_toHomotopyCategory_map _).trans
    (Functor.CoaugmentedLocalization.map_isIso_iff_homtests
      (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
      (fun ⦃X Y⦄ f hf =>
      reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
      reflectionUnit_atReflection_levelWeak reflection_mapUnit_levelWeak
      (fun Z => Z.IsOmega) reflection_isOmega reflectionUnit_levelWeak_of_isOmega f)

/-- All original integer tests are exactly the original K-local Hom tests, on arbitrary arrows. -/
theorem integerPiStar_iff_originalLocalTests
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    integerPiStarEquivalences f ↔ localTestEquivalences f :=
  ((integerPiStar_iff_reflectionLevelWeak f).trans
    (reflectionLevelWeak_iff_omegaHomTests f)).trans
      (originalLocalTestEquivalence_iff_omegaTests f).symm

/-- The complete literal ordinary Omega-test predicate equals the original integer-pi predicate. -/
theorem omegaTestEquivalences_iff_integerPiStar
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    omegaTestEquivalences f ↔ integerPiStarEquivalences f :=
  (omegaTestEquivalences_iff_originalLocalTests f).trans
    (integerPiStar_iff_originalLocalTests f).symm

/-- Equality concerns every actual original arrow and all original integer degrees. -/
theorem omegaTestEquivalences_eq_integerPiStar :
    omegaTestEquivalences.{u, v} = integerPiStarEquivalences := by
  funext X Y f
  exact propext (omegaTestEquivalences_iff_integerPiStar f)

end PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry



namespace PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The entire original inverse acts on every native level-Ho morphism with the actual weak unit. -/
theorem reflectionUnitHoHomEquiv_symm_apply (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega)
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    (reflectionUnitHoHomEquiv X Z hZ).symm g =
      (Functor.CoaugmentedLocalization.localizedFunctor
        (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor
        (fun ⦃X Y⦄ f hf =>
          reflection_preservesLevelWeak (X := X) (Y := Y) f hf)).map g ≫
      (Localization.Construction.wIso (reflectionUnit.app Z)
        (reflectionUnit_levelWeak_of_isOmega Z hZ)).inv :=
  Functor.CoaugmentedLocalization.unitHomEquiv_symm_apply
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf =>
      reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflectionUnit_atReflection_levelWeak reflection_mapUnit_levelWeak
    X Z (reflectionUnit_levelWeak_of_isOmega Z hZ) g

/-- Original source maps retain both unit maps in forward Hom naturality. -/
theorem reflectionUnitHoHomEquiv_source
    {X X' : PointedCGWH.SequentialSpectrum.{u, v}} (f : X' ⟶ X)
    (Z : PointedCGWH.SequentialSpectrum.{u, v}) (hZ : Z.IsOmega)
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj
      (reflectionFunctor.obj X) ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    reflectionUnitHoHomEquiv X' Z hZ
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map
        (reflectionFunctor.map f) ≫ g) =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫
        reflectionUnitHoHomEquiv X Z hZ g :=
  Functor.CoaugmentedLocalization.unitHomEquiv_source
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf =>
      reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflectionUnit_atReflection_levelWeak reflection_mapUnit_levelWeak
    f Z (reflectionUnit_levelWeak_of_isOmega Z hZ) g

/-- Every original source Arrow retains the complete inverse Hom naturality. -/
theorem reflectionUnitHoHomEquiv_source_symm
    {X X' : PointedCGWH.SequentialSpectrum.{u, v}} (f : X' ⟶ X)
    (Z : PointedCGWH.SequentialSpectrum.{u, v}) (hZ : Z.IsOmega)
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    (reflectionUnitHoHomEquiv X' Z hZ).symm
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f ≫ g) =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map (reflectionFunctor.map f) ≫
        (reflectionUnitHoHomEquiv X Z hZ).symm g := by
  apply (reflectionUnitHoHomEquiv X' Z hZ).injective
  rw [Equiv.apply_symm_apply, reflectionUnitHoHomEquiv_source, Equiv.apply_symm_apply]

/-- Ordinary level-Ho target maps retain the full forward Hom function. -/
theorem reflectionUnitHoHomEquiv_target (X Z Z' : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega) (hZ' : Z'.IsOmega)
    (b : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z')
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj
      (reflectionFunctor.obj X) ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    reflectionUnitHoHomEquiv X Z' hZ' (g ≫ b) = reflectionUnitHoHomEquiv X Z hZ g ≫ b := by
  rw [reflectionUnitHoHomEquiv_apply, reflectionUnitHoHomEquiv_apply]
  exact (Category.assoc _ _ _).symm

/-- Every ordinary level-Ho target map retains the complete inverse Hom function. -/
theorem reflectionUnitHoHomEquiv_target_symm (X Z Z' : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega) (hZ' : Z'.IsOmega)
    (b : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z')
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    (reflectionUnitHoHomEquiv X Z' hZ').symm (g ≫ b) =
      (reflectionUnitHoHomEquiv X Z hZ).symm g ≫ b := by
  apply (reflectionUnitHoHomEquiv X Z' hZ').injective
  rw [Equiv.apply_symm_apply, reflectionUnitHoHomEquiv_target X Z Z' hZ hZ' b,
    Equiv.apply_symm_apply]

end PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry


namespace PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The literal original T followed by R descends to the actual native level homotopy category. -/
def reflectionHoFunctor : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v} ⥤
    HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v} :=
  Functor.CoaugmentedLocalization.localizedFunctor
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf)

/-- Both original unit maps descend to one natural transformation on every level-Ho arrow. -/
def reflectionHoUnit : 𝟭 (HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) ⟶
    reflectionHoFunctor :=
  Functor.CoaugmentedLocalization.localizedUnit
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf)

/-- Every descended object retains the actual original R(T(X)) object. -/
theorem reflectionHoFunctor_obj (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    reflectionHoFunctor.obj
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X) =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj (reflectionFunctor.obj X) :=
  Functor.CoaugmentedLocalization.localizedFunctor_obj
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf) X

/-- Every original input map retains its whole original T-map followed by its R-map in level-Ho. -/
theorem reflectionHoFunctor_map {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    reflectionHoFunctor.map
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map f) =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map (reflectionFunctor.map f) :=
  Functor.CoaugmentedLocalization.localizedFunctor_map
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf) f

/-- Every descended unit component is the original two-map unit in the same level localization. -/
theorem reflectionHoUnit_app (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    reflectionHoUnit.app
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X) =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map (reflectionUnit.app X) :=
  Functor.CoaugmentedLocalization.localizedUnit_app
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf) X

/-- The whole native level-Ho unit is the composite of both actual original unit maps. -/
theorem reflectionHoUnit_original_maps (X : PointedCGWH.SequentialSpectrum.{u, v}) :
    reflectionHoUnit.app
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X) =
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map
          (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X) ≫
        (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map
          (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app (telescope X)) := by
  exact (reflectionHoUnit_app X).trans
    ((congrArg (fun a =>
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map a)
      (reflectionUnit_app X)).trans
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map_comp _ _))

/-- Both maps of every original weak-map Iso are retained by the actual descended functor. -/
theorem reflectionHoFunctor_map_wIso {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    reflectionHoFunctor.mapIso (Localization.Construction.wIso f hf) =
      Localization.Construction.wIso (reflectionFunctor.map f)
        (reflection_preservesLevelWeak f hf) := by
  apply Iso.ext
  exact reflectionHoFunctor_map f

/-- Every original weak-map inverse retains the inverse of its actual original T-then-R map. -/
theorem reflectionHoFunctor_map_wIso_inv
    {X Y : PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences PointedCGWH.SequentialSpectrum.{u, v} f) :
    reflectionHoFunctor.map (Localization.Construction.wIso f hf).inv =
      (Localization.Construction.wIso (reflectionFunctor.map f)
        (reflection_preservesLevelWeak f hf)).inv :=
  congrArg (fun e => e.inv) (reflectionHoFunctor_map_wIso f hf)

/-- The derived original iterated-unit weakness gives its Iso at every ordinary level-Ho image. -/
theorem reflectionHoUnit_obj_isIso
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso (reflectionHoUnit.app (reflectionHoFunctor.obj X)) :=
  Functor.CoaugmentedLocalization.localizedUnit_obj_isIso
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflectionUnit_atReflection_levelWeak X

/-- The derived original mapped-unit weakness gives its Iso on every ordinary level-Ho object. -/
theorem reflectionHoFunctor_unit_isIso
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) :
    IsIso (reflectionHoFunctor.map (reflectionHoUnit.app X)) :=
  Functor.CoaugmentedLocalization.localizedFunctor_unit_isIso
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflection_mapUnit_levelWeak X

/-- Both genuine iterated units have the same entire map on every ordinary level-Ho object. -/
theorem reflectionHoFunctor_unit_eq
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) :
    reflectionHoFunctor.map (reflectionHoUnit.app X) =
      reflectionHoUnit.app (reflectionHoFunctor.obj X) :=
  Functor.CoaugmentedLocalization.localizedFunctor_unit_eq
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflectionUnit_atReflection_levelWeak reflection_mapUnit_levelWeak X

/-- The full test category uses precisely original Omega objects of the actual level-Ho carrier. -/
def omegaHoObjects : ObjectProperty (HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) :=
  fun Z => Z.as.obj.IsOmega

/-- Every object of the actual descended functor is a genuine original Omega object. -/
theorem reflectionHoFunctor_isOmega
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) :
    omegaHoObjects (reflectionHoFunctor.obj X) := by
  rcases X with ⟨⟨X⟩⟩
  exact reflection_isOmega X

/-- Every original Omega object has its original unit inverted in the native level-Ho. -/
theorem reflectionHoUnit_isIso_of_isOmega
    (Z : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) (hZ : omegaHoObjects Z) :
    IsIso (reflectionHoUnit.app Z) := by
  rcases Z with ⟨⟨Z⟩⟩
  change IsIso (reflectionHoUnit.app
    ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z))
  rw [reflectionHoUnit_app]
  exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp
    (reflectionUnit_levelWeak_of_isOmega Z hZ)

/-- The canonical full-subcategory lift keeps the entire actual descended T-then-R functor. -/
def reflectionOmegaHoFunctor : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v} ⥤
    omegaHoObjects.FullSubcategory :=
  Functor.CoaugmentedReflection.testFunctor reflectionHoFunctor omegaHoObjects
    reflectionHoFunctor_isOmega

/-- The full Omega test-object unit Iso keeps both original unit maps and their actual inverse. -/
def reflectionOmegaHoUnitIso (Z : omegaHoObjects.FullSubcategory) :
    Z.obj ≅ reflectionHoFunctor.obj Z.obj :=
  Functor.CoaugmentedReflection.testUnitIso reflectionHoFunctor reflectionHoUnit omegaHoObjects
    reflectionHoUnit_isIso_of_isOmega Z

/-- The complete native Omega Hom functions are the actual descended functor and original unit. -/
def reflectionOmegaHoHomEquiv
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v})
    (Z : omegaHoObjects.FullSubcategory) :
    (reflectionOmegaHoFunctor.obj X ⟶ Z) ≃ (X ⟶ Z.obj) :=
  Functor.CoaugmentedReflection.testHomEquiv reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega X Z

/-- Every full-category forward input is precomposed with the same whole original unit. -/
theorem reflectionOmegaHoHomEquiv_apply
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v})
    (Z : omegaHoObjects.FullSubcategory) (g : reflectionOmegaHoFunctor.obj X ⟶ Z) :
    reflectionOmegaHoHomEquiv X Z g = reflectionHoUnit.app X ≫ g.hom := rfl

/-- Every full-category inverse input uses the whole actual level-Ho functor and unit inverse. -/
theorem reflectionOmegaHoHomEquiv_symm_apply
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v})
    (Z : omegaHoObjects.FullSubcategory) (f : X ⟶ Z.obj) :
    ((reflectionOmegaHoHomEquiv X Z).symm f).hom =
      reflectionHoFunctor.map f ≫ (reflectionOmegaHoUnitIso Z).inv := rfl

/-- Both derived iterated units and the actual Omega image give the native Omega adjunction. -/
def reflectionOmegaHoAdjunction : reflectionOmegaHoFunctor.{u, v} ⊣ omegaHoObjects.ι :=
  Functor.CoaugmentedReflection.testAdjunction reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega

/-- The entire native adjunction Hom equivalence retains the complete original Hom functions. -/
theorem reflectionOmegaHoAdjunction_homEquiv
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v})
    (Z : omegaHoObjects.FullSubcategory) :
    reflectionOmegaHoAdjunction.homEquiv X Z = reflectionOmegaHoHomEquiv X Z :=
  Functor.CoaugmentedReflection.testAdjunction_homEquiv reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega X Z

/-- The entire native full-category Hom equivalence equals the original ordinary-Ho equivalence. -/
theorem reflectionOmegaHoHomEquiv_original (X : PointedCGWH.SequentialSpectrum.{u, v})
    (Z : omegaHoObjects.FullSubcategory) :
    reflectionOmegaHoHomEquiv
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X) Z =
      (omegaHoObjects.fullyFaithfulι.homEquiv
        (X := reflectionOmegaHoFunctor.obj
          ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X)) (Y := Z)).trans
        (reflectionUnitHoHomEquiv X Z.obj.as.obj Z.property) := by
  apply Equiv.ext
  intro g
  exact (congrArg (fun a => a ≫ g.hom) (reflectionHoUnit_app X)).trans
    (reflectionUnitHoHomEquiv_apply X Z.obj.as.obj Z.property g.hom).symm

/-- Each native adjunction unit component is the same actual descended original two-map unit. -/
theorem reflectionOmegaHoAdjunction_unit_app
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) :
    reflectionOmegaHoAdjunction.unit.app X = reflectionHoUnit.app X :=
  Functor.CoaugmentedReflection.testAdjunction_unit_app reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega X

/-- The whole native adjunction unit transformation is the original descended unit. -/
theorem reflectionOmegaHoAdjunction_unit :
    reflectionOmegaHoAdjunction.{u, v}.unit = reflectionHoUnit := by
  apply NatTrans.ext
  funext X
  exact reflectionOmegaHoAdjunction_unit_app X

/-- Every native counit component retains the inverse of the same original Omega-object unit. -/
theorem reflectionOmegaHoAdjunction_counit_app (Z : omegaHoObjects.FullSubcategory) :
    (reflectionOmegaHoAdjunction.counit.app Z).hom = (reflectionOmegaHoUnitIso Z).inv :=
  Functor.CoaugmentedReflection.testAdjunction_counit_app reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega Z

/-- The full native left triangle uses the whole original level-Ho unit and actual counit. -/
theorem reflectionOmegaHoAdjunction_left_triangle
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}) :
    reflectionOmegaHoFunctor.map (reflectionHoUnit.app X) ≫
      reflectionOmegaHoAdjunction.counit.app (reflectionOmegaHoFunctor.obj X) =
        𝟙 (reflectionOmegaHoFunctor.obj X) :=
  Functor.CoaugmentedReflection.testAdjunction_left_triangle reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega X

/-- The full native right triangle uses the same original Omega-object unit and actual counit. -/
theorem reflectionOmegaHoAdjunction_right_triangle (Z : omegaHoObjects.FullSubcategory) :
    reflectionHoUnit.app Z.obj ≫ (reflectionOmegaHoAdjunction.counit.app Z).hom = 𝟙 Z.obj :=
  Functor.CoaugmentedReflection.testAdjunction_right_triangle reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega Z

/-- Ordinary level-Ho arrows inverted after T-then-R have exactly the original Omega Hom tests. -/
theorem reflectionHoMap_isIso_iff_omegaHomTests
    {X Y : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}} (f : X ⟶ Y) :
    IsIso (reflectionHoFunctor.map f) ↔
      ∀ Z, omegaHoObjects Z → Function.Bijective (fun g : Y ⟶ Z => f ≫ g) :=
  Functor.CoaugmentedReflection.map_isIso_iff_fixed_homtests reflectionHoFunctor reflectionHoUnit
    reflectionHoUnit_obj_isIso reflectionHoFunctor_unit_isIso omegaHoObjects
    reflectionHoFunctor_isOmega reflectionHoUnit_isIso_of_isOmega f

/-- Arbitrary ordinary level-Ho source maps retain the entire native Omega forward Hom function. -/
theorem reflectionOmegaHoHomEquiv_source
    {X X' : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}} (a : X' ⟶ X)
    (Z : omegaHoObjects.FullSubcategory) (g : reflectionOmegaHoFunctor.obj X ⟶ Z) :
    reflectionOmegaHoHomEquiv X' Z (reflectionOmegaHoFunctor.map a ≫ g) =
      a ≫ reflectionOmegaHoHomEquiv X Z g := by
  change reflectionHoUnit.app X' ≫ (reflectionHoFunctor.map a ≫ g.hom) =
    a ≫ (reflectionHoUnit.app X ≫ g.hom)
  have h : a ≫ reflectionHoUnit.app X =
      reflectionHoUnit.app X' ≫ reflectionHoFunctor.map a := reflectionHoUnit.naturality a
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun b => b ≫ g.hom) h.symm).trans (Category.assoc _ _ _))

/-- Arbitrary ordinary level-Ho source maps retain the entire native Omega inverse Hom function. -/
theorem reflectionOmegaHoHomEquiv_source_symm
    {X X' : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}} (a : X' ⟶ X)
    (Z : omegaHoObjects.FullSubcategory) (f : X ⟶ Z.obj) :
    (reflectionOmegaHoHomEquiv X' Z).symm (a ≫ f) =
      reflectionOmegaHoFunctor.map a ≫ (reflectionOmegaHoHomEquiv X Z).symm f := by
  apply (reflectionOmegaHoHomEquiv X' Z).injective
  exact ((reflectionOmegaHoHomEquiv X' Z).apply_symm_apply (a ≫ f)).trans
    ((congrArg (fun b => a ≫ b)
      ((reflectionOmegaHoHomEquiv X Z).apply_symm_apply f).symm).trans
      (reflectionOmegaHoHomEquiv_source a Z ((reflectionOmegaHoHomEquiv X Z).symm f)).symm)

/-- Arbitrary Omega target level-Ho maps retain the entire native forward Hom function. -/
theorem reflectionOmegaHoHomEquiv_target
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v})
    {Z Z' : omegaHoObjects.FullSubcategory} (b : Z ⟶ Z')
    (g : reflectionOmegaHoFunctor.obj X ⟶ Z) :
    reflectionOmegaHoHomEquiv X Z' (g ≫ b) = reflectionOmegaHoHomEquiv X Z g ≫ b.hom := by
  change reflectionHoUnit.app X ≫ (g.hom ≫ b.hom) =
    (reflectionHoUnit.app X ≫ g.hom) ≫ b.hom
  exact (Category.assoc _ _ _).symm

/-- Arbitrary Omega target level-Ho maps retain the entire native inverse Hom function. -/
theorem reflectionOmegaHoHomEquiv_target_symm
    (X : HomotopyCategory PointedCGWH.SequentialSpectrum.{u, v})
    {Z Z' : omegaHoObjects.FullSubcategory} (b : Z ⟶ Z') (f : X ⟶ Z.obj) :
    (reflectionOmegaHoHomEquiv X Z').symm (f ≫ b.hom) =
      (reflectionOmegaHoHomEquiv X Z).symm f ≫ b := by
  apply (reflectionOmegaHoHomEquiv X Z').injective
  exact ((reflectionOmegaHoHomEquiv X Z').apply_symm_apply (f ≫ b.hom)).trans
    ((congrArg (fun a => a ≫ b.hom)
      ((reflectionOmegaHoHomEquiv X Z).apply_symm_apply f).symm).trans
      (reflectionOmegaHoHomEquiv_target X b ((reflectionOmegaHoHomEquiv X Z).symm f)).symm)

/-- The full original inverse is uniquely characterized by its composite with the original unit. -/
theorem reflectionUnitHoHomEquiv_characteristic (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega)
    (f : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z)
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj
      (reflectionFunctor.obj X) ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    (reflectionUnitHoHomEquiv X Z hZ).symm f = g ↔
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map
        (reflectionUnit.app X) ≫ g = f :=
  Functor.CoaugmentedLocalization.unitHomEquiv_characteristic
    (weakEquivalences PointedCGWH.SequentialSpectrum.{u, v}) reflectionFunctor reflectionUnit
    (fun ⦃X Y⦄ f hf => reflection_preservesLevelWeak (X := X) (Y := Y) f hf)
    reflectionUnit_atReflection_levelWeak reflection_mapUnit_levelWeak X Z
    (reflectionUnit_levelWeak_of_isOmega Z hZ) f g

/-- The original two-map unit followed by the whole inverse Hom function is the original arrow. -/
theorem reflectionUnitHoHomEquiv_right_triangle (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega)
    (f : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj X ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map (reflectionUnit.app X) ≫
      (reflectionUnitHoHomEquiv X Z hZ).symm f = f :=
  (reflectionUnitHoHomEquiv_apply X Z hZ
    ((reflectionUnitHoHomEquiv X Z hZ).symm f)).symm.trans
    ((reflectionUnitHoHomEquiv X Z hZ).apply_symm_apply f)

/-- The complete inverse Hom function returns every whole original forward Hom input. -/
theorem reflectionUnitHoHomEquiv_left_triangle (X Z : PointedCGWH.SequentialSpectrum.{u, v})
    (hZ : Z.IsOmega)
    (g : (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj
      (reflectionFunctor.obj X) ⟶
      (toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).obj Z) :
    (reflectionUnitHoHomEquiv X Z hZ).symm
      ((toHomotopyCategory PointedCGWH.SequentialSpectrum.{u, v}).map (reflectionUnit.app X) ≫ g) =
        g :=
  (congrArg (reflectionUnitHoHomEquiv X Z hZ).symm
    (reflectionUnitHoHomEquiv_apply X Z hZ g).symm).trans
    ((reflectionUnitHoHomEquiv X Z hZ).symm_apply_apply g)

end PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry


/-!
## The original native Q/K and R-after-T reflectors on the same Omega category

The original generator equality transports the actual zero-arrow predicate.
Both derived adjunctions then use the same full subcategory of the original
native level homotopy category. Left-adjoint uniqueness compares the complete
functors and their original units and counits. The integer-pi detector is used
only on the original sequential carrier.
-/

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK
open HomotopicalAlgebra.EnrichedProjective.Native.Diagrams
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStablePiGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerOmegaRecognitionGeometry
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev family : NativeStabilizationFamily.{u, v}
    (CategoryTheory.Spectra.Sequential.Index PointedCGWH.sphereOne.{u, v}) ℕ :=
  PointedCGWH.SequentialSpectrum.StabilizationKAdapter.family.{u, v}
private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev H := toHomotopyCategory Carrier.{u, v}
private abbrev Ho := HomotopyCategory Carrier.{u, v}
private abbrev originalOmegaHoProperty : ObjectProperty Ho.{u, v} :=
  PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry.omegaHoObjects.{u, v}

/-- The entire two full-subcategory predicates concern the same original level-Ho objects. -/
theorem omegaObjectProperties_eq :
    omegaHoObjectProperty family = originalOmegaHoProperty := by
  funext X
  apply propext
  change NativeK.IsOmega family X.as.obj ↔ PointedCGWH.SequentialSpectrum.IsOmega X.as.obj
  exact PointedCGWH.SequentialSpectrum.StableK.nativeOmega_iff_isOmega X.as.obj

/-- The actual original Q/K image lies in the original R-after-T Omega subcategory. -/
theorem nativeQK_image_originalOmega (X : Ho.{u, v}) :
    originalOmegaHoProperty ((localReplacementHo family).obj X) := by
  rw [← omegaObjectProperties_eq]
  exact omegaHoObjectProperty_image family X

/-- The original Q-inverse/K-unit is inverted at every actual original Omega object. -/
theorem nativeQK_unit_originalOmega
    (X : Ho.{u, v}) (hX : originalOmegaHoProperty X) :
    IsIso ((localReplacementHoUnit family).app X) := by
  apply omegaHoObjectProperty_unit_isIso family X
  rwa [omegaObjectProperties_eq]

/-- Retargeting the existing native reflector keeps its original whole object and map functions. -/
def nativeQKOriginalOmegaFunctor : Ho.{u, v} ⥤ originalOmegaHoProperty.FullSubcategory :=
  Functor.CoaugmentedReflection.testFunctor (localReplacementHo family)
    originalOmegaHoProperty nativeQK_image_originalOmega

/-- Both original adjunctions now have the same actual full inclusion as right adjoint. -/
def nativeQKOriginalOmegaAdjunction :
    nativeQKOriginalOmegaFunctor.{u, v} ⊣ originalOmegaHoProperty.ι :=
  Functor.CoaugmentedReflection.testAdjunction (localReplacementHo family)
    (localReplacementHoUnit family) (localReplacementHoUnit_isIso_at_image family)
    (localReplacementHo_mapUnit_isIso family) originalOmegaHoProperty
    nativeQK_image_originalOmega nativeQK_unit_originalOmega

/-- The entire actual native Q/K unit is retained after retargeting the full subcategory. -/
theorem nativeQKOriginalOmegaAdjunction_unit :
    nativeQKOriginalOmegaAdjunction.{u, v}.unit = localReplacementHoUnit family := by
  apply NatTrans.ext
  funext X
  exact Functor.CoaugmentedReflection.testAdjunction_unit_app
    (localReplacementHo family) (localReplacementHoUnit family)
    (localReplacementHoUnit_isIso_at_image family) (localReplacementHo_mapUnit_isIso family)
    originalOmegaHoProperty nativeQK_image_originalOmega nativeQK_unit_originalOmega X

/-- The two complete original Omega reflectors are canonically isomorphic over the same
inclusion. -/
def nativeQKRTFullSubcategoryIso :
    nativeQKOriginalOmegaFunctor.{u, v} ≅ reflectionOmegaHoFunctor :=
  Adjunction.leftAdjointUniq nativeQKOriginalOmegaAdjunction reflectionOmegaHoAdjunction

/-- The complete comparison on the original ordinary level-Ho carrier retains both map functions. -/
def nativeQKRTHoIso : localReplacementHo family ≅ reflectionHoFunctor.{u, v} :=
  Functor.isoWhiskerRight nativeQKRTFullSubcategoryIso originalOmegaHoProperty.ι

/-- The whole ordinary-Ho forward map is the actual full inclusion of the full comparison. -/
theorem nativeQKRTHoIso_wholeHom :
    nativeQKRTHoIso.{u, v}.hom =
      Functor.whiskerRight nativeQKRTFullSubcategoryIso.hom originalOmegaHoProperty.ι := rfl

/-- The whole ordinary-Ho inverse map is the actual full inclusion of the inverse comparison. -/
theorem nativeQKRTHoIso_wholeInv :
    nativeQKRTHoIso.{u, v}.inv =
      Functor.whiskerRight nativeQKRTFullSubcategoryIso.inv originalOmegaHoProperty.ι := rfl

/-- The full ordinary-Ho comparison uses the same full-inclusion map on every original input. -/
theorem nativeQKRTHoIso_hom_app (X : Ho.{u, v}) :
    nativeQKRTHoIso.hom.app X = (nativeQKRTFullSubcategoryIso.hom.app X).hom := rfl

/-- The full ordinary-Ho inverse uses the same full-inclusion inverse on every original input. -/
theorem nativeQKRTHoIso_inv_app (X : Ho.{u, v}) :
    nativeQKRTHoIso.inv.app X = (nativeQKRTFullSubcategoryIso.inv.app X).hom := rfl

/-- Every original ordinary-Ho source arrow retains the whole naturality square. -/
theorem nativeQKRTHoIso_naturality {X Y : Ho.{u, v}} (f : X ⟶ Y) :
    (localReplacementHo family).map f ≫ nativeQKRTHoIso.hom.app Y =
      nativeQKRTHoIso.hom.app X ≫ reflectionHoFunctor.map f :=
  nativeQKRTHoIso.hom.naturality f

/-- The whole original Q-inverse/K-unit followed by the comparison is the original T-then-R unit. -/
theorem nativeQKRTHoIso_wholeUnit :
    localReplacementHoUnit family ≫ nativeQKRTHoIso.hom = reflectionHoUnit.{u, v} := by
  apply NatTrans.ext
  funext X
  rw [NatTrans.comp_app, nativeQKRTHoIso_hom_app]
  have h := congrArg (fun η => η.app X)
    (Adjunction.unit_leftAdjointUniq_hom
      nativeQKOriginalOmegaAdjunction reflectionOmegaHoAdjunction)
  change nativeQKOriginalOmegaAdjunction.unit.app X ≫
      (nativeQKRTFullSubcategoryIso.hom.app X).hom =
    reflectionOmegaHoAdjunction.unit.app X at h
  rwa [nativeQKOriginalOmegaAdjunction_unit, reflectionOmegaHoAdjunction_unit] at h

/-- Both complete original counits commute with the full-subcategory comparison. -/
theorem nativeQKRTFullSubcategoryIso_wholeCounit :
    Functor.whiskerLeft originalOmegaHoProperty.ι nativeQKRTFullSubcategoryIso.hom ≫
      reflectionOmegaHoAdjunction.counit = nativeQKOriginalOmegaAdjunction.{u, v}.counit :=
  Adjunction.leftAdjointUniq_hom_counit
    nativeQKOriginalOmegaAdjunction reflectionOmegaHoAdjunction

/-- On every original input, the unit comparison keeps both literal original R/T unit maps. -/
theorem nativeQKRTHoIso_unit_originalMaps (X : Carrier.{u, v}) :
    (localReplacementHoUnit family).app (H.obj X) ≫ nativeQKRTHoIso.hom.app (H.obj X) =
      H.map (PointedCGWH.SequentialSpectrum.MappingTelescope.unit.app X) ≫
        H.map (PointedCGWH.SequentialSpectrum.OrderedLoop.unit.app
          (PointedCGWH.SequentialSpectrum.MappingTelescope.telescope X)) := by
  exact (congrArg (fun η => η.app (H.obj X)) nativeQKRTHoIso_wholeUnit).trans
    (reflectionHoUnit_original_maps X)

/-- The complete original Q/K map is level weak precisely when the original R-after-T map is. -/
theorem nativeQKMap_weak_iff_RTMap_weak {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Carrier.{u, v} ((cofibrantLocalReplacement family).map f) ↔
      weakEquivalences Carrier.{u, v} (reflectionFunctor.map f) := by
  have hK : weakEquivalences Carrier.{u, v} ((cofibrantLocalReplacement family).map f) ↔
      IsIso ((localReplacementHo family).map (H.map f)) := by
    rw [localReplacementHo_map_projected]
    exact weakEquivalence_iff_isIso_toHomotopyCategory_map _
  have hRT : IsIso (reflectionHoFunctor.map (H.map f)) ↔
      weakEquivalences Carrier.{u, v} (reflectionFunctor.map f) := by
    rw [reflectionHoFunctor_map]
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).symm
  exact hK.trans ((NatIso.isIso_map_iff nativeQKRTHoIso (H.map f)).trans hRT)

/-- On every original sequential arrow, the actual original Q/K map detects all integer degrees. -/
theorem nativeQKMap_weak_iff_originalIntegerPiStar
    {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Carrier.{u, v} ((cofibrantLocalReplacement family).map f) ↔
      integerPiStarEquivalences f :=
  (nativeQKMap_weak_iff_RTMap_weak f).trans (integerPiStar_iff_reflectionLevelWeak f).symm

/-- The actual original Q-inverse/K-unit is invertible exactly at original Omega inputs. -/
theorem nativeQKHoUnit_isIso_iff_originalOmega (X : Carrier.{u, v}) :
    IsIso ((localReplacementHoUnit family).app (H.obj X)) ↔ X.IsOmega :=
  (localReplacementHoUnit_isIso_iff_isOmega_projected family X).trans
    (PointedCGWH.SequentialSpectrum.StableK.nativeOmega_iff_isOmega X)

end PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The target-unit Iso retains the entire original native Q-inverse/K-unit comparison. -/
def nativeQKOriginalOmegaUnitIso (Z : originalOmegaHoProperty.FullSubcategory) :
    Z.obj ≅ (localReplacementHo family).obj Z.obj :=
  Functor.CoaugmentedReflection.testUnitIso (localReplacementHo family)
    (localReplacementHoUnit family) originalOmegaHoProperty nativeQK_unit_originalOmega Z

/-- Both full Hom functions use the original native functor and original lifted comparison. -/
def nativeQKOriginalOmegaHomEquiv (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) :
    (nativeQKOriginalOmegaFunctor.obj X ⟶ Z) ≃ (X ⟶ Z.obj) :=
  Functor.CoaugmentedReflection.testHomEquiv (localReplacementHo family)
    (localReplacementHoUnit family) (localReplacementHoUnit_isIso_at_image family)
    (localReplacementHo_mapUnit_isIso family) originalOmegaHoProperty
    nativeQK_image_originalOmega nativeQK_unit_originalOmega X Z

/-- The entire retargeted adjunction keeps the whole original native Hom equivalence. -/
theorem nativeQKOriginalOmegaAdjunction_homEquiv (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) :
    nativeQKOriginalOmegaAdjunction.homEquiv X Z = nativeQKOriginalOmegaHomEquiv X Z :=
  Functor.CoaugmentedReflection.testAdjunction_homEquiv (localReplacementHo family)
    (localReplacementHoUnit family) (localReplacementHoUnit_isIso_at_image family)
    (localReplacementHo_mapUnit_isIso family) originalOmegaHoProperty
    nativeQK_image_originalOmega nativeQK_unit_originalOmega X Z

/-- Every forward input is precomposed with the same complete original Q-inverse/K-unit. -/
theorem nativeQKOriginalOmegaHomEquiv_apply (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (g : nativeQKOriginalOmegaFunctor.obj X ⟶ Z) :
    nativeQKOriginalOmegaHomEquiv X Z g = (localReplacementHoUnit family).app X ≫ g.hom := rfl

/-- Every inverse input uses the entire original Q/K map and its original target-unit inverse. -/
theorem nativeQKOriginalOmegaHomEquiv_symm_apply (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (f : X ⟶ Z.obj) :
    ((nativeQKOriginalOmegaHomEquiv X Z).symm f).hom =
      (localReplacementHo family).map f ≫ (nativeQKOriginalOmegaUnitIso Z).inv := rfl

/-- The complete native forward Hom function is retained at every ordinary-Ho source. -/
theorem nativeQKOriginalOmegaHomEquiv_wholeForward (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) :
    (nativeQKOriginalOmegaHomEquiv X Z).toFun =
      fun g => (localReplacementHoUnit family).app X ≫ g.hom := rfl

/-- The complete native inverse Hom function is retained at every ordinary-Ho source. -/
theorem nativeQKOriginalOmegaHomEquiv_wholeInverse (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) :
    (fun f => ((nativeQKOriginalOmegaHomEquiv X Z).symm f).hom) =
      fun f => (localReplacementHo family).map f ≫ (nativeQKOriginalOmegaUnitIso Z).inv := rfl

/-- Arbitrary ordinary-Ho source maps preserve the entire original native forward function. -/
theorem nativeQKOriginalOmegaHomEquiv_source {X X' : Ho.{u, v}} (a : X' ⟶ X)
    (Z : originalOmegaHoProperty.FullSubcategory) (g : nativeQKOriginalOmegaFunctor.obj X ⟶ Z) :
    nativeQKOriginalOmegaHomEquiv X' Z (nativeQKOriginalOmegaFunctor.map a ≫ g) =
      a ≫ nativeQKOriginalOmegaHomEquiv X Z g := by
  simpa only [nativeQKOriginalOmegaAdjunction_homEquiv] using
    nativeQKOriginalOmegaAdjunction.homEquiv_naturality_left a g

/-- Arbitrary ordinary-Ho source maps preserve the entire original native inverse function. -/
theorem nativeQKOriginalOmegaHomEquiv_source_symm {X X' : Ho.{u, v}} (a : X' ⟶ X)
    (Z : originalOmegaHoProperty.FullSubcategory) (f : X ⟶ Z.obj) :
    (nativeQKOriginalOmegaHomEquiv X' Z).symm (a ≫ f) =
      nativeQKOriginalOmegaFunctor.map a ≫ (nativeQKOriginalOmegaHomEquiv X Z).symm f := by
  simpa only [nativeQKOriginalOmegaAdjunction_homEquiv] using
    nativeQKOriginalOmegaAdjunction.homEquiv_naturality_left_symm a f

/-- Arbitrary original Omega target maps preserve the full native forward Hom function. -/
theorem nativeQKOriginalOmegaHomEquiv_target (X : Ho.{u, v})
    {Z Z' : originalOmegaHoProperty.FullSubcategory} (b : Z ⟶ Z')
    (g : nativeQKOriginalOmegaFunctor.obj X ⟶ Z) :
    nativeQKOriginalOmegaHomEquiv X Z' (g ≫ b) =
      nativeQKOriginalOmegaHomEquiv X Z g ≫ b.hom := by
  simpa only [nativeQKOriginalOmegaAdjunction_homEquiv, ObjectProperty.ι_obj,
    ObjectProperty.ι_map] using
    nativeQKOriginalOmegaAdjunction.homEquiv_naturality_right g b

/-- Arbitrary original Omega target maps preserve the full native inverse Hom function. -/
theorem nativeQKOriginalOmegaHomEquiv_target_symm (X : Ho.{u, v})
    {Z Z' : originalOmegaHoProperty.FullSubcategory} (b : Z ⟶ Z') (f : X ⟶ Z.obj) :
    (nativeQKOriginalOmegaHomEquiv X Z').symm (f ≫ b.hom) =
      (nativeQKOriginalOmegaHomEquiv X Z).symm f ≫ b := by
  simpa only [nativeQKOriginalOmegaAdjunction_homEquiv, ObjectProperty.ι_obj,
    ObjectProperty.ι_map] using
    nativeQKOriginalOmegaAdjunction.homEquiv_naturality_right_symm f b

/-- The original lifted native unit followed by the full inverse returns every input arrow. -/
theorem nativeQKOriginalOmegaHomEquiv_right_triangle (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (f : X ⟶ Z.obj) :
    (localReplacementHoUnit family).app X ≫
      ((nativeQKOriginalOmegaHomEquiv X Z).symm f).hom = f :=
  (nativeQKOriginalOmegaHomEquiv X Z).apply_symm_apply f

/-- The full inverse returns every whole original forward native Hom input. -/
theorem nativeQKOriginalOmegaHomEquiv_left_triangle (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (g : nativeQKOriginalOmegaFunctor.obj X ⟶ Z) :
    (nativeQKOriginalOmegaHomEquiv X Z).symm
      ((localReplacementHoUnit family).app X ≫ g.hom) = g :=
  (nativeQKOriginalOmegaHomEquiv X Z).symm_apply_apply g

/-- The whole inverse is uniquely characterized by its composite with the actual native unit. -/
theorem nativeQKOriginalOmegaHomEquiv_characteristic (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (f : X ⟶ Z.obj)
    (g : nativeQKOriginalOmegaFunctor.obj X ⟶ Z) :
    (nativeQKOriginalOmegaHomEquiv X Z).symm f = g ↔
      (localReplacementHoUnit family).app X ≫ g.hom = f := by
  constructor
  · intro h
    rw [← h]
    exact nativeQKOriginalOmegaHomEquiv_right_triangle X Z f
  · intro h
    exact (congrArg (nativeQKOriginalOmegaHomEquiv X Z).symm h.symm).trans
      ((nativeQKOriginalOmegaHomEquiv X Z).symm_apply_apply g)

/-- The retargeted counit retains the same entire original inverse target-unit function. -/
theorem nativeQKOriginalOmegaAdjunction_counit_app
    (Z : originalOmegaHoProperty.FullSubcategory) :
    (nativeQKOriginalOmegaAdjunction.counit.app Z).hom = (nativeQKOriginalOmegaUnitIso Z).inv :=
  Functor.CoaugmentedReflection.testAdjunction_counit_app (localReplacementHo family)
    (localReplacementHoUnit family) (localReplacementHoUnit_isIso_at_image family)
    (localReplacementHo_mapUnit_isIso family) originalOmegaHoProperty
    nativeQK_image_originalOmega nativeQK_unit_originalOmega Z

/-- Both original native adjunction triangles survive retargeting to the same Omega inclusion. -/
theorem nativeQKOriginalOmegaAdjunction_wholeTriangles :
    ((fun X : Ho.{u, v} => nativeQKOriginalOmegaFunctor.map
      (nativeQKOriginalOmegaAdjunction.unit.app X) ≫
        nativeQKOriginalOmegaAdjunction.counit.app (nativeQKOriginalOmegaFunctor.obj X)) =
      fun X : Ho.{u, v} => 𝟙 (nativeQKOriginalOmegaFunctor.obj X)) ∧
    ((fun Z : originalOmegaHoProperty.FullSubcategory =>
      nativeQKOriginalOmegaAdjunction.unit.app Z.obj ≫
      originalOmegaHoProperty.ι.map (nativeQKOriginalOmegaAdjunction.counit.app Z)) =
        fun Z : originalOmegaHoProperty.FullSubcategory => 𝟙 Z.obj) := by
  constructor
  · funext X
    exact nativeQKOriginalOmegaAdjunction.left_triangle_components X
  · funext Z
    exact nativeQKOriginalOmegaAdjunction.right_triangle_components Z

/-- The comparison preserves both complete reflected Hom functions through its actual two maps. -/
def nativeQKRTReflectedHomEquiv (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) :
    (nativeQKOriginalOmegaFunctor.obj X ⟶ Z) ≃ (reflectionOmegaHoFunctor.obj X ⟶ Z) :=
  Iso.homCongr (nativeQKRTFullSubcategoryIso.app X) (Iso.refl Z)

/-- The full original Q/K-to-R/T forward Hom comparison uses its actual inverse Iso map. -/
theorem nativeQKRTReflectedHomEquiv_apply (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (g : nativeQKOriginalOmegaFunctor.obj X ⟶ Z) :
    nativeQKRTReflectedHomEquiv X Z g = nativeQKRTFullSubcategoryIso.inv.app X ≫ g := by
  simp only [nativeQKRTReflectedHomEquiv, Iso.homCongr_apply, Iso.refl_hom, Iso.app_inv,
    Category.comp_id]

/-- The full original R/T-to-Q/K inverse Hom comparison uses its actual forward Iso map. -/
theorem nativeQKRTReflectedHomEquiv_symm_apply (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (g : reflectionOmegaHoFunctor.obj X ⟶ Z) :
    (nativeQKRTReflectedHomEquiv X Z).symm g = nativeQKRTFullSubcategoryIso.hom.app X ≫ g := by
  change (nativeQKRTFullSubcategoryIso.app X).hom ≫ g ≫ 𝟙 Z =
    nativeQKRTFullSubcategoryIso.hom.app X ≫ g
  rw [Category.comp_id, Iso.app_hom]

/-- Both complete original reflector Hom functions commute with the same whole unit comparison. -/
theorem nativeQKRTReflectedHomEquiv_compatibility (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (g : nativeQKOriginalOmegaFunctor.obj X ⟶ Z) :
    nativeQKOriginalOmegaHomEquiv X Z g =
      reflectionOmegaHoHomEquiv X Z (nativeQKRTReflectedHomEquiv X Z g) := by
  rw [← nativeQKOriginalOmegaAdjunction_homEquiv,
    nativeQKRTReflectedHomEquiv_apply, ← reflectionOmegaHoAdjunction_homEquiv]
  rw [Adjunction.homEquiv_naturality_right]
  rw [nativeQKRTFullSubcategoryIso, Adjunction.leftAdjointUniq_inv_app,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_unit]

/-- The entire original native Hom equivalence equals the original R/T equivalence after
comparison. -/
theorem nativeQKOriginalOmegaHomEquiv_RT_original (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) :
    nativeQKOriginalOmegaHomEquiv X Z =
      (nativeQKRTReflectedHomEquiv X Z).trans (reflectionOmegaHoHomEquiv X Z) := by
  apply Equiv.ext
  exact nativeQKRTReflectedHomEquiv_compatibility X Z

/-- Both full inverse reflector Hom functions are retained by the same inverse comparison. -/
theorem nativeQKRTReflectedHomEquiv_inverse_compatibility (X : Ho.{u, v})
    (Z : originalOmegaHoProperty.FullSubcategory) (f : X ⟶ Z.obj) :
    (nativeQKRTReflectedHomEquiv X Z).symm ((reflectionOmegaHoHomEquiv X Z).symm f) =
      (nativeQKOriginalOmegaHomEquiv X Z).symm f := by
  apply (nativeQKOriginalOmegaHomEquiv X Z).injective
  rw [nativeQKRTReflectedHomEquiv_compatibility, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Every original native local-test arrow retains exactly all original integer degree tests. -/
theorem nativeLocalTests_iff_originalIntegerPiStar {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    localTestEquivalences family f ↔ integerPiStarEquivalences f :=
  (cofibrantLocalReplacement_map_weak_iff family f).symm.trans
    (nativeQKMap_weak_iff_originalIntegerPiStar f)

/-- Equality retains every actual original source arrow, class argument and integer degree. -/
theorem nativeLocalTestEquivalences_eq_originalIntegerPiStar :
    localTestEquivalences family = integerPiStarEquivalences.{u, v} := by
  funext X Y f
  exact propext (nativeLocalTests_iff_originalIntegerPiStar f)

/-- The entire native local-test class gives the original ordinary-Ho Omega tests on every
source. -/
theorem nativeLocalTests_iff_originalOmegaHomTests {X Y : Carrier.{u, v}} (f : X ⟶ Y) :
    localTestEquivalences family f ↔
      ∀ Z : Carrier.{u, v}, Z.IsOmega → Function.Bijective
        (fun g : H.obj Y ⟶ H.obj Z => H.map f ≫ g) :=
  (nativeLocalTests_iff_originalIntegerPiStar f).trans
    ((integerPiStar_iff_reflectionLevelWeak f).trans (reflectionLevelWeak_iff_omegaHomTests f))

end PointedCGWH.SequentialSpectrum.MappingTelescope.NativeKRTComparisonGeometry
