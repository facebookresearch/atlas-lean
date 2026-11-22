/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.LevelIntegerStableLocalization
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# The original integer localization adjunction

The actual Ω equivalence and original Ω-reflection Hom functions give
an adjunction from original level homotopy to integer localization.
Its full Hom functions retain the equivalence inverse, original RT unit,
original Ω-unit inverse and every source and target naturality. The unit
is the original RT unit and the counit is an actual isomorphism.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open PointedCGWH.SequentialSpectrum.MappingTelescope.RTReflectionGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableLocalizationGeometry
open PointedCGWH.SequentialSpectrum.MappingTelescope.LevelIntegerStableLocalizationGeometry
open scoped CGWH.modelCategory

namespace PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableAdjunctionGeometry

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

private abbrev Carrier := PointedCGWH.SequentialSpectrum.{u, v}
private abbrev Ho := HomotopyCategory Carrier.{u, v}

/-- The right functor retains the actual Ω equivalence and its original level-Ho inclusion. -/
def integerStableToLevelHo : IntegerStableHomotopyCategory.{u, v} ⥤ Ho.{u, v} :=
  integerStableOmegaEquivalence.functor ⋙ omegaHoObjects.ι

/-- Every right-functor map is the complete actual Ω-equivalence map in the level category. -/
theorem integerStableToLevelHo_map {X Y : IntegerStableHomotopyCategory.{u, v}} (f : X ⟶ Y) :
    integerStableToLevelHo.map f = (integerStableOmegaEquivalence.functor.map f).hom := rfl

/-- The entire composite is the original descended RT functor on all objects and all maps. -/
theorem integerStableAdjunction_originalFunctor :
    levelToIntegerStableHo.{u, v} ⋙ integerStableToLevelHo = reflectionHoFunctor :=
  congrArg (fun F => F ⋙ omegaHoObjects.ι) levelToIntegerStableHo_omegaFunctor

/-- The actual Ω equivalence retains every original reflected source map. -/
theorem integerStableOmegaEquivalence_map_level {X Y : Ho.{u, v}} (a : X ⟶ Y) :
    integerStableOmegaEquivalence.functor.map (levelToIntegerStableHo.map a) =
      reflectionOmegaHoFunctor.map a := by
  have h := Functor.congr_hom levelToIntegerStableHo_omegaFunctor a
  change integerStableOmegaEquivalence.functor.map (levelToIntegerStableHo.map a) =
    (𝟙 (reflectionOmegaHoFunctor.obj X)) ≫ reflectionOmegaHoFunctor.map a ≫
      (𝟙 (reflectionOmegaHoFunctor.obj Y)) at h
  simpa only [Category.id_comp, Category.comp_id] using h

/-- The full Hom equivalence is constructed from the actual Ω equivalence and original RT Hom. -/
def integerStableLevelHomEquiv (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) :
    (levelToIntegerStableHo.obj X ⟶ Y) ≃ (X ⟶ integerStableToLevelHo.obj Y) :=
  integerStableOmegaEquivalence.fullyFaithfulFunctor.homEquiv.trans
    (reflectionOmegaHoHomEquiv X (integerStableOmegaEquivalence.functor.obj Y))

/-- The whole forward Hom function precomposes with the same original RT unit. -/
theorem integerStableLevelHomEquiv_apply (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) (f : levelToIntegerStableHo.obj X ⟶ Y) :
    integerStableLevelHomEquiv X Y f =
      reflectionHoUnit.app X ≫ (integerStableOmegaEquivalence.functor.map f).hom := rfl

/-- The full inverse retains both equivalence-unit maps and the original inverse RT Hom function. -/
theorem integerStableLevelHomEquiv_symm_apply (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) (g : X ⟶ integerStableToLevelHo.obj Y) :
    (integerStableLevelHomEquiv X Y).symm g =
      integerStableOmegaEquivalence.unitIso.hom.app (levelToIntegerStableHo.obj X) ≫
        integerStableOmegaEquivalence.inverse.map
          ((reflectionOmegaHoHomEquiv X (integerStableOmegaEquivalence.functor.obj Y)).symm g) ≫
        integerStableOmegaEquivalence.unitIso.inv.app Y := rfl

/-- The exact functor identity types the original RT unit over the integer right functor. -/
def integerStableTypedLevelUnit : 𝟭 Ho.{u, v} ⟶
    levelToIntegerStableHo ⋙ integerStableToLevelHo :=
  reflectionHoUnit ≫ (eqToIso integerStableAdjunction_originalFunctor).inv

/-- Each typed unit component is the same original RT component. -/
theorem integerStableTypedLevelUnit_app (X : Ho.{u, v}) :
    integerStableTypedLevelUnit.app X = reflectionHoUnit.app X := by
  have h : (eqToIso integerStableAdjunction_originalFunctor).inv.app X =
      𝟙 (reflectionHoFunctor.obj X) := by
    rw [eqToIso.inv, eqToHom_app]
    exact eqToHom_refl _ _
  exact (congrArg (fun g => reflectionHoUnit.app X ≫ g) h).trans (Category.comp_id _)

/-- The complete Hom function retains the original unit with its exact composite-functor type. -/
theorem integerStableLevelHomEquiv_apply_typedUnit (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) (f : levelToIntegerStableHo.obj X ⟶ Y) :
    integerStableLevelHomEquiv X Y f =
      integerStableTypedLevelUnit.app X ≫ integerStableToLevelHo.map f :=
  (integerStableLevelHomEquiv_apply X Y f).trans
    (congrArg (fun g : X ⟶ integerStableToLevelHo.obj (levelToIntegerStableHo.obj X) =>
      g ≫ integerStableToLevelHo.map f) (integerStableTypedLevelUnit_app X).symm)

/-- Original level-Ho source arrows retain the complete forward Hom naturality. -/
theorem integerStableLevelHomEquiv_source {X X' : Ho.{u, v}} (a : X' ⟶ X)
    (Y : IntegerStableHomotopyCategory.{u, v}) (f : levelToIntegerStableHo.obj X ⟶ Y) :
    integerStableLevelHomEquiv X' Y (levelToIntegerStableHo.map a ≫ f) =
      a ≫ integerStableLevelHomEquiv X Y f := by
  let R : IntegerStableHomotopyCategory.{u, v} ⥤ Ho.{u, v} := integerStableToLevelHo
  let U : 𝟭 Ho.{u, v} ⟶ levelToIntegerStableHo ⋙ R := integerStableTypedLevelUnit
  have h : U.app X' ≫ R.map (levelToIntegerStableHo.map a ≫ f) =
      a ≫ (U.app X ≫ R.map f) :=
    (congrArg (fun g => U.app X' ≫ g) (R.map_comp (levelToIntegerStableHo.map a) f)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun g => g ≫ R.map f) (U.naturality a).symm).trans
          (Category.assoc _ _ _)))
  exact (integerStableLevelHomEquiv_apply_typedUnit X' Y
      (levelToIntegerStableHo.map a ≫ f)).trans
    (h.trans (congrArg (fun g => a ≫ g)
      (integerStableLevelHomEquiv_apply_typedUnit X Y f).symm))

/-- Original level-Ho source arrows retain the complete inverse Hom naturality. -/
theorem integerStableLevelHomEquiv_source_symm {X X' : Ho.{u, v}} (a : X' ⟶ X)
    (Y : IntegerStableHomotopyCategory.{u, v}) (g : X ⟶ integerStableToLevelHo.obj Y) :
    (integerStableLevelHomEquiv X' Y).symm (a ≫ g) =
      levelToIntegerStableHo.map a ≫ (integerStableLevelHomEquiv X Y).symm g := by
  apply (integerStableLevelHomEquiv X' Y).injective
  rw [Equiv.apply_symm_apply, integerStableLevelHomEquiv_source, Equiv.apply_symm_apply]

/-- Original integer-localization target arrows retain the complete forward Hom naturality. -/
theorem integerStableLevelHomEquiv_target (X : Ho.{u, v})
    {Y Y' : IntegerStableHomotopyCategory.{u, v}} (b : Y ⟶ Y')
    (f : levelToIntegerStableHo.obj X ⟶ Y) :
    integerStableLevelHomEquiv X Y' (f ≫ b) =
      integerStableLevelHomEquiv X Y f ≫ integerStableToLevelHo.map b := by
  let R : IntegerStableHomotopyCategory.{u, v} ⥤ Ho.{u, v} := integerStableToLevelHo
  let U : 𝟭 Ho.{u, v} ⟶ levelToIntegerStableHo ⋙ R := integerStableTypedLevelUnit
  have h : U.app X ≫ R.map (f ≫ b) = (U.app X ≫ R.map f) ≫ R.map b :=
    (congrArg (fun g => U.app X ≫ g) (R.map_comp f b)).trans (Category.assoc _ _ _).symm
  exact (integerStableLevelHomEquiv_apply_typedUnit X Y' (f ≫ b)).trans
    (h.trans (congrArg (fun g => g ≫ R.map b)
      (integerStableLevelHomEquiv_apply_typedUnit X Y f).symm))

/-- Original integer-localization target arrows retain the complete inverse Hom naturality. -/
theorem integerStableLevelHomEquiv_target_symm (X : Ho.{u, v})
    {Y Y' : IntegerStableHomotopyCategory.{u, v}} (b : Y ⟶ Y')
    (g : X ⟶ integerStableToLevelHo.obj Y) :
    (integerStableLevelHomEquiv X Y').symm (g ≫ integerStableToLevelHo.map b) =
      (integerStableLevelHomEquiv X Y).symm g ≫ b := by
  apply (integerStableLevelHomEquiv X Y').injective
  rw [Equiv.apply_symm_apply, integerStableLevelHomEquiv_target, Equiv.apply_symm_apply]

/-- Every original forward Hom input is returned by the complete inverse function. -/
theorem integerStableLevelHomEquiv_left_triangle (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) (f : levelToIntegerStableHo.obj X ⟶ Y) :
    (integerStableLevelHomEquiv X Y).symm (integerStableLevelHomEquiv X Y f) = f :=
  (integerStableLevelHomEquiv X Y).symm_apply_apply f

/-- Every original inverse Hom input is returned by the complete forward function. -/
theorem integerStableLevelHomEquiv_right_triangle (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) (g : X ⟶ integerStableToLevelHo.obj Y) :
    integerStableLevelHomEquiv X Y ((integerStableLevelHomEquiv X Y).symm g) = g :=
  (integerStableLevelHomEquiv X Y).apply_symm_apply g

/-- The full inverse is characterized by precomposition with the original RT unit. -/
theorem integerStableLevelHomEquiv_characteristic (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) (g : X ⟶ integerStableToLevelHo.obj Y)
    (f : levelToIntegerStableHo.obj X ⟶ Y) :
    (integerStableLevelHomEquiv X Y).symm g = f ↔
      reflectionHoUnit.app X ≫ (integerStableOmegaEquivalence.functor.map f).hom = g := by
  constructor
  · intro h
    rw [← h]
    exact integerStableLevelHomEquiv_right_triangle X Y g
  · intro h
    exact (congrArg (integerStableLevelHomEquiv X Y).symm h.symm).trans
      ((integerStableLevelHomEquiv X Y).symm_apply_apply f)

/-- The constructed original Hom equivalence gives the entire level-to-integer adjunction. -/
def integerStableLevelAdjunction : levelToIntegerStableHo.{u, v} ⊣ integerStableToLevelHo :=
  Adjunction.mkOfHomEquiv {
    homEquiv := integerStableLevelHomEquiv
    homEquiv_naturality_left_symm := fun a g => integerStableLevelHomEquiv_source_symm a _ g
    homEquiv_naturality_right := fun f b => integerStableLevelHomEquiv_target _ b f }

/-- The actual adjunction retains the full original forward and inverse Hom functions. -/
theorem integerStableLevelAdjunction_homEquiv (X : Ho.{u, v})
    (Y : IntegerStableHomotopyCategory.{u, v}) :
    integerStableLevelAdjunction.homEquiv X Y = integerStableLevelHomEquiv X Y :=
  congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) X) Y

/-- Each actual adjunction unit is the same original descended two-map RT unit. -/
theorem integerStableLevelAdjunction_unit_app (X : Ho.{u, v}) :
    integerStableLevelAdjunction.unit.app X = reflectionHoUnit.app X := by
  change integerStableLevelHomEquiv X (levelToIntegerStableHo.obj X)
      (𝟙 (levelToIntegerStableHo.obj X)) = _
  rw [integerStableLevelHomEquiv_apply]
  have h : (integerStableOmegaEquivalence.functor.map
      (𝟙 (levelToIntegerStableHo.obj X))).hom = 𝟙 (reflectionHoFunctor.obj X) :=
    congrArg (fun f : integerStableOmegaEquivalence.functor.obj (levelToIntegerStableHo.obj X) ⟶
        integerStableOmegaEquivalence.functor.obj (levelToIntegerStableHo.obj X) => f.hom)
      (integerStableOmegaEquivalence.functor.map_id (levelToIntegerStableHo.obj X))
  exact (congrArg (fun f : reflectionHoFunctor.obj X ⟶ reflectionHoFunctor.obj X =>
      reflectionHoUnit.app X ≫ f) h).trans (Category.comp_id _)

/-- The entire adjunction unit retains the original RT unit after its exact functor identity. -/
theorem integerStableLevelAdjunction_originalUnit :
    integerStableLevelAdjunction.{u, v}.unit ≫
      (eqToIso integerStableAdjunction_originalFunctor).hom = reflectionHoUnit := by
  apply NatTrans.ext
  funext X
  have h : (eqToIso integerStableAdjunction_originalFunctor).hom.app X =
      𝟙 (reflectionHoFunctor.obj X) := by
    rw [eqToIso.hom, eqToHom_app]
    exact eqToHom_refl _ _
  exact (congrArg (fun g => integerStableLevelAdjunction.unit.app X ≫ g) h).trans
    ((Category.comp_id _).trans (integerStableLevelAdjunction_unit_app X))

/-- Each actual counit retains the complete original inverse Hom function at the identity input. -/
theorem integerStableLevelAdjunction_counit_app
    (Y : IntegerStableHomotopyCategory.{u, v}) :
    integerStableLevelAdjunction.counit.app Y =
      (integerStableLevelHomEquiv (integerStableToLevelHo.obj Y) Y).symm
        (𝟙 (integerStableToLevelHo.obj Y)) := rfl

/-- The counit preserves the actual inverse Ω-Hom and both equivalence-unit functions. -/
theorem integerStableLevelAdjunction_counit_originalFunctions
    (Y : IntegerStableHomotopyCategory.{u, v}) :
    integerStableLevelAdjunction.counit.app Y =
      integerStableOmegaEquivalence.unitIso.hom.app
          (levelToIntegerStableHo.obj (integerStableToLevelHo.obj Y)) ≫
        integerStableOmegaEquivalence.inverse.map
          ((reflectionOmegaHoHomEquiv (integerStableToLevelHo.obj Y)
            (integerStableOmegaEquivalence.functor.obj Y)).symm
              (𝟙 (integerStableToLevelHo.obj Y))) ≫
        integerStableOmegaEquivalence.unitIso.inv.app Y :=
  integerStableLevelHomEquiv_symm_apply _ _ _

/-- The original left triangle holds with the actual constructed unit and counit. -/
theorem integerStableLevelAdjunction_left_triangle (X : Ho.{u, v}) :
    levelToIntegerStableHo.map (integerStableLevelAdjunction.unit.app X) ≫
      integerStableLevelAdjunction.counit.app (levelToIntegerStableHo.obj X) =
        𝟙 (levelToIntegerStableHo.obj X) :=
  integerStableLevelAdjunction.left_triangle_components X

/-- The original right triangle holds with the actual constructed unit and counit. -/
theorem integerStableLevelAdjunction_right_triangle
    (Y : IntegerStableHomotopyCategory.{u, v}) :
    integerStableLevelAdjunction.unit.app (integerStableToLevelHo.obj Y) ≫
      integerStableToLevelHo.map (integerStableLevelAdjunction.counit.app Y) =
        𝟙 (integerStableToLevelHo.obj Y) :=
  integerStableLevelAdjunction.right_triangle_components Y

/-- The actual right functor is fully faithful through the Ω equivalence and full inclusion. -/
theorem integerStableToLevelHo_full : integerStableToLevelHo.{u, v}.Full := by
  unfold integerStableToLevelHo
  infer_instance

/-- The actual right functor is faithful through the Ω equivalence and full inclusion. -/
theorem integerStableToLevelHo_faithful : integerStableToLevelHo.{u, v}.Faithful := by
  unfold integerStableToLevelHo
  infer_instance

/-- Every constructed counit is an actual isomorphism of the original integer localization. -/
theorem integerStableLevelAdjunction_counit_isIso
    (Y : IntegerStableHomotopyCategory.{u, v}) :
    IsIso (integerStableLevelAdjunction.counit.app Y) := by
  let _ := integerStableToLevelHo_full
  let _ := integerStableToLevelHo_faithful
  infer_instance

/-- Both counit-isomorphism functions retain the same original constructed counit. -/
def integerStableLevelCounitIso (Y : IntegerStableHomotopyCategory.{u, v}) :
    levelToIntegerStableHo.obj (integerStableToLevelHo.obj Y) ≅ Y := by
  let _ := integerStableLevelAdjunction_counit_isIso Y
  exact asIso (integerStableLevelAdjunction.counit.app Y)

/-- The complete counit-isomorphism forward function is the original constructed counit. -/
theorem integerStableLevelCounitIso_hom (Y : IntegerStableHomotopyCategory.{u, v}) :
    (integerStableLevelCounitIso Y).hom = integerStableLevelAdjunction.counit.app Y := rfl

end PointedCGWH.SequentialSpectrum.MappingTelescope.IntegerStableAdjunctionGeometry
