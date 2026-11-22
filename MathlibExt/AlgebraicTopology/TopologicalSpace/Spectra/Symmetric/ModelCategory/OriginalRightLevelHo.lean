/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativePresentation.ReplacementHoComparison
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.RightModules
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.StandardRightMigration
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Symmetric.ModelCategory.RightFactorization
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.CanonicalProjectiveModels
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.ConstructionHomotopyComparison

/-!
# Actual original symmetric RIGHT zero, original replacements and level Ho

Use the accepted whole standard-RIGHT sphere-module carrier and its actual
operator equivalence. Both original standard and converted-left free classes
retain their distinct interfaces. Original κ/I/J/Z/i/p/fac and all natural
replacement comparisons remain the given data. D_R and R26 remain separate.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.modelCategory CGWH.limits MonoidalClosed ZeroObject

namespace PointedCGWH.Spectra.Symmetric.RightPresentationModel.LevelHomotopy

attribute [local instance] PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
theorem zero_isZero : IsZero ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Zero.object
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})) :=
  NativePresentation.Zero.isZero (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] Native.modelCategory

theorem hoCategory_eq_model :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) = HomotopyCategory
      (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) := rfl

theorem projection_eq_model :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) = toHomotopyCategory
      (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) := rfl

theorem toNativeHo_projection :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor =
      (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙ toHomotopyCategory
      (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}) :=
  NativePresentation.LevelHo.forward_projection
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem fromNativeHo_projection :
    toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse =
      (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse
      ⋙ (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  NativePresentation.LevelHo.inverse_projection
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem toNativeHo_map_projected {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶
  Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor.map f) :=
  NativePresentation.LevelHo.forward_map_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem fromNativeHo_map_projected {X Y : PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse).map
      ((toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map f) =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map
        ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse.map f) :=
  NativePresentation.LevelHo.inverse_map_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem unitIso_hom_projected (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).hom.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map
      ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso.hom.app X) :=
  NativePresentation.LevelHo.unitIso_hom_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem unitIso_inv_projected (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).inv.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map
      ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso.inv.app X) :=
  NativePresentation.LevelHo.unitIso_inv_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem counitIso_hom_projected (X : PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).hom.app
      ((toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso.hom.app X) :=
  NativePresentation.LevelHo.counitIso_hom_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem counitIso_inv_projected (X : PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).inv.app
      ((toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso.inv.app X) :=
  NativePresentation.LevelHo.counitIso_inv_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem unitIso_naturality {X Y : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    f ≫ ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).hom.app Y =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).hom.app X ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse).map f :=
  NativePresentation.LevelHo.unitIso_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem counitIso_naturality
    {X Y : HomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).hom.app Y =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).hom.app X ≫ f :=
  NativePresentation.LevelHo.counitIso_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem toNativeHo_triangle :
    Functor.whiskerRight ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).hom
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor) ≫
      Functor.whiskerLeft ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor)
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).hom = 𝟙
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor) :=
  NativePresentation.LevelHo.forward_unit_counit
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem fromNativeHo_triangle :
    Functor.whiskerLeft ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse)
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).hom ≫
      Functor.whiskerRight ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).hom
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse) = 𝟙
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse) :=
  NativePresentation.LevelHo.inverse_unit_counit
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

/-- The whole source Q is the frozen original source I data on its actual source zero arrows. -/
theorem cofibrantReplacement_eq_original_data :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      NativePresentation.Zero.fromZeroArrow
      (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z := rfl

/-- The whole source R is the same frozen original source J data on its actual arrows to zero. -/
theorem fibrantReplacement_eq_original_data :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      NativePresentation.Zero.toZeroArrow
      (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z := rfl

theorem cofibrantReplacement_map_original_data
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map
      ((NativePresentation.Zero.fromZeroArrow
        (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f) := rfl

theorem fibrantReplacement_map_original_data
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).Z.map
      ((NativePresentation.Zero.toZeroArrow
        (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f) := rfl

theorem cofibrantReplacement_fac (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.initialToCofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementCounit
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X =
      NativePresentation.Zero.toObject (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u,
        v}) X :=
  NativePresentation.Replacement.cofibrantReplacement_fac
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem fibrantReplacement_fac (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementUnit
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementToZero
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X =
      NativePresentation.Zero.fromObject
        (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X :=
  NativePresentation.Replacement.fibrantReplacement_fac
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem cofibrantReplacement_classes (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    cofibrations (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.initialToCofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X) ∧
      trivialFibrations (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementCounit
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X) :=
  NativePresentation.Replacement.cofibrantReplacement_classes
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem fibrantReplacement_classes (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialCofibrations (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementUnit
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X) ∧
      fibrations (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementToZero
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X) :=
  NativePresentation.Replacement.fibrantReplacement_classes
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem isCofibrant_cofibrantReplacement (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    IsCofibrant (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) :=
  NativePresentation.Replacement.isCofibrant_cofibrantReplacement
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem isFibrant_fibrantReplacement (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    IsFibrant (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) :=
  NativePresentation.Replacement.isFibrant_fibrantReplacement
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

/-- The complete original replacement action commutes strictly with its source projection. -/
theorem cofibrantReplacementHo_projection :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  NativePresentation.Replacement.cofibrantReplacementHo_projection
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem cofibrantReplacementHoComparisonIso_hom_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.cofibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X) :=
  NativePresentation.Replacement.cofibrantReplacementHoComparisonIso_hom_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem cofibrantReplacementHoComparisonIso_naturality
    {X Y : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app Y =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X ≫
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
          Native.Replacement.cofibrantReplacementHo
          (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map f :=
  NativePresentation.Replacement.cofibrantReplacementHoComparisonIso_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

/-- The complete original replacement action commutes strictly with its source projection. -/
theorem fibrantReplacementHo_projection :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
      :=
  NativePresentation.Replacement.fibrantReplacementHo_projection
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem fibrantReplacementHoComparisonIso_hom_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.fibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X) :=
  NativePresentation.Replacement.fibrantReplacementHoComparisonIso_hom_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem fibrantReplacementHoComparisonIso_naturality
    {X Y : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app Y =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X ≫
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
          Native.Replacement.fibrantReplacementHo
          (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map f :=
  NativePresentation.Replacement.fibrantReplacementHoComparisonIso_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    f

/-- The complete original replacement action commutes strictly with its source projection. -/
theorem cofibrantFibrantReplacementHo_projection :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  NativePresentation.Replacement.cofibrantFibrantReplacementHo_projection
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem cofibrantFibrantReplacementHoComparisonIso_hom_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.cofibrantFibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X) :=
  NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso_hom_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem cofibrantFibrantReplacementHoComparisonIso_naturality
    {X Y : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f ≫
      ((NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app Y =
      ((NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X ≫
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
          Native.Replacement.cofibrantFibrantReplacementHo
          (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map f :=
  NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

/-- The complete original replacement action commutes strictly with its source projection. -/
theorem fibrantCofibrantReplacementHo_projection :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) =
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) :=
  NativePresentation.Replacement.fibrantCofibrantReplacementHo_projection
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})

theorem fibrantCofibrantReplacementHoComparisonIso_hom_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.fibrantCofibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X) :=
  NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso_hom_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem fibrantCofibrantReplacementHoComparisonIso_naturality
    {X Y : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacementHo
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f ≫
      ((NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app Y =
      ((NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app X ≫
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
          Native.Replacement.fibrantCofibrantReplacementHo
          (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map f :=
  NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem isBifibrant_cofibrantFibrantReplacement (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u,
  v}) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    IsCofibrant (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) ∧ IsFibrant
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacement
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) :=
  ⟨NativePresentation.Replacement.isCofibrant_cofibrantFibrantReplacement
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X,
    NativePresentation.Replacement.isFibrant_cofibrantFibrantReplacement
      (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X⟩

theorem isBifibrant_fibrantCofibrantReplacement (X : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u,
  v}) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    IsCofibrant (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) ∧ IsFibrant
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacement
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) :=
  ⟨NativePresentation.Replacement.isCofibrant_fibrantCofibrantReplacement
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X,
    NativePresentation.Replacement.isFibrant_fibrantCofibrantReplacement
      (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X⟩

/-- The source π is retained literally through the actual source/native Ho equivalence. -/
theorem cofibrantReplacementHoComparisonIso_p_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) ≫
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        (Native.Replacement.cofibrantReplacementCounit.app
          ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor.obj X)) =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementCounit
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X))
        :=
  NativePresentation.Replacement.cofibrantReplacementHoComparisonIso_p_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

/-- The source ι is retained literally through that same actual equivalence. -/
theorem fibrantReplacementHoComparisonIso_i_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementUnit
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).app X)) ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).hom.app
        (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
        (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
          (Native.Replacement.fibrantReplacementUnit.app
            ((PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor.obj X)) :=
  NativePresentation.Replacement.fibrantReplacementHoComparisonIso_i_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    X

/-- The entire original source I first natural arrow is retained. -/
theorem initialToCofibrantReplacement_eq_original_i :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.initialToCofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) = Functor.whiskerLeft
      (NativePresentation.Zero.fromZeroArrow
        (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}))
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i := rfl

/-- Retain the entire original source I second natural arrow. -/
theorem cofibrantReplacementCounit_eq_original_p :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementCounit
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) = Functor.whiskerLeft
      (NativePresentation.Zero.fromZeroArrow
        (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}))
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.cofibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p := rfl

/-- Retain the entire original source J first natural arrow. -/
theorem fibrantReplacementUnit_eq_original_i :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementUnit
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) = Functor.whiskerLeft
      (NativePresentation.Zero.toZeroArrow
        (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}))
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).i := rfl

/-- Retain the entire original source J second natural arrow. -/
theorem fibrantReplacementToZero_eq_original_p :
    (HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementToZero
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) = Functor.whiskerLeft
      (NativePresentation.Zero.toZeroArrow
        (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}))
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.fibrantFactorizationData
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).p := rfl

/-- This actual source replacement reflects exactly the constructed original source weak class. -/
theorem cofibrantReplacement_map_weakEquivalence_iff
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f) ↔
      weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) f :=
  NativePresentation.Replacement.cofibrantReplacement_map_weakEquivalence_iff
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    f

/-- This actual source replacement reflects exactly the constructed original source weak class. -/
theorem fibrantReplacement_map_weakEquivalence_iff
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f) ↔
      weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) f :=
  NativePresentation.Replacement.fibrantReplacement_map_weakEquivalence_iff
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

/-- This actual source replacement reflects exactly the constructed original source weak class. -/
theorem cofibrantFibrantReplacement_map_weakEquivalence_iff
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f) ↔
      weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) f :=
  NativePresentation.Replacement.cofibrantFibrantReplacement_map_weakEquivalence_iff
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

/-- This actual source replacement reflects exactly the constructed original source weak class. -/
theorem fibrantCofibrantReplacement_map_weakEquivalence_iff
    {X Y : PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}} (f : X ⟶ Y) :
    letI : ModelCategory (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v})
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacement
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).map f) ↔
      weakEquivalences (PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) f :=
  NativePresentation.Replacement.fibrantCofibrantReplacement_map_weakEquivalence_iff
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem unitIso_inv_naturality {X Y : (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse).map f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).inv.app Y =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).unitIso).inv.app X ≫ f :=
  NativePresentation.LevelHo.unitIso_inv_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem counitIso_inv_naturality {X Y : HomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})} (f : X ⟶ Y) :
    f ≫ ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).inv.app Y =
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).counitIso).inv.app X ≫
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).inverse ⋙
        (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f :=
  NativePresentation.LevelHo.counitIso_inv_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem cofibrantReplacementHoComparisonIso_inv_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.cofibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X) :=
  NativePresentation.Replacement.cofibrantReplacementHoComparisonIso_inv_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem cofibrantReplacementHoComparisonIso_inv_naturality {X Y :
  (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
      Native.Replacement.cofibrantReplacementHo (B := B) (A :=
      PointedCGWH.SymmetricOperatorIndex.{u, v})).map f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app Y =
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHoComparisonIso
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X ≫
          ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantReplacementHo
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
          (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f :=
  NativePresentation.Replacement.cofibrantReplacementHoComparisonIso_inv_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem fibrantReplacementHoComparisonIso_inv_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.fibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X) :=
  NativePresentation.Replacement.fibrantReplacementHoComparisonIso_inv_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem fibrantReplacementHoComparisonIso_inv_naturality {X Y :
  (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶ Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
      Native.Replacement.fibrantReplacementHo (B := B) (A :=
      PointedCGWH.SymmetricOperatorIndex.{u, v})).map f ≫
      ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app Y =
        ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHoComparisonIso
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X ≫
          ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantReplacementHo
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
          (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f :=
  NativePresentation.Replacement.fibrantReplacementHoComparisonIso_inv_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem cofibrantFibrantReplacementHoComparisonIso_inv_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.cofibrantFibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X) :=
  NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso_inv_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem cofibrantFibrantReplacementHoComparisonIso_inv_naturality {X Y :
  (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶
  Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
      Native.Replacement.cofibrantFibrantReplacementHo (B := B) (A :=
      PointedCGWH.SymmetricOperatorIndex.{u, v})).map f ≫
      ((NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app Y =
        ((NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X ≫
          ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.cofibrantFibrantReplacementHo
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
            (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f :=
  NativePresentation.Replacement.cofibrantFibrantReplacementHoComparisonIso_inv_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f

theorem fibrantCofibrantReplacementHoComparisonIso_inv_projected (X :
  PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v}) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app
      (((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.projection
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).obj X) =
      (toHomotopyCategory (PointedCGWH.Spectra.Symmetric.Spectrum.{u, v})).map
        ((NativePresentation.Replacement.fibrantCofibrantReplacementComparisonIso
          (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X) :=
  NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso_inv_projected
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) X

theorem fibrantCofibrantReplacementHoComparisonIso_inv_naturality {X Y :
  (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.HoCategory
  PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})} (f : X ⟶
  Y) :
    ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor ⋙
      Native.Replacement.fibrantCofibrantReplacementHo (B := B) (A :=
      PointedCGWH.SymmetricOperatorIndex.{u, v})).map f ≫
      ((NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso
        PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app Y =
        ((NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso
          PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})).inv.app X ≫
          ((HomotopicalAlgebra.EnrichedProjective.NativePresentation.Replacement.fibrantCofibrantReplacementHo
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) ⋙
            (HomotopicalAlgebra.EnrichedProjective.NativePresentation.LevelHo.equivalence
            PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}).functor).map f :=
  NativePresentation.Replacement.fibrantCofibrantReplacementHoComparisonIso_inv_naturality
    (PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}) f


/-- The full actual right-coend diagram weak class is evaluated through the original native diagram
equivalence. -/
theorem weakEquivalences_eq :
    letI : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    weakEquivalences PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = (weakEquivalences
      PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).inverseImage
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor := rfl

/-- Its complete cofibration class is the original native I class transported by the actual full
action. -/
theorem cofibrations_eq :
    letI : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    cofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = (cofibrations
      PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).inverseImage
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor := rfl

theorem fibrations_eq :
    letI : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    fibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = (fibrations
      PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).inverseImage
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor
      := rfl

theorem trivialFibrations_eq :
    letI : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialFibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = (trivialFibrations
      PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).inverseImage
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor := rfl

theorem trivialCofibrations_eq :
    letI : ModelCategory PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} :=
      (HomotopicalAlgebra.EnrichedProjective.NativePresentation.modelCategory
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v})
    trivialCofibrations PointedCGWH.SymmetricRightModulePresentation.RightSphereModule.{u, v} = (trivialCofibrations
      PointedCGWH.Spectra.Symmetric.Spectrum.{u, v}).inverseImage
      PointedCGWH.SymmetricRightModulePresentation.rightModuleOperatorEquivalence.{u, v}.functor := rfl


end PointedCGWH.Spectra.Symmetric.RightPresentationModel.LevelHomotopy

namespace PointedCGWH.Spectra.Symmetric.LevelHomotopy

open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalOpposite

attribute [local instance] PointedCGWH.Spectra.Symmetric.levelModel
  PointedCGWH.originalSymmetricSequenceMonoidal
  PointedCGWH.originalSymmetricSequenceBraided PointedCGWH.originalSymmetricSequenceSymmetric
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal
  PointedCGWH.sphereSequenceMonObj PointedCGWH.sphereSequenceIsCommMonObj
  MonoidalLeftAction.monoidalOppositeLeftAction


/-- The actual canonical native zero diagram. -/
abbrev zero : Spectrum.{u, v} := Native.Diagrams.zeroDiagram (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

theorem zero_isZero : IsZero zero.{u, v} := Native.Diagrams.zeroDiagram_isZero (A :=
  PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The localization of the named canonical spectrum model. -/
abbrev HoCategory := @HomotopyCategory Spectrum.{u, v} inferInstance levelModel.{u, v}

/-- The actual canonical weak-class quotient projection. -/
abbrev projection : Spectrum.{u, v} ⥤ HoCategory.{u, v} :=
  @toHomotopyCategory Spectrum.{u, v} inferInstance levelModel.{u, v}

/-- The original I algorithm on every actual native zero-to-object arrow. -/
def cofibrantReplacement : Spectrum.{u, v} ⥤ Spectrum.{u, v} :=
  Native.Diagrams.fromZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) ⋙
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z

/-- The original J algorithm on every actual native object-to-zero arrow. -/
def fibrantReplacement : Spectrum.{u, v} ⥤ Spectrum.{u, v} :=
  Native.Diagrams.toZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) ⋙
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z

/-- The first map of the original I data on the whole zero-arrow family. -/
def initialToCofibrantReplacement :
    (Functor.const Spectrum.{u, v}).obj zero ⟶ cofibrantReplacement.{u, v} :=
  Functor.whiskerLeft (Native.Diagrams.fromZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v}))
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.i

/-- The second map of those same I data on every original zero arrow. -/
def cofibrantReplacementCounit : cofibrantReplacement.{u, v} ⟶ 𝟭 Spectrum.{u, v} :=
  Functor.whiskerLeft (Native.Diagrams.fromZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v}))
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.p

/-- The first map of the original J data on the whole terminal-arrow family. -/
def fibrantReplacementUnit : 𝟭 Spectrum.{u, v} ⟶ fibrantReplacement.{u, v} :=
  Functor.whiskerLeft (Native.Diagrams.toZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v}))
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.i

/-- The second map of those same J data on every original terminal arrow. -/
def fibrantReplacementToZero : fibrantReplacement.{u, v} ⟶
    (Functor.const Spectrum.{u, v}).obj zero :=
  Functor.whiskerLeft (Native.Diagrams.toZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v}))
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.p

/-- Every Q map is the original I middle map on that same native zero square. -/
theorem cofibrantReplacement_map_original_data {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    cofibrantReplacement.map f = PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.Z.map
      ((Native.Diagrams.fromZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map f) := rfl

/-- Every R map is the original J middle map on that same native terminal square. -/
theorem fibrantReplacement_map_original_data {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    fibrantReplacement.map f = PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.Z.map
      ((Native.Diagrams.toZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).map f) := rfl

/-- Both Q legs factor the actual original zero-to-object arrow. -/
theorem cofibrantReplacement_fac (X : Spectrum.{u, v}) :
    initialToCofibrantReplacement.app X ≫ cofibrantReplacementCounit.app X =
      Native.Diagrams.zeroTo X :=
  PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData_fac
    ((Native.Diagrams.fromZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).obj X)

/-- Both R legs factor the actual original object-to-zero arrow. -/
theorem fibrantReplacement_fac (X : Spectrum.{u, v}) :
    fibrantReplacementUnit.app X ≫ fibrantReplacementToZero.app X = Native.Diagrams.toZero X :=
  PointedCGWH.Spectra.Symmetric.fibrantFactorizationData_fac
    ((Native.Diagrams.toZeroArrow (A := PointedCGWH.SymmetricOperatorIndex.{u, v})).obj X)

/-- The two Q maps retain the original canonical I class pair. -/
theorem cofibrantReplacement_classes (X : Spectrum.{u, v}) :
    cofibrations Spectrum.{u, v} (initialToCofibrantReplacement.app X) ∧
      trivialFibrations Spectrum.{u, v} (cofibrantReplacementCounit.app X) :=
  ⟨PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.hi _,
    PointedCGWH.Spectra.Symmetric.cofibrantFactorizationData.hp _⟩

/-- The two R maps retain the original canonical J class pair. -/
theorem fibrantReplacement_classes (X : Spectrum.{u, v}) :
    trivialCofibrations Spectrum.{u, v} (fibrantReplacementUnit.app X) ∧
      fibrations Spectrum.{u, v} (fibrantReplacementToZero.app X) :=
  ⟨PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.hi _,
    PointedCGWH.Spectra.Symmetric.fibrantFactorizationData.hp _⟩

theorem isCofibrant_cofibrantReplacement (X : Spectrum.{u, v}) :
    IsCofibrant (cofibrantReplacement.obj X) :=
  Native.Replacement.isCofibrant_cofibrantReplacement (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) X

theorem isFibrant_fibrantReplacement (X : Spectrum.{u, v}) :
    IsFibrant (fibrantReplacement.obj X) :=
  Native.Replacement.isFibrant_fibrantReplacement (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) X

/-- The whole original I/J replacement keeps the prescribed order. -/
def cofibrantFibrantReplacement : Spectrum.{u, v} ⥤ Spectrum.{u, v} :=
  cofibrantReplacement ⋙ fibrantReplacement

/-- The whole original J/I replacement keeps the other prescribed order. -/
def fibrantCofibrantReplacement : Spectrum.{u, v} ⥤ Spectrum.{u, v} :=
  fibrantReplacement ⋙ cofibrantReplacement

theorem isBifibrant_cofibrantFibrantReplacement (X : Spectrum.{u, v}) :
    IsCofibrant (cofibrantFibrantReplacement.obj X) ∧
      IsFibrant (cofibrantFibrantReplacement.obj X) :=
  ⟨Native.Replacement.isCofibrant_cofibrantFibrantReplacement (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) X,
    Native.Replacement.isFibrant_cofibrantFibrantReplacement (B := Native.Construction.generatorOrderBot.{v}) (A :=
      PointedCGWH.SymmetricOperatorIndex.{u, v}) X⟩

theorem isBifibrant_fibrantCofibrantReplacement (X : Spectrum.{u, v}) :
    IsCofibrant (fibrantCofibrantReplacement.obj X) ∧
      IsFibrant (fibrantCofibrantReplacement.obj X) :=
  ⟨Native.Replacement.isCofibrant_fibrantCofibrantReplacement (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) X,
    Native.Replacement.isFibrant_fibrantCofibrantReplacement (B := Native.Construction.generatorOrderBot.{v}) (A :=
      PointedCGWH.SymmetricOperatorIndex.{u, v}) X⟩

theorem cofibrantReplacementCounit_naturality {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    cofibrantReplacement.map f ≫ cofibrantReplacementCounit.app Y =
      cofibrantReplacementCounit.app X ≫ f := cofibrantReplacementCounit.naturality f

theorem fibrantReplacementUnit_naturality {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    f ≫ fibrantReplacementUnit.app Y = fibrantReplacementUnit.app X ≫
      fibrantReplacement.map f := fibrantReplacementUnit.naturality f

/-- The original native Q projection preserves the entire original right Day action. -/
theorem cofibrantReplacementCounit_rightAction (X : Spectrum.{u, v}) :
    (SymmetricRightModulePresentation.operatorToRightModule.obj
      (cofibrantReplacement.obj X)).mod.smul ≫
      (SymmetricRightModulePresentation.operatorToRightModule.map
        (cofibrantReplacementCounit.app X)).hom =
      ((SymmetricRightModulePresentation.operatorToRightModule.map
        (cofibrantReplacementCounit.app X)).hom ▷ sphereSequence.{u, v}) ≫
      (SymmetricRightModulePresentation.operatorToRightModule.obj X).mod.smul :=
  (SymmetricRightModulePresentation.operatorToRightModule.map
    (cofibrantReplacementCounit.app X)).isModHom.smul_hom

/-- The original native R inclusion preserves that same whole right Day action. -/
theorem fibrantReplacementUnit_rightAction (X : Spectrum.{u, v}) :
    (SymmetricRightModulePresentation.operatorToRightModule.obj X).mod.smul ≫
      (SymmetricRightModulePresentation.operatorToRightModule.map
        (fibrantReplacementUnit.app X)).hom =
      ((SymmetricRightModulePresentation.operatorToRightModule.map
        (fibrantReplacementUnit.app X)).hom ▷ sphereSequence.{u, v}) ≫
      (SymmetricRightModulePresentation.operatorToRightModule.obj
        (fibrantReplacement.obj X)).mod.smul :=
  (SymmetricRightModulePresentation.operatorToRightModule.map
    (fibrantReplacementUnit.app X)).isModHom.smul_hom

/-- The whole original cofibrantReplacement quotient functor on the canonical model. -/
def cofibrantReplacementHo : HoCategory.{u, v} ⥤ HoCategory.{u, v} :=
  Native.Replacement.cofibrantReplacementHo (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original quotient projection square keeps the entire native functor. -/
theorem cofibrantReplacementHo_projection : projection.{u, v} ⋙ cofibrantReplacementHo.{u, v} =
    cofibrantReplacement.{u, v} ⋙ projection.{u, v} :=
  Native.Replacement.cofibrantReplacementHo_projection (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original projected map is the image of the same native replacement map. -/
theorem cofibrantReplacementHo_map_projected {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    cofibrantReplacementHo.map (projection.map f) = projection.map (cofibrantReplacement.map f) :=
  Native.Replacement.cofibrantReplacementHo_map_projected (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) f

/-- The complete quotient isomorphism uses the original chosen replacement projection. -/
def cofibrantReplacementHoIso : cofibrantReplacementHo.{u, v} ≅ 𝟭 HoCategory.{u, v} :=
  Native.Replacement.cofibrantReplacementHoIso (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Naturality retains every original quotient morphism. -/
theorem cofibrantReplacementHoIso_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    cofibrantReplacementHo.map f ≫ cofibrantReplacementHoIso.hom.app Y = cofibrantReplacementHoIso.hom.app X ≫ f :=
  cofibrantReplacementHoIso.hom.naturality f

/-- Inverse naturality retains the complete original quotient map. -/
theorem cofibrantReplacementHoIso_inv_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    f ≫ cofibrantReplacementHoIso.inv.app Y = cofibrantReplacementHoIso.inv.app X ≫ cofibrantReplacementHo.map f :=
  cofibrantReplacementHoIso.inv.naturality f

/-- Weak maps are detected by the actual original native replacement. -/
theorem cofibrantReplacement_map_weakEquivalence_iff {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Spectrum.{u, v} (cofibrantReplacement.map f) ↔ weakEquivalences Spectrum.{u, v} f :=
  Native.Replacement.cofibrantReplacement_map_weakEquivalence_iff (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) f

/-- The whole original fibrantReplacement quotient functor on the canonical model. -/
def fibrantReplacementHo : HoCategory.{u, v} ⥤ HoCategory.{u, v} :=
  Native.Replacement.fibrantReplacementHo (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original quotient projection square keeps the entire native functor. -/
theorem fibrantReplacementHo_projection : projection.{u, v} ⋙ fibrantReplacementHo.{u, v} =
    fibrantReplacement.{u, v} ⋙ projection.{u, v} :=
  Native.Replacement.fibrantReplacementHo_projection (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original projected map is the image of the same native replacement map. -/
theorem fibrantReplacementHo_map_projected {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    fibrantReplacementHo.map (projection.map f) = projection.map (fibrantReplacement.map f) :=
  Native.Replacement.fibrantReplacementHo_map_projected (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) f

/-- The complete quotient isomorphism uses the original chosen replacement projection. -/
def fibrantReplacementHoIso : fibrantReplacementHo.{u, v} ≅ 𝟭 HoCategory.{u, v} :=
  Native.Replacement.fibrantReplacementHoIso (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Naturality retains every original quotient morphism. -/
theorem fibrantReplacementHoIso_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    fibrantReplacementHo.map f ≫ fibrantReplacementHoIso.hom.app Y = fibrantReplacementHoIso.hom.app X ≫ f :=
  fibrantReplacementHoIso.hom.naturality f

/-- Inverse naturality retains the complete original quotient map. -/
theorem fibrantReplacementHoIso_inv_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    f ≫ fibrantReplacementHoIso.inv.app Y = fibrantReplacementHoIso.inv.app X ≫ fibrantReplacementHo.map f :=
  fibrantReplacementHoIso.inv.naturality f

/-- Weak maps are detected by the actual original native replacement. -/
theorem fibrantReplacement_map_weakEquivalence_iff {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Spectrum.{u, v} (fibrantReplacement.map f) ↔ weakEquivalences Spectrum.{u, v} f :=
  Native.Replacement.fibrantReplacement_map_weakEquivalence_iff (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) f

/-- The whole original cofibrantFibrantReplacement quotient functor on the canonical model. -/
def cofibrantFibrantReplacementHo : HoCategory.{u, v} ⥤ HoCategory.{u, v} :=
  Native.Replacement.cofibrantFibrantReplacementHo (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original quotient projection square keeps the entire native functor. -/
theorem cofibrantFibrantReplacementHo_projection : projection.{u, v} ⋙ cofibrantFibrantReplacementHo.{u, v} =
    cofibrantFibrantReplacement.{u, v} ⋙ projection.{u, v} :=
  Native.Replacement.cofibrantFibrantReplacementHo_projection (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original projected map is the image of the same native replacement map. -/
theorem cofibrantFibrantReplacementHo_map_projected {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    cofibrantFibrantReplacementHo.map (projection.map f) = projection.map (cofibrantFibrantReplacement.map f) :=
  Native.Replacement.cofibrantFibrantReplacementHo_map_projected (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) f

/-- The complete quotient isomorphism uses the original chosen replacement projection. -/
def cofibrantFibrantReplacementHoIso : cofibrantFibrantReplacementHo.{u, v} ≅ 𝟭 HoCategory.{u, v} :=
  Native.Replacement.cofibrantFibrantReplacementHoIso (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Naturality retains every original quotient morphism. -/
theorem cofibrantFibrantReplacementHoIso_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    cofibrantFibrantReplacementHo.map f ≫ cofibrantFibrantReplacementHoIso.hom.app Y =
      cofibrantFibrantReplacementHoIso.hom.app X ≫ f :=
  cofibrantFibrantReplacementHoIso.hom.naturality f

/-- Inverse naturality retains the complete original quotient map. -/
theorem cofibrantFibrantReplacementHoIso_inv_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    f ≫ cofibrantFibrantReplacementHoIso.inv.app Y = cofibrantFibrantReplacementHoIso.inv.app X ≫
      cofibrantFibrantReplacementHo.map f :=
  cofibrantFibrantReplacementHoIso.inv.naturality f

/-- Weak maps are detected by the actual original native replacement. -/
theorem cofibrantFibrantReplacement_map_weakEquivalence_iff {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Spectrum.{u, v} (cofibrantFibrantReplacement.map f) ↔ weakEquivalences Spectrum.{u, v} f :=
  Native.Replacement.cofibrantFibrantReplacement_map_weakEquivalence_iff (B :=
    Native.Construction.generatorOrderBot.{v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) f

/-- The whole original fibrantCofibrantReplacement quotient functor on the canonical model. -/
def fibrantCofibrantReplacementHo : HoCategory.{u, v} ⥤ HoCategory.{u, v} :=
  Native.Replacement.fibrantCofibrantReplacementHo (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original quotient projection square keeps the entire native functor. -/
theorem fibrantCofibrantReplacementHo_projection : projection.{u, v} ⋙ fibrantCofibrantReplacementHo.{u, v} =
    fibrantCofibrantReplacement.{u, v} ⋙ projection.{u, v} :=
  Native.Replacement.fibrantCofibrantReplacementHo_projection (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Every original projected map is the image of the same native replacement map. -/
theorem fibrantCofibrantReplacementHo_map_projected {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    fibrantCofibrantReplacementHo.map (projection.map f) = projection.map (fibrantCofibrantReplacement.map f) :=
  Native.Replacement.fibrantCofibrantReplacementHo_map_projected (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v}) f

/-- The complete quotient isomorphism uses the original chosen replacement projection. -/
def fibrantCofibrantReplacementHoIso : fibrantCofibrantReplacementHo.{u, v} ≅ 𝟭 HoCategory.{u, v} :=
  Native.Replacement.fibrantCofibrantReplacementHoIso (B := Native.Construction.generatorOrderBot.{v}) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- Naturality retains every original quotient morphism. -/
theorem fibrantCofibrantReplacementHoIso_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    fibrantCofibrantReplacementHo.map f ≫ fibrantCofibrantReplacementHoIso.hom.app Y =
      fibrantCofibrantReplacementHoIso.hom.app X ≫ f :=
  fibrantCofibrantReplacementHoIso.hom.naturality f

/-- Inverse naturality retains the complete original quotient map. -/
theorem fibrantCofibrantReplacementHoIso_inv_naturality {X Y : HoCategory.{u, v}} (f : X ⟶ Y) :
    f ≫ fibrantCofibrantReplacementHoIso.inv.app Y = fibrantCofibrantReplacementHoIso.inv.app X ≫
      fibrantCofibrantReplacementHo.map f :=
  fibrantCofibrantReplacementHoIso.inv.naturality f

/-- Weak maps are detected by the actual original native replacement. -/
theorem fibrantCofibrantReplacement_map_weakEquivalence_iff {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    weakEquivalences Spectrum.{u, v} (fibrantCofibrantReplacement.map f) ↔ weakEquivalences Spectrum.{u, v} f :=
  Native.Replacement.fibrantCofibrantReplacement_map_weakEquivalence_iff (B :=
    Native.Construction.generatorOrderBot.{v}) (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) f

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The entire Q functor, including every map, is the original I algorithm at every caller bottom. -/
theorem cofibrantReplacement_eq_atCallerBottom : cofibrantReplacement.{u, v} =
    Native.Replacement.cofibrantReplacement (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  Native.Construction.fixedCofibrantReplacement_eq_native (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The entire R functor retains the same original J algorithm at every caller bottom. -/
theorem fibrantReplacement_eq_atCallerBottom : fibrantReplacement.{u, v} =
    Native.Replacement.fibrantReplacement (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v}) :=
  Native.Construction.fixedFibrantReplacement_eq_native (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The complete original Q projection retains every component at that actual bottom. -/
theorem cofibrantReplacementCounit_heq_atCallerBottom :
    HEq cofibrantReplacementCounit.{u, v}
      (Native.Replacement.cofibrantReplacementCounit (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})) :=
  Native.Construction.fixedCofibrantReplacementCounit_heq_native (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u,
    v})

/-- The complete original R inclusion retains every component at that actual bottom. -/
theorem fibrantReplacementUnit_heq_atCallerBottom :
    HEq fibrantReplacementUnit.{u, v}
      (Native.Replacement.fibrantReplacementUnit (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})) :=
  Native.Construction.fixedFibrantReplacementUnit_heq_native (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The complete original initial I leg keeps its actual zero and every map. -/
theorem initialToCofibrantReplacement_heq_atCallerBottom :
    HEq initialToCofibrantReplacement.{u, v}
      (Native.Replacement.initialToCofibrantReplacement (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})) :=
  Native.Construction.fixedInitialToCofibrantReplacement_heq_native (B := B) (A :=
    PointedCGWH.SymmetricOperatorIndex.{u, v})

/-- The complete original terminal J leg keeps its actual zero and every map. -/
theorem fibrantReplacementToZero_heq_atCallerBottom :
    HEq fibrantReplacementToZero.{u, v}
      (Native.Replacement.fibrantReplacementToZero (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})) :=
  Native.Construction.fixedFibrantReplacementToZero_heq_native (B := B) (A := PointedCGWH.SymmetricOperatorIndex.{u, v})

end PointedCGWH.Spectra.Symmetric.LevelHomotopy
