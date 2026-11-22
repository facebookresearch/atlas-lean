/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.FreeComparison

/-!
# Balanced carrier of sequential-to-symmetric induction

The map from the symmetrized ordered sphere to the symmetric sphere defines
a scalar bimodule whose right action uses sphere multiplication. Extension
of scalars presents module induction as a relative tensor, with explicit
balancing arrows, unit generators and maps through the quotient. The
module–operator equivalences identify the carrier of native induction with
that same relative-tensor carrier.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj tensorSphereMap_isMonHom
  symmetricSequenceClosed symmetricSequenceColimits symmetricTensorLeftPreservesColimits
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The original sphere bimodule uses the entire original sphere map and sphere multiplication. -/
theorem sphereBimodule_rightAction :
    (Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight =
      (sphereSequence.{u, v} ◁ tensorSphereMap.{u, v}) ≫ μ[sphereSequence.{u, v}] := rfl

/-- The actual right sphere action satisfies the full original source monoid unit equation. -/
theorem sphereBimodule_rightUnit :
    (sphereSequence.{u, v} ◁ η[G.obj orderedSphere.{u, v}]) ≫
      (Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight =
      (ρ_ sphereSequence.{u, v}).hom :=
  Mod.ExtensionOfScalars.rightAction_one tensorSphereMap.{u, v}

/-- The actual right sphere action satisfies the full original source monoid multiplication equation. -/
theorem sphereBimodule_rightAssociativity :
    (sphereSequence.{u, v} ◁ μ[G.obj orderedSphere.{u, v}]) ≫
      (Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight =
      (α_ sphereSequence.{u, v} (G.obj orderedSphere.{u, v}) (G.obj orderedSphere.{u, v})).inv ≫
        ((Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight ▷ G.obj orderedSphere.{u, v}) ≫
          (Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight :=
  Mod.ExtensionOfScalars.rightAction_assoc tensorSphereMap.{u, v}

/-- The original left sphere action commutes with the complete original right tensor-algebra action. -/
theorem sphereBimodule_middleAssociativity :
    (μ[sphereSequence.{u, v}] ▷ G.obj orderedSphere.{u, v}) ≫
      (Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight =
      (α_ sphereSequence.{u, v} sphereSequence.{u, v} (G.obj orderedSphere.{u, v})).hom ≫
        (sphereSequence.{u, v} ◁ (Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight) ≫
          μ[sphereSequence.{u, v}] :=
  Mod.ExtensionOfScalars.rightAction_middle tensorSphereMap.{u, v}

/-- Every original module gives the full source-action balancing map on its entire symmetrization. -/
theorem moduleInduction_balancingLeft
    (M : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v}) :
    (Mod.ExtensionOfScalars.leftMap (B := sphereSequence.{u, v})
      ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)).hom =
      sphereSequence.{u, v} ◁ ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M).mod.smul :=
  Mod.ExtensionOfScalars.leftMap_hom ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)

/-- Every original module gives the full original sphere-map balancing arrow and actual right action. -/
theorem moduleInduction_balancingRight
    (M : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v}) :
    (Mod.ExtensionOfScalars.rightMap tensorSphereMap.{u, v}
      ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)).hom =
      (α_ sphereSequence.{u, v} (G.obj orderedSphere.{u, v})
        ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M).X).inv ≫
          ((Mod.ExtensionOfScalars.scalarBimodule tensorSphereMap.{u, v}).actRight ▷
            ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M).X) :=
  Mod.ExtensionOfScalars.rightMap_hom tensorSphereMap.{u, v}
    ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)

/-- The original full quotient identifies both balancing maps on every original symmetrized module. -/
theorem moduleInduction_balance
    (M : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v}) :
    Mod.ExtensionOfScalars.leftMap ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) ≫
      Mod.ExtensionOfScalars.π tensorSphereMap.{u, v}
        ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) =
    Mod.ExtensionOfScalars.rightMap tensorSphereMap.{u, v}
      ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) ≫
      Mod.ExtensionOfScalars.π tensorSphereMap.{u, v}
        ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) :=
  Mod.ExtensionOfScalars.balance tensorSphereMap.{u, v}
    ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)

/-- The whole original induction unit carries the original free-module generator through the balancing quotient. -/
theorem moduleInduction_generator
    (M : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v}) :
    ((Mod.ExtensionOfScalars.adjunction tensorSphereMap.{u, v}).unit.app
      ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)).hom =
        Mod.ExtensionOfScalars.freeUnit (((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M).X) ≫
          (Mod.ExtensionOfScalars.π tensorSphereMap.{u, v}
            ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)).hom :=
  Mod.ExtensionOfScalars.unit_hom tensorSphereMap.{u, v}
    ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)

/-- Every actual original module map descends through the full original balancing quotient. -/
theorem moduleInduction_map_quotient
    {M N : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v}} (f : M ⟶ N) :
    Mod.ExtensionOfScalars.π tensorSphereMap.{u, v}
      ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) ≫
      (Mod.ExtensionOfScalars.induction tensorSphereMap.{u, v}).map
        ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).map f) =
      (Mod.free sphereSequence.{u, v}).map (((Functor.mapMod G.{u, v} orderedSphere.{u, v}).map f).hom) ≫
        Mod.ExtensionOfScalars.π tensorSphereMap.{u, v}
          ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj N) :=
  Mod.ExtensionOfScalars.π_induction_map tensorSphereMap.{u, v}
    ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).map f)

/-- The entire original induction carrier is the actual relative tensor over its full tensor algebra. -/
def moduleInductionRelativeTensorCarrierIso
    (M : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v}) :
    (moduleInduction.{u, v}.obj M).X ≅
      Mod.ExtensionOfScalars.relativeTensorCarrier tensorSphereMap.{u, v}
        ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) :=
  Mod.ExtensionOfScalars.carrierIso tensorSphereMap.{u, v}
    ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M)

/-- Returning the actual original induction spectrum to modules retains the full original equivalence unit. -/
def nativeInductionModuleComparison :
    V.{u, v} ⋙ SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse ≅
      sequentialModuleEquivalence.{u, v}.functor ⋙ moduleInduction.{u, v} :=
  (isoWhiskerRight
    (Functor.associator sequentialModuleEquivalence.{u, v}.functor moduleInduction.{u, v}
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor).symm
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse) ≪≫
  ((Functor.associator
      (sequentialModuleEquivalence.{u, v}.functor ⋙ moduleInduction.{u, v})
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse) ≪≫
    (isoWhiskerLeft (sequentialModuleEquivalence.{u, v}.functor ⋙ moduleInduction.{u, v})
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.unitIso.symm) ≪≫
    Functor.rightUnitor (sequentialModuleEquivalence.{u, v}.functor ⋙ moduleInduction.{u, v}))

/-- Every original spectrum has the full actual sphere relative-tensor carrier in the native module presentation. -/
def nativeInductionRelativeTensorCarrierIso (X : NativeIndexKanComposition.SequentialCarrier.{u, v}) :
    (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse.obj (V.obj X)).X ≅
      Mod.ExtensionOfScalars.relativeTensorCarrier tensorSphereMap.{u, v}
        ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj
          (sequentialModuleEquivalence.{u, v}.functor.obj X)) :=
  (Mod.forget sphereSequence.{u, v}).mapIso (nativeInductionModuleComparison.app X) ≪≫
    moduleInductionRelativeTensorCarrierIso (sequentialModuleEquivalence.{u, v}.functor.obj X)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
