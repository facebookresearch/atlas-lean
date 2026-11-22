/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.NativeRestrictionStructure
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.ReconstructedSuccessorAction

/-!
# Sequential spectra recovered by module restriction

Identifies the structure maps obtained by restricting a symmetric sphere module with those of its underlying sequential spectrum. These equalities recover the full sequential spectrum and its native enriched restriction object.
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
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj

/-- The complete original inverse module functor and direct restriction give the original source structure map. -/
theorem directModuleRestriction_reconstructed_structureMap_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : ℕ) :
    CategoryTheory.Sequence.TensorPowerModule.structureMap
      ((directModuleRestriction.{u, v}).obj
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F)) n =
      symmetricToSequentialSourceStructureMap.{u, v} F n := by
  let M := (PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F
  let a := CategoryTheory.Sequence.index 1
  let b := CategoryTheory.Sequence.index n
  let c := CategoryTheory.Sequence.index (n + 1)
  let f : a ⊗ b ⟶ c := degreeSuccessorArrow n
  let X := M.X.functor.obj (degreeInclusion.obj b)
  let l := (λ_ PointedCGWH.sphereOne.{u, v}).inv ⊗ₘ 𝟙 X
  have hi : (degreeTensorIso a b).hom =
      𝟙 (degreeInclusion.obj a ⊗ degreeInclusion.obj b) := rfl
  have hf : (degreeTensorIso a b).hom ≫ degreeInclusion.map f = degreeInclusion.map f :=
    (congrArg (fun q => q ≫ degreeInclusion.map f) hi).trans (Category.id_comp _)
  have ha := congrArg (fun g : degreeInclusion.obj a ⊗ degreeInclusion.obj b ⟶ degreeInclusion.obj c =>
    l ≫ PointedCGWH.SymmetricModulePresentation.arrowAction M
      (degreeInclusion.obj a) (degreeInclusion.obj b) (degreeInclusion.obj c) g) hf
  have hm := directModuleRestriction_structureMap_original M n
  have hs := reconstructedModule_successor_original F n
  let p := (DayFunctor.η sphereSequence.{u, v} M.X).app
    (degreeInclusion.obj a, degreeInclusion.obj b)
  let s := M.mod.smul.natTrans.app (degreeInclusion.obj a ⊗ degreeInclusion.obj b)
  let g := M.X.functor.map (degreeInclusion.map f)
  have hpair : PointedCGWH.SymmetricModulePresentation.pairAction M
      (degreeInclusion.obj a) (degreeInclusion.obj b) = p ≫ s := rfl
  have hc := congrArg (fun q => l ≫ q) (Category.assoc p s g).symm
  have hp := congrArg (fun q => l ≫ (q ≫ g)) hpair
  exact hm.trans (hc.trans (hp.symm.trans (ha.symm.trans hs)))


/-- The complete original inverse module and direct restriction recover the whole original structural spectrum. -/
theorem directModuleRestriction_inverse_sourceSpectrum_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    (CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v}).inverse.obj
      ((directModuleRestriction.{u, v}).obj
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F)) =
      symmetricToSequentialSourceSpectrum.{u, v} F := by
  let K := PointedCGWH.sphereOne.{u, v}
  let L := fun n => F.toEnrichedFunctor.obj
    (PointedCGWH.symmetricOperatorObj.{u, v} (card n))
  let M := (PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F
  have h : (fun n => CategoryTheory.Sequence.TensorPowerModule.structureMap
      ((directModuleRestriction.{u, v}).obj M) n) =
      (fun n => symmetricToSequentialSourceStructureMap.{u, v} F n) := by
    funext n
    exact directModuleRestriction_reconstructed_structureMap_original F n
  exact congrArg (fun maps : ∀ n, K ⊗ L n ⟶ L (n + 1) =>
    (⟨L, maps⟩ : CategoryTheory.SequentialSpectrum PointedCGWH.{u, v} K)) h

/-- Equality of the full original structural spectrum gives the complete original enriched restriction object. -/
theorem directModuleRestriction_inverse_operatorObject_original
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    sequentialModuleEquivalence.{u, v}.inverse.obj
      ((directModuleRestriction.{u, v}).obj
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F)) =
      NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj F :=
  (congrArg (CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctor
    PointedCGWH.sphereOne.{u, v})
    (directModuleRestriction_inverse_sourceSpectrum_original F)).trans
      (symmetricToSequentialSourceObject_eq.{u, v} F)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
