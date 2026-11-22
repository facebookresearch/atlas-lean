/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionSpectrumAndObject

/-!
# Components of the module-restriction comparison

Sequential spectra with the same level objects and equal structure maps
have an isomorphism given by identities at every level. In the braided
closed setting with an initial object, the enriched presentation retains
the forward and inverse level components. Applied to native module
restriction, this identifies inverse module restriction with direct operator
restriction through isomorphisms whose components are identities at every
sequential degree.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe uC vC
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]

/-- Both complete spectrum maps and inverse laws are constructed on the full shared original level family. -/
private def identitySpectrumIso (K : C) (L : ℕ → C) (s t : ∀ n, K ⊗ L n ⟶ L (n + 1))
    (h : ∀ n, s n = t n) :
    (⟨L,s⟩ : CategoryTheory.SequentialSpectrum C K) ≅
      (⟨L,t⟩ : CategoryTheory.SequentialSpectrum C K) :=
  { hom :=
      { levelMap := fun n => 𝟙 (L n)
        naturality := fun n =>
          (congrArg (fun q => q ≫ t n) (MonoidalCategory.whiskerLeft_id K (L n))).trans
            ((Category.id_comp (t n)).trans ((h n).symm.trans (Category.comp_id (s n)).symm)) }
    inv :=
      { levelMap := fun n => 𝟙 (L n)
        naturality := fun n =>
          (congrArg (fun q => q ≫ s n) (MonoidalCategory.whiskerLeft_id K (L n))).trans
            ((Category.id_comp (s n)).trans ((h n).trans (Category.comp_id (t n)).symm)) }
    hom_inv_id := by
      apply CategoryTheory.SequentialSpectrum.hom_ext
      intro n
      exact Category.id_comp (𝟙 (L n))
    inv_hom_id := by
      apply CategoryTheory.SequentialSpectrum.hom_ext
      intro n
      exact Category.id_comp (𝟙 (L n)) }

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe uC vC
variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalClosed C] [HasInitial C]
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The complete forward enriched lift keeps the original full structural component. -/
private theorem enrichedLiftIso_hom_component (K : C) (S : CategoryTheory.SequentialSpectrum C K)
    (F : CategoryTheory.SequentialSpectrum.EnrichedPresentation.Carrier K)
    (h : S ≅ CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor K F) (n : ℕ) :
    EnrichedFunctorCat.component
      (((CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctors K).mapIso h) ≪≫
        CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedCounitIsoApp K F).hom
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) = h.hom.levelMap n := by
  let a := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n
  let lift := (CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctors K).map h.hom
  let counit := (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedCounitIsoApp K F).hom
  have hc := EnrichedFunctorCat.component_comp lift counit a
  have hl := CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctorMap_component
    K h.hom a
  have he := CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedCounitIsoApp_hom_component
    K F n
  exact hc.trans ((congrArg (fun q => q ≫ EnrichedFunctorCat.component counit a) hl).trans
    ((congrArg (fun q => h.hom.levelMap n ≫ q) he).trans (Category.comp_id _)))

/-- The complete inverse enriched lift keeps the original full inverse structural component. -/
private theorem enrichedLiftIso_inv_component (K : C) (S : CategoryTheory.SequentialSpectrum C K)
    (F : CategoryTheory.SequentialSpectrum.EnrichedPresentation.Carrier K)
    (h : S ≅ CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor K F) (n : ℕ) :
    EnrichedFunctorCat.component
      (((CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctors K).mapIso h) ≪≫
        CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedCounitIsoApp K F).inv
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n) = h.inv.levelMap n := by
  let a := CategoryTheory.SequentialSpectrum.EnrichedIndex.degree K n
  let lift := (CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctors K).map h.inv
  let counit := (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedCounitIsoApp K F).inv
  have hc := EnrichedFunctorCat.component_comp counit lift a
  have hl := CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctorMap_component
    K h.inv a
  have he := CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedCounitIsoApp_inv_component
    K F n
  exact hc.trans ((congrArg (fun q => q ≫ EnrichedFunctorCat.component lift a) he).trans
    ((congrArg (fun q => 𝟙 (F.toEnrichedFunctor.obj a) ≫ q) hl).trans (Category.id_comp _)))

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- Both full structural spectrum maps keep the original identity on every level. -/
def directModuleRestrictionInverseStructuralIso
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    (CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v}).inverse.obj
      ((directModuleRestriction.{u, v}).obj
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F)) ≅
      CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor
        PointedCGWH.sphereOne.{u, v}
        (NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj F) := by
  let K := PointedCGWH.sphereOne.{u, v}
  let L := fun n => F.toEnrichedFunctor.obj
    (PointedCGWH.symmetricOperatorObj.{u, v} (card n))
  let M := (PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F
  let S := (CategoryTheory.SequentialSpectrum.moduleEquivalence K).inverse.obj
    ((directModuleRestriction.{u, v}).obj M)
  let T := CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctor K
    (NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj F)
  have h (n : ℕ) : S.structureMap n = T.structureMap n :=
    (directModuleRestriction_reconstructed_structureMap_original F n).trans
      (symmetricToSequentialSourceStructureMap_eq.{u, v} F n).symm
  exact identitySpectrumIso K L S.structureMap T.structureMap h

/-- The whole enriched comparison lifts both original structural maps and the original enriched counit. -/
def directModuleRestrictionInverseOperatorIso
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) :
    sequentialModuleEquivalence.{u, v}.inverse.obj
      ((directModuleRestriction.{u, v}).obj
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F)) ≅
      NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj F :=
  ((CategoryTheory.SequentialSpectrum.EnrichedPresentation.toEnrichedFunctors
      PointedCGWH.sphereOne.{u, v}).mapIso (directModuleRestrictionInverseStructuralIso F)) ≪≫
    CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedCounitIsoApp
      PointedCGWH.sphereOne.{u, v}
      (NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj F)

/-- The complete forward comparison has the original identity component at every sequential degree. -/
theorem directModuleRestriction_inverse_operatorIso_hom_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : ℕ) :
    EnrichedFunctorCat.component (directModuleRestrictionInverseOperatorIso F).hom
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n) =
      𝟙 (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (card n))) := by
  exact enrichedLiftIso_hom_component PointedCGWH.sphereOne.{u, v}
    ((CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v}).inverse.obj
      ((directModuleRestriction.{u, v}).obj
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F)))
    (NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj F)
    (directModuleRestrictionInverseStructuralIso F) n

/-- The complete inverse comparison has the original identity component at every sequential degree. -/
theorem directModuleRestriction_inverse_operatorIso_inv_component
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v}) (n : ℕ) :
    EnrichedFunctorCat.component (directModuleRestrictionInverseOperatorIso F).inv
      (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne.{u, v} n) =
      𝟙 (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (card n))) := by
  exact enrichedLiftIso_inv_component PointedCGWH.sphereOne.{u, v}
    ((CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v}).inverse.obj
      ((directModuleRestriction.{u, v}).obj
        ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse.obj F)))
    (NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.obj F)
    (directModuleRestrictionInverseStructuralIso F) n

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
