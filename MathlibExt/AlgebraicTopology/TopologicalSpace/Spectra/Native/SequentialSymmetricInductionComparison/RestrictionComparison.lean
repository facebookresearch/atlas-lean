/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionMapComponents
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.RestrictionAppliedComponents

/-!
# Comparing module and operator restriction

Builds natural isomorphisms between direct restriction of symmetric sphere modules and
restriction of their operator diagrams. Component formulas retain every degree and arbitrary
module morphism across the presentation equivalences.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open CategoryTheory.Spectra.SpectrumIndexMaps
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj

namespace CategoryTheory.Equivalence.FunctorComparison
universe uA vA uS vS uD vD uB vB
variable {A : Type uA} [Category.{vA} A] {S : Type uS} [Category.{vS} S]
  {D : Type uD} [Category.{vD} D] {B : Type uB} [Category.{vB} B]

/-- Both full functor associations have the same complete original object, map and functor-law data. -/
private theorem functor_assoc_eq (F : A ⥤ S) (G : S ⥤ D) (H : D ⥤ B) :
    (F ⋙ G) ⋙ H = F ⋙ G ⋙ H := rfl

/-- Both original whole equivalences determine the exact complete module/operator inverse before its arguments. -/
private def descendComparison (E : S ≌ B) (M : S ≌ D) (F : A ⥤ D) (G : A ⥤ B)
    (e : F ⋙ M.inverse ≅ G ⋙ E.inverse) : F ⋙ (E.symm.trans M).inverse ≅ G :=
  (isoWhiskerRight e E.functor) ≪≫ isoWhiskerLeft G E.counitIso

/-- The full forward family is the two actual original equivalence maps at every original object. -/
private theorem descendComparison_hom_family (E : S ≌ B) (M : S ≌ D) (F : A ⥤ D) (G : A ⥤ B)
    (e : F ⋙ M.inverse ≅ G ⋙ E.inverse) :
    (fun X => (descendComparison E M F G e).hom.app X) =
      (fun X => ((E.functor.mapIso (e.app X)) ≪≫ E.counitIso.app (G.obj X)).hom) := rfl

/-- The full inverse family is the two actual original inverse equivalence maps at every original object. -/
private theorem descendComparison_inv_family (E : S ≌ B) (M : S ≌ D) (F : A ⥤ D) (G : A ⥤ B)
    (e : F ⋙ M.inverse ≅ G ⋙ E.inverse) :
    (fun X => (descendComparison E M F G e).inv.app X) =
      (fun X => ((E.functor.mapIso (e.app X)) ≪≫ E.counitIso.app (G.obj X)).inv) := rfl

end CategoryTheory.Equivalence.FunctorComparison

namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
open CategoryTheory.Equivalence.FunctorComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  copowerUnderlyingEnrichedOrdinary copowerUnderlyingMonoidal
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj
  CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

/-- The complete direct module restriction is reconstructed on its actual full structural-spectrum functor. -/
def directModuleRestrictionStructuralFunctor :
    NativeIndexKanComposition.SymmetricCarrier.{u, v} ⥤
      CategoryTheory.SequentialSpectrum PointedCGWH.{u, v} PointedCGWH.sphereOne.{u, v} :=
  ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse ⋙
    directModuleRestriction.{u, v}) ⋙
      (CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v}).inverse

/-- The whole structural functor keeps both original full module functors and the original module equivalence. -/
theorem directModuleRestriction_structuralFunctor_eq :
    directModuleRestrictionStructuralFunctor.{u, v} =
      (PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse ⋙
        directModuleRestriction.{u, v} ⋙
          (CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v}).inverse :=
  functor_assoc_eq
    (PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse
    directModuleRestriction.{u, v}
    (CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v}).inverse

/-- Every entire reconstructed direct-restriction map retains its full original operator component. -/
theorem directModuleRestrictionStructuralFunctor_map_level
    {F G : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : F ⟶ G) (n : ℕ) :
    (directModuleRestrictionStructuralFunctor.{u, v}.map f).levelMap n =
      EnrichedFunctorCat.component f (PointedCGWH.symmetricOperatorObj.{u, v} (card n)) :=
  PointedCGWH.symmetricSequenceRestriction_component.{u, v} f
    (degreeInclusion.obj (CategoryTheory.Sequence.index n))

/-- Every entire native-restriction map reconstructs the identical original operator component. -/
theorem nativeRestriction_structuralMap_level
    {F G : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : F ⟶ G) (n : ℕ) :
    ((NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v} ⋙
      (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedEquivalence
        PointedCGWH.sphereOne.{u, v}).inverse).map f).levelMap n =
      EnrichedFunctorCat.component f (PointedCGWH.symmetricOperatorObj.{u, v} (card n)) :=
  (CategoryTheory.SequentialSpectrum.EnrichedPresentation.fromEnrichedFunctorMap_levelMap
    PointedCGWH.sphereOne.{u, v} (NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}.map f) n).trans
      (nativeSequentialSymmetricRestriction_map_component f n)

/-- Both complete structural comparison maps are natural on every original symmetric transformation. -/
theorem directModuleRestrictionStructuralComparison_naturality
    {F G : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : F ⟶ G) :
    directModuleRestrictionStructuralFunctor.{u, v}.map f ≫
      (directModuleRestrictionInverseStructuralIso G).hom =
    (directModuleRestrictionInverseStructuralIso F).hom ≫
      ((NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v} ⋙
        (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedEquivalence
          PointedCGWH.sphereOne.{u, v}).inverse).map f) := by
  apply CategoryTheory.SequentialSpectrum.hom_ext
  intro n
  change (directModuleRestrictionStructuralFunctor.{u, v}.map f).levelMap n ≫
      𝟙 (G.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (card n))) =
    𝟙 (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} (card n))) ≫
      ((NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v} ⋙
        (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedEquivalence
          PointedCGWH.sphereOne.{u, v}).inverse).map f).levelMap n
  exact ((congrArg (fun q => q ≫ 𝟙 _) (directModuleRestrictionStructuralFunctor_map_level f n)).trans
    (Category.comp_id _)).trans
      (((Category.id_comp _).symm).trans
        (congrArg (fun q => 𝟙 _ ≫ q) (nativeRestriction_structuralMap_level f n).symm))

/-- The whole structural comparison retains both original complete level-map families and inverse laws. -/
def directModuleRestrictionStructuralComparison :
    directModuleRestrictionStructuralFunctor.{u, v} ≅
      NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v} ⋙
        (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedEquivalence
          PointedCGWH.sphereOne.{u, v}).inverse :=
  NatIso.ofComponents directModuleRestrictionInverseStructuralIso
    directModuleRestrictionStructuralComparison_naturality

/-- Both complete original module comparison maps are natural on every original enriched transformation. -/
def directModuleRestrictionNativeComparison :
    ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse ⋙
      directModuleRestriction.{u, v} ⋙ sequentialModuleEquivalence.{u, v}.inverse) ≅
      NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v} :=
  (Functor.associator
    (PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse
    directModuleRestriction.{u, v} sequentialModuleEquivalence.{u, v}.inverse).symm ≪≫
    descendComparison
    (CategoryTheory.SequentialSpectrum.EnrichedPresentation.enrichedEquivalence PointedCGWH.sphereOne.{u, v})
    (CategoryTheory.SequentialSpectrum.moduleEquivalence PointedCGWH.sphereOne.{u, v})
    ((PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse ⋙
      directModuleRestriction.{u, v})
    NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v}
    directModuleRestrictionStructuralComparison.{u, v}

/-- The complete lifted forward function is exactly the original full enriched comparison-map family. -/
theorem directModuleRestrictionNativeComparison_hom_family :
    (fun F => directModuleRestrictionNativeComparison.{u, v}.hom.app F) =
      (fun F => (directModuleRestrictionInverseOperatorIso F).hom) := by
  funext F
  change 𝟙 _ ≫ (directModuleRestrictionInverseOperatorIso F).hom =
    (directModuleRestrictionInverseOperatorIso F).hom
  exact Category.id_comp _

/-- The complete lifted inverse function is exactly the original full inverse enriched comparison-map family. -/
theorem directModuleRestrictionNativeComparison_inv_family :
    (fun F => directModuleRestrictionNativeComparison.{u, v}.inv.app F) =
      (fun F => (directModuleRestrictionInverseOperatorIso F).inv) := by
  funext F
  change (directModuleRestrictionInverseOperatorIso F).inv ≫ 𝟙 _ =
    (directModuleRestrictionInverseOperatorIso F).inv
  exact Category.comp_id _

/-- The original W and actual native restriction retain both complete comparison directions. -/
def nativeRestrictionComparison :
    W.{u, v} ≅ NativeIndexKanComposition.sequentialSymmetricRestriction.{u, v} :=
  (isoWhiskerLeft (PointedCGWH.SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}).inverse
    (isoWhiskerRight moduleRestrictionIso.{u, v} sequentialModuleEquivalence.{u, v}.inverse)) ≪≫
      directModuleRestrictionNativeComparison.{u, v}

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
