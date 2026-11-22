/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Monoidal.Closed.UncurryComposition
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Core

/-!
# Original ordered arrows and complete reconstructed module coefficients

Every ordered degree arrow retains its original finite operator generator,
source braid and entire closed coefficient action.
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
  orderedSphereMonObj sphereSequenceMonObj
local notation "N" => CategoryTheory.Sequence.Index

/-- Every original ordered degree arrow gives the complete original finite ordered operator generator. -/
theorem degreeInclusion_operatorGenerator (p n k : ℕ) (h : p + n = k)
    (f : CategoryTheory.Sequence.index p ⊗ CategoryTheory.Sequence.index n ⟶ CategoryTheory.Sequence.index k) :
    PointedCGWH.SymmetricModulePresentation.operatorGenerator
      (degreeInclusion.obj (CategoryTheory.Sequence.index p))
      (degreeInclusion.obj (CategoryTheory.Sequence.index n))
      (degreeInclusion.obj (CategoryTheory.Sequence.index k))
      ((degreeTensorIso (CategoryTheory.Sequence.index p) (CategoryTheory.Sequence.index n)).hom ≫
        degreeInclusion.map f) = orderedSymmetricOperatorHom.{u, v} n k p h := by
  cases h
  have hf : f = 𝟙 (CategoryTheory.Sequence.index p ⊗ CategoryTheory.Sequence.index n) := Discrete.hom_eq
  have hi : (degreeTensorIso (CategoryTheory.Sequence.index p) (CategoryTheory.Sequence.index n)).hom =
      𝟙 (degreeInclusion.obj (CategoryTheory.Sequence.index p) ⊗
        degreeInclusion.obj (CategoryTheory.Sequence.index n)) := rfl
  have hm : degreeInclusion.map f =
      𝟙 (degreeInclusion.obj (CategoryTheory.Sequence.index p ⊗ CategoryTheory.Sequence.index n)) :=
    (congrArg (fun q : CategoryTheory.Sequence.index p ⊗ CategoryTheory.Sequence.index n ⟶
        CategoryTheory.Sequence.index p ⊗ CategoryTheory.Sequence.index n => degreeInclusion.map q) hf).trans
      (degreeInclusion.map_id (CategoryTheory.Sequence.index p ⊗ CategoryTheory.Sequence.index n))
  have hl : (degreeTensorIso (CategoryTheory.Sequence.index p) (CategoryTheory.Sequence.index n)).hom ≫
      degreeInclusion.map f =
      𝟙 (degreeInclusion.obj (CategoryTheory.Sequence.index p) ⊗
        degreeInclusion.obj (CategoryTheory.Sequence.index n)) :=
    (congrArg (fun q =>
      (degreeTensorIso (CategoryTheory.Sequence.index p) (CategoryTheory.Sequence.index n)).hom ≫ q) hm).trans
        ((Category.comp_id _).trans hi)
  exact (congrArg (fun q => PointedCGWH.SymmetricModulePresentation.operatorGenerator
    (degreeInclusion.obj (CategoryTheory.Sequence.index p))
    (degreeInclusion.obj (CategoryTheory.Sequence.index n))
    (degreeInclusion.obj (CategoryTheory.Sequence.index (p + n))) q) hl).trans (by rfl)



/-- Every original reconstructed arrow retains its entire closed operator generator. -/
theorem reconstructedArrowAction_closed
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (a n k : CategoryTheory.Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    PointedCGWH.SymmetricModulePresentation.reconstructedArrowAction F a n k f =
      (β_ (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))
        (sphereSequence.{u, v}.functor.obj a)).inv ≫
      (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n) ◁
        PointedCGWH.SymmetricModulePresentation.operatorGenerator a n k f) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map
        (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k)) :=
  MonoidalClosed.braiding_uncurry_comp
    (PointedCGWH.SymmetricModulePresentation.operatorGenerator a n k f)
    (F.toEnrichedFunctor.map
      (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k))

/-- Every complete reconstructed module arrow has the same original closed operator coefficient. -/
theorem reconstructedModule_arrowAction_closed
    (F : EnrichedFunctorCat PointedCGWH.{u, v} PointedCGWH.SymmetricOperatorIndex.{u, v})
    (a n k : CategoryTheory.Operad.SmallFinBijGroupoid) (f : a ⊗ n ⟶ k) :
    PointedCGWH.SymmetricModulePresentation.arrowAction
      (PointedCGWH.SymmetricModulePresentation.reconstructedModule F) a n k f =
      (β_ (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n))
        (sphereSequence.{u, v}.functor.obj a)).inv ≫
      (F.toEnrichedFunctor.obj (PointedCGWH.symmetricOperatorObj.{u, v} n) ◁
        PointedCGWH.SymmetricModulePresentation.operatorGenerator a n k f) ≫
      MonoidalClosed.uncurry (F.toEnrichedFunctor.map
        (PointedCGWH.symmetricOperatorObj.{u, v} n) (PointedCGWH.symmetricOperatorObj.{u, v} k)) :=
  (PointedCGWH.SymmetricModulePresentation.reconstructedModule_arrowAction F a n k f).trans
    (reconstructedArrowAction_closed F a n k f)

end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
