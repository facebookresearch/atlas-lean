/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.ModelCategory.NativePresentation
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.FreeLevelCofibrations
import MathlibExt.CategoryTheory.SmallObject.Image
import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Original orthogonal projective cofibrations at every degree

The model is the canonical native level model with its original free families.
Actual native Hom cofibrancy makes their evaluated generator maps coefficient
cofibrations and trivial cofibrations. The original cardinal cell construction
and mapped Arrow retract then give the same inclusions for every projective
left map. All degree labels, coefficient maps and the caller's ordinal bottom
remain unchanged.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra MorphismProperty
open scoped CGWH.modelCategory

namespace PointedCGWH.Spectra.Orthogonal.NativePresentation

open CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalCoendThom

private theorem nativeColimits : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} CGWH.{u, v} := CGWH.instHasColimitsOfSize
  change HasColimitsOfSize.{v, v} (Under CGWH.point.{u, v})
  infer_instance

private theorem coefficientCofibrationCoproducts :
    (cofibrations PointedCGWH.{u, v}).IsStableUnderCoproducts.{v} :=
  IsStableUnderCoproducts.of_llp_eq (cofibrations PointedCGWH.{u, v})
    (trivialFibrations PointedCGWH.{u, v}) (trivialFibrations_llp PointedCGWH.{u, v})

private theorem coefficientTrivialCofibrationCoproducts :
    (trivialCofibrations PointedCGWH.{u, v}).IsStableUnderCoproducts.{v} :=
  IsStableUnderCoproducts.of_llp_eq (trivialCofibrations PointedCGWH.{u, v})
    (fibrations PointedCGWH.{u, v}) (fibrations_llp PointedCGWH.{u, v})

private theorem coefficientCofibrationTransfinite :
    (cofibrations PointedCGWH.{u, v}).IsStableUnderTransfiniteComposition.{v} := by
  rw [← trivialFibrations_llp PointedCGWH.{u, v}]
  infer_instance

private theorem coefficientTrivialCofibrationTransfinite :
    (trivialCofibrations PointedCGWH.{u, v}).IsStableUnderTransfiniteComposition.{v} := by
  rw [← fibrations_llp PointedCGWH.{u, v}]
  infer_instance

attribute [local instance] nativeColimits coefficientCofibrationCoproducts
  coefficientTrivialCofibrationCoproducts coefficientCofibrationTransfinite
  coefficientTrivialCofibrationTransfinite

private theorem boundaryTensor_mem_cofibrations
    (a b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedBoundaryInclusions.{u, v} f) :
    cofibrations PointedCGWH.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  have hBase := PointedCGWH.realizedBoundaryInclusions.{u, v}.le_llp_rlp f hf
  change PointedCGWH.cofibrantGenerationData.{u, v}.I.rlp.llp f at hBase
  rw [PointedCGWH.cofibrantGenerationData.{u, v}.I_rlp, trivialFibrations_llp] at hBase
  obtain ⟨n, rfl⟩ := ofIndex_surjective a
  obtain ⟨k, rfl⟩ := ofIndex_surjective b
  have h := nativeFreeMapValue_mem_cofibrations n k f hBase
  simpa only [nativeFreeMapValue, EnrichedFunctorCat.Free.coefficientMap_component] using h

private theorem hornTensor_mem_trivialCofibrations
    (a b : CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v})
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : PointedCGWH.realizedHornInclusions.{u, v} f) :
    trivialCofibrations PointedCGWH.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  have hBase := PointedCGWH.realizedHornInclusions.{u, v}.le_llp_rlp f hf
  change PointedCGWH.cofibrantGenerationData.{u, v}.J.rlp.llp f at hBase
  rw [PointedCGWH.cofibrantGenerationData.{u, v}.J_rlp, fibrations_llp] at hBase
  obtain ⟨n, rfl⟩ := ofIndex_surjective a
  obtain ⟨k, rfl⟩ := ofIndex_surjective b
  have h := nativeFreeMapValue_mem_trivialCofibrations n k f hBase
  simpa only [nativeFreeMapValue, EnrichedFunctorCat.Free.coefficientMap_component] using h

/-- Every original free boundary generator evaluates to a coefficient cofibration. -/
theorem boundaryGenerators_evaluation_le (k : CategoryTheory.Spectra.OrthogonalIndex) :
    boundaryGenerators.{u, v} ≤
      (cofibrations PointedCGWH.{u, v}).inverseImage (evaluation k) := by
  rw [boundaryGenerators_eq]
  exact EnrichedProjective.generators_evaluation_le
    PointedCGWH.realizedBoundaryInclusions (cofibrations PointedCGWH.{u, v})
    boundaryTensor_mem_cofibrations (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex k)

/-- Every original free horn generator evaluates to a coefficient trivial cofibration. -/
theorem hornGenerators_evaluation_le (k : CategoryTheory.Spectra.OrthogonalIndex) :
    hornGenerators.{u, v} ≤
      (trivialCofibrations PointedCGWH.{u, v}).inverseImage (evaluation k) := by
  rw [hornGenerators_eq]
  exact EnrichedProjective.generators_evaluation_le
    PointedCGWH.realizedHornInclusions (trivialCofibrations PointedCGWH.{u, v})
    hornTensor_mem_trivialCofibrations (CategoryTheory.Spectra.OrthogonalOperatorIndex.ofIndex k)

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

omit B in
private theorem evaluationContinuous (k : CategoryTheory.Spectra.OrthogonalIndex) :
    PreservesWellOrderContinuousOfShape realizedGeneratorCardinal.{v}.ord.ToType
      (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
        (OrthogonalOperatorIndex.ofIndex.{u, v} k)) where
  preservesColimitsOfShape _ _ := inferInstance

attribute [local instance] evaluationContinuous

local instance : Fact realizedGeneratorCardinal.{v}.IsRegular :=
  ⟨isRegular_realizedGeneratorCardinal.{v}⟩

/-- The actual cardinal boundary-cell endpoint is a cofibration at every original degree. -/
theorem boundaryCardinalCells_levels {F G : Carrier.{u, v}} (f : F ⟶ G)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => boundaryGenerators.{u, v}.homFamily)
      f) :
    ∀ k : CategoryTheory.Spectra.OrthogonalIndex,
      cofibrations PointedCGWH.{u, v} (levelMap f k) :=
  fun k => c.map_mem_of_le
    (EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex k)) boundaryGenerators
    (cofibrations PointedCGWH.{u, v}) (boundaryGenerators_evaluation_le k)

/-- The actual cardinal horn-cell endpoint is trivial at every original degree. -/
theorem hornCardinalCells_levels {F G : Carrier.{u, v}} (f : F ⟶ G)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => hornGenerators.{u, v}.homFamily) f) :
    ∀ k : CategoryTheory.Spectra.OrthogonalIndex,
      trivialCofibrations PointedCGWH.{u, v} (levelMap f k) :=
  fun k => c.map_mem_of_le
    (EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex k)) hornGenerators
    (trivialCofibrations PointedCGWH.{u, v}) (hornGenerators_evaluation_le k)

/-- Every mapped boundary-cell transition retains its actual coefficient cofibration. -/
theorem boundaryCardinalCells_transitions {F G : Carrier.{u, v}} (f : F ⟶ G)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => boundaryGenerators.{u, v}.homFamily)
      f)
    {s t : realizedGeneratorCardinal.{v}.ord.ToType} (φ : s ⟶ t) :
    ∀ k : CategoryTheory.Spectra.OrthogonalIndex,
      cofibrations PointedCGWH.{u, v} (levelMap (c.F.map φ) k) :=
  fun k => c.map_map_mem_of_le
    (EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex k)) boundaryGenerators
    (cofibrations PointedCGWH.{u, v}) (boundaryGenerators_evaluation_le k) φ

/-- Every mapped horn-cell transition retains its actual coefficient trivial cofibration. -/
theorem hornCardinalCells_transitions {F G : Carrier.{u, v}} (f : F ⟶ G)
    (c : RelativeCellComplex.{v}
      (fun (_ : realizedGeneratorCardinal.{v}.ord.ToType) => hornGenerators.{u, v}.homFamily) f)
    {s t : realizedGeneratorCardinal.{v}.ord.ToType} (φ : s ⟶ t) :
    ∀ k : CategoryTheory.Spectra.OrthogonalIndex,
      trivialCofibrations PointedCGWH.{u, v} (levelMap (c.F.map φ) k) :=
  fun k => c.map_map_mem_of_le
    (EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex k)) hornGenerators
    (trivialCofibrations PointedCGWH.{u, v}) (hornGenerators_evaluation_le k) φ

omit B in
/-- Every cofibration of the same native projective model is a cofibration at all degrees. -/
theorem cofibrations_levelMap {F G : Carrier.{u, v}} (f : F ⟶ G) :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    cofibrations Carrier.{u, v} f →
      ∀ k : CategoryTheory.Spectra.OrthogonalIndex,
        cofibrations PointedCGWH.{u, v} (levelMap f k) := by
  let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
    EnrichedProjective.Native.Construction.generatorOrderBot
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  intro hf k
  rw [cofibrations_eq] at hf
  let _ : boundaryGenerators.{u, v}.IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := by
    rw [boundaryGenerators_eq]
    exact EnrichedProjective.Native.Construction.generatorsI_isCardinalForSmallObjectArgument
  exact (rlp_llp_le_inverseImage_of_cardinal_closure boundaryGenerators
    (cofibrations PointedCGWH.{u, v})
    (EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex k))
    realizedGeneratorCardinal.{v}
    (boundaryGenerators_evaluation_le k)) f hf

omit B in
/-- Every trivial cofibration of that same model is trivial at all original degrees. -/
theorem trivialCofibrations_levelMap {F G : Carrier.{u, v}} (f : F ⟶ G) :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    trivialCofibrations Carrier.{u, v} f →
      ∀ k : CategoryTheory.Spectra.OrthogonalIndex,
        trivialCofibrations PointedCGWH.{u, v} (levelMap f k) := by
  let _ : OrderBot realizedGeneratorCardinal.{v}.ord.ToType :=
    EnrichedProjective.Native.Construction.generatorOrderBot
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  intro hf k
  rw [trivialCofibrations_eq] at hf
  let _ : hornGenerators.{u, v}.IsCardinalForSmallObjectArgument
      realizedGeneratorCardinal.{v} := by
    rw [hornGenerators_eq]
    exact EnrichedProjective.Native.Construction.generatorsJ_isCardinalForSmallObjectArgument
  exact (rlp_llp_le_inverseImage_of_cardinal_closure hornGenerators
    (trivialCofibrations PointedCGWH.{u, v})
    (EnrichedFunctorCat.evaluation (OrthogonalOperatorIndex.ofIndex k))
    realizedGeneratorCardinal.{v}
    (hornGenerators_evaluation_le k)) f hf

omit B in
/-- Cofibrant objects of the same model have cofibrant levels in every original degree. -/
theorem isCofibrant_level (F : Carrier.{u, v}) :
    letI : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
    ∀ [IsCofibrant F] (k : CategoryTheory.Spectra.OrthogonalIndex),
      IsCofibrant (level F k) := by
  let _ : ModelCategory Carrier.{u, v} := PointedCGWH.Spectra.Orthogonal.levelModel
  intro _ k
  have hMap := cofibrations_levelMap (initial.to F) (mem_cofibrations (initial.to F)) k
  have hInitial := initialIsInitial.isInitialObj
    (EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
      (OrthogonalOperatorIndex.ofIndex k)) (⊥_ Carrier.{u, v})
  exact (isCofibrant_iff_of_isInitial
    ((EnrichedFunctorCat.evaluation (V := PointedCGWH.{u, v})
      (OrthogonalOperatorIndex.ofIndex k)).map (initial.to F)) hInitial).mpr
    ((HomotopicalAlgebra.cofibration_iff _).mpr hMap)

end PointedCGWH.Spectra.Orthogonal.NativePresentation
