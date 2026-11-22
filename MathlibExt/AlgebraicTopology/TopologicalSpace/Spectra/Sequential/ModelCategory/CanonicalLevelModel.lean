/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Sequential.Basic
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNativeConstruction
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHSpherePowers
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHClosedChainSmallness
import MathlibExt.Topology.Category.CGWH.Limits

/-!
# The native canonical projective level constructor on the original sequential carrier

Native sphere-coordinate Hom tensors and the original source-colimit witnesses
specialize the shared enriched projective factory on the canonical functor carrier.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory HomotopicalAlgebra Opposite
open HomotopicalAlgebra.EnrichedProjective
open scoped CGWH.limits CGWH.modelCategory

namespace PointedCGWH.Spectra.Sequential

attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory

private theorem pointedSmallLimits : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasLimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasLimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

private theorem pointedSmallColimits : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{v, v} PointedCGWH.{u, v} := inferInstance
  exact hasColimitsOfSizeShrink.{0, 0} PointedCGWH.{u, v}

attribute [local instance] pointedSmallLimits pointedSmallColimits

/-- Every complete sphere-coordinate index Hom object is cofibrant. -/
theorem hom_isCofibrant (a b : Index.{u, v}) :
    IsCofibrant (a ⟶[PointedCGWH.{u, v}] b) := by
  change IsCofibrant
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom PointedCGWH.sphereOne a b)
  by_cases h : a.degree ≤ b.degree
  · rw [CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_le _ _ _ h]
    exact PointedCGWH.modelCategory.tensorPowObj_sphereOne_isCofibrant _
  · rw [CategoryTheory.SequentialSpectrum.EnrichedIndex.indexHom_of_gt _ _ _
      (Nat.lt_of_not_ge h)]
    change Cofibration (initial.to (⊥_ PointedCGWH.{u, v}))
    have hId : (initial.to (⊥_ PointedCGWH.{u, v})) = 𝟙 _ :=
      initialIsInitial.hom_ext _ _
    rw [hId]
    infer_instance

/-- Right tensor by an actual index Hom preserves the original base cofibration. -/
theorem homTensor_mem_cofibrations (a b : Index.{u, v})
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : cofibrations PointedCGWH.{u, v} f) :
    cofibrations PointedCGWH.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  let H := a ⟶[PointedCGWH.{u, v}] b
  let _ : IsCofibrant H := hom_isCofibrant a b
  have hLeft : cofibrations PointedCGWH.{u, v} (H ◁ f) :=
    IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_cofibrations H f hf
  have hSquare : (f ▷ H) ≫ (β_ Y H).hom = (β_ X H).hom ≫ (H ◁ f) :=
    BraidedCategory.braiding_naturality_left f H
  exact ((cofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (Arrow.isoMk (β_ X H) (β_ Y H) hSquare.symm)).mpr hLeft

/-- Right tensor by an actual index Hom preserves the original base trivial cofibration. -/
theorem homTensor_mem_trivialCofibrations (a b : Index.{u, v})
    {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (hf : trivialCofibrations PointedCGWH.{u, v} f) :
    trivialCofibrations PointedCGWH.{u, v} (f ▷ (a ⟶[PointedCGWH.{u, v}] b)) := by
  let H := a ⟶[PointedCGWH.{u, v}] b
  let _ : IsCofibrant H := hom_isCofibrant a b
  have hLeft : trivialCofibrations PointedCGWH.{u, v} (H ◁ f) :=
    IsClosedSymmetricMonoidalModelCategory.whiskerLeft_mem_trivialCofibrations H f hf
  have hSquare : (f ▷ H) ≫ (β_ Y H).hom = (β_ X H).hom ≫ (H ◁ f) :=
    BraidedCategory.braiding_naturality_left f H
  exact ((trivialCofibrations PointedCGWH.{u, v}).arrow_mk_iso_iff
    (Arrow.isoMk (β_ X H) (β_ Y H) hSquare.symm)).mpr hLeft

attribute [local instance] Native.Construction.generatorOrderBot

/-- The actual native canonical constructor on the identical original sequential carrier. -/
@[instance_reducible]
def levelModel : ModelCategory Spectrum.{u, v} :=
  Native.Construction.modelCategory (A := Index.{u, v})

/-- The entire original weak class is evaluated on every actual enriched-index object. -/
theorem levelModel_weakEquivalences :
    levelModel.{u, v}.categoryWithWeakEquivalences.weakEquivalences =
      EvaluationTransfer.evaluationProperty
        (fun a : Index.{u, v} => EnrichedFunctorCat.evaluation a)
        (weakEquivalences PointedCGWH.{u, v}) :=
  Native.Construction.weakEquivalences_eq

/-- The original full fibration class is evaluated on every actual enriched-index object. -/
theorem levelModel_fibrations :
    levelModel.{u, v}.categoryWithFibrations.fibrations =
      EvaluationTransfer.evaluationProperty
        (fun a : Index.{u, v} => EnrichedFunctorCat.evaluation a)
        (fibrations PointedCGWH.{u, v}) :=
  Native.Construction.fibrations_eq

/-- The canonical weak class is detected by every original native level map. -/
theorem levelModel_weakEquivalences_iff
    {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    (levelModel.{u, v}).categoryWithWeakEquivalences.weakEquivalences f ↔
      ∀ n : ℕ, weakEquivalences PointedCGWH.{u, v}
        (CategoryTheory.Spectra.Sequential.levelMap f n) := by
  rw [levelModel_weakEquivalences, EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    exact h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
  · intro h a
    exact h a.degree

/-- The canonical fibration class is detected by every original native level map. -/
theorem levelModel_fibrations_iff
    {X Y : Spectrum.{u, v}} (f : X ⟶ Y) :
    (levelModel.{u, v}).categoryWithFibrations.fibrations f ↔
      ∀ n : ℕ, fibrations PointedCGWH.{u, v}
        (CategoryTheory.Spectra.Sequential.levelMap f n) := by
  rw [levelModel_fibrations, EvaluationTransfer.evaluationProperty_iff]
  constructor
  · intro h n
    exact h (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)
  · intro h a
    exact h a.degree

/-- The original full cofibration class retains the unchanged original I generators. -/
theorem levelModel_cofibrations :
    levelModel.{u, v}.categoryWithCofibrations.cofibrations =
      (generators (A := Index.{u, v}) PointedCGWH.cofibrantGenerationData.{u, v}.I).rlp.llp :=
  Native.Construction.cofibrations_eq

/-- The original full trivial-fibration class is the actual evaluated intersection. -/
theorem levelModel_trivialFibrations :
    let _ : ModelCategory Spectrum.{u, v} := levelModel
    trivialFibrations Spectrum.{u, v} =
      EvaluationTransfer.evaluationProperty
        (fun a : Index.{u, v} => EnrichedFunctorCat.evaluation a)
        (trivialFibrations PointedCGWH.{u, v}) :=
  Native.Construction.trivialFibrations_eq

/-- The original full trivial-cofibration class retains the unchanged original J generators. -/
theorem levelModel_trivialCofibrations :
    let _ : ModelCategory Spectrum.{u, v} := levelModel
    trivialCofibrations Spectrum.{u, v} =
      (generators (A := Index.{u, v}) PointedCGWH.cofibrantGenerationData.{u, v}.J).rlp.llp :=
  Native.Construction.trivialCofibrations_eq

/-- Both complete original same-cardinal factorization systems are actual constructor outputs. -/
theorem levelModel_functorialFactorizations :
    let _ : ModelCategory Spectrum.{u, v} := levelModel
    MorphismProperty.HasFunctorialFactorization (cofibrations Spectrum.{u, v})
        (trivialFibrations Spectrum.{u, v}) ∧
      MorphismProperty.HasFunctorialFactorization (trivialCofibrations Spectrum.{u, v})
        (fibrations Spectrum.{u, v}) :=
  Native.Construction.functorialFactorizations

/-- The actual original canonical free/evaluation adjunction is Quillen at every degree. -/
theorem freeAtEvaluation_isQuillenAdjunction (n : ℕ) :
    let _ : ModelCategory Spectrum.{u, v} := levelModel
    (CategoryTheory.Spectra.Sequential.freeAtEvaluationAdjunction
      PointedCGWH.sphereOne.{u, v} n).IsQuillenAdjunction :=
  Native.Construction.freeAtEvaluation_isQuillenAdjunction
    (CategoryTheory.SequentialSpectrum.EnrichedIndex.degree PointedCGWH.sphereOne n)

end PointedCGWH.Spectra.Sequential
