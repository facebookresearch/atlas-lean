/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.OriginalEnrichedProjective
public import MathlibExt.CategoryTheory.Enriched.PointwiseCartesian
public import MathlibExt.AlgebraicTopology.ModelCategory.PushoutProductGeneratorCriterion

/-!
# The actual genuine pointwise projective tensor model

A cartesian closed coefficient category supplies the compatible enriched
diagonal. The pointwise tensor and its true Kan/end internal Hom are
constructed. Source products of the literal original generators and genuine
unit cofibrancy give the monoidal model axioms on the same original model.
The unit witness retains the original fixed-cardinal factor object and map.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
noncomputable section

universe w uA uV vV

open CategoryTheory Limits MorphismProperty MonoidalCategory

namespace HomotopicalAlgebra.OriginalEnrichedPointwiseMonoidal

variable {V : Type uV} [Category.{vV} V] [CartesianMonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V] [ModelCategory V]
  {A : Type uA} [EnrichedCategory V A]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [Small.{w} A] [LocallySmall.{w} V] [HasColimitsOfSize.{w, w} V]
  [HasProducts.{uA} V] [HasEqualizers V]
  (d : CofibrantGenerationData V κ)
  (s : OriginalEnrichedProjective.SourceConditions (A := A) d)

/-- Source tests use only the original free I/J maps and the actual pointwise tensor. -/
structure GeneratorConditions : Prop where
  II :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
    PushoutProductLe (EnrichedProjective.generators (A := A) d.I)
      (EnrichedProjective.generators (A := A) d.I)
      (EnrichedProjective.generators (A := A) d.I).rlp.llp
  JI :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
    PushoutProductLe (EnrichedProjective.generators (A := A) d.J)
      (EnrichedProjective.generators (A := A) d.I)
      (EnrichedProjective.generators (A := A) d.J).rlp.llp
  unit :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
    (EnrichedProjective.generators (A := A) d.I).rlp.llp (initial.to (𝟙_ (EnrichedFunctorCat V A)))

/-- Construct all pointwise monoidal model laws with the original chosen unit factor. -/
theorem monoidalModel (h : GeneratorConditions (A := A) d) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
    letI : BraidedCategory (EnrichedFunctorCat V A) := BraidedCategory.ofCartesianMonoidalCategory
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalClosed (V := V) (A := A)
    IsClosedSymmetricMonoidalModelCategory (EnrichedFunctorCat V A) := by
  let _ : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
  let _ := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
  let _ : BraidedCategory (EnrichedFunctorCat V A) := BraidedCategory.ofCartesianMonoidalCategory
  let _ := EnrichedFunctorCat.PointwiseCartesian.monoidalClosed (V := V) (A := A)
  let E := OriginalEnrichedProjective.generationData d s
  let _ : IsCofibrant (𝟙_ (EnrichedFunctorCat V A)) := by
    apply (isCofibrant_iff _).mpr
    apply (cofibration_iff _).mpr
    rw [EnrichedProjective.cofibrations_eq d s.I_tensor s.J_tensor s.I_source s.J_source]
    exact h.unit
  apply E.monoidalModelOfGeneratorProducts
  · change PushoutProductLe (EnrichedProjective.generators (A := A) d.I)
      (EnrichedProjective.generators (A := A) d.I) (cofibrations (EnrichedFunctorCat V A))
    rw [EnrichedProjective.cofibrations_eq d s.I_tensor s.J_tensor s.I_source s.J_source]
    exact h.II
  · change PushoutProductLe (EnrichedProjective.generators (A := A) d.J)
      (EnrichedProjective.generators (A := A) d.I) (trivialCofibrations (EnrichedFunctorCat V A))
    rw [EnrichedProjective.trivialCofibrations_eq d
      s.I_tensor s.J_tensor s.I_source s.J_source]
    exact h.JI
  · exact (OriginalEnrichedProjective.cofibrantFactorizationData d s).factorizationData
      (initial.to (𝟙_ (EnrichedFunctorCat V A)))

/-- Retain the original unit replacement as data, including its actual middle object and right
factor. -/
def unitWitness (h : GeneratorConditions (A := A) d) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
    letI : BraidedCategory (EnrichedFunctorCat V A) := BraidedCategory.ofCartesianMonoidalCategory
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalClosed (V := V) (A := A)
    MonoidalUnitAxiomWitness (EnrichedFunctorCat V A) := by
  letI : ModelCategory (EnrichedFunctorCat V A) :=
    EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
  letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
  letI : BraidedCategory (EnrichedFunctorCat V A) := BraidedCategory.ofCartesianMonoidalCategory
  letI := EnrichedFunctorCat.PointwiseCartesian.monoidalClosed (V := V) (A := A)
  let _ : IsCofibrant (𝟙_ (EnrichedFunctorCat V A)) := by
    apply (isCofibrant_iff _).mpr
    apply (cofibration_iff _).mpr
    rw [EnrichedProjective.cofibrations_eq d s.I_tensor s.J_tensor s.I_source s.J_source]
    exact h.unit
  let m := monoidalModel d s h
  let pp : MonoidalPushoutProductAxiom (EnrichedFunctorCat V A) :=
    ⟨m.cofibration_pushoutProduct, m.trivial_pushoutProduct_left, m.trivial_pushoutProduct_right⟩
  exact pp.unitAxiomWitnessOfFunctorialFactorization
    (OriginalEnrichedProjective.cofibrantFactorizationData d s)

/-- The unit witness uses the exact original fixed-cardinal factor object. -/
theorem unitWitness_Q (h : GeneratorConditions (A := A) d) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
    letI : BraidedCategory (EnrichedFunctorCat V A) := BraidedCategory.ofCartesianMonoidalCategory
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalClosed (V := V) (A := A)
    (unitWitness d s h).Q = (OriginalEnrichedProjective.cofibrantFactorizationData d s).Z.obj
      (Arrow.mk (initial.to (𝟙_ (EnrichedFunctorCat V A)))) := rfl

/-- The same original factor's entire right map is the unit replacement map. -/
theorem unitWitness_q (h : GeneratorConditions (A := A) d) :
    letI : ModelCategory (EnrichedFunctorCat V A) :=
      EnrichedProjective.modelCategory d s.I_tensor s.J_tensor s.I_source s.J_source
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalCategory (V := V) (A := A)
    letI : BraidedCategory (EnrichedFunctorCat V A) := BraidedCategory.ofCartesianMonoidalCategory
    letI := EnrichedFunctorCat.PointwiseCartesian.monoidalClosed (V := V) (A := A)
    (unitWitness d s h).q = (OriginalEnrichedProjective.cofibrantFactorizationData d s).p.app
      (Arrow.mk (initial.to (𝟙_ (EnrichedFunctorCat V A)))) := rfl

end HomotopicalAlgebra.OriginalEnrichedPointwiseMonoidal
