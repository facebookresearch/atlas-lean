/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerLeftClassRecognition
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallLimits
import MathlibExt.AlgebraicTopology.SimplicialCategory.CarrierSmallColimits
import Mathlib.AlgebraicTopology.ModelCategory.Basic

/-!
# The genuine original varying-object Bergner model structure

The original C0 generating cofibrations, original complete Hom-Kan and
component-isofibration class, and original Dwyer–Kan weak class satisfy
the model axioms. The actual native combined A1/A2 small-object
factorization and genuine simultaneous/transfinite acyclicity give the
second weak factorization system. The first is the existing actual
boundary/object-addition system. All objects and enriched Hom maps vary.

This proves the model-structure theorem of Bergner, v2, Theorem 1.1,
with its original F1/F2 and W1/W2 conditions. No coherent Quillen
equivalence or higher-height strictification is asserted here.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.Bergner

/-- The actual original varying-object Bergner model uses exactly its original C0, full F1/F2 and DK classes. -/
@[instance_reducible]
def modelCategory : ModelCategory Carrier.{u} := by
  let _ : CategoryWithFibrations Carrier.{u} := ⟨localFibrations⟩
  let _ : CategoryWithCofibrations Carrier.{u} := ⟨cofibrations⟩
  let _ : CategoryWithWeakEquivalences Carrier.{u} := ⟨EnrichedDwyerKan.weakEquivalences⟩
  let _ : HasFiniteLimits Carrier.{u} := inferInstance
  let _ : HasFiniteColimits Carrier.{u} := { out _J _ _ := inferInstance }
  let _ : (HomotopicalAlgebra.weakEquivalences Carrier.{u}).HasTwoOutOfThreeProperty := by
    change EnrichedDwyerKan.weakEquivalences.HasTwoOutOfThreeProperty
    infer_instance
  let _ : MorphismProperty.IsWeakFactorizationSystem
      (HomotopicalAlgebra.cofibrations Carrier.{u}) (HomotopicalAlgebra.trivialFibrations Carrier.{u}) := by
    change MorphismProperty.IsWeakFactorizationSystem cofibrations
      (localFibrations ⊓ EnrichedDwyerKan.weakEquivalences)
    exact BoundaryFactorization.weakFactorizationSystem_original
  let _ : MorphismProperty.IsWeakFactorizationSystem
      (HomotopicalAlgebra.trivialCofibrations Carrier.{u}) (HomotopicalAlgebra.fibrations Carrier.{u}) := by
    change MorphismProperty.IsWeakFactorizationSystem
      (cofibrations ⊓ EnrichedDwyerKan.weakEquivalences) localFibrations
    exact OriginalBergnerIntervalFamily.originalTrivialCofibrationFibrationWFS
  exact ModelCategory.mk' Carrier.{u}

/-- The genuine model weak maps are precisely the same original full-Hom and component-object DK weak maps. -/
theorem weakEquivalence_iff_original {C D : Carrier.{u}} (f : C ⟶ D) :
    let _ : ModelCategory Carrier.{u} := modelCategory
    WeakEquivalence f ↔ EnrichedDwyerKan.weakEquivalences f := by
  dsimp only
  rw [HomotopicalAlgebra.weakEquivalence_iff]
  rfl

/-- The genuine model fibrations are precisely the same original complete Hom-Kan/component-isofibration maps. -/
theorem fibration_iff_original {C D : Carrier.{u}} (f : C ⟶ D) :
    let _ : ModelCategory Carrier.{u} := modelCategory
    Fibration f ↔ localFibrations f := by
  dsimp only
  rw [HomotopicalAlgebra.fibration_iff]
  rfl

/-- The genuine model cofibrations are the original object-addition and all-boundary generator left class. -/
theorem cofibration_iff_original {C D : Carrier.{u}} (f : C ⟶ D) :
    let _ : ModelCategory Carrier.{u} := modelCategory
    Cofibration f ↔ generatingCofibrations.rlp.llp f := by
  dsimp only
  rw [HomotopicalAlgebra.cofibration_iff]
  rfl

/-- The genuine model trivial cofibrations are precisely the same complete original A1/A2 left class. -/
theorem trivialCofibration_iff_original {C D : Carrier.{u}} (f : C ⟶ D) :
    let _ : ModelCategory Carrier.{u} := modelCategory
    (Cofibration f ∧ WeakEquivalence f) ↔
      OriginalBergnerIntervalFamily.generatingTrivialCofibrations.rlp.llp f := by
  dsimp only
  rw [HomotopicalAlgebra.cofibration_iff, HomotopicalAlgebra.weakEquivalence_iff]
  change (cofibrations ⊓ EnrichedDwyerKan.weakEquivalences) f ↔ _
  rw [← OriginalBergnerIntervalFamily.combinedLeft_eq_cofibration_weak]

/-- The genuine model trivial fibrations are precisely the same original object-surjective full-Hom boundary right
class. -/
theorem trivialFibration_iff_original {C D : Carrier.{u}} (f : C ⟶ D) :
    let _ : ModelCategory Carrier.{u} := modelCategory
    (Fibration f ∧ WeakEquivalence f) ↔ generatingCofibrations.rlp f := by
  dsimp only
  rw [HomotopicalAlgebra.fibration_iff, HomotopicalAlgebra.weakEquivalence_iff]
  change (localFibrations ⊓ EnrichedDwyerKan.weakEquivalences) f ↔ _
  rw [← generatingCofibrations_rlp_eq_localFibrations_inf_weak]

end CategoryTheory.SimplicialEnrichment.Bergner
