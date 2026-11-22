/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerNativeFactorization
import MathlibExt.AlgebraicTopology.SimplicialCategory.BergnerBoundaryFactorization
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanRetracts

/-!
# Exact original combined left-class recognition

The same original native countable factorization and its full arrow
retract prove that the combined-generator left class is precisely
the original C0/Dwyer–Kan weak intersection. The converse uses the
same original right map, full fibration recognition and two out of
three; no global model structure is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra

namespace CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily

/-- Every original combined-generator left map is genuinely C0 cofibrant and DK weak. -/
theorem combinedLeft_le_cofibration_weak :
    generatingTrivialCofibrations.{u}.rlp.llp ≤
      Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences := by
  intro C D f hf
  let d := NativeFactorization.data f
  let _ : HasLiftingProperty f d.p := hf d.p (NativeFactorization.right_mem f)
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty d.fac) d.hi

/-- Every actual original C0 and DK weak map belongs to the same complete original combined left class. -/
theorem cofibration_weak_le_combinedLeft :
    Bergner.cofibrations.{u} ⊓ EnrichedDwyerKan.weakEquivalences ≤
      generatingTrivialCofibrations.rlp.llp := by
  intro C D f hf
  let d := NativeFactorization.data f
  have hw : EnrichedDwyerKan.weakEquivalences d.p :=
    EnrichedDwyerKan.weakEquivalences.of_precomp d.i d.p d.hi.2 (d.fac.symm ▸ hf.2)
  have hp : Bergner.generatingCofibrations.rlp d.p := by
    rw [Bergner.generatingCofibrations_rlp_eq_localFibrations_inf_weak]
    exact ⟨d.hp, hw⟩
  let _ : HasLiftingProperty f d.p := hf.1 d.p hp
  exact MorphismProperty.of_retract (RetractArrow.ofLeftLiftingProperty d.fac)
    (NativeFactorization.left_mem f)

/-- The SAME complete original combined-generator left class is exactly the original C0/DK-weak intersection. -/
theorem combinedLeft_eq_cofibration_weak :
    generatingTrivialCofibrations.{u}.rlp.llp =
      Bergner.cofibrations ⊓ EnrichedDwyerKan.weakEquivalences :=
  le_antisymm combinedLeft_le_cofibration_weak cofibration_weak_le_combinedLeft

/-- The exact original weak-cofibration and full original fibration classes have a genuine weak factorization system. -/
theorem originalTrivialCofibrationFibrationWFS : MorphismProperty.IsWeakFactorizationSystem
    (Bergner.cofibrations.{u} ⊓ EnrichedDwyerKan.weakEquivalences) Bergner.localFibrations := by
  rw [← combinedLeft_eq_cofibration_weak, ← generatingTrivialCofibrations_rlp_eq]
  exact combinedWFS

end CategoryTheory.SimplicialEnrichment.OriginalBergnerIntervalFamily
