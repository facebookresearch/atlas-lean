/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationPairTransition
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleOmegaConjugacy

/-! The genuine secondary feasible axis is an original plus-pair signed-short axis.
Its actual 93,150-vector orbit therefore supplies a finite physical short-coordinate
domain for the next feasible transition column. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Actual triality takes the opposite minus-pair axis to the original plus-pair axis. -/
theorem generatedFeasibleSecondaryAxis_eq_short (p : Fin 276) :
    generatedFeasibleSecondaryAxis p = conwayShortAxis (Sum.inl (1, p)) 1 := by
  rw [generatedFeasibleSecondaryAxis, generatedAxis_triality_pair_exact]
  norm_num

/-- The entire actual secondary feasible orbit lies among the original signed-short axes. -/
theorem generatedFeasibleSecondaryLocalOrbit_subset_signed (p : Fin 276) :
    generatedFeasibleSecondaryLocalOrbit p ⊆ generatedSignedShortAxes := by
  rintro x ⟨h, rfl⟩
  rw [generatedFeasibleSecondaryAxis_eq_short]
  have hx : rhoLocal h.val (conwayShortAxis (Sum.inl (1, p)) 1) ∈
      generatedAxisLocalOrbit (Sum.inl (1, p)) 1 := ⟨h.val, rfl⟩
  rwa [generatedAxisLocalOrbit_eq_signed] at hx

/-- Actual right transition cosets are the secondary orbit, with the inverse orbit map
matching the genuine right-coset convention. -/
def generatedFeasibleSecondaryOrbitCosetEquiv (p : Fin 276) :
    generatedFeasibleSecondaryLocalOrbit p ≃ generatedFeasibleTransitionCosetSpace p := by
  change MulAction.orbit (localAxisStabilizer p) (generatedFeasibleSecondaryAxis p) ≃ _
  have e := MulAction.orbitEquivQuotientStabilizer (localAxisStabilizer p)
    (generatedFeasibleSecondaryAxis p)
  rw [generatedFeasibleSecondaryAxis_stabilizer] at e
  exact e.trans (QuotientGroup.quotientRightRelEquivQuotientLeftRel
    (localFeasibleTransitionSubgroup p)).symm

/-- Full Ω conjugates and actual secondary feasible signed-short axes count the same inputs. -/
def generatedFeasibleSecondaryOmegaEquiv (p : Fin 276) :
    generatedFeasibleSecondaryLocalOrbit p ≃ generatedFeasibleOmegaConjugacyOrbit p :=
  (generatedFeasibleSecondaryOrbitCosetEquiv p).trans (generatedFeasibleOmegaConjugacyEquiv p)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
