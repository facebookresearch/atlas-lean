/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedFeasibleContainingNewDestinationSeparation

/-! Complete original encoder octad intersection certificates relative to source label 2063. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 20000

/-- Original occupied code coordinates within the original containing source support. -/
def generatedFeasibleContainingCodeSelectedWeight (d : Fin 4096) : ℕ :=
  ∑ i : Fin 24, if i.val < 8 ∧
    (golayEncodedMask d.val).testBit i.val then 1 else 0

/-- All original code labels for incident octads of the given actual intersection size. -/
def generatedFeasibleContainingSelectedIncidentCodes (k : Fin 3) : Finset (Fin 4096) :=
  golayOctads.filter fun d =>
    ((golayEncodedMask d.val).testBit 0 = true ∧
      (golayEncodedMask d.val).testBit 1 = true) ∧
        generatedFeasibleContainingCodeSelectedWeight d = (![2, 4, 8] : Fin 3 → ℕ) k

/-- All original code labels for outside octads of the given actual intersection size. -/
def generatedFeasibleContainingSelectedOutsideCodes (k : Fin 3) : Finset (Fin 4096) :=
  golayOctads.filter fun d =>
    ((golayEncodedMask d.val).testBit 0 = false ∧
      (golayEncodedMask d.val).testBit 1 = false) ∧
        generatedFeasibleContainingCodeSelectedWeight d = (![0, 2, 4] : Fin 3 → ℕ) k

set_option maxHeartbeats 120000000 in
-- Check all original 4096 code labels and all three incident intersection sizes.
/-- Complete original encoder gate for the incident intersection counts. -/
theorem generatedFeasibleContainingSelectedIncidentCodes_card (k : Fin 3) :
    (generatedFeasibleContainingSelectedIncidentCodes k).card =
      (![16, 60, 1] : Fin 3 → ℕ) k := by
  have h : ∀ k : Fin 3, (generatedFeasibleContainingSelectedIncidentCodes k).card =
      (![16, 60, 1] : Fin 3 → ℕ) k := by decide +kernel
  exact h k

set_option maxHeartbeats 120000000 in
-- Check all original 4096 code labels and all three outside intersection sizes.
/-- Complete original encoder gate for the outside intersection counts. -/
theorem generatedFeasibleContainingSelectedOutsideCodes_card (k : Fin 3) :
    (generatedFeasibleContainingSelectedOutsideCodes k).card =
      (![30, 240, 60] : Fin 3 → ℕ) k := by
  have h : ∀ k : Fin 3, (generatedFeasibleContainingSelectedOutsideCodes k).card =
      (![30, 240, 60] : Fin 3 → ℕ) k := by decide +kernel
  exact h k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
