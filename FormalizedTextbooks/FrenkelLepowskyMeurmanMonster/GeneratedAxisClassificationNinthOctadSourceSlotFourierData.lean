/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumeratorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Candidate sparse Fourier numerators retain the original octad Fourier matrix. The
actual signed source-numerator and source-word certificates are separate prerequisites. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- Original Fourier matrix evaluated on the checked eight-slot integer source numerators. -/
def generatedNinthFinalOctadSlotFastNumerator (o : Fin 759) (e : Fin 64) : ℤ :=
  ∑ j : Fin 8, trialityIntegerMatrix e (generatedNinthOctadSourceSlotSign o j) *
    generatedNinthOctadSlotNumeratorFast o j

/-- A source block contains at most two possibly nonzero slots. -/
def GeneratedNinthOctadTwoSlotShape (o : Fin 759) : Prop :=
  ∀ j : Fin 8, 2 ≤ j.val → generatedNinthOctadSlotNumeratorFast o j = 0

/-- Four nonzero source terms have zero original label XOR and negative sign product. -/
def GeneratedNinthOctadFourSlotShape (o : Fin 759) : Prop :=
  (∀ j : Fin 8, 4 ≤ j.val → generatedNinthOctadSlotNumeratorFast o j = 0) ∧
    |generatedNinthOctadSlotNumeratorFast o 0| = 2 ∧
    |generatedNinthOctadSlotNumeratorFast o 1| = 2 ∧
    |generatedNinthOctadSlotNumeratorFast o 2| = 2 ∧
    |generatedNinthOctadSlotNumeratorFast o 3| = 2 ∧
    trialityXor
      (trialityXor (generatedNinthOctadSourceSlotSign o 0)
        (generatedNinthOctadSourceSlotSign o 1))
      (trialityXor (generatedNinthOctadSourceSlotSign o 2)
        (generatedNinthOctadSourceSlotSign o 3)) = 0 ∧
    generatedNinthOctadSlotNumeratorFast o 0 * generatedNinthOctadSlotNumeratorFast o 1 *
      generatedNinthOctadSlotNumeratorFast o 2 * generatedNinthOctadSlotNumeratorFast o 3 = -16

/-- Each candidate slot has numerator magnitude at most two, including empty slots. -/
theorem generatedNinth_octad_slot_fast_abs_le_two (o : Fin 759) (j : Fin 8) :
    |generatedNinthOctadSlotNumeratorFast o j| ≤ 2 := by
  unfold generatedNinthOctadSlotNumeratorFast
  split_ifs <;> norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
