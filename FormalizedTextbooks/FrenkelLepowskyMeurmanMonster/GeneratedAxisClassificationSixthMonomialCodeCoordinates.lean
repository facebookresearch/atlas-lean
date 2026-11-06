/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthMonomialMaskData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthShortPhysical

/-! The original monomial spin coordinate rows act on the genuine physical Golay encoder. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

set_option maxHeartbeats 4000000 in
-- Check the actual twelve code basis vectors at all 24 physical coordinates for four words.
/-- Each original source code-basis column pulls back to the target Golay generator. -/
theorem generatedSixth_monomial_code_basis_coordinates :
    ∀ k : Fin 4, ∀ a : Fin 12, ∀ i : Fin 24,
      (∑ b : Fin 12, (representativeMatrix (generatedSixthMonomialMaskCoordinateRows k)) b a *
        (golayGeneratorBit b (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) :
          ZMod 2)) = (golayGeneratorBit a i : ZMod 2) := by
  decide +kernel

/-- The source code transform is correct for every binary code coefficient vector. -/
theorem generatedSixth_monomial_code_coordinates (k : Fin 4) (c : SpinIndex) (i : Fin 24) :
    golayEncoder ((representativeMatrix (generatedSixthMonomialMaskCoordinateRows k)) *ᵥ c)
      (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) =
    golayEncoder c i := by
  change (∑ b : Fin 12,
    (∑ a : Fin 12, (representativeMatrix (generatedSixthMonomialMaskCoordinateRows k)) b a * c a) *
      (golayGeneratorBit b (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) :
        ZMod 2)) = ∑ a : Fin 12, c a * (golayGeneratorBit a i : ZMod 2)
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = c a * ∑ b : Fin 12,
        (representativeMatrix (generatedSixthMonomialMaskCoordinateRows k)) b a *
          (golayGeneratorBit b
            (sixthFrameOrbitSpatialInput (Fin.natAdd 10 (Fin.castAdd 2 k)) i) : ZMod 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = _ := by rw [generatedSixth_monomial_code_basis_coordinates]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
