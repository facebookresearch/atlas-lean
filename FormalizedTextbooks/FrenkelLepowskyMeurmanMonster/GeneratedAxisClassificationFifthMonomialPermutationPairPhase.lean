/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortPhaseFast

/-! Exact original preferred-pair phase, including the correcting Pauli character. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Pauli character on the preferred physical pair syndrome. -/
def generatedFifthPermutationPairPhase (k : Fin 6) (a b : Fin 24) : ZMod 2 :=
  spinDot (golayLabelCoefficients (generatedFifthMonomialPermutationTranslation k))
    (fun i => (golayGeneratorBit i a : ZMod 2) + (golayGeneratorBit i b : ZMod 2))

private theorem phase_zero (k : Fin 6) :
    generatedFifthMonomialPermutationModelPhase k 0 = 0 := by
  simp [generatedFifthMonomialPermutationModelPhase, monsterMonomialQuadratic]

private theorem phase_pair (k : Fin 6) (s : Fin 2) :
    generatedFifthMonomialPermutationModelPhase k
      (if s = 0 then 0 else Pi.single 11 1) = 0 := by
  split_ifs
  · exact phase_zero k
  · have h := generatedFifth_permutation_phase_omega k 0 1
    rw [zero_add, one_smul, phase_zero] at h
    exact h

/-- The complete actual pair phase equals the original physical correcting-code character. -/
theorem generatedFifth_permutation_pair_phase (k : Fin 6) (s : Fin 2)
    (p : {p : Fin 24 × Fin 24 // p.1 < p.2}) :
    generatedFifthMonomialPermutationShortPhase k (Sum.inl (s, p)) =
      generatedFifthPermutationPairPhase k p.val.1 p.val.2 := by
  rw [generatedFifthMonomialPermutationShortPhase]
  simp only [generatedFifthXiShortCachedQ, generatedAxisFourthQFromSpin_translation]
  rw [phase_pair, zero_add]
  simp only [generatedFifthSignCachedShortPhase, qBeta_spin_coordinates,
    generatedFifthXiShortCachedQ, generatedAxisFourthQFromSpin_translation,
    generatedAxisFourthQFromSpin_modulation]
  have hz : spinDot (if s = 0 then 0 else Pi.single 11 1)
      (spinModulation (generatedFifthMonomialPermutationCorrection k)) = 0 := by
    split_ifs
    · simp [spinDot]
    · rw [spinDot_comm, generatedFifth_permutation_correction_omega]
  rw [hz, add_zero]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
