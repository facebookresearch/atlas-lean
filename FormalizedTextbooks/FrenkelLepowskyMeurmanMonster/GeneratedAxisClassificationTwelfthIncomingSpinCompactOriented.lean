/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthIncomingSpinCompactSource

/-! A genuine central factor chooses the useful candidate tensor orientation without source assumptions. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative

/-- The full candidate Pauli is allowed one actual central sign. -/
def generatedTwelfthIncomingSpinCompactOrientedPauli (i : Fin 1) : Q :=
  qCentralInvolution * generatedTwelfthIncomingSpinCompactPauli i

/-- The explicitly oriented candidate is a product of genuine spin normalizer elements. -/
def generatedTwelfthIncomingSpinCompactOriented (i : Fin 1) : SpinHolomorph :=
  spinHolomorphIncl (generatedTwelfthIncomingSpinCompactOrientedPauli i) *
    monsterMonomialPermutationHolomorph (generatedTwelfthIncomingSpinCompactLeft i) *
    monsterMonomialDiagonalHolomorph
      (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactFirstPhaseRows i)) *
    ((generatedTwelfthIncomingSpinCompactHadamardWord i).map generatedNinthLowerSpinHadamard).prod *
    monsterMonomialDiagonalHolomorph
      (generatedTwelfthIncomingSpinCompactPhase (generatedTwelfthIncomingSpinCompactSecondPhaseRows i)) *
    monsterMonomialPermutationHolomorph (generatedTwelfthIncomingSpinCompactRight i)

/-- The chosen central factor retains precisely the full original source conjugation. -/
theorem generatedTwelfth_incoming_spin_compact_oriented_conjugation :
    spinConjugation (generatedTwelfthIncomingSpinCompactOriented 0) =
      spinConjugation (generatedTenthQWordFiber 9).val.1 := by
  have he : generatedTwelfthIncomingSpinCompactOriented 0 =
      spinHolomorphIncl qCentralInvolution * generatedTwelfthIncomingSpinCompact 0 := by
    simp only [generatedTwelfthIncomingSpinCompactOriented,
      generatedTwelfthIncomingSpinCompactOrientedPauli,
      generatedTwelfthIncomingSpinCompact, map_mul, mul_assoc]
  rw [he, map_mul]
  have hz : spinConjugation (spinHolomorphIncl qCentralInvolution) = 1 := by
    apply MulEquiv.ext
    intro q
    rw [spinConjugation_incl]
    change qCentral (1 : ZMod 2) * q * (qCentral 1)⁻¹ = q
    rw [← qCentral_commute, mul_assoc, mul_inv_cancel, mul_one]
  rw [hz, one_mul, generatedTwelfth_incoming_spin_compact_source_conjugation]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
