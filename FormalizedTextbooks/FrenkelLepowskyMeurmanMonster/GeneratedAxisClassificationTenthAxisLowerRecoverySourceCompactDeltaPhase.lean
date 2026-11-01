/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactShiftedDelta

/-! Ungated complete paired sparse compact source formula; no finite cache proof is assumed. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
open scoped BigOperators
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- The genuine compact delta0 phase includes its full central Pauli coefficient and quadratic. -/
def generatedTenthSourceCompactDeltaZeroPhase (t : SpinIndex) : ZMod 2 :=
  spinPhase (generatedTenthAxisLowerRecoverySourceCompactPauli 0) t +
    monsterMonomialQuadratic (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows 0))
      ((generatedTenthAxisLowerRecoverySourceCompactLeft 0).symm
        (t + spinTranslation (generatedTenthAxisLowerRecoverySourceCompactPauli 0)))

/-- A shifted source delta retains the actual transformed full-Q central coefficient. -/
def generatedTenthSourceCompactDeltaPhase (a t : SpinIndex) : ZMod 2 :=
  let q := generatedTenthAxisLowerRecoverySourceCompactQImage 0
    (generatedTenthSourceCompactTranslationQ a)
  spinPhase q t + generatedTenthSourceCompactDeltaZeroPhase (t + spinTranslation q)

private theorem permutation_delta (E : SpinIndex ≃ₗ[ZMod 2] SpinIndex) :
    (monsterMonomialPermutationHolomorph E).val (Pi.single (0 : SpinIndex) (1 : ℝ)) =
      Pi.single (0 : SpinIndex) (1 : ℝ) := by
  funext t
  have hz : E.symm t = 0 ↔ t = 0 := by
    constructor
    · intro h
      have hh := congrArg E h
      simpa only [LinearEquiv.apply_symm_apply, map_zero] using hh
    · intro h
      rw [h, map_zero]
  change ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) (E.symm t) =
    ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) t
  simp [Pi.single_apply, hz]

private theorem diagonal_delta (M : Fin 12 → Fin 12 → ZMod 2) :
    (monsterMonomialDiagonalHolomorph M).val (Pi.single (0 : SpinIndex) (1 : ℝ)) =
      Pi.single (0 : SpinIndex) (1 : ℝ) := by
  funext t
  change qSign (monsterMonomialQuadratic M t) *
    ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) t =
      ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace) t
  by_cases ht : t = 0
  · subst t
    simp [monsterMonomialQuadratic, qSign]
  · simp [ht]

/-- All4096 original compact delta0 coefficients follow from the genuine full Hadamard word. -/
theorem generatedTenth_source_compact_delta_zero_phase (t : SpinIndex) :
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
      (Pi.single (0 : SpinIndex) (1 : ℝ)) t =
        qSign (generatedTenthSourceCompactDeltaZeroPhase t) / 64 := by
  have hword := generatedTenth_source_compact_anchor_uniform
  rw [generatedTenth_source_compact_anchor_word_eq] at hword
  change (spinRepresentation (generatedTenthAxisLowerRecoverySourceCompactPauli 0))
    ((monsterMonomialPermutationHolomorph
      (generatedTenthAxisLowerRecoverySourceCompactLeft 0)).val
      ((monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
        (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows 0))).val
        ((((generatedTenthAxisLowerRecoverySourceCompactHadamardWord 0).map
          generatedNinthLowerSpinHadamard).prod).val
          ((monsterMonomialDiagonalHolomorph (generatedTwelfthSpinCompactPhase
            (generatedTenthAxisLowerRecoverySourceCompactSecondPhaseRows 0))).val
            ((monsterMonomialPermutationHolomorph
              (generatedTenthAxisLowerRecoverySourceCompactRight 0)).val
              ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace)))))) t = _
  rw [permutation_delta, diagonal_delta, hword]
  change qSign (spinPhase (generatedTenthAxisLowerRecoverySourceCompactPauli 0) t) *
    (qSign (monsterMonomialQuadratic (generatedTwelfthSpinCompactPhase
      (generatedTenthAxisLowerRecoverySourceCompactFirstPhaseRows 0))
      ((generatedTenthAxisLowerRecoverySourceCompactLeft 0).symm
        (t + spinTranslation (generatedTenthAxisLowerRecoverySourceCompactPauli 0)))) *
          (1 / 64)) = _
  unfold generatedTenthSourceCompactDeltaZeroPhase
  rw [qSign_add]
  ring

/-- Every shifted original source delta has a full explicit phase formula. -/
theorem generatedTenth_source_compact_delta_phase (a t : SpinIndex) :
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val (Pi.single a (1 : ℝ)) t =
      qSign (generatedTenthSourceCompactDeltaPhase a t) / 64 := by
  rw [generatedTenth_source_compact_shifted_delta, generatedTenth_source_compact_delta_zero_phase]
  unfold generatedTenthSourceCompactDeltaPhase
  rw [qSign_add]
  ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
