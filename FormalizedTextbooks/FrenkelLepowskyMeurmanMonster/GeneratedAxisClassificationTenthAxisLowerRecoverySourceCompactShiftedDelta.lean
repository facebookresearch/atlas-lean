/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactAnchorSpin

/-! Ungated genuine compact source binding; full central signs are retained. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency true
set_option maxRecDepth 100000

/-- The genuine positive translation has no modulation and no central correction. -/
def generatedTenthSourceCompactTranslationQ (a : SpinIndex) : Q :=
  ⟨ofAdd (Fin.append a (0 : SpinIndex)), 1⟩

/-- The positive translation takes the complete genuine delta0 vector to deltaa. -/
theorem generatedTenth_source_compact_translation_delta (a : SpinIndex) :
    spinRepresentation (generatedTenthSourceCompactTranslationQ a)
      (Pi.single (0 : SpinIndex) (1 : ℝ)) = Pi.single a (1 : ℝ) := by
  funext t
  have htrans : spinTranslation (generatedTenthSourceCompactTranslationQ a) = a := by
    funext i
    simp [spinTranslation, generatedTenthSourceCompactTranslationQ]
  have hmod : spinModulation (generatedTenthSourceCompactTranslationQ a) = 0 := by
    funext i
    simpa only [spinModulation, generatedTenthSourceCompactTranslationQ,
      toAdd_ofAdd] using Fin.append_right a (0 : SpinIndex) i
  have hp : spinPhase (generatedTenthSourceCompactTranslationQ a) t = 0 := by
    rw [spinPhase, hmod, spinDot_zero_left]
    rfl
  have haa : a + a = 0 := by
    ext i
    exact ZModModule.add_self (a i)
  have hz : t + a = 0 ↔ t = a := by
    constructor
    · intro h
      have hh := congrArg (fun x : SpinIndex => x + a) h
      simpa only [add_assoc, haa, add_zero, zero_add] using hh
    · intro h
      rw [h, haa]
  change qSign (spinPhase (generatedTenthSourceCompactTranslationQ a) t) *
    ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace)
      (t + spinTranslation (generatedTenthSourceCompactTranslationQ a)) =
        ((Pi.single a (1 : ℝ)) : SpinSpace) t
  rw [hp, htrans, qSign_zero, one_mul]
  simp [Pi.single_apply, hz]

/-- Genuine Pauli conjugation reduces every shifted delta coefficient to the delta0 image.
The complete original central phase is retained in the transformed Pauli element. -/
theorem generatedTenth_source_compact_shifted_delta_generic
    (s : SpinHolomorph) (a t : SpinIndex) :
    s.val (Pi.single a (1 : ℝ)) t =
      qSign (spinPhase (spinConjugation s (generatedTenthSourceCompactTranslationQ a)) t) *
        s.val (Pi.single (0 : SpinIndex) (1 : ℝ))
          (t + spinTranslation (spinConjugation s (generatedTenthSourceCompactTranslationQ a))) :=
            by
  have h := congrArg (fun e : SpinSpace ≃ₗ[ℝ] SpinSpace =>
    e (s.val ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace)))
      (spinConjugation_representation s (generatedTenthSourceCompactTranslationQ a))
  change spinRepresentation (spinConjugation s (generatedTenthSourceCompactTranslationQ a))
    (s.val ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace)) =
      s.val (spinRepresentation (generatedTenthSourceCompactTranslationQ a)
        (s.val.symm (s.val ((Pi.single (0 : SpinIndex) (1 : ℝ)) : SpinSpace)))) at h
  rw [LinearEquiv.symm_apply_apply, generatedTenth_source_compact_translation_delta] at h
  exact (congrFun h t).symm

/-- The actual twelve-Hadamard source word has a complete full-phase shifted-delta formula. -/
theorem generatedTenth_source_compact_hadamard_shifted_delta (a t : SpinIndex) :
    generatedTenthSourceCompactAnchorWord.val (Pi.single a (1 : ℝ)) t =
      qSign (spinPhase (spinConjugation generatedTenthSourceCompactAnchorWord
        (generatedTenthSourceCompactTranslationQ a)) t) / 64 := by
  rw [generatedTenth_source_compact_shifted_delta_generic,
    generatedTenth_source_compact_anchor_uniform]
  ring

/-- The complete genuine compact source product uses its exact full-Q phase and translation. -/
theorem generatedTenth_source_compact_shifted_delta (a t : SpinIndex) :
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val (Pi.single a (1 : ℝ)) t =
      qSign (spinPhase (generatedTenthAxisLowerRecoverySourceCompactQImage 0
        (generatedTenthSourceCompactTranslationQ a)) t) *
        (generatedTenthAxisLowerRecoverySourceCompactSpin 0).val
          (Pi.single (0 : SpinIndex) (1 : ℝ))
          (t + spinTranslation (generatedTenthAxisLowerRecoverySourceCompactQImage 0
            (generatedTenthSourceCompactTranslationQ a))) := by
  have h := generatedTenth_source_compact_shifted_delta_generic
    (generatedTenthAxisLowerRecoverySourceCompactSpin 0) a t
  simpa only [generatedTenth_axis_lower_recovery_source_compact_conjugation] using h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
