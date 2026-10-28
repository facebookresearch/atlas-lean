/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryFinalShortSourceTensor
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsPairCoordinates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.NortonUIntegerSpinBasic

/-! Ungated complete final-short source formula. Matrix and cache bindings remain explicit. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Normalized outgoing short formula retains every pair, octad, odd label, and zero. -/
def generatedTenthFinalShortSourceGenericFormula
    (M : Matrix (Fin 24) (Fin 24) ℚ) (C : GriessShortIndex → ℤ)
    (T : Fin 4096 → Fin 24 → ℚ) : GriessShortIndex → ℚ
  | Sum.inl (s, p) =>
      (if s = 0 then 128 else -128) *
        M (generatedAxisGlobalPairCoordinates p).1 (generatedAxisGlobalPairCoordinates p).2 +
      4 * ((C (Sum.inl (0, p)) : ℚ) - (C (Sum.inl (1, p)) : ℚ))
  | Sum.inr (Sum.inl (o, e)) =>
      ∑ f : Fin 64, (trialityIntegerMatrix e f : ℚ) * (C (Sum.inr (Sum.inl (o, f))) : ℚ)
  | Sum.inr (Sum.inr (d, i)) =>
      64 * (nortonUIntegerSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ℚ) *
        (T ⟨d.val, by omega⟩ i + T ⟨d.val + 2048, by omega⟩ i)

/-- The genuine positive middle-triality step has this entire rational short formula. -/
theorem generatedTenth_final_short_source_generic_actual
    (a : ConwayRawSpace) (M : Matrix (Fin 24) (Fin 24) ℚ)
    (C : GriessShortIndex → ℤ) (T : Fin 4096 → Fin 24 → ℚ)
    (hm : ∀ i j, a.1 i j = (M i j : ℝ))
    (hc : ∀ r, a.2.1 r = (C r : ℝ) / 16)
    (ht : ∀ k i, a.2.2 (golayLabelCoefficients k) i = (T k i : ℝ) / Real.sqrt 2)
    (r : GriessShortIndex) :
    128 * generatedAxisGlobalRawTrialityShort a r =
      (generatedTenthFinalShortSourceGenericFormula M C T r : ℝ) := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · simp only [generatedAxisGlobalRawTrialityShort, generatedTenthFinalShortSourceGenericFormula]
    rw [← generatedAxisGlobalPairCoordinates_actual p, hm, hc, hc]
    push_cast
    split_ifs <;> ring
  · simp only [generatedAxisGlobalRawTrialityShort, generatedTenthFinalShortSourceGenericFormula]
    push_cast
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    rw [hc]
    simp only [trialityRealMatrix, Matrix.smul_apply, Matrix.map_apply,
      Int.coe_castRingHom, smul_eq_mul]
    ring
  · simp only [generatedAxisGlobalRawTrialityShort, generatedTenthFinalShortSourceGenericFormula]
    rw [ht, ht]
    push_cast
    simp only [nortonUIntegerSign_real]
    have hn : Real.sqrt 2 ≠ 0 := by positivity
    field_simp [hn]
    ring_nf
    simp only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring

/-- The original incoming dictionary is bound through its complete actual source certificate. -/
theorem generatedTenth_final_short_source_incoming_C
    (h : GeneratedTenthRootTwoIncomingShortCertificate) (r : GriessShortIndex) :
    generatedAxisGlobalFifthRoot02Packet.2.1 r =
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient r : ℝ) / 16 := by
  have hc := generatedTenth_root_two_incoming_short_actual h r
  rw [generatedAxisGlobalFifthShortWordFiber_local,
    generatedAxisGlobalFifthRoot02Packet_actual] at hc
  exact hc

/-- Exact full final source formula from the Root02 incoming C and all eight incoming T factors. -/
def generatedTenthFinalShortSourceFormula (M : Matrix (Fin 24) (Fin 24) ℚ) :
    GriessShortIndex → ℚ :=
  generatedTenthFinalShortSourceGenericFormula M
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
    generatedTenthFinalShortSourceTensorQ

/-- All final Tenth short coefficients follow from the genuine inputs and matrix calibration. -/
theorem generatedTenth_final_short_source_formula_actual
    (h : GeneratedTenthRootTwoIncomingShortCertificate)
    (M : Matrix (Fin 24) (Fin 24) ℚ)
    (hm : ∀ i j, generatedAxisGlobalFifthRoot02Packet.1 i j = (M i j : ℝ))
    (r : GriessShortIndex) :
    128 * (griessConwayEncode generatedTenthAxis).2.1 r =
      (generatedTenthFinalShortSourceFormula M r : ℝ) := by
  rw [generatedTenth_short]
  change 128 * generatedAxisGlobalRawTrialityShort generatedAxisGlobalFifthRoot02Packet r = _
  exact generatedTenth_final_short_source_generic_actual _ M _ _ hm
    (generatedTenth_final_short_source_incoming_C h)
    generatedTenth_final_short_source_tensor_actual r

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
