/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The actual preferred Q-product phase for two signed vectors in one octad. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.OctadOddSpinDictionary

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The extension coefficient is exactly the Schrödinger cross-character. -/
theorem q_product_coeff_spinDot (g h : Q) :
    toAdd (g * h).coeff = toAdd g.coeff + toAdd h.coeff +
      spinDot (spinModulation h) (spinTranslation g) := by
  change toAdd g.coeff + toAdd h.coeff + qBeta (toAdd g.base) (toAdd h.base) = _
  simp only [qBeta, spinDot, spinModulation, spinTranslation, mul_comm]

/-- The preferred short lifts have zero central coefficient. -/
theorem griessShortQ_product_coeff_spinDot (r s : GriessShortIndex) :
    toAdd (griessShortQ r * griessShortQ s).coeff =
      spinDot (spinModulation (griessShortQ s)) (spinTranslation (griessShortQ r)) := by
  rw [q_product_coeff_spinDot]
  change 0 + 0 + _ = _
  simp

theorem griessShortQ_self_dot (r : GriessShortIndex) :
    spinDot (spinModulation (griessShortQ r)) (spinTranslation (griessShortQ r)) = 0 := by
  have h := congrArg (fun g : Q => toAdd g.coeff) (griessShortQ_square r)
  rw [griessShortQ_product_coeff_spinDot] at h
  exact h

/-- The dual-code syndrome character evaluates the encoded physical word. -/
theorem golaySyndrome_spinDot (c : Fin 24 → ZMod 2) (a : SpinIndex) :
    spinDot (golaySyndrome c) a = ∑ i, c i * golayEncoder a i := by
  change (∑ k, (∑ i, c i * (golayGeneratorBit k i : ZMod 2)) * a k) =
    ∑ i, c i * (∑ k, a k * (golayGeneratorBit k i : ZMod 2))
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Count the actual physical negative positions of an octad representative. -/
theorem griessOctadNegativeInteger_sum (o : Fin 759) (e : Fin 64) :
    (∑ i, griessOctadNegativeInteger o e i) =
      (trialityBitWeight8 (trialityEvenMask e) : ℤ) := by
  have h := griessOctadSignMask_weight o e
  simpa only [golayMaskWeight, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, griessOctadNegativeInteger] using congrArg (fun n : ℕ => (n : ℤ)) h

/-- Negative octad subsets have even cardinality. -/
theorem griessOctadNegative_parity_sum (o : Fin 759) (e : Fin 64) :
    (∑ i, integerParity (griessOctadNegativeInteger o e) i) = 0 := by
  change (∑ i, (griessOctadNegativeInteger o e i : ZMod 2)) = 0
  rw [← Int.cast_sum, griessOctadNegativeInteger_sum]
  rcases trialityEvenMask_even e with ⟨n, hn⟩
  rw [hn]
  simp [show (2 : ZMod 2) = 0 by decide]

/-- The octad code word is orthogonal to its negative-position syndrome. -/
theorem griessOctadNegative_dot_code (o : Fin 759) (e : Fin 64) :
    spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e)))
      (golayLabelCoefficients (golayOctadLabel o)) = 0 := by
  rw [golaySyndrome_spinDot]
  calc
    _ = ∑ i, integerParity (griessOctadNegativeInteger o e) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [golayLabelEncoder_boolean]
      by_cases hn : (griessOctadSignMask o e).testBit i.val = true
      · have hc := griessOctadSignMask_subset o e i hn
        simp [integerParity, griessOctadNegativeInteger, hn, hc, golayBooleanCast]
      · simp [integerParity, griessOctadNegativeInteger, hn]
    _ = 0 := griessOctadNegative_parity_sum o e

/-- The all-one word is orthogonal to every even negative-position syndrome. -/
theorem griessOctadNegative_dot_omega (o : Fin 759) (e : Fin 64) :
    spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o e)))
      (Pi.single 11 1) = 0 := by
  rw [golaySyndrome_spinDot, golay_all_one]
  simp only [mul_one]
  exact griessOctadNegative_parity_sum o e

theorem spinDot_smul_right (b t : SpinIndex) (a : ZMod 2) :
    spinDot b (a • t) = a * spinDot b t := by
  simp only [spinDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The negative-position syndrome pairs trivially with every code/Ω
translation of a signed vector in the same octad. -/
theorem griessOctadNegative_dot_translation (o : Fin 759) (e f : Fin 64) :
    spinDot (golaySyndrome (integerParity (griessOctadNegativeInteger o f)))
      (spinTranslation (griessShortQ (Sum.inr (Sum.inl (o,e))))) = 0 := by
  rw [griessOctad_translation, spinDot_add_right, griessOctadNegative_dot_code,
    spinDot_smul_right, griessOctadNegative_dot_omega, mul_zero, add_zero]

/-- All actual preferred Q products within one signed-octad family have
central phase zero. No Parker-section phase assumption is used. -/
theorem griessOctadQ_product_coeff (o : Fin 759) (e f : Fin 64) :
    toAdd (griessShortQ (Sum.inr (Sum.inl (o,e))) *
      griessShortQ (Sum.inr (Sum.inl (o,f)))).coeff = 0 := by
  rw [griessShortQ_product_coeff_spinDot, griessOctad_modulation,
    spinDot_add_left, griessOctadNegative_dot_translation, add_zero]
  have h := griessShortQ_self_dot (Sum.inr (Sum.inl (o,e)))
  rw [griessOctad_modulation, spinDot_add_left,
    griessOctadNegative_dot_translation, add_zero] at h
  exact h

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
