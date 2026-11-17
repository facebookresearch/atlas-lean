/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.FiniteAMModulator
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Ideal AM envelope

## i. Overview

The complex envelope observation of an amplitude-modulated
carrier (in the convention of
`PhyslibExt.Communications.FiniteAMModulator`, imported) has
real part the modulated carrier and modulus `|A + mu m_j|`, so
the ideal envelope detector recovers the message exactly when
the envelope stays positive, and fails under overmodulation.

## ii. Key results

- `envelopeDetector_eq_message`: exact message recovery in
  the non-overmodulated regime.
- `envelopeDetector_overmodulated_ne`: the overmodulated
  counterexample.

## iii. Table of contents

- A. The ideal envelope detector

## iv. References

- B. P. Lathi and Z. Ding, *Modern Digital and Analog
  Communication Systems*, fourth edition, Oxford University
  Press, 2010: amplitude modulation and envelope detection.

## A. The ideal envelope detector
-/

@[expose] public section

namespace PhyslibExt.Communications.IdealAMEnvelope

/-- The ideal complex-envelope observation `z_j = (A + μ m_j) exp(2π i k j / N)` on `ZMod N`,
with the carrier angle `2π k.val j.val / N` of the finite AM model. -/
noncomputable def envelopeObservation (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k : ZMod N) : ZMod N → ℂ :=
  fun j => ((A + μ * m j : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * (k.val : ℝ) * (j.val : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The envelope detector `(‖z‖ - A) / μ` applied to one complex observation. -/
noncomputable def envelopeDetector (A μ : ℝ) (z : ℂ) : ℝ :=
  (‖z‖ - A) / μ

/-- Same AM convention: the real part of the observation is the finite AM signal sample
`(A + μ m_j) cos(2π k j / N)` (the body of `FiniteAMModulator.amSignal`). -/
lemma re_envelopeObservation (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ) (k j : ZMod N) :
    (envelopeObservation N A μ m k j).re =
      FiniteAMModulator.amSignal N A μ m k j := by
  simp only [envelopeObservation, FiniteAMModulator.amSignal, FiniteAMModulator.carrierCos]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The modulus of the observation is the absolute value of the envelope `A + μ m_j`. -/
lemma norm_envelopeObservation (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k j : ZMod N) :
    ‖envelopeObservation N A μ m k j‖ = |A + μ * m j| := by
  simp only [envelopeObservation]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Under `μ > 0`, `|m_j| ≤ M` and `A > μ M` the envelope `A + μ m_j` is strictly positive. -/
lemma envelope_pos (N : ℕ) [NeZero N] (A μ M : ℝ) (m : ZMod N → ℝ) (hμ : 0 < μ)
    (hm : ∀ j, |m j| ≤ M) (hA : μ * M < A) (j : ZMod N) :
    0 < A + μ * m j := by
  have h1 : -M ≤ m j := (abs_le.mp (hm j)).1
  nlinarith

/-- **Ideal AM envelope reconstruction.** For a supplied ideal complex-envelope observation
`z_j = (A + μ m_j) exp(2π i k j / N)` with `μ > 0`, `|m_j| ≤ M` for all `j` and `A > μ M`,
the envelope detector recovers the message: `(‖z_j‖ - A) / μ = m_j`. -/
lemma envelopeDetector_eq_message (N : ℕ) [NeZero N] (A μ M : ℝ) (m : ZMod N → ℝ)
    (k : ZMod N) (z : ZMod N → ℂ) (hz : ∀ j, z j = envelopeObservation N A μ m k j)
    (hμ : 0 < μ) (hm : ∀ j, |m j| ≤ M) (hA : μ * M < A) (j : ZMod N) :
    envelopeDetector A μ (z j) = m j := by
  rw [envelopeDetector, hz, norm_envelopeObservation,
    abs_of_pos (envelope_pos N A μ M m hμ hm hA j)]
  field_simp
  ring

/-- Function form: the detector applied samplewise to the observation is the message. -/
lemma envelopeDetector_comp_eq_message (N : ℕ) [NeZero N] (A μ M : ℝ) (m : ZMod N → ℝ)
    (k : ZMod N) (hμ : 0 < μ) (hm : ∀ j, |m j| ≤ M) (hA : μ * M < A) :
    (fun j => envelopeDetector A μ (envelopeObservation N A μ m k j)) = m := by
  funext j
  exact envelopeDetector_eq_message N A μ M m k _ (fun _ => rfl) hμ hm hA j

/-! ### Validation: positive and negative messages under a positive envelope -/

/-- Positive constant message `m = 1/2` (`A = 1`, `μ = 1`, `M = 1/2`) is recovered. -/
lemma envelopeDetector_const_pos (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 1 1 (envelopeObservation N 1 1 (fun _ => 1 / 2) k j) = 1 / 2 := by
  rw [envelopeDetector, norm_envelopeObservation]
  norm_num

/-- Negative constant message `m = -1/2` (`A = 1`, `μ = 1`, `M = 1/2`) is recovered. -/
lemma envelopeDetector_const_neg (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 1 1 (envelopeObservation N 1 1 (fun _ => -1 / 2) k j) = -1 / 2 := by
  rw [envelopeDetector, norm_envelopeObservation]
  norm_num

/-! ### Validation: overmodulation and the absolute-value ambiguity -/

/-- A negative envelope `A + μ m_j < 0` (overmodulation, `μ > 0`) makes the detector read
`-(2A/μ) - m_j`, which is not `m_j`. -/
lemma envelopeDetector_of_envelope_neg (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k j : ZMod N) (hμ : 0 < μ) (hneg : A + μ * m j < 0) :
    envelopeDetector A μ (envelopeObservation N A μ m k j) = -(2 * A / μ) - m j ∧
      envelopeDetector A μ (envelopeObservation N A μ m k j) ≠ m j := by
  have h : envelopeDetector A μ (envelopeObservation N A μ m k j) = -(2 * A / μ) - m j := by
    rw [envelopeDetector, norm_envelopeObservation, abs_of_neg hneg]
    field_simp
    ring
  refine ⟨h, ?_⟩
  rw [h]
  intro he
  have h2 : A + μ * m j = 0 := by
    field_simp at he
    linarith
  linarith

/-- Absolute-value ambiguity: with `A = μ = 1`, the overmodulated message `-3` (envelope
`-2`) and the message `1` (envelope `2`) produce observations of equal modulus. -/
lemma norm_envelopeObservation_overmodulated (N : ℕ) [NeZero N] (k j : ZMod N) :
    ‖envelopeObservation N 1 1 (fun _ => -3) k j‖ =
      ‖envelopeObservation N 1 1 (fun _ => 1) k j‖ := by
  rw [norm_envelopeObservation, norm_envelopeObservation]
  norm_num

/-- The detector returns `1` on the overmodulated message `-3`, so it does not recover it. -/
lemma envelopeDetector_overmodulated_ne (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 1 1 (envelopeObservation N 1 1 (fun _ => -3) k j) = 1 ∧
      envelopeDetector 1 1 (envelopeObservation N 1 1 (fun _ => -3) k j) ≠ -3 := by
  rw [envelopeDetector, norm_envelopeObservation]
  norm_num

end PhyslibExt.Communications.IdealAMEnvelope
