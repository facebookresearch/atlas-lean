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

This module assumes that the receiver observes the complex envelope
(the in-phase/quadrature pair) of an amplitude-modulated carrier in
the convention of `PhyslibExt.Communications.FiniteAMModulator`
(imported): the sample `z_j = (A + mu m_j) exp(2 pi i k j / N)`.
That observation is a receiver-model premise. It is not computed from
the real signal `FiniteAMModulator.amSignal`, and no analytic-signal
or Hilbert-transform construction is made; its quadrature part carries
the envelope even where the carrier cosine vanishes.

Given that assumed observation, the module proves that its real part
is the transmitted `amSignal` sample, that its modulus is
`|A + mu m_j|`, and that the ideal envelope detector
`(‖z_j‖ - A) / mu` recovers the message exactly whenever the envelope
`A + mu m_j` is nonnegative, including the 100% modulation boundary
`A = mu M`. A negative envelope (overmodulation) makes the detector
fail through the absolute-value ambiguity.

## ii. Key results

- `envelopeDetector_eq_message`: exact message recovery from the
  assumed complex-envelope observation when every envelope sample is
  nonnegative.
- `envelopeDetector_eq_message_of_abs_le`: the same under the
  boundary-inclusive bound `|m_j| ≤ M`, `mu M ≤ A`.
- `envelopeDetector_overmodulated_ne`: the overmodulated
  counterexample.

## iii. Table of contents

- A. Envelope detection on an assumed complex envelope

## iv. References

- B. P. Lathi and Z. Ding, *Modern Digital and Analog
  Communication Systems*, fourth edition, Oxford University
  Press, 2010: amplitude modulation and envelope detection.

## A. Envelope detection on an assumed complex envelope
-/

@[expose] public section

namespace PhyslibExt.Communications.IdealAMEnvelope

/-- The assumed complex-envelope (in-phase/quadrature) observation
`z_j = (A + μ m_j) exp(2π i k j / N)` on `ZMod N`, with the carrier angle `2π k.val j.val / N`
of the finite AM model. This is a receiver-model premise, not a function of
`FiniteAMModulator.amSignal`; its real part is that signal (`re_complexEnvelopeObservation`). -/
noncomputable def complexEnvelopeObservation (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k : ZMod N) : ZMod N → ℂ :=
  fun j => ((A + μ * m j : ℝ) : ℂ) *
    Complex.exp (((2 * Real.pi * (k.val : ℝ) * (j.val : ℝ) / (N : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The envelope detector `(‖z‖ - A) / μ` applied to one complex observation. -/
noncomputable def envelopeDetector (A μ : ℝ) (z : ℂ) : ℝ :=
  (‖z‖ - A) / μ

/-- Same AM convention: the real part of the observation is the finite AM signal sample
`(A + μ m_j) cos(2π k j / N)` (the body of `FiniteAMModulator.amSignal`). -/
lemma re_complexEnvelopeObservation (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k j : ZMod N) :
    (complexEnvelopeObservation N A μ m k j).re =
      FiniteAMModulator.amSignal N A μ m k j := by
  simp only [complexEnvelopeObservation, FiniteAMModulator.amSignal,
    FiniteAMModulator.carrierCos]
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The modulus of the observation is the absolute value of the envelope `A + μ m_j`. -/
lemma norm_complexEnvelopeObservation (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k j : ZMod N) :
    ‖complexEnvelopeObservation N A μ m k j‖ = |A + μ * m j| := by
  simp only [complexEnvelopeObservation]
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Under `0 ≤ μ`, `|m_j| ≤ M` and `μ M ≤ A` the envelope `A + μ m_j` is nonnegative. -/
lemma envelope_nonneg (N : ℕ) [NeZero N] (A μ M : ℝ) (m : ZMod N → ℝ) (hμ : 0 ≤ μ)
    (hm : ∀ j, |m j| ≤ M) (hA : μ * M ≤ A) (j : ZMod N) :
    0 ≤ A + μ * m j := by
  have h1 : -M ≤ m j := (abs_le.mp (hm j)).1
  nlinarith

/-- **Ideal AM envelope reconstruction.** For an assumed complex-envelope observation
`z_j = (A + μ m_j) exp(2π i k j / N)` with `μ > 0` and a nonnegative envelope
`0 ≤ A + μ m_j` at every sample, the envelope detector recovers the message:
`(‖z_j‖ - A) / μ = m_j`. -/
lemma envelopeDetector_eq_message (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k : ZMod N) (z : ZMod N → ℂ) (hz : ∀ j, z j = complexEnvelopeObservation N A μ m k j)
    (hμ : 0 < μ) (henv : ∀ j, 0 ≤ A + μ * m j) (j : ZMod N) :
    envelopeDetector A μ (z j) = m j := by
  rw [envelopeDetector, hz, norm_complexEnvelopeObservation, abs_of_nonneg (henv j)]
  field_simp
  ring

/-- Boundary-inclusive modulation-depth form: with `μ > 0`, `|m_j| ≤ M` for all `j` and
`μ M ≤ A` (so `A = μ M`, 100% modulation, is allowed), the envelope detector recovers the
message from the assumed complex-envelope observation. -/
lemma envelopeDetector_eq_message_of_abs_le (N : ℕ) [NeZero N] (A μ M : ℝ) (m : ZMod N → ℝ)
    (k : ZMod N) (z : ZMod N → ℂ) (hz : ∀ j, z j = complexEnvelopeObservation N A μ m k j)
    (hμ : 0 < μ) (hm : ∀ j, |m j| ≤ M) (hA : μ * M ≤ A) (j : ZMod N) :
    envelopeDetector A μ (z j) = m j :=
  envelopeDetector_eq_message N A μ m k z hz hμ (envelope_nonneg N A μ M m hμ.le hm hA) j

/-- Function form: the detector applied samplewise to the assumed complex-envelope
observation is the message whenever every envelope sample is nonnegative. -/
lemma envelopeDetector_comp_eq_message (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k : ZMod N) (hμ : 0 < μ) (henv : ∀ j, 0 ≤ A + μ * m j) :
    (fun j => envelopeDetector A μ (complexEnvelopeObservation N A μ m k j)) = m := by
  funext j
  exact envelopeDetector_eq_message N A μ m k _ (fun _ => rfl) hμ henv j

/-! ### Validation: positive and negative messages under a positive envelope -/

/-- Positive constant message `m = 1/2` (`A = 1`, `μ = 1`, `M = 1/2`) is recovered. -/
lemma envelopeDetector_const_pos (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 1 1 (complexEnvelopeObservation N 1 1 (fun _ => 1 / 2) k j) = 1 / 2 := by
  rw [envelopeDetector, norm_complexEnvelopeObservation]
  norm_num

/-- Negative constant message `m = -1/2` (`A = 1`, `μ = 1`, `M = 1/2`) is recovered. -/
lemma envelopeDetector_const_neg (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 1 1 (complexEnvelopeObservation N 1 1 (fun _ => -1 / 2) k j) = -1 / 2 := by
  rw [envelopeDetector, norm_complexEnvelopeObservation]
  norm_num

/-! ### Validation: overmodulation and the absolute-value ambiguity -/

/-- A negative envelope `A + μ m_j < 0` (overmodulation, `μ > 0`) makes the detector read
`-(2A/μ) - m_j`, which is not `m_j`. -/
lemma envelopeDetector_of_envelope_neg (N : ℕ) [NeZero N] (A μ : ℝ) (m : ZMod N → ℝ)
    (k j : ZMod N) (hμ : 0 < μ) (hneg : A + μ * m j < 0) :
    envelopeDetector A μ (complexEnvelopeObservation N A μ m k j) = -(2 * A / μ) - m j ∧
      envelopeDetector A μ (complexEnvelopeObservation N A μ m k j) ≠ m j := by
  have h :
      envelopeDetector A μ (complexEnvelopeObservation N A μ m k j) = -(2 * A / μ) - m j := by
    rw [envelopeDetector, norm_complexEnvelopeObservation, abs_of_neg hneg]
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
lemma norm_complexEnvelopeObservation_overmodulated (N : ℕ) [NeZero N] (k j : ZMod N) :
    ‖complexEnvelopeObservation N 1 1 (fun _ => -3) k j‖ =
      ‖complexEnvelopeObservation N 1 1 (fun _ => 1) k j‖ := by
  rw [norm_complexEnvelopeObservation, norm_complexEnvelopeObservation]
  norm_num

/-- The detector returns `1` on the overmodulated message `-3`, so it does not recover it. -/
lemma envelopeDetector_overmodulated_ne (N : ℕ) [NeZero N] (k j : ZMod N) :
    envelopeDetector 1 1 (complexEnvelopeObservation N 1 1 (fun _ => -3) k j) = 1 ∧
      envelopeDetector 1 1 (complexEnvelopeObservation N 1 1 (fun _ => -3) k j) ≠ -3 := by
  rw [envelopeDetector, norm_complexEnvelopeObservation]
  norm_num

end PhyslibExt.Communications.IdealAMEnvelope
