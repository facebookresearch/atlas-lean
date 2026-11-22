/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sensor aliasing

## i. Overview

Signals that agree at every uniform sample time remain
indistinguishable after the same affine calibrated sensor map and
common additive noise. The zero signal and `sin (π * t)` are a
concrete aliased pair at unit sampling.

## ii. Key results

* `calibrated_samples_eq`: calibrated samples of aliased signals agree.
* `calibrated_sample_equality`: the same for noisy calibrated samples.
* `sin_alias_not_identified`: the sampled observation map is not
  injective, witnessed by the zero signal and `sin (π * t)`.

## iii. Table of contents

* A. Calibrated sample agreement.
* B. A concrete aliased pair.

## iv. References

* `Real.sin_nat_mul_pi` and `Real.sin_pi_div_two` from Mathlib's
  trigonometric API.
-/

@[expose] public section

namespace PhyslibExt.BiomedicalInstrumentation.Aliasing

/-- **Calibrated samples of aliased signals agree.** Two signals
with the same samples at multiples of `tau` have the same samples
after the same affine sensor map `x ↦ a * x + b`. -/
lemma calibrated_samples_eq {f g : ℝ → ℝ} {a b tau : ℝ}
    (hsamp : ∀ n : ℕ, f (n * tau) = g (n * tau)) (n : ℕ) :
    a * f (n * tau) + b = a * g (n * tau) + b := by
  rw [hsamp n]

/-- **Noisy calibrated samples of aliased signals agree.** If two
signals agree at every sample time, their calibrated samples with
any common additive noise sequence agree at every sample. -/
lemma calibrated_sample_equality {f g : ℝ → ℝ} {a b tau : ℝ}
    (e : ℕ → ℝ)
    (hsamp : ∀ n : ℕ, f (n * tau) = g (n * tau)) :
    ∀ n : ℕ, (a * f (n * tau) + b) + e n = (a * g (n * tau) + b) + e n := by
  intro n
  rw [hsamp n]

/-- The sampled calibrated observation of a signal: affine sensor
map at uniform sample times, plus common additive noise. -/
noncomputable def sampledObservation (f : ℝ → ℝ) (a b tau : ℝ)
    (e : ℕ → ℝ) : ℕ → ℝ :=
  fun n => a * f (n * tau) + b + e n

/-- **A concrete aliased pair.** At unit sampling, the zero signal
and `t ↦ sin (π * t)` have identical sampled calibrated
observations (for every affine calibration and common noise), yet
they are distinct signals. Hence the sampled observation map is
not injective. -/
lemma sin_alias_not_identified (a b : ℝ) (e : ℕ → ℝ) :
    ¬ Function.Injective
      (fun f : ℝ → ℝ => sampledObservation f a b 1 e) := by
  intro hInj
  have hne : (fun _ : ℝ => (0:ℝ)) ≠ (fun t : ℝ => Real.sin (Real.pi * t)) := by
    intro h
    have hh := congrFun h (1 / 2)
    have hpi : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring
    rw [hpi, Real.sin_pi_div_two] at hh
    norm_num at hh
  apply hne
  apply hInj
  funext n
  unfold sampledObservation
  have hs : Real.sin (Real.pi * ((n : ℝ) * 1)) = 0 := by
    have h2 : Real.pi * ((n : ℝ) * 1) = (n : ℝ) * Real.pi := by ring
    rw [h2]
    exact Real.sin_nat_mul_pi n
  have hs2 : Real.sin (Real.pi * (n : ℝ)) = 0 := by
    simpa using hs
  simp [sampledObservation, hs2]


end PhyslibExt.BiomedicalInstrumentation.Aliasing
