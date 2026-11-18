/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Topology.ContinuousOn

/-!
# Sensor aliasing

Signals that agree at every uniform sample time remain indistinguishable after the same affine calibrated sensor map and common additive noise.
-/

@[expose] public section

namespace PhyslibExt.BiomedicalInstrumentation.Aliasing

/-- **Calibrated samples of aliased signals agree.** Two signals
with the same samples at multiples of `tau` have the same samples
after the same affine sensor map `x ↦ a * x + b`. -/
theorem calibrated_samples_eq {f g : ℝ → ℝ} {a b tau : ℝ}
    (hsamp : ∀ n : ℕ, f (n * tau) = g (n * tau)) (n : ℕ) :
    a * f (n * tau) + b = a * g (n * tau) + b := by
  rw [hsamp n]

/-- **Aliasing is not identified by calibrated samples.** If two
signals agree at every sample time but differ somewhere, their
calibrated samples (with any common additive noise sequence) agree
everywhere while the signals are distinct. -/
theorem alias_not_identified {f g : ℝ → ℝ} {a b tau : ℝ}
    (e : ℕ → ℝ)
    (hsamp : ∀ n : ℕ, f (n * tau) = g (n * tau))
    (hdiff : ∃ t : ℝ, f t ≠ g t) :
    (∀ n : ℕ, (a * f (n * tau) + b) + e n = (a * g (n * tau) + b) + e n) ∧
      f ≠ g := by
  constructor
  · intro n
    rw [hsamp n]
  · obtain ⟨t, ht⟩ := hdiff
    intro hfg
    apply ht
    rw [hfg]


end PhyslibExt.BiomedicalInstrumentation.Aliasing
