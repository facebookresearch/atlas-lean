/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalInstrumentation.Aliasing

/-! Tests: aliased signals at numeric sample times. -/

namespace PhyslibExtTest.BiomedicalInstrumentation.Aliasing

open PhyslibExt.BiomedicalInstrumentation.Aliasing

/-- Signals `t` and `t + (t - n)` agree at integers; use `f = g` sample case. -/
example {f g : ℝ → ℝ} (h : ∀ n : ℕ, f (n * (1:ℝ)) = g (n * (1:ℝ))) (n : ℕ) :
    2 * f (n * 1) + 3 = 2 * g (n * 1) + 3 :=
  calibrated_samples_eq h n

/-- Aliased distinct signals: same noisy calibrated observations,
distinct signals. -/
example {f g : ℝ → ℝ} (h : ∀ n : ℕ, f (n * (1:ℝ)) = g (n * (1:ℝ)))
    (hd : ∃ t : ℝ, f t ≠ g t) :
    (∀ n : ℕ, (2 * f (n * 1) + 3) + (0:ℝ) = (2 * g (n * 1) + 3) + 0) ∧
      f ≠ g := by
  refine ⟨calibrated_sample_equality (fun _ => (0:ℝ)) h, ?_⟩
  obtain ⟨t, ht⟩ := hd
  intro hfg
  apply ht
  rw [hfg]

/-- The concrete sine alias defeats sampled-observation injectivity. -/
example : ¬ Function.Injective
    (fun f : ℝ → ℝ => sampledObservation f 2 3 1 (fun _ => (0:ℝ))) :=
  sin_alias_not_identified 2 3 (fun _ => (0:ℝ))

end PhyslibExtTest.BiomedicalInstrumentation.Aliasing
