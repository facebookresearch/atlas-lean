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

/-- Distinct signals with equal samples are not identified. -/
example {f g : ℝ → ℝ} (h : ∀ n : ℕ, f (n * (1:ℝ)) = g (n * (1:ℝ)))
    (hd : ∃ t : ℝ, f t ≠ g t) : f ≠ g :=
  (alias_not_identified (a := 2) (b := 3) (tau := 1) (fun _ => (0:ℝ)) h hd).2

end PhyslibExtTest.BiomedicalInstrumentation.Aliasing
