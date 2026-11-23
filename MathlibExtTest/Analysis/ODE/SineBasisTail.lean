/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.ODE.SineBasisTail
import Mathlib.Tactic

/-!
# Tests for the sine-basis tail bound

* For unit coefficients, the tail modes `2 .. 3` (coefficient
  indices `1 .. 2`) of the sine Hilbert basis have squared norm at
  most that of the full sum over modes `1 .. 3` (coefficient
  indices `0 .. 2`).
-/

open Real Set

/-- Sine-basis tail bound at unit coefficients. -/
example :
    ‖∑ k ∈ Finset.Ico 1 3,
        (1 : ℝ) • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 ≤
      ‖∑ k ∈ Finset.Ico 0 3,
        (1 : ℝ) • MathlibExt.Analysis.ODE.GreensOperator.sineHilbertBasis
          ⟨k + 1, Nat.succ_pos k⟩‖ ^ 2 :=
  MathlibExt.Analysis.ODE.SineBasisTail.sineBasis_tail_norm_sq_le
    (fun _ => 1) (by norm_num)
