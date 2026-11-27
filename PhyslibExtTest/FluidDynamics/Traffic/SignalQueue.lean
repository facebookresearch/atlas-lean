/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.FluidDynamics.Traffic.SignalQueue

/-!
# Signal-queue checks

Focused checks for `PhyslibExt.FluidDynamics.Traffic.SignalQueue`:
the witness `lam = 1, mu = 3, R = G = 2` has queue `2` at the end of
red, clears at time `3`, and is empty at the cycle end `4`.

These are elaboration and non-vacuity checks, not new results.
-/

open FluidDynamics.Traffic.SignalQueue

/-- Witness values through computation and the public theorems. -/
example : queueLen 1 3 2 2 = 2 ∧ queueLen 1 3 2 3 = 0
    ∧ queueLen 1 3 2 (2 + 2) = 0 := by
  refine ⟨by norm_num [queueLen], by norm_num [queueLen], ?_⟩
  exact queueLen_cycle_end (lam := 1) (mu := 3) (R := 2) (G := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Rates on the witness: red rate `1`, green rate `-2`. -/
example : deriv (queueLen 1 3 2) 1 = 1 ∧ deriv (queueLen 1 3 2) (5 / 2) = -(3 - 1) :=
  ⟨queueLen_deriv_red (lam := 1) (mu := 3) (R := 2) (t := 1) (by norm_num) (by norm_num),
    queueLen_deriv_green (lam := 1) (mu := 3) (R := 2) (G := 2) (t := 5 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩

/-- Clearance API on the witness: zero at `t = 3` and after, and the
post-clearance derivative is `0`. -/
example : queueLen 1 3 2 3 = 0 ∧ deriv (queueLen 1 3 2) (7 / 2) = 0 :=
  ⟨queueLen_eq_zero_of_clearance (lam := 1) (mu := 3) (R := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    queueLen_deriv_after_clearance (lam := 1) (mu := 3) (R := 2) (G := 2)
      (t := 7 / 2) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)⟩

/-- Exact-capacity boundary: `lam = 1, mu = 3, R = 2, G = 1` has
`lam * (R + G) = mu * G`, and the queue is empty at the cycle end. -/
example : queueLen 1 3 2 (2 + 1) = 0 :=
  queueLen_cycle_end (lam := 1) (mu := 3) (R := 2) (G := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- HasDerivAt forms on the witness: red rate , post-clearance . -/
example : HasDerivAt (queueLen 1 3 2) 1 1
    ∧ HasDerivAt (queueLen 1 3 2) 0 (7 / 2) :=
  ⟨queueLen_hasDerivAt_red (lam := 1) (mu := 3) (R := 2) (t := 1)
      (by norm_num) (by norm_num),
    queueLen_hasDerivAt_after_clearance (lam := 1) (mu := 3) (R := 2)
      (G := 2) (t := 7 / 2) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)⟩
