/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Complexity.BPPAmplification

import Mathlib.Tactic.NormNum

/-- Computation: majority of a single `true` vote is `true`, of a
single `false` vote is `false`. -/
example : majority (fun _ : Fin 1 => true) = true ∧
    majority (fun _ : Fin 1 => false) = false := by
  decide

/-- Boundary check: the amplification bound instantiates for a
fair-coin-or-better vote at `n = 1`. -/
example (p : PMF Bool) (hp : (2 / 3 : ℝ) ≤ (p true).toReal) :
    (∑ v : Fin 1 → Bool, (∏ i, (p (v i)).toReal) *
      (if majority v = false then 1 else 0)) ≤ Real.exp (-(((1 : ℕ) : ℝ) / 18)) :=
  bpp_majority_amplify (n := 1) (by norm_num) p hp
