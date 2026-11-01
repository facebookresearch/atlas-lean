/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Phylogenetics.MotifConservation
import Mathlib.Tactic.NormNum

/-!
# Motif conservation score tests

`P(Bin(2, 1/2) ≥ 1) = 3/4` and `P(Bin(2, 1/4) ≥ 1) = 7/16 < 3/4` (strict monotonicity in `p`);
the boundary values `P(X ≥ 0) = 1` and `P(X ≥ 3) = 0` for `n = 2`; `P(Bin(2, p) ≥ 2) ≤
P(Bin(2, p) ≥ 1)`; the MCS of `30` conserved out of `100` at `p = 1/5` is `(30 - 20)/4 = 5/2`.
At `p = 0` the MCS divides by `√0 = 0` and returns the junk value `0`, outside the domain
`0 < p < 1` of `mcs_strictMono`.
-/

namespace MathlibExt.Biology.Phylogenetics.MotifConservation

example : binomTail 2 1 (1 / 2) = 3 / 4 := by
  norm_num [binomTail, Finset.sum_Icc_succ_top]

example : binomTail 2 1 (1 / 4) = 7 / 16 := by
  norm_num [binomTail, Finset.sum_Icc_succ_top]

example : binomTail 2 1 (1 / 4) < binomTail 2 1 (1 / 2) :=
  strictMonoOn_binomTail (by norm_num) (by norm_num) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ (by norm_num)

example (p : ℝ) : binomTail 2 0 p = 1 := binomTail_zero 2 p

example (p : ℝ) : binomTail 2 3 p = 0 := binomTail_of_lt (by norm_num) p

example {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) : binomTail 2 2 p ≤ binomTail 2 1 p :=
  binomTail_succ_le 2 1 h0 h1

example : mcs 100 30 (1 / 5) = 5 / 2 := by
  have : Real.sqrt ((100 : ℕ) * (1 / 5) * (1 - 1 / 5)) = 4 := by
    rw [show ((100 : ℕ) : ℝ) * (1 / 5) * (1 - 1 / 5) = 4 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  rw [mcs, this]; norm_num

/-- Junk value outside the domain: at `p = 0` the MCS is `0`. -/
example : mcs 100 30 0 = 0 := by
  simp [mcs]

end MathlibExt.Biology.Phylogenetics.MotifConservation
