/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.Renorm
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.Renorm`

* `rrn_renorm_iterate` and `rrn_renorm_super_exp` for `b k = (1/2)^(2^k)`, which satisfies the
  squaring recursion with equality.
* `rrn_subunit_seed_of_not_bddBelow` at `C = 2`, `u = 1/4`.
-/

@[expose] public section

open StatMech.RSW.Renorm

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.Renorm

/-- The doubly exponential sequence `(1/2)^(2^k)`. -/
noncomputable def b (k : ℕ) : ℝ := (1 / 2) ^ (2 ^ k)

theorem b_sq (k : ℕ) : b (k + 1) ≤ b k ^ 2 := by
  unfold b; rw [← pow_mul, pow_succ]

example (k : ℕ) : b k ≤ b 0 ^ (2 ^ k) :=
  rrn_renorm_iterate b (fun _ => by unfold b; positivity) b_sq k

example : ∃ c : ℝ, 0 < c ∧ ∀ k, b k ≤ Real.exp (-c * (2 ^ k : ℕ)) :=
  rrn_renorm_super_exp b (fun _ => by unfold b; positivity) (by norm_num [b]) (by norm_num [b])
    b_sq

example : 0 ≤ (2 : ℝ) * (fun _ : ℕ => (1 / 4 : ℝ)) 0 ∧ (2 : ℝ) * (fun _ : ℕ => (1 / 4 : ℝ)) 0 < 1 :=
  rrn_subunit_seed_of_not_bddBelow (u := fun _ : ℕ => (1 / 4 : ℝ)) (by norm_num)
    (fun _ => by norm_num) (n₀ := 0) (by norm_num)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.Renorm
