/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.Push
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.Push`

* `rpu_push_lower`, `rpu_push_constant_pos` and `rpu_push` for `g j n = (1/2)^(j+1)`, which
  meets the base and step hypotheses with equality.
* `rpu_push_constant_eq` at `β = 2`.
-/

@[expose] public section

open StatMech.RSW.Push

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.Push

theorem step (j : ℕ) : (1 / 2 : ℝ) ^ (j + 1) * (1 / 2) ≤ (1 / 2) ^ (j + 1 + 1) :=
  le_of_eq (pow_succ _ _).symm

example (j : ℕ) : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2) ^ (j + 1) :=
  rpu_push_lower (fun i => (1 / 2 : ℝ) ^ (i + 1)) (by norm_num) (by norm_num) step j

example (j : ℕ) : 0 < (1 / 2 : ℝ) ^ (j + 1) :=
  rpu_push_constant_pos (fun i => (1 / 2 : ℝ) ^ (i + 1)) (by norm_num) (by norm_num) step j

example : ∀ j, ∃ c : ℝ, 0 < c ∧ ∀ _n : ℕ, c ≤ (1 / 2 : ℝ) ^ (j + 1) :=
  rpu_push (fun i _ => (1 / 2 : ℝ) ^ (i + 1)) (by norm_num) (fun _ => by norm_num)
    (fun j _ => step j)

example : (fun i => (2 : ℝ) ^ (i + 1)) 3 = (fun i => (2 : ℝ) ^ (i + 1)) 2 * 2 :=
  rpu_push_constant_eq 2

end MathlibExtTest.StatMech.Probability.Percolation.RSW.Push
