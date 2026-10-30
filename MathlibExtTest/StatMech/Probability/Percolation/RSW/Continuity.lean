/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.Continuity
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.Continuity`

* `roc_continuity` with `θ = 0` and the extremal sequence `a n = (1/2)^⌊log₂ n⌋`.
* `roc_continuity_of_polynomial` with `θ = 0` and `a n = n^{-1}`.
* `roc_eq_zero_of_le_tendsto` for `a n = 1/(n+1)`.
-/

@[expose] public section

open StatMech.RSW.Continuity

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.Continuity

example : (0 : ℝ) = 0 :=
  roc_continuity (fun n => (1 - 1 / 2 : ℝ) ^ Nat.log 2 n) (by norm_num) (by norm_num) le_rfl
    (fun _ => by positivity) (fun _ => by positivity) (fun _ _ => le_rfl)

example : (0 : ℝ) = 0 :=
  roc_continuity_of_polynomial (fun n : ℕ => (n : ℝ) ^ (-(1 : ℝ))) (C := 1) one_pos le_rfl
    (fun _ => by positivity) (fun _ _ => by simp)

example : (0 : ℝ) = 0 :=
  roc_eq_zero_of_le_tendsto le_rfl (fun _ => by positivity) tendsto_one_div_add_atTop_nhds_zero_nat

end MathlibExtTest.StatMech.Probability.Percolation.RSW.Continuity
