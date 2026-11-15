/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Graham's list-scheduling bound

For list scheduling on `m` machines with makespan `M`, largest
job `p`, and total work `T`, the standard argument shows every
machine is busy until after `M - p`, giving `m * (M - p) < T`.
This module proves the inequality core of Graham's bound from
that hypothesis, and the resulting `M ≤ 2 * OPT` form. The
scheduling construction itself is not formalized here.
-/

@[expose] public section

/-- Graham's list-scheduling bound, inequality core of DPA-28:
if every one of `m` machines finishes by time `M`, some machine
finishes exactly at `M`, every machine is busy until after
`M - p` (the last job assigned anywhere started before `M - p`
is impossible: all loads exceed `M - p`), and total work is
`T`, then `m * (M - p) < T`, hence `M <= T / m + p`. With
`T / m <= OPT` and `p <= OPT` this gives `M <= 2 * OPT`. -/
theorem graham_bound (m M p T : ℝ) (hm : 0 < m)
    (h : m * (M - p) < T) : M ≤ T / m + p := by
  have h1 : M - p < T / m := (lt_div_iff₀ hm).mpr (by linarith)
  linarith

theorem graham_two_approx (m M p T OPT : ℝ) (hm : 0 < m)
    (h : m * (M - p) < T) (hT : T / m ≤ OPT) (hp : p ≤ OPT) :
    M ≤ 2 * OPT := by
  have hMb := graham_bound m M p T hm h
  linarith

end
