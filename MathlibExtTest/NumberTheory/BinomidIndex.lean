/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BinomidIndex

open MetaMathlibExt

/-- A sequence with plateaus still satisfies the binomid inequality on every shifted block. -/
example (k m : ℕ) :
    ∑ i ∈ Finset.range k, i / 2 ≤ ∑ i ∈ Finset.Ico m (m + k), i / 2 := by
  have h : IsBinomidIndex (fun i => i / 2) :=
    isBinomidIndex_of_monotone fun _ _ hij => Nat.div_le_div_right hij
  simpa using h k (m + k) (Nat.le_add_left k m)

/-- A drop from one to zero violates the binomid inequality on the second singleton block. -/
example : ¬ IsBinomidIndex (fun i => if i = 0 then 1 else 0) := by
  intro h
  exact absurd (h 1 2 (by decide)) (by decide)

/-- A single prepended zero contributes to the denominator of the first two terms' average. -/
example : binomidAverage (binomidShift 1 (fun _ => 3)) 2 = 3 / 2 := by
  simp [binomidAverage, Finset.sum_range_succ, binomidShift]
