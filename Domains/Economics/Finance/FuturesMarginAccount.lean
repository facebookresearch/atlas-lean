/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

/-!
# Futures margin-account telescoping

A zero-interest futures margin account pays the contract multiplier times
each day's price change; the cumulative gain telescopes to the multiplier
times the total price change.

## Main results

* `futuresMarginGain_eq`: the telescoping identity, from `Finset.mul_sum`
  and `Finset.sum_range_sub`.
* `futuresMarginGain_example`: a concrete instance.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.FuturesMarginAccount

/-- Cumulative zero-interest variation-margin gain over `n` settlements for a
futures position with contract multiplier `multiplier` and futures prices
`F : ℕ → ℝ`: `∑ i ∈ range n, multiplier * (F (i + 1) - F i)`. Each daily
settlement pays the multiplier times that day's price change; there is no
interest on the margin account. -/
noncomputable def futuresMarginGain (multiplier : ℝ) (F : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, multiplier * (F (i + 1) - F i)

/-- A zero-interest futures margin-account gain telescopes to the contract
multiplier times the total price change `F n - F 0`. This is
`Finset.mul_sum` plus `Finset.sum_range_sub`; do not reprove either. -/
theorem futuresMarginGain_eq (multiplier : ℝ) (F : ℕ → ℝ) (n : ℕ) :
    futuresMarginGain multiplier F n = multiplier * (F n - F 0) := by
  unfold futuresMarginGain
  rw [← Finset.mul_sum, Finset.sum_range_sub]

/-- Concrete instance: multiplier `2`, prices `F i = i ^ 2`, `n = 3`:
daily gains `2 * (1 + 3 + 5) = 18 = 2 * (9 - 0)`. -/
theorem futuresMarginGain_example :
    futuresMarginGain 2 (fun i => (i : ℝ) ^ 2) 3 = 18 := by
  rw [futuresMarginGain_eq]
  norm_num

end MathlibExt.Probability.Finance.FuturesMarginAccount
