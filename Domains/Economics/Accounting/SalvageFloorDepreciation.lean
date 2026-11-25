/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

@[expose] public section

/-!
# Salvage-floor depreciation (Atlas AC02.T02)

Book value starts at cost; each period it becomes `max salvage (v - charge n v)`.
Straight-line and declining-balance schedules are special cases of the charge rule.
If the asset starts at or above salvage, book value never falls below salvage, and
with nonnegative charges it never increases.

## Main results

* `MathlibExt.Economics.Accounting.salvage_le_floorBookValue`
* `MathlibExt.Economics.Accounting.floorBookValue_succ_le`

## References

* OpenStax, *Principles of Accounting, Volume 1: Financial Accounting*, §11.3
  (declining-balance depreciation stops at salvage value).
-/

namespace MathlibExt.Economics.Accounting

/-- Book value under a salvage-floor depreciation recursion: start at `cost`; in period
`n` charge `charge n v` at current book value `v`, but never write the asset below
`salvage`. Straight-line (`charge n v = c`) and declining-balance (`charge n v = r * v`)
schedules are special cases. -/
noncomputable def floorBookValue (cost salvage : ℝ) (charge : ℕ → ℝ → ℝ) : ℕ → ℝ
  | 0 => cost
  | n + 1 => max salvage
      (floorBookValue cost salvage charge n - charge n (floorBookValue cost salvage charge n))

/-- If the asset starts at or above salvage, the salvage-floor recursion never takes book
value below salvage. -/
theorem salvage_le_floorBookValue {cost salvage : ℝ} (charge : ℕ → ℝ → ℝ)
    (h0 : salvage ≤ cost) (n : ℕ) :
    salvage ≤ floorBookValue cost salvage charge n := by
  induction n with
  | zero => exact h0
  | succ n _ => exact le_max_left _ _

/-- With charges that are nonnegative at every book value at or above salvage (and a start at
or above salvage), book value never increases. This covers declining-balance rules such as
`charge n v = r * v` with `0 ≤ r` and `0 ≤ salvage`, whose charge is negative only below zero. -/
theorem floorBookValue_succ_le {cost salvage : ℝ} {charge : ℕ → ℝ → ℝ}
    (h0 : salvage ≤ cost) (hcharge : ∀ n v, salvage ≤ v → 0 ≤ charge n v) (n : ℕ) :
    floorBookValue cost salvage charge (n + 1) ≤ floorBookValue cost salvage charge n := by
  have hv : salvage ≤ floorBookValue cost salvage charge n :=
    salvage_le_floorBookValue charge h0 n
  have hc : 0 ≤ charge n (floorBookValue cost salvage charge n) := hcharge n _ hv
  simp only [floorBookValue]
  exact max_le hv (sub_le_self _ hc)

end MathlibExt.Economics.Accounting
