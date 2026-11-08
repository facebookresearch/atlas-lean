/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

/-!
# Whitt's generalized Catalan numbers

`whittGeneralizedCatalan α n = ∑_{k=0}^{n-1} (1 - k/n) C(n-1+k, k) α^k` (OEIS A064062 for
`α = 2`), from W. Whitt, *Fluid models for many-server queues with abandonments*, quoted as
`C(α, n+1) = ∑_{k=0}^{n} (1 - k/(n+1)) C(n+k, k) α^k` by Sabar Taoufik,
*A New Triangle of Numbers: Properties and Observations*, INTEGERS 26 (2026), Article A27,
Section 5.
-/

namespace MetaMathlibExt

@[expose] public section

/-- The generalized Catalan numbers of Whitt (OEIS A064062 for `α = 2`):
`C(α, n) = ∑_{k=0}^{n-1} (1 - k/n) C(n-1+k, k) α^k`, i.e. the source's
`C(α, n+1) = ∑_{k=0}^{n} (1 - k/(n+1)) C(n+k, k) α^k` with `n + 1` renamed `n`
(`C(α, 0) = 0`, the empty sum).

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`, quoting W. Whitt, J. Integer Seq. 14
(2011)). -/
def whittGeneralizedCatalan (α : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 - (k : ℚ) / n) * ((n - 1 + k).choose k : ℚ) * α ^ k

/-- The defining sum, in the source's indexing: `C(α, n+1) = ∑_{k=0}^{n} (1 - k/(n+1)) C(n+k, k) α^k`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`). -/
theorem whittGeneralizedCatalan_succ (α : ℚ) (n : ℕ) :
    whittGeneralizedCatalan α (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (1 - (k : ℚ) / ((n : ℚ) + 1)) * ((n + k).choose k : ℚ) * α ^ k := by
  simp [whittGeneralizedCatalan]

/-- `C(α, 0) = 0` (the empty sum).

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`). -/
@[simp] theorem whittGeneralizedCatalan_zero (α : ℚ) : whittGeneralizedCatalan α 0 = 0 := by
  simp [whittGeneralizedCatalan]

/-- `C(α, 1) = 1` for every `α`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)` at `n = 0`). -/
@[simp] theorem whittGeneralizedCatalan_one (α : ℚ) : whittGeneralizedCatalan α 1 = 1 := by
  simp [whittGeneralizedCatalan]

/-- `C(0, n) = 1` for `n ≥ 1`: only the `k = 0` term survives.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`). -/
theorem whittGeneralizedCatalan_zero_left {n : ℕ} (hn : 0 < n) :
    whittGeneralizedCatalan 0 n = 1 := by
  rw [whittGeneralizedCatalan, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.2 hn) h

/-- Characteristic values: `C(2, 1) = 1`, `C(2, 2) = 3`, `C(2, 3) = 13`, `C(2, 4) = 67`.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (OEIS A064062). -/
theorem whittGeneralizedCatalan_two_small :
    whittGeneralizedCatalan 2 1 = 1 ∧ whittGeneralizedCatalan 2 2 = 3 ∧
      whittGeneralizedCatalan 2 3 = 13 ∧ whittGeneralizedCatalan 2 4 = 67 := by
  simp [whittGeneralizedCatalan, Finset.sum_range_succ, Nat.choose]
  norm_num

end

end MetaMathlibExt
