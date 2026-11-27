/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.NumberTheory.PrimeCounting.DusartMertensReciprocalSumDefs

/-!
# Tests for the Meissel–Mertens constant

These examples check the interface of `MetaMathlibExt.meisselMertensConstant`: it is the limit
of the differences $\sum_{p \le n} 1/p - \log \log n$ whenever they converge, it depends only on
their tail, and the finite sums in it are the expected sums over primes. None of them assumes or
proves that the differences converge, or a numerical value of the constant.
-/

open Filter Topology

namespace MetaMathlibExt

/-- The constant is, by definition, the `limUnder` of the differences
$\sum_{p \le n} 1/p - \log \log n$ along the natural numbers. -/
example : meisselMertensConstant =
    limUnder atTop (fun n : ℕ =>
      (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
        1 / (p : ℝ)) - Real.log (Real.log n)) := rfl

/-- If the differences converge to `L`, the constant is `L`. -/
example {L : ℝ}
    (h : Tendsto (fun n : ℕ =>
      (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
        1 / (p : ℝ)) - Real.log (Real.log n)) atTop (𝓝 L)) :
    meisselMertensConstant = L :=
  h.limUnder_eq

/-- The constant depends only on the tail: a sequence that eventually agrees with the
differences and converges to `L` also identifies the constant as `L`. -/
example {L : ℝ} (g : ℕ → ℝ)
    (hg : ∀ᶠ n in atTop, g n =
      (∑ p ∈ Finset.filter Nat.Prime (Finset.range (n + 1)),
        1 / (p : ℝ)) - Real.log (Real.log n))
    (h : Tendsto g atTop (𝓝 L)) :
    meisselMertensConstant = L :=
  (h.congr' hg).limUnder_eq

/-- At `n = 1` the difference is `0`: no prime is at most `1`, and `log (log 1) = 0`. -/
example : (∑ p ∈ Finset.filter Nat.Prime (Finset.range (1 + 1)), 1 / (p : ℝ)) -
    Real.log (Real.log ((1 : ℕ) : ℝ)) = 0 := by
  rw [show Finset.filter Nat.Prime (Finset.range (1 + 1)) = ∅ by decide]
  simp

/-- The partial sum at `n = 5` runs over the primes `2`, `3` and `5`. -/
example : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (5 + 1)), 1 / (p : ℝ) =
    1 / 2 + 1 / 3 + 1 / 5 := by
  rw [show Finset.filter Nat.Prime (Finset.range (5 + 1)) = {2, 3, 5} by decide]
  norm_num [Finset.sum_insert]

/-- The partial sums change only at primes: the composite `4` adds nothing. -/
example : ∑ p ∈ Finset.filter Nat.Prime (Finset.range (4 + 1)), 1 / (p : ℝ) =
    ∑ p ∈ Finset.filter Nat.Prime (Finset.range (3 + 1)), 1 / (p : ℝ) := by
  rw [show Finset.filter Nat.Prime (Finset.range (4 + 1)) =
    Finset.filter Nat.Prime (Finset.range (3 + 1)) by decide]

end MetaMathlibExt
