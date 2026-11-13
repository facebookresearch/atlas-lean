/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# An alternating sum of the floor function of square roots

Statement from Marc Chamberland and Karl Dilcher, "An Alternating Sum
of the Floor Function of Square Roots", *Journal of Integer Sequences*
29 (2026), Article 26.2.1
(<https://cs.uwaterloo.ca/journals/JIS/VOL29/Dilcher/dilcher24.html>).

For a natural number `a`, `Nat.sqrt a` is the integer floor of `√a`.
The sum is stated over `ℤ`, with the right-hand side written as the
natural-number quotient `(n + 1) / 2`, which is exact for odd `n`.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

open scoped BigOperators

namespace MathlibExt.NumberTheory.AlternatingFloorSqrtSumWanted

/-- **An alternating sum of floors of square roots.** For every odd positive integer $n$,
$\sum_{j=1}^{n} (-1)^{j+1} \lfloor \sqrt{jn} \rfloor = (n+1)/2$.

Source: Marc Chamberland and Karl Dilcher, "An Alternating Sum of the
Floor Function of Square Roots", Theorem 1 (TeX label `thm:7.1`). -/
theorem_wanted alternating_sum_floor_sqrt_mul
    {n : ℕ} (hn : 1 ≤ n) (hodd : Odd n) :
    (∑ j ∈ Finset.Icc 1 n,
      (-1 : ℤ) ^ (j + 1) * (Nat.sqrt (j * n) : ℤ)) =
      (((n + 1) / 2 : ℕ) : ℤ)

end MathlibExt.NumberTheory.AlternatingFloorSqrtSumWanted
