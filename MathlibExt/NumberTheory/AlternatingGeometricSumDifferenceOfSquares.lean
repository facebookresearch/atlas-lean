/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.Ring.Int.Parity

/-!
# Alternating geometric sums as differences of squares

An alternating geometric sum with an odd base and an odd number of terms is odd, so it is
the difference of two consecutive integer squares.
-/

namespace MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted

/-- **Alternating geometric sums for primes $p \equiv 3 \pmod 4$ and odd $n$ are differences of
two squares.** Let $p$ be a prime with $p \equiv 3 \pmod 4$ and let $n$ be a positive odd integer.
Then there are integers $a, b$ with
$\sum_{j=0}^{p-1} (-1)^j p^{nj} = 1 - p^n + p^{2n} - \cdots + p^{(p-1)n} = a^2 - b^2$.

Source: Lorenz Halbeisen, Norbert Hungerbühler, and
Franz Lemmermeyer, "Geometric Sums as Sums of Two
Squares", Proposition 9. -/
public theorem altGeomSum_eq_sq_sub_sq (p n : ℕ) (hp : p.Prime)
    (hp4 : p % 4 = 3) (hn : Odd n) (hn0 : 0 < n) :
    ∃ a b : ℤ,
      (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) =
        a ^ 2 - b ^ 2 := by
  have hpOdd : Odd (p : ℤ) := (Int.odd_natCast p).2 (hp.odd_of_ne_two (by omega))
  have hbase : Odd ((-(p : ℤ)) ^ n) := (Int.odd_pow' hn0.ne').2 hpOdd.neg
  have hterm (j : ℕ) : (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j) ≡ 1 [ZMOD 2] := by
    rw [pow_mul, ← mul_pow, ← neg_eq_neg_one_mul, ← hn.neg_pow]
    exact Int.odd_iff.mp hbase.pow
  have hsum : (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (p : ℤ) ^ (n * j)) ≡ (p : ℤ) [ZMOD 2] := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_one] using
      Int.ModEq.sum (s := Finset.range p) (fun j _ ↦ hterm j)
  have hpOne : (p : ℤ) ≡ 1 [ZMOD 2] := Int.odd_iff.mp hpOdd
  obtain ⟨k, hk⟩ := Int.odd_iff.mpr (hsum.trans hpOne)
  refine ⟨k + 1, k, hk.trans ?_⟩
  rw [sq_sub_sq, add_sub_cancel_left, mul_one, two_mul, add_right_comm]

end MathlibExt.NumberTheory.GeometricSumsTwoSquaresWanted
