/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.NumberTheory.Composite
import Mathlib.Data.Int.Fib.Lemmas
import Mathlib.Data.Nat.Prime.Basic

/-!
# Fibonacci squares plus one

For every index `k ≥ 4`, Shakov's corollary gives the compositeness of `Nat.fib k ^ 2 + 1`.
Catalan's identity factors this number using Fibonacci indices at distance one or two from `k`.
-/

namespace MathlibExt.NumberTheory.ShakovTwoRegularWanted

-- Catalan's identity gives a nontrivial factorization when the starting index is odd
-- and the Fibonacci number at the offset is one.
private theorem composite_of_odd_start {n d : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hd : Nat.fib d = 1) : Nat.IsComposite (Nat.fib (n + d) ^ 2 + 1) := by
  have hfactor : Nat.fib (n + d) ^ 2 + 1 = Nat.fib n * Nat.fib (n + 2 * d) := by
    have h := Int.fib_add_sq_sub_fib_mul_fib_add_two_mul n d
    rw [Int.natAbs_natCast, hodd.neg_one_pow, Int.fib_natCast d, hd] at h
    apply Int.ofNat_inj.mp
    push_cast
    simp only [← Int.fib_natCast, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    omega
  have hleft : 1 < Nat.fib n := lt_of_lt_of_le (by decide : 1 < Nat.fib 3) (Nat.fib_mono hn)
  have hright := hleft.trans_le (Nat.fib_mono (Nat.le_add_right n (2 * d)))
  rw [hfactor]
  exact ⟨one_lt_mul_of_lt_of_le hleft hright.le, Nat.not_prime_mul hleft.ne' hright.ne'⟩

/-- **Fibonacci squares plus one are eventually composite.** Let $F_k$ denote the $k$-th
Fibonacci number, with $F_0 = 0$ and $F_1 = 1$. For every natural number $k \ge 4$, the number
$F_k^2 + 1$ is composite.

In the source's numbering of the Fibonacci numbers, which is shifted by one, this reads
"$F_n^2 + 1$ is composite for $n > 4$".

Source: Anton Shakov, "A 2-Regular Sequence That
Counts The Divisors of `n^2 + 1`", Corollary 10. -/
public theorem fib_sq_add_one_composite (k : ℕ) (hk : 4 ≤ k) :
    Nat.IsComposite (Nat.fib k ^ 2 + 1) := by
  by_cases heven : k % 2 = 0
  · rw [show k = (k - 1) + 1 by omega]
    exact composite_of_odd_start (by omega) (Nat.odd_iff.mpr (by omega)) Nat.fib_one
  · rw [show k = (k - 2) + 2 by omega]
    exact composite_of_odd_start (by omega) (Nat.odd_iff.mpr (by omega)) Nat.fib_two

end MathlibExt.NumberTheory.ShakovTwoRegularWanted
