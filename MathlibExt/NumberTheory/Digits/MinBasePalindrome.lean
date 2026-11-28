/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/Data/Nat/Digits/Div.lean` (Mathlib):
Copyright (c) 2020 Kim Morrison. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kim Morrison, Shing Tak Lam, Mario Carneiro
-/

module

public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Defs
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Digits.Div

/-!
# Even-length palindromes are divisible by the base plus one

Let `b ≥ 2`. If the base-`b` digits of a natural number `N` form a palindrome with an even number
of digits, then `b + 1` divides `N` (`MetaMathlibExt.succ_dvd_of_palindrome_even_length`). The
base-`b` digits of `N` are Mathlib's little-endian list `Nat.digits b N`, and `N` is a palindrome
in base `b` when this list is a `List.Palindrome`. For `b = 10` the theorem is Mathlib's
`Nat.eleven_dvd_of_palindrome`. If `N = p ^ n` for a prime `p`, every divisor of `N` is a power
of `p`, so the base has the form `p ^ x - 1`
(`MetaMathlibExt.base_eq_prime_pow_sub_one_of_palindrome`). In particular, if the base-`b`
digits of `2 ^ n` form a palindrome with an even number of digits, then `b = 2 ^ x - 1` for some
`x` (`MetaMathlibExt.base_eq_two_pow_sub_one_of_palindrome`).

## Proof outline

Since `b ≡ -1 [ZMOD b + 1]`, the number `N = ∑ i, c i * b ^ i` with digits `c i` is congruent
modulo `b + 1` to the alternating sum `∑ i, (-1) ^ i * c i` of its digits
(`Nat.dvd_iff_dvd_ofDigits`, `Nat.ofDigits_neg_one`). Reversing a list of even length negates its
alternating sum (`List.alternatingSum_reverse`), and the digit list of `N` is its own reverse, so
this alternating sum is zero. The proof adapts Mathlib's proof of `Nat.eleven_dvd_of_palindrome`
to an arbitrary base. The source groups the terms in pairs instead: for digits
`c 0, …, c (2 * k + 1)` with `c i = c (2 * k + 1 - i)` it writes `N` as the sum over `i ≤ k` of
`c i * (b ^ i + b ^ (2 * k + 1 - i))`, and `b + 1` divides each `b ^ i + b ^ (2 * k + 1 - i)`.

## Implementation notes

The hypothesis `2 ≤ b` follows the source, whose bases are at least `2`; the proof does not use
it, so the conclusion holds in every base. The theorem keeps the full name and the statement it
had as a wanted theorem in `WantedExt.NumberTheory.Digits.MinBasePalindromeWanted`, so the
hypothesis stays and the unused-variables linter is turned off for this declaration only.

The source proves the statement for powers of two directly from the divisibility lemma and
generalizes it to prime powers afterwards. Here the power-of-two statement is derived as the case
`p = 2` of the prime-power theorem.

## References

* D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic Representations of Powers of 2*,
  INTEGERS 24 (2024), Article A69; preprint arXiv:2401.07351, Lemma 2.2 and its proof,
  Corollary 2.3 and Theorem 3.1 (<https://arxiv.org/abs/2401.07351>).
-/

@[expose] public section

namespace MetaMathlibExt

set_option linter.unusedVariables false in
/-- **Even-length palindromes are divisible by the base plus one.** Let $b \ge 2$ and let $N$ be a
natural number whose base-$b$ digits form a palindrome with an even number of digits. Then
$b + 1$ divides $N$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 3
(`integers-2024-A69-lem-3`). -/
theorem succ_dvd_of_palindrome_even_length (N b : ℕ) (hb : 2 ≤ b)
    (hp : (Nat.digits b N).Palindrome) (he : Even (Nat.digits b N).length) : b + 1 ∣ N := by
  -- The alternating sum of the digits, read as integers, vanishes: reversing a list of even
  -- length negates its alternating sum, and the digit list is its own reverse.
  have h0 : ((Nat.digits b N).map fun d : ℕ => (d : ℤ)).alternatingSum = 0 := by
    have h := ((Nat.digits b N).map fun d : ℕ => (d : ℤ)).alternatingSum_reverse
    rw [(hp.map _).reverse_eq, List.length_map, pow_succ', he.neg_one_pow, mul_one,
      neg_one_zsmul] at h
    omega
  -- Since `b ≡ -1 [ZMOD b + 1]`, `N` is congruent to that alternating sum modulo `b + 1`.
  rw [Nat.dvd_iff_dvd_ofDigits (b + 1) b (-1) (by simp) N, Nat.ofDigits_neg_one, h0]
  exact dvd_zero _

/-- **Even-length palindromic prime powers have base one less than a power of the prime.** Let
$p$ be a prime and let $n$ and $b \ge 2$ be natural numbers. If the base-$b$ representation of
$p^n$ is a palindrome with an even number of digits, then $b = p^x - 1$ for some natural number
$x$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 6
(`integers-2024-A69-thm-6`). -/
theorem base_eq_prime_pow_sub_one_of_palindrome (p n b : ℕ) (hp : p.Prime)
    (hb : 2 ≤ b) (hpal : (Nat.digits b (p ^ n)).Palindrome)
    (he : Even (Nat.digits b (p ^ n)).length) : ∃ x, b = p ^ x - 1 := by
  have hdvd := succ_dvd_of_palindrome_even_length (p ^ n) b hb hpal he
  obtain ⟨x, _, hx⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  exact ⟨x, Nat.eq_sub_of_add_eq hx⟩

/-- **Even-length palindromic powers of 2 have base one less than a power of 2.** Let $n$ and
$b \ge 2$ be natural numbers. If the base-$b$ representation of $2^n$ is a palindrome with an
even number of digits, then $b = 2^x - 1$ for some natural number $x$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Corollary 2
(`integers-2024-A69-cor-2`). -/
theorem base_eq_two_pow_sub_one_of_palindrome (n b : ℕ) (hb : 2 ≤ b)
    (hp : (Nat.digits b (2 ^ n)).Palindrome) (he : Even (Nat.digits b (2 ^ n)).length) :
    ∃ x, b = 2 ^ x - 1 :=
  base_eq_prime_pow_sub_one_of_palindrome 2 n b Nat.prime_two hb hp he

end MetaMathlibExt
