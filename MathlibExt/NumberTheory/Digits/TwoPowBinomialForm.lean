/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.SmallBaseBinomialForm
import MathlibExt.NumberTheory.Digits.BinomialDigits

/-!
# A sufficient condition for binomial forms of powers of two

Statement from D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69 (arXiv:2401.07351).

The main result, `hasBinomialForm_two_pow`, is the corollary in the paper's introduction
(Corollary 1.3 of arXiv:2401.07351): if `n = x * k + r` with `1 ≤ k` and
`2 ^ r * k.choose ((k + 1) / 2) < 2 ^ x - 1`, where `(k + 1) / 2` is `⌈k / 2⌉`, then `2 ^ n` has a
base-`(2 ^ x - 1)` representation in binomial form. As in the paper's proof, with `b = 2 ^ x - 1`
and `α = 2 ^ r` we have `2 ^ n = α * (1 + b) ^ k`, so the scaled binomial digit expansion
`digits_mul_one_add_pow` (Lemma 1.2 there) gives the digits `α * k.choose i`.
-/

namespace MetaMathlibExt

/-- **Sufficient condition for a binomial form of a power of 2.** Let $n$, $x$, $k$ and $r$ be
natural numbers with $k \ge 1$, $n = xk + r$ and $2^r\binom{k}{\lceil k/2 \rceil} < 2^x - 1$.
Then $2^n$ has a base-$(2^x - 1)$ representation in binomial form.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Corollary 1
(`integers-2024-A69-cor-1`). -/
public theorem hasBinomialForm_two_pow (n x k r : ℕ) (hk : 1 ≤ k) (hn : n = x * k + r)
    (h : 2 ^ r * k.choose ((k + 1) / 2) < 2 ^ x - 1) : HasBinomialForm (2 ^ x - 1) (2 ^ n) := by
  have hα : 1 ≤ (2 : ℕ) ^ r := Nat.one_le_two_pow
  have hdigits := digits_mul_one_add_pow (2 ^ r) k (2 ^ x - 1) hα h
  have hbase : 1 + (2 ^ x - 1 : ℕ) = 2 ^ x := by
    have hx : 1 ≤ (2 : ℕ) ^ x := Nat.one_le_two_pow
    omega
  rw [hbase, ← pow_mul, ← pow_add, Nat.add_comm r, ← hn] at hdigits
  exact ⟨2 ^ r, k, hα, hk, hdigits⟩

end MetaMathlibExt
