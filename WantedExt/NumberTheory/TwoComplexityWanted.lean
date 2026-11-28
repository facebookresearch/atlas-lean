/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The 2-complexity of even positive integers

Statements from Pengcheng Zhang, "The 2-Complexity of Even
Positive Integers", *INTEGERS* 24 (2024), Article A109
(<https://math.colgate.edu/~integers/vol24.html>).

The paper's `l`-complexity `‖n‖_l` (for `l > 1` and `n` a
positive multiple of `l`) is the least number of copies of
`l` in an expression for `n` using addition, multiplication
and parentheses; here `CanBuild l k n` says `n` is obtained
from `k` copies of `l`, and `complexityL l n` is the least
such `k` (`0` when `n` is not obtainable, e.g. `l ∤ n`).
Logarithms are real (`Real.logb`). The extracted statements
flatten superscripts (`2m` for `2^m`, `lm` for `l^m`,
`6r` for `6^r`, `105` for `10^5`); the readings used here
were all verified by exhaustive BFS over expressions with
at most 14 copies of `2` (values up to `2^14`), 9 copies of
`3`, and 8 copies of `4`, which confirms every statement
below on that grid (for Theorem 2, the grid reaches
`2^m * 6^r` with `m + 3r ≤ 14` and `2^m * 10^r` with
`m + 4r ≤ 14`).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import MathlibExt.NumberTheory.TwoComplexityLowerBound
public import MathlibExt.NumberTheory.TwoComplexitySum
public import MathlibExt.NumberTheory.TwoComplexityComplexityLDecomp
public import MathlibExt.NumberTheory.TwoComplexityComplexityLEqAddOneIff
public import MathlibExt.NumberTheory.TwoComplexityComplexityLEqAddTwoOfForm
public import MathlibExt.NumberTheory.TwoComplexityComplexityLPowAddPow
public import MathlibExt.NumberTheory.TwoComplexityLogbTwoBounds

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoComplexityWanted

/-- **Logarithmic bounds for the $l$-complexity.** Write $\|n\|_l$ for the $l$-complexity of
$n$. Let $l > 1$ be a natural number and let $n$ be a positive multiple of $l$. Then
$\log_l n \le \|n\|_l \le l \log_l n - 1$, where $\log_l$ is the real logarithm to base $l$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 1. -/
theorem_wanted logb_le_complexityL_le (l n : ℕ) (hl : 1 < l)
    (hln : l ∣ n) (hn : 1 ≤ n) :
    Real.logb l n ≤ (complexityL l n : ℝ) ∧
      (complexityL l n : ℝ) ≤ l * Real.logb l n - 1

/-- **Even numbers in $(2^m, 2^{m+1}]$ with 2-complexity $m + 2$.** Write $\|n\|_2$ for the
2-complexity of $n$. Let $m \ge 3$ and let $n$ be an even natural number with
$2^m < n \le 2^{m+1}$. Then $\|n\|_2 = m + 2$ if and only if $n$ has one of the following
forms, where all exponents are natural numbers:
(a) $n = 2^m + 2^{m_2} + 2^{m_3}$ with $m > m_2 > m_3 \ge 1$;
(b) $n = 2^m + 2^{m_2} + 2^{m_3} + 2^{m_4}$ with $m > m_2 > m_3 > m_4 \ge 2$ and
$m + m_4 = m_2 + m_3$;
(c) $n = 2^m + 2^{m-3} + 2^{m_2} + 2^{m_2-1}$ with $m \ge m_2 + 3 \ge 6$;
(d) $n = 2^m + 2^{m-5} + 2^{m-6} + 2^{m-7}$ with $m \ge 10$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 4 and Theorem 1. -/
theorem_wanted complexityL_eq_add_two_iff (m n : ℕ)
    (hm : 3 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1)) :
    complexityL 2 n = m + 2 ↔ twoComplexityAddTwoForm m n

/-- **Lower bound for the 2-complexity of even sums of five or more distinct powers of two.**
Write $\|n\|_2$ for the 2-complexity of $n$. Let $n \ge 1$ be an even natural number and let $S$
be a finite set of natural numbers with at least five elements such that $n = \sum_{e \in S} 2^e$.
Then $\log_2 n + 2 \le \|n\|_2$, where $\log_2$ is the real base-2 logarithm.

This is a particular case of Corollary 4 of the source.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 4. -/
theorem_wanted logb_two_add_two_le_of_five_powers (n : ℕ)
    (s : Finset ℕ) (h2n : 2 ∣ n) (hn : 1 ≤ n)
    (hs : n = ∑ e ∈ s, 2 ^ e) (hcard : 5 ≤ s.card) :
    Real.logb 2 n + 2 ≤ (complexityL 2 n : ℝ)

/-- **The 2-complexity of $2^m \cdot 6^r$ for $1 \le r \le 7$.** Write $\|n\|_2$ for the
$2$-complexity of $n$. For all natural numbers $m$ and $r$ with $1 \le r \le 7$, one has
$\|2^m \cdot 6^r\|_2 = m + 3r$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 5 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_six_pow_eq (m r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 7) :
    complexityL 2 (2 ^ m * 6 ^ r) = m + 3 * r

/-- **Bounds for the 2-complexity of $2^m \cdot 6^r$ when $8 \le r \le 9$.** Write $\|n\|_2$ for
the $2$-complexity of $n$. For all natural numbers $m$ and $r$ with $8 \le r \le 9$, one has
$m + 3r - 1 \le \|2^m \cdot 6^r\|_2 \le m + 3r$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 5 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_six_pow_bounds
    (m r : ℕ) (hr1 : 8 ≤ r) (hr2 : r ≤ 9) :
    m + 3 * r - 1 ≤ complexityL 2 (2 ^ m * 6 ^ r) ∧
      complexityL 2 (2 ^ m * 6 ^ r) ≤ m + 3 * r

/-- **The 2-complexity of $2^m \cdot 10^r$ for $1 \le r \le 4$.** Write $\|n\|_2$ for the
$2$-complexity of $n$. For all natural numbers $m$ and $r$ with $1 \le r \le 4$, one has
$\|2^m \cdot 10^r\|_2 = m + 4r$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 6 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_ten_pow_eq (m r : ℕ)
    (hr1 : 1 ≤ r) (hr2 : r ≤ 4) :
    complexityL 2 (2 ^ m * 10 ^ r) = m + 4 * r

/-- **Bounds for the 2-complexity of $2^m \cdot 10^5$.** Write $\|n\|_2$ for the $2$-complexity
of $n$. For every natural number $m$, one has $m + 19 \le \|2^m \cdot 10^5\|_2 \le m + 20$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 6 and Theorem 2. -/
theorem_wanted complexityL_two_pow_mul_ten_pow_five_bounds
    (m : ℕ) :
    m + 19 ≤ complexityL 2 (2 ^ m * 10 ^ 5) ∧
      complexityL 2 (2 ^ m * 10 ^ 5) ≤ m + 20

end MathlibExt.NumberTheory.TwoComplexityWanted
