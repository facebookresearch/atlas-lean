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
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Find
public import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.TwoComplexityWanted

/-- **Numbers built from copies of $l$.** For natural numbers $l$, $k$ and $n$, the number $n$
can be built from $k$ copies of $l$ when $n$ is the value of an expression that uses exactly $k$
copies of $l$, combined by addition and multiplication with arbitrary parentheses. Inductively,
$l$ is built from $1$ copy, and if $x$ is built from $a$ copies and $y$ from $b$ copies, then
$x + y$ and $x y$ are built from $a + b$ copies. -/
inductive CanBuild (l : ℕ) : ℕ → ℕ → Prop
  | base : CanBuild l 1 l
  | add {a b x y : ℕ} : CanBuild l a x → CanBuild l b y →
      CanBuild l (a + b) (x + y)
  | mul {a b x y : ℕ} : CanBuild l a x → CanBuild l b y →
      CanBuild l (a + b) (x * y)

/-- **The $l$-complexity of a natural number.** For natural numbers $l$ and $n$, the
$l$-complexity $\|n\|_l$ of $n$ is the least number $k$ such that $n$ can be built from $k$
copies of $l$ using addition and multiplication (with arbitrary parentheses), and
$\|n\|_l = 0$ if $n$ cannot be built from copies of $l$ at all. -/
noncomputable def complexityL (l n : ℕ) : ℕ := by
  classical
  exact if h : ∃ k, CanBuild l k n then Nat.find h else 0

/-- **Every build uses at least one copy.** If $n$ can be obtained from $k$ copies of $l$ using
addition and multiplication, then $k \ge 1$. -/
theorem CanBuild.one_le {l k n : ℕ} (h : CanBuild l k n) : 1 ≤ k := by
  induction h with
  | base => exact Nat.le_refl 1
  | add _ _ iha _ => exact Nat.le_add_right_of_le iha
  | mul _ _ iha _ => exact Nat.le_add_right_of_le iha

/-- **A buildable number is built from as many copies as its $l$-complexity.** For natural
numbers $l$ and $n$, if $n$ can be built from some number of copies of $l$ using addition and
multiplication, then $n$ can be built in this way from $c$ copies of $l$, where $c$ is the
$l$-complexity of $n$. -/
theorem complexityL_spec {l n : ℕ} (h : ∃ k, CanBuild l k n) :
    CanBuild l (complexityL l n) n := by
  classical
  unfold complexityL
  rw [dif_pos h]
  exact Nat.find_spec h

/-- **The $l$-complexity is at most the size of any build.** For natural numbers $l$, $k$ and
$n$, if $n$ can be built from $k$ copies of $l$ using addition and multiplication, then the
$l$-complexity of $n$ is at most $k$. -/
theorem complexityL_min_le {l n k : ℕ} (h : CanBuild l k n) :
    complexityL l n ≤ k := by
  classical
  unfold complexityL
  rw [dif_pos ⟨k, h⟩]
  exact Nat.find_min' ⟨k, h⟩ h

/-- **The $l$-complexity vanishes exactly on numbers that cannot be built.** For natural
numbers $l$ and $n$, the $l$-complexity of $n$ is $0$ if and only if there is no $k$ such that
$n$ can be built from $k$ copies of $l$ using addition and multiplication. -/
theorem complexityL_eq_zero_iff {l n : ℕ} :
    complexityL l n = 0 ↔ ¬ ∃ k, CanBuild l k n := by
  classical
  by_cases h : ∃ k, CanBuild l k n
  · constructor
    · intro h0
      have hspec := complexityL_spec h
      rw [h0] at hspec
      exact absurd hspec.one_le (by simp)
    · intro hne
      exact absurd h hne
  · simp [complexityL, h]

/-- **Zhang's four exceptional forms.** For natural numbers $m$ and $n$, $n$ has one of the four
exceptional forms for $m$ when one of the following holds:
(a) $n = 2^m + 2^{m_2} + 2^{m_3}$ for some natural numbers $m > m_2 > m_3 \ge 1$;
(b) $n = 2^m + 2^{m_2} + 2^{m_3} + 2^{m_4}$ for some natural numbers $m > m_2 > m_3 > m_4 \ge 2$
with $m + m_4 = m_2 + m_3$;
(c) $n = 2^m + 2^{m-3} + 2^{m_2} + 2^{m_2 - 1}$ for some natural number $m_2$ with
$m \ge m_2 + 3 \ge 6$;
(d) $m \ge 10$ and $n = 2^m + 2^{m-5} + 2^{m-6} + 2^{m-7}$.

These are the forms of Corollary 3 and Theorem 1(2) of Zhang's paper, which concern even $n$
with $2^m < n \le 2^{m+1}$ and 2-complexity $m + 2$. -/
def twoComplexityAddTwoForm (m n : ℕ) : Prop :=
  (∃ m2 m3 : ℕ, m2 < m ∧ m3 < m2 ∧ 1 ≤ m3 ∧
    n = 2 ^ m + 2 ^ m2 + 2 ^ m3) ∨
  (∃ m2 m3 m4 : ℕ, m2 < m ∧ m3 < m2 ∧ m4 < m3 ∧ 2 ≤ m4 ∧
    m + m4 = m2 + m3 ∧
    n = 2 ^ m + 2 ^ m2 + 2 ^ m3 + 2 ^ m4) ∨
  (∃ m2 : ℕ, m2 + 3 ≤ m ∧ 6 ≤ m2 + 3 ∧
    n = 2 ^ m + 2 ^ (m - 3) + 2 ^ m2 + 2 ^ (m2 - 1)) ∨
  (10 ≤ m ∧
    n = 2 ^ m + 2 ^ (m - 5) + 2 ^ (m - 6) + 2 ^ (m - 7))

/-- **The largest number built from $m$ copies of $l$.** Let $l > 1$ and $m \ge 1$ be natural
numbers. Then $l^m$ can be built from exactly $m$ copies of $l$ using addition and
multiplication, and every natural number that can be built from $m$ copies of $l$ in this way
is at most $l^m$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 1. -/
theorem_wanted canBuild_max (l m : ℕ) (hl : 1 < l)
    (hm : 1 ≤ m) :
    CanBuild l m (l ^ m) ∧
      ∀ n : ℕ, CanBuild l m n → n ≤ l ^ m

/-- **Logarithmic bounds for the $l$-complexity.** Write $\|n\|_l$ for the $l$-complexity of
$n$. Let $l > 1$ be a natural number and let $n$ be a positive multiple of $l$. Then
$\log_l n \le \|n\|_l \le l \log_l n - 1$, where $\log_l$ is the real logarithm to base $l$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 1. -/
theorem_wanted logb_le_complexityL_le (l n : ℕ) (hl : 1 < l)
    (hln : l ∣ n) (hn : 1 ≤ n) :
    Real.logb l n ≤ (complexityL l n : ℝ) ∧
      (complexityL l n : ℝ) ≤ l * Real.logb l n - 1

/-- **The $l$-complexity of $l^m + l^{m'}$.** Write $\|n\|_l$ for the $l$-complexity of $n$.
For natural numbers $l > 1$ and $m \ge m' \ge 1$, $\|l^m + l^{m'}\|_l = m + 1$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 1. -/
theorem_wanted complexityL_pow_add_pow (l m m' : ℕ)
    (hl : 1 < l) (h : m' ≤ m) (hm' : 1 ≤ m') :
    complexityL l (l ^ m + l ^ m') = m + 1

/-- **The 2-complexity of a power of two and of a sum of two powers of two.** Write
$\|n\|_2$ for the $2$-complexity of $n$. For all natural numbers $m_1$ and $m_2$ with
$m_1 > m_2 \ge 1$, one has $\|2^{m_1}\|_2 = m_1$ and $\|2^{m_1} + 2^{m_2}\|_2 = m_1 + 1$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
theorem_wanted complexityL_two_pow_and_add (m1 m2 : ℕ)
    (h : m2 < m1) (hm2 : 1 ≤ m2) :
    complexityL 2 (2 ^ m1) = m1 ∧
      complexityL 2 (2 ^ m1 + 2 ^ m2) = m1 + 1

/-- **An upper bound for the 2-complexity of a sum of distinct powers of two.** Write
$\|n\|_2$ for the $2$-complexity of $n$. Let $S$ be a nonempty finite set of positive integers
with $k$ elements and largest element $m_1$. Then $\|\sum_{e \in S} 2^e\|_2 \le m_1 + k - 1$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
theorem_wanted complexityL_sum_two_pow_le (s : Finset ℕ)
    (hs : ∀ e ∈ s, 1 ≤ e) (hne : s.Nonempty) :
    complexityL 2 (∑ e ∈ s, 2 ^ e) ≤ s.max' hne + s.card - 1

/-- **Logarithmic bounds for the 2-complexity (Zhang's Lemma 3(3)).** Write $\|n\|_2$ for the
2-complexity of $n$: the least number of copies of $2$ from which $n$ can be built using addition
and multiplication, and $0$ if $n$ cannot be built. For every even natural number $n \ge 1$,
$\log_2 n \le \|n\|_2 \le 2 \log_2 n - 1$, where $\log_2$ is the real base-2 logarithm.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Lemma 3. -/
theorem_wanted logb_two_bounds (n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n) :
    Real.logb 2 n ≤ (complexityL 2 n : ℝ) ∧
      (complexityL 2 n : ℝ) ≤ 2 * Real.logb 2 n - 1

/-- **A lower bound for the 2-complexity outside sums of two powers of two.** Write
$\|n\|_2$ for the $2$-complexity of $n$. Let $n$ be a positive even integer that cannot be
written as $2^a + 2^b$ with natural numbers $a \le b$. Then $\log_2 n + 1 \le \|n\|_2$.

Since $n$ is even, the hypothesis says that $n$ is neither a power of $2$ nor a sum of two
distinct powers of $2$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 2. -/
theorem_wanted logb_two_add_one_le (n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n)
    (hform : ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b) :
    Real.logb 2 n + 1 ≤ (complexityL 2 n : ℝ)

/-- **Adding a small multiple of $l$ to a multiple of $l^2$.** Write $\|n\|_l$ for the
$l$-complexity of $n$. Let $l > 1$, let $b \ge 1$ be a multiple of $l^2$, let $a$ be a natural
number with $a \le l - 1$, and let $n = b + a l$. Then $\|n\|_l = \|b\|_l + a$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 2. -/
theorem_wanted complexityL_decomp (l n b a : ℕ) (hl : 1 < l)
    (hn : n = b + a * l) (hb : l ^ 2 ∣ b) (hb0 : 1 ≤ b)
    (ha : a ≤ l - 1) :
    complexityL l n = complexityL l b + a

/-- **Even $n$ with $2^m < n \le 2^{m+1}$ and 2-complexity $m + 1$.** Write $\|n\|_2$ for the
2-complexity of $n$. Let $m \ge 1$ and let $n$ be an even natural number with
$2^m < n \le 2^{m+1}$. Then $\|n\|_2 = m + 1$ if and only if $n = 2^m + 2^t$ for some natural
number $t$ with $1 \le t \le m$.

The case $t = m$ gives $n = 2^{m+1}$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Proposition 3 and Theorem 1. -/
theorem_wanted complexityL_eq_add_one_iff (m n : ℕ)
    (hm : 1 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1)) :
    complexityL 2 n = m + 1 ↔
      ∃ t : ℕ, 1 ≤ t ∧ t ≤ m ∧ n = 2 ^ m + 2 ^ t

/-- **Four forms of even numbers with 2-complexity $m + 2$.** Write $\|n\|_2$ for the
2-complexity of $n$. Let $m \ge 3$ and let $n$ be an even natural number with
$2^m < n \le 2^{m+1}$. Suppose that $n$ has one of the following forms, where all exponents
are natural numbers:
(a) $n = 2^m + 2^{m_2} + 2^{m_3}$ with $m > m_2 > m_3 \ge 1$;
(b) $n = 2^m + 2^{m_2} + 2^{m_3} + 2^{m_4}$ with $m > m_2 > m_3 > m_4 \ge 2$ and
$m + m_4 = m_2 + m_3$;
(c) $n = 2^m + 2^{m-3} + 2^{m_2} + 2^{m_2-1}$ with $m \ge m_2 + 3 \ge 6$;
(d) $n = 2^m + 2^{m-5} + 2^{m-6} + 2^{m-7}$ with $m \ge 10$.
Then $\|n\|_2 = m + 2$.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 3. -/
theorem_wanted complexityL_eq_add_two_of_form (m n : ℕ)
    (hm : 3 ≤ m) (h2n : 2 ∣ n) (hn1 : 2 ^ m < n)
    (hn2 : n ≤ 2 ^ (m + 1))
    (hform : twoComplexityAddTwoForm m n) :
    complexityL 2 n = m + 2

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

/-- **Lower bound $\log_2 n + 2$ for the 2-complexity (Zhang's Corollary 4).** Write $\|n\|_2$
for the 2-complexity of $n$: the least number of copies of $2$ from which $n$ can be built using
addition and multiplication, and $0$ if $n$ cannot be built. Let $m$ and $n$ be natural numbers
with $n$ even, $n \ge 1$ and $2^m < n \le 2^{m+1}$. Suppose that $n \ne 2^a + 2^b$ for all
natural numbers $a \le b$, and that $n$ has none of Zhang's four exceptional forms for $m$.
Then $\log_2 n + 2 \le \|n\|_2$, where $\log_2$ is the real base-2 logarithm.

Source: Pengcheng Zhang, "The 2-Complexity of Even Positive
Integers", Corollary 4. -/
theorem_wanted logb_two_add_two_le (m n : ℕ) (h2n : 2 ∣ n)
    (hn : 1 ≤ n) (hn1 : 2 ^ m < n) (hn2 : n ≤ 2 ^ (m + 1))
    (hpow : ¬ ∃ a b : ℕ, a ≤ b ∧ n = 2 ^ a + 2 ^ b)
    (hform : ¬ twoComplexityAddTwoForm m n) :
    Real.logb 2 n + 2 ≤ (complexityL 2 n : ℝ)

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
