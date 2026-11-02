/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.List.Palindrome
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Minimum-base palindromic representations of powers of 2

Statements from D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69
(arXiv:2401.07351).

The base-`b` representation `(c_k, …, c_0)_b` of `N` (leading digit nonzero) is
Mathlib's little-endian `Nat.digits b N = [c_0, …, c_k]`; `N` is a palindrome in
base `b` when this list is a `List.Palindrome`. A `(k+1)`-digit representation
has `(Nat.digits b N).length = k + 1`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Minimum palindromic base.** For a natural number $N$, $b(N)$ is the smallest base $b \ge 2$
in which $N$ is a palindrome, that is, in which the base-$b$ digits of $N$ read the same forwards
and backwards. Such a base exists: $0$ has no digits and is a palindrome in every base, and for
$N \ge 1$ the number $N$ is written with the single digit $N$ in base $N + 1$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1. -/
public noncomputable def minPalindromicBase (N : ℕ) : ℕ :=
  sInf {b | 2 ≤ b ∧ (Nat.digits b N).Palindrome}

/-- **Binomial form.** A natural number $N$ has a base-$b$ representation in binomial form if
there are natural numbers $\alpha \ge 1$ and $k \ge 1$ such that the base-$b$ digits of $N$, from
the most significant to the least significant, are
$\alpha\binom{k}{k}, \alpha\binom{k}{k-1}, \dots, \alpha\binom{k}{0}$.

The one-digit case $k = 0$ is excluded as degenerate.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1
(definition of binomial form). -/
public def HasBinomialForm (b N : ℕ) : Prop :=
  ∃ α k : ℕ, 1 ≤ α ∧ 1 ≤ k ∧ Nat.digits b N = (List.range (k + 1)).map fun i => α * k.choose i

/-- **The minimum palindromic base of two.** The smallest base $b \ge 2$ in which the number $2$
is a palindrome is $b(2) = 3$: in base $2$ the number $2$ is written $(1, 0)_2$, which is not a
palindrome, while in base $3$ it is the one-digit palindrome $(2)_3$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Table 1. -/
public theorem minPalindromicBase_two : minPalindromicBase 2 = 3 := by
  have h3 : (3 : ℕ) ∈ {b | 2 ≤ b ∧ (Nat.digits b 2).Palindrome} := by
    refine ⟨by norm_num, ?_⟩
    rw [show Nat.digits 3 2 = [2] by norm_num]
    exact List.Palindrome.singleton 2
  unfold minPalindromicBase
  apply le_antisymm (Nat.sInf_le h3)
  apply le_csInf ⟨3, h3⟩
  rintro b ⟨hb, hp⟩
  by_contra h
  have hb2 : b = 2 := by omega
  subst hb2
  rw [show Nat.digits 2 2 = [0, 1] by norm_num] at hp
  have := hp.reverse_eq
  simp at this

/-- **The binomial form of 2023 in base 16.** The number $2023$ has a base-$16$ representation in
binomial form: its base-$16$ digits are $7, 14, 7$, that is
$7\binom{2}{2}, 7\binom{2}{1}, 7\binom{2}{0}$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Section 1. -/
public theorem hasBinomialForm_16_2023 : HasBinomialForm 16 2023 :=
  ⟨7, 2, by norm_num, by norm_num, by norm_num [List.range_succ]⟩

/-- **Brown's theorem on minimal palindromic base one less than the number.** Let $N \ge 1$ be a
natural number and let $b(N)$ be the smallest base $b \ge 2$ in which $N$ is a palindrome. If
$b(N) = N - 1$, then $N \in \{3, 4, 6\}$, or $N > 6$ and $N$ is prime.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 1
(`integers-2024-A69-thm-1`), credited to K. Brown. -/
public theorem_wanted minPalindromicBase_eq_pred (N : ℕ) (hN : 1 ≤ N)
    (h : minPalindromicBase N = N - 1) : N = 3 ∨ N = 4 ∨ N = 6 ∨ (6 < N ∧ N.Prime)

/-- **Digits of a multiple of a power of one more than the base.** Let $\alpha \ge 1$, $k$ and $b$
be natural numbers with $\alpha\binom{k}{\lceil k/2 \rceil} < b$. Then the base-$b$
representation of $\alpha(1 + b)^k$ has exactly the $k + 1$ digits
$\alpha\binom{k}{k}, \alpha\binom{k}{k-1}, \dots, \alpha\binom{k}{0}$, from the most significant
to the least significant.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 1
(`integers-2024-A69-lem-1`). -/
public theorem_wanted digits_mul_one_add_pow (α k b : ℕ) (hα : 1 ≤ α)
    (h : α * k.choose ((k + 1) / 2) < b) :
    Nat.digits b (α * (1 + b) ^ k) = (List.range (k + 1)).map fun i => α * k.choose i

/-- **Sufficient condition for a binomial form of a power of 2.** Let $n$, $x$, $k$ and $r$ be
natural numbers with $k \ge 1$, $n = xk + r$ and $2^r\binom{k}{\lceil k/2 \rceil} < 2^x - 1$.
Then $2^n$ has a base-$(2^x - 1)$ representation in binomial form.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Corollary 1
(`integers-2024-A69-cor-1`). -/
public theorem_wanted hasBinomialForm_two_pow (n x k r : ℕ) (hk : 1 ≤ k) (hn : n = x * k + r)
    (h : 2 ^ r * k.choose ((k + 1) / 2) < 2 ^ x - 1) : HasBinomialForm (2 ^ x - 1) (2 ^ n)

/-- **Bases of binomial forms of powers of 2.** Let $n$, $b \ge 2$, $\alpha \ge 1$ and $k \ge 1$
be natural numbers. If the base-$b$ digits of $2^n$, from the most significant to the least
significant, are $\alpha\binom{k}{k}, \alpha\binom{k}{k-1}, \dots, \alpha\binom{k}{0}$, then
$b = 2^x - 1$ for some natural number $x \le n$, and $\alpha = 2^i$ for some natural number $i$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 2
(`integers-2024-A69-lem-2`). -/
public theorem_wanted binomialForm_two_pow_base (n b α k : ℕ) (hb : 2 ≤ b) (hα : 1 ≤ α)
    (hk : 1 ≤ k) (h : Nat.digits b (2 ^ n) = (List.range (k + 1)).map fun i => α * k.choose i) :
    (∃ x ≤ n, b = 2 ^ x - 1) ∧ ∃ i, α = 2 ^ i

/-- **Even-length palindromes are divisible by the base plus one.** Let $b \ge 2$ and let $N$ be a
natural number whose base-$b$ digits form a palindrome with an even number of digits. Then
$b + 1$ divides $N$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 3
(`integers-2024-A69-lem-3`). -/
public theorem_wanted succ_dvd_of_palindrome_even_length (N b : ℕ) (hb : 2 ≤ b)
    (hp : (Nat.digits b N).Palindrome) (he : Even (Nat.digits b N).length) : b + 1 ∣ N

/-- **Even-length palindromic powers of 2 have base one less than a power of 2.** Let $n$ and
$b \ge 2$ be natural numbers. If the base-$b$ representation of $2^n$ is a palindrome with an
even number of digits, then $b = 2^x - 1$ for some natural number $x$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Corollary 2
(`integers-2024-A69-cor-2`). -/
public theorem_wanted base_eq_two_pow_sub_one_of_palindrome (n b : ℕ) (hb : 2 ≤ b)
    (hp : (Nat.digits b (2 ^ n)).Palindrome) (he : Even (Nat.digits b (2 ^ n)).length) :
    ∃ x, b = 2 ^ x - 1

/-- **Three-digit palindromic powers of two.** Let $n$ be a natural number, let $b \ge 2$ be a
base, and let $c = 2^n \bmod b$. The base-$b$ representation of $2^n$ is a palindrome with exactly
three digits if and only if $b^2 + 1 \le 2^n \le b^3 - 1$, $c \ne 0$, and
$\frac{1}{b} \lfloor 2^n / b \rfloor - \frac{b - 1}{b} \le c \le
\frac{1}{b} \lfloor 2^n / b \rfloor$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 2
(`integers-2024-A69-thm-2`). -/
public theorem_wanted three_digit_palindrome_two_pow_iff (n b : ℕ) (hb : 2 ≤ b) :
    ((Nat.digits b (2 ^ n)).Palindrome ∧ (Nat.digits b (2 ^ n)).length = 3) ↔
      b ^ 2 + 1 ≤ 2 ^ n ∧ 2 ^ n ≤ b ^ 3 - 1 ∧ 2 ^ n % b ≠ 0 ∧
        ((2 ^ n / b : ℕ) : ℚ) / b - ((b : ℚ) - 1) / b ≤ ((2 ^ n % b : ℕ) : ℚ) ∧
        ((2 ^ n % b : ℕ) : ℚ) ≤ ((2 ^ n / b : ℕ) : ℚ) / b

/-- **Three-digit binomial forms of powers of two.** Let $n$ and $\alpha \ge 1$ be natural numbers
and let $b \ge 2$ be a base. The base-$b$ representation of $2^n$ is
$(\alpha, 2\alpha, \alpha)_b$ if and only if there is a natural number $i$ with $3i + 2 < n$,
$n \equiv i \pmod 2$, $\alpha = 2^i$ and $b = 2^{(n - i)/2} - 1$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 3
(`integers-2024-A69-thm-3`). -/
public theorem_wanted three_digit_binomialForm_two_pow_iff (n b α : ℕ) (hb : 2 ≤ b)
    (hα : 1 ≤ α) :
    Nat.digits b (2 ^ n) = [α, 2 * α, α] ↔
      ∃ i : ℕ, 3 * i + 2 < n ∧ n % 2 = i % 2 ∧ α = 2 ^ i ∧ b = 2 ^ ((n - i) / 2) - 1

/-- **Three-digit representations of powers of two with outer digits one.** Let $n$ be a natural
number and $b \ge 2$ a base. There is a digit $c \ne 2$ such that the base-$b$ representation of
$2^n$ is $(1, c, 1)_b$, that is, $2^n = 1 + cb + b^2$ with $0 \le c < b$, if and only if
(i) $2^n - 1 = kb$ for some natural number $k$ with $b \le k \le 2b - 1$, and (ii) it is not the
case that $n$ is even and $b = 2^{n/2} - 1$.

The excluded digit $c = 2$ gives the binomial form $(1, 2, 1)_b = (b + 1)^2$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 4
(`integers-2024-A69-thm-4`). -/
public theorem_wanted one_c_one_two_pow_iff (n b : ℕ) (hb : 2 ≤ b) :
    (∃ c, c ≠ 2 ∧ Nat.digits b (2 ^ n) = [1, c, 1]) ↔
      (∃ k, 2 ^ n - 1 = k * b ∧ b ≤ k ∧ k ≤ 2 * b - 1) ∧ ¬ (Even n ∧ b = 2 ^ (n / 2) - 1)

/-- **Palindromic powers of two in a base one less than a power of two.** Let $x \ge 2$ and
$n \ge 1$ be natural numbers, let $b = 2^x - 1$, and suppose that the base-$b$ representation
$2^n = (c_k, \dots, c_0)_b$ is a palindrome with $k + 1$ digits. Then (1) $n > k(x - 1)$; and
(2) if $n = kx + r$ for a natural number $r$, and either $k \le x - r$, or $3 \le k \le x - r + 1$
and $x \ge 3$, then $c_i = 2^r \binom{k}{i}$ for $i = 0, \dots, k$, that is, the representation
is the binomial form $2^r (\binom{k}{k}, \dots, \binom{k}{0})_b$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Lemma 4
(`integers-2024-A69-lem-4`). -/
public theorem_wanted palindrome_two_pow_base_two_pow_sub_one (x n k : ℕ) (hx : 2 ≤ x)
    (hn : 1 ≤ n) (hp : (Nat.digits (2 ^ x - 1) (2 ^ n)).Palindrome)
    (hk : (Nat.digits (2 ^ x - 1) (2 ^ n)).length = k + 1) :
    k * (x - 1) < n ∧
      ∀ r : ℕ, n = k * x + r →
        ((k : ℤ) ≤ (x : ℤ) - r ∨ (3 ≤ k ∧ (k : ℤ) ≤ (x : ℤ) - r + 1 ∧ 3 ≤ x)) →
        Nat.digits (2 ^ x - 1) (2 ^ n) = (List.range (k + 1)).map fun i => 2 ^ r * k.choose i

/-- **Powers of 2 have binomial forms in small bases.** For every natural number $n \ge 2$ there
are natural numbers $y$ and $b$ with $y \le \lceil \sqrt{2n} \rceil + 1$ and $2 \le b \le 2^y - 1$
such that $2^n$ has a base-$b$ representation in binomial form.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 5
(`integers-2024-A69-thm-5`). -/
public theorem_wanted exists_small_base_binomialForm_two_pow (n : ℕ) (hn : 2 ≤ n) :
    ∃ y b : ℕ, y ≤ ⌈Real.sqrt (2 * n)⌉₊ + 1 ∧ 2 ≤ b ∧ b ≤ 2 ^ y - 1 ∧ HasBinomialForm b (2 ^ n)

/-- **Even-length palindromic prime powers have base one less than a power of the prime.** Let
$p$ be a prime and let $n$ and $b \ge 2$ be natural numbers. If the base-$b$ representation of
$p^n$ is a palindrome with an even number of digits, then $b = p^x - 1$ for some natural number
$x$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 6
(`integers-2024-A69-thm-6`). -/
public theorem_wanted base_eq_prime_pow_sub_one_of_palindrome (p n b : ℕ) (hp : p.Prime)
    (hb : 2 ≤ b) (hpal : (Nat.digits b (p ^ n)).Palindrome)
    (he : Even (Nat.digits b (p ^ n)).length) : ∃ x, b = p ^ x - 1

/-- **Digits of a power of the base and of its successor.** Let $z \ge 2$ and $n$ be natural
numbers. Then the base-$z$ digits of $z^n$ are a $1$ followed by $n$ zeros, and, if $n \ge 1$,
the base-$z$ digits of $z^n + 1$ are a $1$, then $n - 1$ zeros, then a $1$.

Part (III) of the source theorem is omitted: as printed ($z^n - 1 = (1, 1, \dots, 1)_z$) it is
false for $z \ge 3$, for example $3^2 - 1 = 8 = (2, 2)_3$.

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 7
(`integers-2024-A69-thm-7`), parts (I) and (II). -/
public theorem_wanted digits_pow_and_pow_add_one (z n : ℕ) (hz : 2 ≤ z) :
    Nat.digits z (z ^ n) = List.replicate n 0 ++ [1] ∧
      (1 ≤ n → Nat.digits z (z ^ n + 1) = [1] ++ List.replicate (n - 1) 0 ++ [1])

/-- **The Nagell–Ljunggren equation in natural numbers (Bugeaud–Mihăilescu).** Let $x, y, n, q$
be natural numbers with $x \ge 2$, $y \ge 2$, $n \ge 3$ and $q \ge 2$ such that
$(x^n - 1)/(x - 1) = y^q$. If $q = 2$, or $3 \mid n$, or $4 \mid n$, or $q = 3$ and
$n \not\equiv 5 \pmod 6$, then $(x, y, n, q)$ is one of $(3, 11, 5, 2)$, $(7, 20, 4, 2)$ and
$(18, 7, 3, 3)$; these are $11^2 = (1,1,1,1,1)_3$, $20^2 = (1,1,1,1)_7$ and $7^3 = (1,1,1)_{18}$.

The ranges $x, y \ge 2$, $n \ge 3$, $q \ge 2$ are the standard ones for this equation (not
displayed in the paper).

Source: D. L. Kreher and D. R. Stinson, *On Minimum-Base Palindromic
Representations of Powers of 2*, INTEGERS 24 (2024), Article A69, Theorem 8
(`integers-2024-A69-thm-8`), quoting Bugeaud and Mihăilescu. -/
public theorem_wanted nagell_ljunggren_solutions (x y n q : ℕ) (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hn : 3 ≤ n) (hq : 2 ≤ q) (h : (x ^ n - 1) / (x - 1) = y ^ q)
    (hc : q = 2 ∨ 3 ∣ n ∨ 4 ∣ n ∨ (q = 3 ∧ n % 6 ≠ 5)) :
    (x, y, n, q) = (3, 11, 5, 2) ∨ (x, y, n, q) = (7, 20, 4, 2) ∨ (x, y, n, q) = (18, 7, 3, 3)

end

end MetaMathlibExt
