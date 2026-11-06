/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A note on Sylvester's sequence

Statements from Abderrahim Makki Naciri, "A Note on Sylvester's
Sequence", *INTEGERS* 24 (2024), Article A117
(<https://math.colgate.edu/~integers/y117/y117.pdf>).

The classical Sylvester sequence starts with `S₀ = 2` and satisfies
`Sₙ₊₁ = Sₙ(Sₙ - 1) + 1`.  This is exactly
`Nat.generalizedSylvester 1` from MathlibExt, whose parameter gives
initial value `1 + 1 = 2` and the same recurrence.

Proposition 1, Proposition 2, and Corollary 1 are split into their
atomic congruence, divisibility, and classification claims.
Proposition 3 is split into its perfect-power and `a^m ± 1` claims.
The quoted Theorem 1 is F. Luca, Sz. Tengely, and A. Togbé,
"On the Diophantine equation `x² + C = 4yⁿ`", *Annales des Sciences
Mathématiques du Québec* 33(2) (2009), 171--184, Theorem 1.1, for
`C = 3` and `C = 7`, as quoted by Naciri.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.NumberTheory.Divisors
public import MathlibExt.NumberTheory.GeneralizedSylvester

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

/-- **Sylvester numbers.** The Sylvester numbers $S_0, S_1, S_2, \dots$ are the natural numbers
given by $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$ for $n \ge 0$, so the sequence begins
$2, 3, 7, 43, 1807, \dots$. It is the generalized Sylvester sequence with parameter $1$. -/
abbrev sylvesterNumber (n : ℕ) : ℕ :=
  Nat.generalizedSylvester 1 n

/-- **Divisibility of differences of Sylvester numbers.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For all natural numbers $k$, $m$ and $n$
with $k \ge 1$, $m \ge k$ and $n \ge k$, the integer $(S_k - 1)^2$ divides $S_n - S_m$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, divisibility (4). -/
theorem_wanted sylvester_sub_dvd
    (k m n : ℕ) (hk : 1 ≤ k) (hm : k ≤ m) (hn : k ≤ n) :
    ((sylvesterNumber k : ℤ) - 1) ^ 2 ∣
      (sylvesterNumber n : ℤ) - (sylvesterNumber m : ℤ)

/-- **Sylvester numbers modulo 4.** Let $(S_n)_{n \ge 0}$ be the Sylvester sequence,
$S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 1$, $S_n \equiv 3 \pmod 4$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (5). -/
theorem_wanted sylvester_modEq_three_mod_four
    (n : ℕ) (hn : 1 ≤ n) :
    sylvesterNumber n % 4 = 3

/-- **Sylvester numbers modulo 36.** Let $(S_n)_{n \ge 0}$ be the Sylvester sequence,
$S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 2$, $S_n \equiv 7 \pmod{36}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (6). -/
theorem_wanted sylvester_modEq_seven_mod_thirty_six
    (n : ℕ) (hn : 2 ≤ n) :
    sylvesterNumber n % 36 = 7

/-- **Sylvester numbers modulo 1764.** Let $(S_n)_{n \ge 0}$ be the Sylvester sequence,
$S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 3$, $S_n \equiv 43 \pmod{1764}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 1, congruence (7). -/
theorem_wanted sylvester_modEq_forty_three_mod_1764
    (n : ℕ) (hn : 3 ≤ n) :
    sylvesterNumber n % 1764 = 43

/-- **Alternating divisibility for Sylvester numbers.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For all natural numbers $k$ and $n$ with
$1 \le k \le n$, the integer $S_k^2 + 1$ divides the integer $S_n - (-1)^{n-k} S_k$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, divisibility (8). -/
theorem_wanted sylvester_sq_add_one_dvd_sub
    (k n : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    (sylvesterNumber k : ℤ) ^ 2 + 1 ∣
      (sylvesterNumber n : ℤ) -
        (-1 : ℤ) ^ (n - k) * (sylvesterNumber k : ℤ)

/-- **Sylvester numbers of even index modulo 10.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $i \ge 1$,
$S_{2i} \equiv 7 \pmod{10}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, congruence (9), even indices. -/
theorem_wanted sylvester_even_index_mod_ten
    (i : ℕ) (hi : 1 ≤ i) :
    sylvesterNumber (2 * i) % 10 = 7

/-- **Sylvester numbers of odd index modulo 10.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $i \ge 1$,
$S_{2i+1} \equiv 3 \pmod{10}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, congruence (9), odd indices. -/
theorem_wanted sylvester_odd_index_mod_ten
    (i : ℕ) (hi : 1 ≤ i) :
    sylvesterNumber (2 * i + 1) % 10 = 3

/-- **Mersenne numbers in the Sylvester sequence.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. The natural numbers $x$ such that $x = S_n$
for some $n$ and $x = 2^r - 1$ for some $r \ge 1$ are exactly $3$ and $7$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(a). -/
theorem_wanted mersenne_sylvester_values_eq :
    {x : ℕ | ∃ n r : ℕ, 1 ≤ r ∧ x = sylvesterNumber n ∧
      x = 2 ^ r - 1} = {3, 7}

/-- **The only triangular Sylvester number is $3$.** Let $S_n$ denote the $n$-th Sylvester
number. A natural number $x$ equals $S_n$ for some $n$ and satisfies $2x = m(m + 1)$ for some
natural number $m \ge 1$ if and only if $x = 3$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(b). -/
theorem_wanted triangular_sylvester_values_eq :
    {x : ℕ | ∃ n m : ℕ, 1 ≤ m ∧ x = sylvesterNumber n ∧
      2 * x = m * (m + 1)} = {3}

/-- **No Sylvester number is perfect.** For every natural number $n$, the $n$-th Sylvester number
$S_n$ is not a perfect number.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(c). -/
theorem_wanted sylvester_not_perfect
    (n : ℕ) :
    ¬ (sylvesterNumber n).Perfect

/-- **Prime divisors congruent to 3 modulo 4 of Sylvester numbers.** Let $(S_n)_{n \ge 0}$ be the
Sylvester sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n \ge 1$, $S_n$ has a
prime divisor $p$ with $p \equiv 3 \pmod 4$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(d). -/
theorem_wanted sylvester_exists_prime_divisor_mod_four_eq_three
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ p ∣ sylvesterNumber n ∧ p % 4 = 3

/-- **Sylvester numbers are not perfect powers.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n$ there are no natural numbers
$a \ge 2$ and $m \ge 2$ with $S_n = a^m$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 3(a). -/
theorem_wanted sylvester_not_perfect_power
    (n : ℕ) :
    ¬ ∃ a m : ℕ, 2 ≤ a ∧ 2 ≤ m ∧ sylvesterNumber n = a ^ m

/-- **Sylvester numbers next to perfect powers.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $n$ other than $1$ and $2$ there
are no natural numbers $a \ge 2$ and $m \ge 2$ with $S_n = a^m + 1$ or $S_n = a^m - 1$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 3(b). -/
theorem_wanted sylvester_ne_pow_add_or_sub_one
    (n : ℕ) (hn1 : n ≠ 1) (hn2 : n ≠ 2) :
    ¬ ∃ a m : ℕ, 2 ≤ a ∧ 2 ≤ m ∧
      ((sylvesterNumber n : ℤ) = (a : ℤ) ^ m + 1 ∨
        (sylvesterNumber n : ℤ) = (a : ℤ) ^ m - 1)

/-- **Coprime solutions of $x^2 + 3 = 4y^n$.** For natural numbers $n$, $x$ and $y$, the
conditions $n \ge 3$, $x \ge 1$, $y \ge 1$, $\gcd(x, y) = 1$ and $x^2 + 3 = 4y^n$ hold if and only
if $n \ge 3$ and either $x = y = 1$ or $(n, x, y) = (3, 37, 7)$ (Luca–Tengely–Togbé).

Source: F. Luca, Sz. Tengely, and A. Togbé, "On the Diophantine equation x² + C = 4yⁿ", Theorem 1.1, as quoted in Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Theorem 1, equation with C = 3. -/
theorem_wanted lebesgue_nagell_three_solutions_iff
    (n x y : ℕ) :
    (3 ≤ n ∧ 1 ≤ x ∧ 1 ≤ y ∧ Nat.Coprime x y ∧
        x ^ 2 + 3 = 4 * y ^ n) ↔
      (3 ≤ n ∧ ((x = 1 ∧ y = 1) ∨ (n = 3 ∧ x = 37 ∧ y = 7)))

/-- **Coprime solutions of $x^2 + 7 = 4y^n$.** For natural numbers $n$, $x$ and $y$, the
conditions $n \ge 3$, $x \ge 1$, $y \ge 1$, $\gcd(x, y) = 1$ and $x^2 + 7 = 4y^n$ hold if and only
if $(n, x, y)$ is $(3, 5, 2)$, $(5, 11, 2)$ or $(13, 181, 2)$ (Luca–Tengely–Togbé).

Source: F. Luca, Sz. Tengely, and A. Togbé, "On the Diophantine equation x² + C = 4yⁿ", Theorem 1.1, as quoted in Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Theorem 1, equation with C = 7. -/
theorem_wanted lebesgue_nagell_seven_solutions_iff
    (n x y : ℕ) :
    (3 ≤ n ∧ 1 ≤ x ∧ 1 ≤ y ∧ Nat.Coprime x y ∧
        x ^ 2 + 7 = 4 * y ^ n) ↔
      ((n = 3 ∧ x = 5 ∧ y = 2) ∨ (n = 5 ∧ x = 11 ∧ y = 2) ∨
        (n = 13 ∧ x = 181 ∧ y = 2))

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted
