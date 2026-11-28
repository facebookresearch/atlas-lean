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
atomic congruence, divisibility, and classification claims; the claim
`mersenne_sylvester_values_eq` is proved in
`MathlibExt.NumberTheory.Recurrences.SylvesterSequenceMersenneSylvesterValuesEq`.
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
public import MathlibExt.NumberTheory.Recurrences.SylvesterModuloFour
public import MathlibExt.NumberTheory.Recurrences.SylvesterSequence
public import MathlibExt.NumberTheory.Recurrences.SylvesterSequenceMersenneSylvesterValuesEq
public import MathlibExt.NumberTheory.Recurrences.SylvesterSequenceModTen

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

/-- **Alternating divisibility for Sylvester numbers.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For all natural numbers $k$ and $n$ with
$1 \le k \le n$, the integer $S_k^2 + 1$ divides the integer $S_n - (-1)^{n-k} S_k$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, divisibility
(8). -/
theorem_wanted sylvester_sq_add_one_dvd_sub
    (k n : ℕ) (hk : 1 ≤ k) (hn : k ≤ n) :
    (sylvesterNumber k : ℤ) ^ 2 + 1 ∣
      (sylvesterNumber n : ℤ) -
        (-1 : ℤ) ^ (n - k) * (sylvesterNumber k : ℤ)

/-- **Sylvester numbers of odd index modulo 10.** Let $(S_n)_{n \ge 0}$ be the Sylvester
sequence, $S_0 = 2$ and $S_{n+1} = S_n^2 - S_n + 1$. For every $i \ge 1$,
$S_{2i+1} \equiv 3 \pmod{10}$.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Proposition 2, congruence (9),
odd indices. -/
theorem_wanted sylvester_odd_index_mod_ten
    (i : ℕ) (hi : 1 ≤ i) :
    sylvesterNumber (2 * i + 1) % 10 = 3

/-- **No Sylvester number is perfect.** For every natural number $n$, the $n$-th Sylvester number
$S_n$ is not a perfect number.

Source: Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Corollary 1(c). -/
theorem_wanted sylvester_not_perfect
    (n : ℕ) :
    ¬ (sylvesterNumber n).Perfect

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

Source: F. Luca, Sz. Tengely, and A. Togbé, "On the Diophantine equation x² + C = 4yⁿ",
Theorem 1.1, as quoted in Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Theorem 1,
equation with C = 3. -/
theorem_wanted lebesgue_nagell_three_solutions_iff
    (n x y : ℕ) :
    (3 ≤ n ∧ 1 ≤ x ∧ 1 ≤ y ∧ Nat.Coprime x y ∧
        x ^ 2 + 3 = 4 * y ^ n) ↔
      (3 ≤ n ∧ ((x = 1 ∧ y = 1) ∨ (n = 3 ∧ x = 37 ∧ y = 7)))

/-- **Coprime solutions of $x^2 + 7 = 4y^n$.** For natural numbers $n$, $x$ and $y$, the
conditions $n \ge 3$, $x \ge 1$, $y \ge 1$, $\gcd(x, y) = 1$ and $x^2 + 7 = 4y^n$ hold if and only
if $(n, x, y)$ is $(3, 5, 2)$, $(5, 11, 2)$ or $(13, 181, 2)$ (Luca–Tengely–Togbé).

Source: F. Luca, Sz. Tengely, and A. Togbé, "On the Diophantine equation x² + C = 4yⁿ",
Theorem 1.1, as quoted in Abderrahim Makki Naciri, "A Note on Sylvester's Sequence", Theorem 1,
equation with C = 7. -/
theorem_wanted lebesgue_nagell_seven_solutions_iff
    (n x y : ℕ) :
    (3 ≤ n ∧ 1 ≤ x ∧ 1 ≤ y ∧ Nat.Coprime x y ∧
        x ^ 2 + 7 = 4 * y ^ n) ↔
      ((n = 3 ∧ x = 5 ∧ y = 2) ∨ (n = 5 ∧ x = 11 ∧ y = 2) ∨
        (n = 13 ∧ x = 181 ∧ y = 2))

end MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted
