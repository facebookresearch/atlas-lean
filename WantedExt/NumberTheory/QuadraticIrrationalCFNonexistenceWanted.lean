/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Translations
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Set.Card

/-!
# Nonexistence of continued fractions of `√d` with a given symmetric period

Statements from Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic
Irrational Number with a Given Sequence*, INTEGERS 26 (2026), Article A69.

For a symmetric sequence of positive integers `a₁, …, a_{l-1}` the paper characterizes,
through the parity of convergent denominators, when some `√d` has the continued fraction
`[a₀; a₁, …, a_{l-1}, 2a₀]` with that period, and counts the parity patterns of
`(a₁, …, a_{⌊l/2⌋})` for which no such `d` exists.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Convergent denominators as continuants.** For a sequence of natural numbers
$a_0, a_1, a_2, \dots$, its convergent denominators $q_0, q_1, q_2, \dots$ are the natural
numbers defined by $q_0 = 1$, $q_1 = a_1$ and $q_{i+2} = a_{i+2} q_{i+1} + q_i$ for $i \ge 0$.
They are the denominators of the convergents of $[a_0; a_1, a_2, \dots]$, and $q_i$ is the
continuant $K(a_1, \dots, a_i)$; the term $a_0$ is never used.

The denominators $r_i$ of the paper, those of the convergents of $[a_1; a_2, \dots, a_i]$, are
the convergent denominators of the shifted sequence $(a_{n+1})_{n \ge 0}$ at index $i - 1$, for
$i \ge 1$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, notation of
Proposition 2 (`integers-2026-A69-prop-2`). -/
def convergentDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * convergentDen a (n + 1) + convergentDen a n

/-- **The convergent denominator $q_0$ equals $1$.** For every sequence of natural numbers
$a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$, we have $q_0 = 1$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_zero (a : ℕ → ℕ) : convergentDen a 0 = 1 := rfl

/-- **The convergent denominator $q_1$ equals $a_1$.** For every sequence of natural numbers
$a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$, we have $q_1 = a_1$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_one (a : ℕ → ℕ) : convergentDen a 1 = a 1 := rfl

/-- **Recurrence for the convergent denominators.** For every sequence of natural numbers
$a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$ and every natural
number $n$, we have $q_{n+2} = a_{n+2} q_{n+1} + q_n$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_add_two (a : ℕ → ℕ) (n : ℕ) :
    convergentDen a (n + 2) = a (n + 2) * convergentDen a (n + 1) + convergentDen a n := rfl

/-- **The convergent denominator $q_2$ equals $a_2 a_1 + 1$.** For every sequence of natural
numbers $a_0, a_1, a_2, \dots$ with convergent denominators $q_0, q_1, q_2, \dots$, we have
$q_2 = a_2 a_1 + 1$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_two (a : ℕ → ℕ) : convergentDen a 2 = a 2 * a 1 + 1 := rfl

/-- **Continued fractions with a prescribed period.** For a real number $x$, natural numbers
$a_0$, $l$, $c$ and a sequence of natural numbers $a_1, a_2, \dots$, we write
$x = [a_0; \overline{a_1, \dots, a_{l-1}, c}]$ when the regular continued fraction of $x$ is the
infinite expansion $[a_0; a_1, \dots, a_{l-1}, c, a_1, \dots, a_{l-1}, c, \dots]$: its integer
part is $a_0$, and for every $k \ge 1$ its $k$-th partial quotient exists and equals $c$ when $l$
divides $k$ and $a_{k \bmod l}$ otherwise. The period $l$ need not be minimal.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, the expansions
`√d = [a₀; a₁, …, a_{l-1}, 2a₀]` of Theorem 1 (`integers-2026-A69-thm-1`). -/
def HasPeriodicCF (x : ℝ) (a₀ : ℕ) (a : ℕ → ℕ) (l c : ℕ) : Prop :=
  (GenContFract.of x).h = a₀ ∧ ∀ n : ℕ, (GenContFract.of x).partDens.get? n =
    some (if (n + 1) % l = 0 then (c : ℝ) else (a ((n + 1) % l) : ℝ))

/-- **The integer part of a periodic continued fraction is the floor.** Let $x$ be a real
number and let $a_0$, $l$, $c$ and $a_1, a_2, \dots$ be natural numbers. Suppose that the regular
continued fraction of $x$ has integer part $a_0$ and that, for every $k \ge 1$, its $k$-th
partial quotient is $c$ when $l$ divides $k$ and $a_r$ otherwise, where $r$ is the remainder of
$k$ modulo $l$ (so $r = k$ when $l = 0$). For $l \ge 1$ this says that the continued fraction
is $[a_0; a_1, \dots, a_{l-1}, c, a_1, \dots, a_{l-1}, c, \dots]$. Then $\lfloor x \rfloor = a_0$.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, Theorem 1 (`a₀ = ⌊√d⌋`). -/
theorem HasPeriodicCF.floor_eq {x : ℝ} {a₀ : ℕ} {a : ℕ → ℕ} {l c : ℕ}
    (h : HasPeriodicCF x a₀ a l c) : ⌊x⌋ = a₀ := by
  have h0 := h.1
  rw [GenContFract.of_h_eq_floor] at h0
  exact_mod_cast h0

/-- **Parity criterion for $\sqrt{d}$ with a given symmetric period, odd length.** Let $l$ be odd
and let $a_1, \dots, a_{l-1}$ be positive integers with $a_i = a_{l-i}$ for $1 \le i \le l - 1$.
For $0 \le i \le l - 1$ let $q_i = K(a_1, \dots, a_i)$ be the continuant, given by $q_0 = 1$,
$q_1 = a_1$ and $q_{i+2} = a_{i+2} q_{i+1} + q_i$. Then there are a natural number $d$ that is
not a perfect square and a natural number $a_0$ with
$\sqrt{d} = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0}]$ if and only if $q_{l-1}$ is odd.

The paper fixes $d$ in its preamble; here $d$ and $a_0$ are quantified existentially, as in its
Proposition 2.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 1 (i)
(`integers-2026-A69-thm-1`). -/
public theorem_wanted sqrt_hasPeriodicCF_exists_iff_of_odd (l : ℕ) (hl : Odd l) (a : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)) ↔
      Odd (convergentDen a (l - 1))

/-- **Parity criterion for $\sqrt{d}$ with a given symmetric period, even length.** Let $l \ge 2$
be even and let $a_1, \dots, a_{l-1}$ be positive integers with $a_i = a_{l-i}$ for
$1 \le i \le l - 1$. For $0 \le i \le l - 1$ let $q_i = K(a_1, \dots, a_i)$ be the continuant,
given by $q_0 = 1$, $q_1 = a_1$ and $q_{i+2} = a_{i+2} q_{i+1} + q_i$. Then there are a natural
number $d$ that is not a perfect square and a natural number $a_0$ with
$\sqrt{d} = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0}]$ if and only if either $a_{l/2}$ and
$q_{l-1}$ are both odd, or $a_{l/2}$ is even.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 1 (ii)
(`integers-2026-A69-thm-1`). -/
public theorem_wanted sqrt_hasPeriodicCF_exists_iff_of_even (l : ℕ) (hl : Even l) (hl0 : 0 < l)
    (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)) ↔
      (Odd (a (l / 2)) ∧ Odd (convergentDen a (l - 1))) ∨ Even (a (l / 2))

/-- **Splitting the last convergent denominator of a symmetric sequence.** Let $l$ be a
natural number and let $a_0, a_1, a_2, \dots$ be natural numbers with convergent denominators
$q_0, q_1, q_2, \dots$, such that $a_i = a_{l-i}$ for $1 \le i < l$. Then for every $i$ with
$1 \le i \le l - 2$,
$$q_{l-1} = q_i q_{l-1-i} + q_{i-1} q_{l-2-i}.$$

The case $i = 0$ of the paper, which uses $q_{-1} = 0$, is omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Proposition 3 (i)
(`integers-2026-A69-prop-3`). -/
public theorem_wanted convergentDen_symm_split (l : ℕ) (a : ℕ → ℕ)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) (i : ℕ) (hi : 1 ≤ i) (hil : i + 2 ≤ l) :
    convergentDen a (l - 1) =
      convergentDen a i * convergentDen a (l - 1 - i) +
        convergentDen a (i - 1) * convergentDen a (l - 2 - i)

/-- **Splitting the shifted continuant of a symmetric sequence.** Let $l$ be a natural number
and let $a_1, \dots, a_{l-1}$ be natural numbers with $a_i = a_{l-i}$ for $1 \le i \le l - 1$.
For $j \ge 1$ let $r_j = K(a_2, \dots, a_j)$ be the continuant, given by $r_1 = 1$,
$r_2 = a_2$ and $r_{j+2} = a_{j+2} r_{j+1} + r_j$. Then for every $i$ with $2 \le i \le l - 3$,
$$r_{l-2} = r_i \, r_{l-1-i} + r_{i-1} \, r_{l-2-i}.$$

The cases $i \in \{0, 1, l - 2\}$ of the paper, which need $r_0 = 0$ and $r_{-1} = 1$, are
omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Proposition 3 (ii)
(`integers-2026-A69-prop-3`). -/
public theorem_wanted shifted_convergentDen_symm_split (l : ℕ) (a : ℕ → ℕ)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) (i : ℕ) (hi : 2 ≤ i) (hil : i + 3 ≤ l) :
    convergentDen (fun n => a (n + 1)) (l - 3) =
      convergentDen (fun n => a (n + 1)) (i - 1) *
          convergentDen (fun n => a (n + 1)) (l - 2 - i) +
        convergentDen (fun n => a (n + 1)) (i - 2) *
          convergentDen (fun n => a (n + 1)) (l - 3 - i)

/-- **Parity of $q_{l-1}$ for a symmetric sequence, even $l$.** Let $l \ge 2$ be even and let
$a_0, a_1, a_2, \dots$ be natural numbers with convergent denominators $q_0, q_1, q_2, \dots$,
such that $a_i = a_{l-i}$ for $1 \le i < l$. Then $q_{l-1} \equiv a_{l/2} \, q_{l/2-1} \pmod 2$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 1 (i)
(`integers-2026-A69-cor-1`). -/
public theorem_wanted convergentDen_parity_of_even (l : ℕ) (hl : Even l) (hl0 : 0 < l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen a (l - 1) ≡ a (l / 2) * convergentDen a (l / 2 - 1) [MOD 2]

/-- **Parity of the shifted continuant of a symmetric sequence, even length.** Let $l \ge 4$ be
even and let $a_1, \dots, a_{l-1}$ be natural numbers with $a_i = a_{l-i}$ for
$1 \le i \le l - 1$. For $j \ge 1$ let $r_j = K(a_2, \dots, a_j)$ be the continuant, given by
$r_1 = 1$, $r_2 = a_2$ and $r_{j+2} = a_{j+2} r_{j+1} + r_j$. Then
$r_{l-2} \equiv a_{l/2} \, r_{l/2-1} \pmod 2$.

The case $l = 2$ of the paper, which needs $r_0 = 0$, is omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 1 (ii)
(`integers-2026-A69-cor-1`). -/
public theorem_wanted shifted_convergentDen_parity_of_even (l : ℕ) (hl : Even l) (hl4 : 4 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen (fun n => a (n + 1)) (l - 3) ≡
      a (l / 2) * convergentDen (fun n => a (n + 1)) (l / 2 - 2) [MOD 2]

/-- **Parity of $q_{l-1}$ for a symmetric sequence, odd $l$.** Let $l \ge 3$ be odd and let
$a_0, a_1, a_2, \dots$ be natural numbers with convergent denominators $q_0, q_1, q_2, \dots$,
such that $a_i = a_{l-i}$ for $1 \le i < l$. Then
$q_{l-1} \equiv q_{(l-1)/2} + q_{(l-3)/2} \pmod 2$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 2 (i)
(`integers-2026-A69-cor-2`). -/
public theorem_wanted convergentDen_parity_of_odd (l : ℕ) (hl : Odd l) (hl3 : 3 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen a (l - 1) ≡
      convergentDen a ((l - 1) / 2) + convergentDen a ((l - 3) / 2) [MOD 2]

/-- **Parity of the shifted continuant of a symmetric sequence, odd length.** Let $l \ge 5$ be
odd and let $a_1, \dots, a_{l-1}$ be natural numbers with $a_i = a_{l-i}$ for
$1 \le i \le l - 1$. For $j \ge 1$ let $r_j = K(a_2, \dots, a_j)$ be the continuant, given by
$r_1 = 1$, $r_2 = a_2$ and $r_{j+2} = a_{j+2} r_{j+1} + r_j$. Then
$r_{l-2} \equiv r_{(l-1)/2} + r_{(l-3)/2} \pmod 2$.

The case $l = 3$ of the paper, which needs $r_0 = 0$, is omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 2 (ii)
(`integers-2026-A69-cor-2`). -/
public theorem_wanted shifted_convergentDen_parity_of_odd (l : ℕ) (hl : Odd l) (hl5 : 5 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen (fun n => a (n + 1)) (l - 3) ≡
      convergentDen (fun n => a (n + 1)) ((l - 1) / 2 - 1) +
        convergentDen (fun n => a (n + 1)) ((l - 3) / 2 - 1) [MOD 2]

/-- **Number of unrealizable parity patterns for $\sqrt{d}$, odd length.** Let $l \ge 3$ be odd.
Call a parity pattern $(v_1, \dots, v_{(l-1)/2}) \in (\mathbb{Z}/2)^{(l-1)/2}$ realizable if
there are positive integers $a_1, \dots, a_{l-1}$ with $a_i = a_{l-i}$ for $1 \le i \le l - 1$
and $a_j \equiv v_j \pmod 2$ for $1 \le j \le (l-1)/2$, a natural number $d$ that is not a
perfect square and a natural number $a_0$ with
$\sqrt{d} = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0}]$. If $A$ is the number of parity
patterns that are not realizable, then $3A = 2^{(l-1)/2} - (-1)^{(l-1)/2}$.

Writing $A_m$ for $A$ when $l = 2m + 1$, this gives $A_1 = A_2 = 1$ and
$A_m = A_{m-1} + 2A_{m-2}$ for $m \ge 3$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 3
(`integers-2026-A69-thm-3`). -/
public theorem_wanted sqrt_periodicCF_obstruction_count_of_odd (l : ℕ) (hl : Odd l)
    (hl3 : 3 ≤ l) :
    3 * (Set.ncard {v : Fin (l / 2) → ZMod 2 | ¬∃ a : ℕ → ℕ,
        (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
        (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
        ∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)} : ℤ) =
      2 ^ (l / 2) - (-1) ^ (l / 2)

/-- **Number of unrealizable parity patterns for $\sqrt{d}$, even length.** Let $l \ge 4$ be
even. Call a parity pattern $(v_1, \dots, v_{l/2}) \in (\mathbb{Z}/2)^{l/2}$ realizable if there
are positive integers $a_1, \dots, a_{l-1}$ with $a_i = a_{l-i}$ for $1 \le i \le l - 1$ and
$a_j \equiv v_j \pmod 2$ for $1 \le j \le l/2$, a natural number $d$ that is not a perfect square
and a natural number $a_0$ with $\sqrt{d} = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0}]$. If $B$
is the number of parity patterns that are not realizable, then
$3B = 2^{l/2 - 1} - (-1)^{l/2 - 1}$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 4
(`integers-2026-A69-thm-4`). -/
public theorem_wanted sqrt_periodicCF_obstruction_count_of_even (l : ℕ) (hl : Even l)
    (hl4 : 4 ≤ l) :
    3 * (Set.ncard {v : Fin (l / 2) → ZMod 2 | ¬∃ a : ℕ → ℕ,
        (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
        (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
        ∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)} : ℤ) =
      2 ^ (l / 2 - 1) - (-1) ^ (l / 2 - 1)

/-- **Every parity pattern is realized by $(1 + \sqrt{d})/2$ for odd period length.** Let $l$ be
odd. For every parity pattern $(v_1, \dots, v_{(l-1)/2}) \in (\mathbb{Z}/2)^{(l-1)/2}$ there are
positive integers $a_1, \dots, a_{l-1}$ with $a_i = a_{l-i}$ for $1 \le i \le l - 1$ and
$a_j \equiv v_j \pmod 2$ for $1 \le j \le (l-1)/2$, a natural number $d$ that is not a perfect
square and a natural number $a_0$ with
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$. That is, the number $A'_l$
of patterns that are not realized is $0$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 5
(`integers-2026-A69-thm-5`). -/
public theorem_wanted half_one_add_sqrt_periodicCF_obstruction_count_of_odd (l : ℕ)
    (hl : Odd l) :
    Set.ncard {v : Fin (l / 2) → ZMod 2 | ¬∃ a : ℕ → ℕ,
        (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
        (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
        ∃ d a₀ : ℕ, ¬IsSquare d ∧
          HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)} = 0

/-- **Unrealizable parity patterns for $(1 + \sqrt d)/2$ with even $l$.** Let $l \ge 2$ be
even. Call a parity pattern $(v_1, \dots, v_{l/2}) \in (\mathbb{Z}/2)^{l/2}$ realizable if there
are positive integers $a_1, \dots, a_{l-1}$ with $a_i = a_{l-i}$ for $1 \le i < l$ and
$a_j \equiv v_j \pmod 2$ for $1 \le j \le l/2$, together with natural numbers $d$ and $a_0$
such that $d \equiv 1 \pmod 4$, $d$ is not a perfect square and the regular continued fraction
of $(1 + \sqrt d)/2$ is
$$[a_0; a_1, \dots, a_{l-1}, 2a_0 - 1, a_1, \dots, a_{l-1}, 2a_0 - 1, \dots].$$
Then the number $B'_l$ of parity patterns that are not realizable is $2^{l/2 - 1}$.

Without the hypothesis $d \equiv 1 \pmod 4$ one would get $B'_2 = 0$, since $d = 15$
realizes $a_1 = 2$.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 6
(`integers-2026-A69-thm-6`). -/
public theorem_wanted half_one_add_sqrt_periodicCF_obstruction_count_of_even (l : ℕ)
    (hl : Even l) (hl0 : 0 < l) :
    Set.ncard {v : Fin (l / 2) → ZMod 2 | ¬∃ a : ℕ → ℕ,
        (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
        (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
        ∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
          HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)} = 2 ^ (l / 2 - 1)

end

end MetaMathlibExt
