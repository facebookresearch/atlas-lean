/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Set.Card
public import MathlibExt.NumberTheory.QuadraticIrrationalCFClassification
public import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistence
public import MathlibExt.NumberTheory.SymmetricContinuantParity
public import MathlibExt.NumberTheory.SymmetricConvergentDenParity
public import MathlibExt.NumberTheory.QuadraticIrrationalCFNonexistenceHalfOneAddSqrtPeriodicCFObstructionCountOfOdd

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

end

end MetaMathlibExt
