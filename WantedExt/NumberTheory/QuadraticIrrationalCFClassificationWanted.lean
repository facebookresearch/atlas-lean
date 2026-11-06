/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Squarefree.Basic
public import WantedExt.NumberTheory.QuadraticIrrationalCFNonexistenceWanted

/-!
# Existence of continued fractions of `√d` and `(1 + √d)/2` with a given period (statements)

Statement-only targets from Jun Ho Lee, *Classification for Existence of the Continued Fraction
Expansions of √D and (1 + √D)/2*. They reuse the notation of the same author's
`QuadraticIrrationalCFNonexistenceWanted`: for a symmetric sequence of positive integers
`a₁, …, a_{l-1}`, `q_j = convergentDen a j` is the denominator of the `j`-th convergent of
`[a₀; a₁, …]`, `r_j = convergentDen (fun n => a (n + 1)) (j - 1)` (for `j ≥ 1`) is the
denominator of the `j`-th convergent `q_j / r_j` of `[a₁; a₂, …]`, and
`HasPeriodicCF x a₀ a l c` says `x = [a₀; a₁, …, a_{l-1}, c]` with that period. `d` ranges
over positive nonsquare integers.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Parity criterion for $\sqrt{d}$ with a given symmetric period.** Let $l \ge 3$ and let
$a_1, \dots, a_{l-1}$ be positive integers with $a_i = a_{l-i}$ for $1 \le i < l$. Let $q_j$ be the
denominator of the $j$-th convergent of $[a_0; a_1, a_2, \dots]$ (so $q_0 = 1$, $q_1 = a_1$ and
$q_{j+2} = a_{j+2} q_{j+1} + q_j$), and let $r_{l-2}$ be the denominator of the $(l-3)$-th
convergent of $[a_1; a_2, a_3, \dots]$. There are natural numbers $d$ and $a_0$ with $d$ not a
perfect square and $\sqrt{d} = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0}]$ if and only if
$q_{l-1}$ is odd, or $q_{l-1}$ and $r_{l-2}$ are even and $q_{l-2}$ is odd.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Proposition 1 (`integers-2024-A50-prop-1`). -/
public theorem_wanted sqrt_hasPeriodicCF_exists_iff_parity (l : ℕ) (hl : 3 ≤ l) (a : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)) ↔
      Odd (convergentDen a (l - 1)) ∨
        (Even (convergentDen a (l - 1)) ∧ Even (convergentDen (fun n => a (n + 1)) (l - 3)) ∧
          Odd (convergentDen a (l - 2)))

/-- **Parity criterion for $(1 + \sqrt{d})/2$ with a given symmetric period.** Let $l \ge 3$ and
let $a_1, \dots, a_{l-1}$ be positive integers with $a_i = a_{l-i}$ for $1 \le i < l$. Let $q_j$ be
the denominator of the $j$-th convergent of $[a_0; a_1, a_2, \dots]$ (so $q_0 = 1$, $q_1 = a_1$ and
$q_{j+2} = a_{j+2} q_{j+1} + q_j$), and let $r_{l-2}$ be the denominator of the $(l-3)$-th
convergent of $[a_1; a_2, a_3, \dots]$. There are natural numbers $d$ and $a_0$ with
$d \equiv 1 \pmod 4$, $d$ not a perfect square, and
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$ if and only if $q_{l-1}$ is
odd, or $q_{l-2}$ and $r_{l-2}$ are odd and $q_{l-1}$ is even.

The restriction $d \equiv 1 \pmod 4$ is needed: $(1 + \sqrt{2})/2 = [1; \overline{4, 1}]$ fits
$l = 6$ with $(a_1, \dots, a_5) = (4, 1, 4, 1, 4)$, where $q_5 = 140$, $q_4 = 29$ and $r_4 = 6$
violate the criterion.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Proposition 2 (`integers-2024-A50-prop-2`). -/
public theorem_wanted half_one_add_sqrt_hasPeriodicCF_exists_iff_parity (l : ℕ) (hl : 3 ≤ l)
    (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧ HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ↔
      Odd (convergentDen a (l - 1)) ∨
        (Odd (convergentDen a (l - 2)) ∧ Odd (convergentDen (fun n => a (n + 1)) (l - 3)) ∧
          Even (convergentDen a (l - 1)))

/-- **Existence of $(1 + \sqrt{d})/2$ with a given symmetric period.** Let $l$ be a natural number
and $a_1, \dots, a_{l-1}$ positive integers with $a_i = a_{l-i}$ for $1 \le i < l$. If $l$ is odd,
there are natural numbers $d$ and $a_0$ with $d \equiv 1 \pmod 4$, $d$ not a perfect square, and
$(1 + \sqrt{d})/2 = [a_0; \overline{a_1, \dots, a_{l-1}, 2a_0 - 1}]$. If $l$ is even and positive,
such $d$ and $a_0$ exist if and only if $a_{l/2}$ is odd.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Theorem 3 (`integers-2024-A50-thm-3`). -/
public theorem_wanted half_one_add_sqrt_hasPeriodicCF_exists_classification (l : ℕ)
    (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (Odd l →
      ∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧ HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ∧
    (Even l → 0 < l →
      ((∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧ HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ↔
        Odd (a (l / 2))))


/-- **Fundamental unit from the period of $\sqrt{d}$.** Let $d \ge 2$ be a squarefree integer, let
$\varepsilon$ be the least real number $u > 1$ of the form $u = (x + y\sqrt{d})/2$ with
$x, y \in \mathbb{Z}$ and $x^2 - d y^2 = \pm 4$ (the fundamental unit of $\mathbb{Q}(\sqrt{d})$),
let $\sqrt{d} = [a_0; a_1, a_2, \dots]$ be the regular continued fraction of $\sqrt{d}$, with
convergents $p_k / q_k$ (so $p_0 = a_0$ and $q_0 = 1$), and let $l$ be the least positive integer
such that $a_{k+l} = a_k$ for all $k \ge 1$. Then $p_{l-1} + q_{l-1}\sqrt{d} = \varepsilon$, or
$p_{l-1} + q_{l-1}\sqrt{d} = \varepsilon^3$ and $d \equiv 5 \pmod 8$.

For squarefree $d$ the numbers $(x + y\sqrt{d})/2$ above are exactly the units of the ring of
integers of $\mathbb{Q}(\sqrt{d})$. The paper's positive squarefree $d$ is restricted to $d \ge 2$,
since $\mathbb{Q}(\sqrt{1})$ is not a quadratic field.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Theorem 1 (`integers-2024-A50-thm-1`). -/
public theorem_wanted fundamentalUnit_eq_convergent_or_cube (d : ℕ) (hd : Squarefree d)
    (hd2 : 2 ≤ d) (ε : ℝ)
    (hε : IsLeast {u : ℝ | 1 < u ∧ ∃ x y : ℤ,
      (x ^ 2 - d * y ^ 2 = 4 ∨ x ^ 2 - d * y ^ 2 = -4) ∧ u = (x + y * √(d : ℝ)) / 2} ε)
    (l : ℕ) (hl : IsLeast {l : ℕ | 0 < l ∧ ∀ k : ℕ,
      (GenContFract.of √(d : ℝ)).partDens.get? (k + l) =
        (GenContFract.of √(d : ℝ)).partDens.get? k} l) :
    (GenContFract.of √(d : ℝ)).nums (l - 1) + (GenContFract.of √(d : ℝ)).dens (l - 1) * √(d : ℝ) =
        ε ∨
      ((GenContFract.of √(d : ℝ)).nums (l - 1) +
          (GenContFract.of √(d : ℝ)).dens (l - 1) * √(d : ℝ) = ε ^ 3 ∧ d % 8 = 5)

end

end MetaMathlibExt
