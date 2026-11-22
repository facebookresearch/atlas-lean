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

/-- Proposition 1 (quoted from [7]): for `l ≥ 3` and a symmetric sequence of positive integers
`a₁, …, a_{l-1}`, some positive nonsquare `d` has `√d = [a₀; a₁, …, a_{l-1}, 2a₀]` if and only
if (i) `q_{l-1}` is odd, or (ii) `q_{l-1}` and `r_{l-2}` are even and `q_{l-2}` is odd. The
cases `l ≤ 2`, where `r_{l-2}` needs the convention `r_0 = 0`, are omitted.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Proposition 1 (`integers-2024-A50-prop-1`). -/
public theorem_wanted sqrt_hasPeriodicCF_exists_iff_parity (l : ℕ) (hl : 3 ≤ l) (a : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)) ↔
      Odd (convergentDen a (l - 1)) ∨
        (Even (convergentDen a (l - 1)) ∧ Even (convergentDen (fun n => a (n + 1)) (l - 3)) ∧
          Odd (convergentDen a (l - 2)))

/-- Proposition 2 (quoted from [10]): for `l ≥ 3` and a symmetric sequence of positive integers
`a₁, …, a_{l-1}`, some positive nonsquare `d ≡ 1 (mod 4)` has
`(1 + √d)/2 = [a₀; a₁, …, a_{l-1}, 2a₀ - 1]` if and only if (i) `q_{l-1}` is odd, or (ii) `q_{l-2}` and `r_{l-2}` are odd and `q_{l-1}` is
even. The paper's primed letters `a'_i, q'_i, r'_i` are written unprimed; the cases `l ≤ 2`
are omitted as in Proposition 1. The restriction `d ≡ 1 (mod 4)` (the setting of
`(1 + √d)/2`) is needed: `(1 + √2)/2 = [1; 4, 1, 4, 1, 4, 1, …]` fits `l = 6` with
`a₁, …, a₅ = 4, 1, 4, 1, 4`, where `q₅ = 140` and `q₄ = 29`, `r₄ = 6` violate the criterion.

Source: Jun Ho Lee, *Classification for Existence of the Continued Fraction Expansions of √D and
(1 + √D)/2*, INTEGERS 24 (2024), Article A50, Proposition 2 (`integers-2024-A50-prop-2`). -/
public theorem_wanted half_one_add_sqrt_hasPeriodicCF_exists_iff_parity (l : ℕ) (hl : 3 ≤ l)
    (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧ HasPeriodicCF ((1 + √(d : ℝ)) / 2) a₀ a l (2 * a₀ - 1)) ↔
      Odd (convergentDen a (l - 1)) ∨
        (Odd (convergentDen a (l - 2)) ∧ Odd (convergentDen (fun n => a (n + 1)) (l - 3)) ∧
          Even (convergentDen a (l - 1)))

/-- Theorem 3: for a symmetric sequence of positive integers `a₁, …, a_{l-1}`, (i) if `l` is
odd, some positive nonsquare `d ≡ 1 (mod 4)` has `(1 + √d)/2 = [a₀; a₁, …, a_{l-1}, 2a₀ - 1]`; (ii) if `l`
is even (and positive), such a `d` exists if and only if `a_{l/2}` is odd.

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


/-- Theorem 1 (quoted from [4, 12]): let `d ≥ 2` be squarefree, `ε_d` the fundamental unit of
`ℚ(√d)`, `l_d` the length of the period of the continued fraction of `√d` and
`p_{l_d-1}/q_{l_d-1}` its `(l_d - 1)`-th convergent. Then `ε_d = p_{l_d-1} + q_{l_d-1}√d` or
`ε_d³ = p_{l_d-1} + q_{l_d-1}√d`, and the latter can only occur if `d ≡ 5 (mod 8)`.
The fundamental unit is pinned as the least real number `> 1` of the form `(x + y√d)/2` with
`x, y ∈ ℤ` and `x² - d y² = ±4` (for squarefree `d` these numbers are exactly the units of the
ring of integers of `ℚ(√d)`); `l_d` is the least `l > 0` with `a_{k+l} = a_k` for all `k ≥ 1`;
`p_k, q_k` are Mathlib's `nums`, `dens` of `GenContFract.of √d`. The paper's "positive
squarefree" `d` is restricted to `d ≥ 2` (`ℚ(√1)` is not a quadratic field).

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
