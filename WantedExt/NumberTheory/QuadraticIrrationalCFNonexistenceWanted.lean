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

/-- The denominators `q_i` of the convergents `p_i / q_i` of `[a₀; a₁, a₂, …]`:
`q₀ = 1`, `q₁ = a₁` and `q_{i+2} = a_{i+2} q_{i+1} + q_i`, i.e. the continuant
`K(a₁, …, a_i)`. The value `a 0` is never used. The denominators `r_i` of the paper
(the convergents `q_i / r_i` of `[a₁; a₂, …, a_i]`) are
`convergentDen (fun n => a (n + 1)) (i - 1)` for `i ≥ 1`.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, notation of
Proposition 2 (`integers-2026-A69-prop-2`). -/
def convergentDen (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | 1 => a 1
  | n + 2 => a (n + 2) * convergentDen a (n + 1) + convergentDen a n

/-- `q₀ = 1`.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_zero (a : ℕ → ℕ) : convergentDen a 0 = 1 := rfl

/-- `q₁ = a₁`.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_one (a : ℕ → ℕ) : convergentDen a 1 = a 1 := rfl

/-- The convergent-denominator recurrence `q_{n+2} = a_{n+2} q_{n+1} + q_n`.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_add_two (a : ℕ → ℕ) (n : ℕ) :
    convergentDen a (n + 2) = a (n + 2) * convergentDen a (n + 1) + convergentDen a n := rfl

/-- `q₂ = a₁ a₂ + 1`.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, notation of Proposition 2. -/
theorem convergentDen_two (a : ℕ → ℕ) : convergentDen a 2 = a 2 * a 1 + 1 := rfl

/-- `HasPeriodicCF x a₀ a l c` says that the regular continued fraction of `x` is
`[a₀; a₁, …, a_{l-1}, c, a₁, …, a_{l-1}, c, …]`: its integer part is `a₀` and its `k`-th
partial quotient (`k ≥ 1`) is `c` when `l ∣ k` and `a (k % l)` otherwise. The period `l`
need not be minimal.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, the expansions
`√d = [a₀; a₁, …, a_{l-1}, 2a₀]` of Theorem 1 (`integers-2026-A69-thm-1`). -/
def HasPeriodicCF (x : ℝ) (a₀ : ℕ) (a : ℕ → ℕ) (l c : ℕ) : Prop :=
  (GenContFract.of x).h = a₀ ∧ ∀ n : ℕ, (GenContFract.of x).partDens.get? n =
    some (if (n + 1) % l = 0 then (c : ℝ) else (a ((n + 1) % l) : ℝ))

/-- The integer part in `HasPeriodicCF` is `⌊x⌋`.

Source: Jun Ho Lee, INTEGERS 26 (2026), Article A69, Theorem 1 (`a₀ = ⌊√d⌋`). -/
theorem HasPeriodicCF.floor_eq {x : ℝ} {a₀ : ℕ} {a : ℕ → ℕ} {l c : ℕ}
    (h : HasPeriodicCF x a₀ a l c) : ⌊x⌋ = a₀ := by
  have h0 := h.1
  rw [GenContFract.of_h_eq_floor] at h0
  exact_mod_cast h0

/-- Theorem 1 (i): for odd `l` and a symmetric sequence of positive integers
`a₁, …, a_{l-1}`, some positive nonsquare `d` has `√d = [a₀; a₁, …, a_{l-1}, 2a₀]` if and
only if `q_{l-1}` is odd. The paper fixes `d` in the preamble; the statement is the
existence of `d` (and `a₀`), as in Proposition 2.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 1 (i)
(`integers-2026-A69-thm-1`). -/
public theorem_wanted sqrt_hasPeriodicCF_exists_iff_of_odd (l : ℕ) (hl : Odd l) (a : ℕ → ℕ)
    (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)) ↔
      Odd (convergentDen a (l - 1))

/-- Theorem 1 (ii): for even `l ≥ 2` and a symmetric sequence of positive integers
`a₁, …, a_{l-1}`, some positive nonsquare `d` has `√d = [a₀; a₁, …, a_{l-1}, 2a₀]` if and
only if both `a_{l/2}` and `q_{l-1}` are odd, or `a_{l/2}` is even.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Theorem 1 (ii)
(`integers-2026-A69-thm-1`). -/
public theorem_wanted sqrt_hasPeriodicCF_exists_iff_of_even (l : ℕ) (hl : Even l) (hl0 : 0 < l)
    (a : ℕ → ℕ) (hpos : ∀ i, 1 ≤ i → i < l → 0 < a i)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    (∃ d a₀ : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) a₀ a l (2 * a₀)) ↔
      (Odd (a (l / 2)) ∧ Odd (convergentDen a (l - 1))) ∨ Even (a (l / 2))

/-- Proposition 3 (i): for a symmetric sequence `a₁, …, a_{l-1}` and `1 ≤ i ≤ l - 2`,
`q_{l-1} = q_i q_{l-1-i} + q_{i-1} q_{l-2-i}`. The case `i = 0` (with `q_{-1} = 0`) is
omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Proposition 3 (i)
(`integers-2026-A69-prop-3`). -/
public theorem_wanted convergentDen_symm_split (l : ℕ) (a : ℕ → ℕ)
    (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) (i : ℕ) (hi : 1 ≤ i) (hil : i + 2 ≤ l) :
    convergentDen a (l - 1) =
      convergentDen a i * convergentDen a (l - 1 - i) +
        convergentDen a (i - 1) * convergentDen a (l - 2 - i)

/-- Proposition 3 (ii): for a symmetric sequence `a₁, …, a_{l-1}` and `2 ≤ i ≤ l - 3`,
`r_{l-2} = r_i r_{l-1-i} + r_{i-1} r_{l-2-i}`, where `r_j = K(a₂, …, a_j)` is
`convergentDen (fun n => a (n + 1)) (j - 1)`. The cases `i ∈ {0, 1, l - 2}`, which need
`r_0 = 0` and `r_{-1} = 1`, are omitted.

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

/-- Corollary 1 (i): for even `l ≥ 2` and a symmetric sequence `a₁, …, a_{l-1}`,
`q_{l-1} ≡ a_{l/2} q_{l/2-1} (mod 2)`.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 1 (i)
(`integers-2026-A69-cor-1`). -/
public theorem_wanted convergentDen_parity_of_even (l : ℕ) (hl : Even l) (hl0 : 0 < l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen a (l - 1) ≡ a (l / 2) * convergentDen a (l / 2 - 1) [MOD 2]

/-- Corollary 1 (ii): for even `l ≥ 4` and a symmetric sequence `a₁, …, a_{l-1}`,
`r_{l-2} ≡ a_{l/2} r_{l/2-1} (mod 2)` with `r_j = K(a₂, …, a_j)`. The case `l = 2`,
which needs `r_0 = 0`, is omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 1 (ii)
(`integers-2026-A69-cor-1`). -/
public theorem_wanted shifted_convergentDen_parity_of_even (l : ℕ) (hl : Even l) (hl4 : 4 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen (fun n => a (n + 1)) (l - 3) ≡
      a (l / 2) * convergentDen (fun n => a (n + 1)) (l / 2 - 2) [MOD 2]

/-- Corollary 2 (i): for odd `l ≥ 3` and a symmetric sequence `a₁, …, a_{l-1}`,
`q_{l-1} ≡ q_{(l-1)/2} + q_{(l-3)/2} (mod 2)`.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 2 (i)
(`integers-2026-A69-cor-2`). -/
public theorem_wanted convergentDen_parity_of_odd (l : ℕ) (hl : Odd l) (hl3 : 3 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen a (l - 1) ≡
      convergentDen a ((l - 1) / 2) + convergentDen a ((l - 3) / 2) [MOD 2]

/-- Corollary 2 (ii): for odd `l ≥ 5` and a symmetric sequence `a₁, …, a_{l-1}`,
`r_{l-2} ≡ r_{(l-1)/2} + r_{(l-3)/2} (mod 2)` with `r_j = K(a₂, …, a_j)`. The case `l = 3`,
which needs `r_0 = 0`, is omitted.

Source: Jun Ho Lee, *Nonexistence of the Continued Fraction of a Quadratic Irrational
Number with a Given Sequence*, INTEGERS 26 (2026), Article A69, Corollary 2 (ii)
(`integers-2026-A69-cor-2`). -/
public theorem_wanted shifted_convergentDen_parity_of_odd (l : ℕ) (hl : Odd l) (hl5 : 5 ≤ l)
    (a : ℕ → ℕ) (hsymm : ∀ i, 1 ≤ i → i < l → a i = a (l - i)) :
    convergentDen (fun n => a (n + 1)) (l - 3) ≡
      convergentDen (fun n => a (n + 1)) ((l - 1) / 2 - 1) +
        convergentDen (fun n => a (n + 1)) ((l - 3) / 2 - 1) [MOD 2]

/-- Theorem 3: for odd `l ≥ 3`, let `A` be the number of parity patterns
`(a₁, …, a_{(l-1)/2}) ∈ (ℤ/2)^{(l-1)/2}` such that no symmetric sequence of positive
integers `a₁, …, a_{l-1}` with these parities admits a positive nonsquare `d` with
`√d = [a₀; a₁, …, a_{l-1}, 2a₀]`. Then `3A = 2^{(l-1)/2} - (-1)^{(l-1)/2}` (so `A₁ = A₂ = 1`
and `A_m = A_{m-1} + 2A_{m-2}`).

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

/-- Theorem 4: for even `l ≥ 4`, let `B` be the number of parity patterns
`(a₁, …, a_{l/2}) ∈ (ℤ/2)^{l/2}` such that no symmetric sequence of positive integers
`a₁, …, a_{l-1}` with these parities admits a positive nonsquare `d` with
`√d = [a₀; a₁, …, a_{l-1}, 2a₀]`. Then `3B = 2^{(l-2)/2} - (-1)^{(l-2)/2}`.

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

/-- Theorem 5: for odd `l`, every parity pattern `(a₁, …, a_{(l-1)/2}) ∈ (ℤ/2)^{(l-1)/2}` is
realized: some symmetric sequence of positive integers `a₁, …, a_{l-1}` with these parities
and some positive nonsquare `d` satisfy `(1 + √d)/2 = [a₀; a₁, …, a_{l-1}, 2a₀ - 1]`, i.e. the
number `A'_l` of unrealized patterns is `0`.

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

/-- Theorem 6: for even `l ≥ 2`, the number `B'_l` of parity patterns
`(a₁, …, a_{l/2}) ∈ (ℤ/2)^{l/2}` such that no symmetric sequence of positive integers
`a₁, …, a_{l-1}` with these parities admits a positive nonsquare `d ≡ 1 (mod 4)` with
`(1 + √d)/2 = [a₀; a₁, …, a_{l-1}, 2a₀ - 1]` is `2^{l/2 - 1}`. The hypothesis
`d ≡ 1 (mod 4)` is the setting of `half_one_add_sqrt_hasPeriodicCF_exists_iff_parity` and
`half_one_add_sqrt_hasPeriodicCF_exists_classification` in
`QuadraticIrrationalCFClassificationWanted`, which also state this paper's Proposition 2 and
Theorem 2; without it `B'_2 = 0` (`d = 15` realizes `a_1 = 2`).

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
