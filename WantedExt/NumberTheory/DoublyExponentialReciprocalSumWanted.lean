/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import MathlibExt.NumberTheory.GeneralizedSylvester

/-!
# Reciprocal sums of doubly exponential sequences

Statements from Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly
Exponential Sequences*, INTEGERS 26 (2026), Article A28 (arXiv:2504.05933). Sequences are
indexed from `0` (the paper's `a₁` is `a 0`), the nearest-integer function
`⌊x⌉ = ⌊x + 1/2⌋` is written out, and "for `n ≫ 0`" is `∀ᶠ n in atTop`. The Sylvester
sequence is `Nat.generalizedSylvester 1` (`2, 3, 7, 43, …`), and the paper's `F_(2^n)` is
`Nat.fib (2 ^ (n + 1))` after the index shift.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- The remainder sequence `x_n` of the pseudo-greedy expansion of a real number `r`, indexed
from `0`: `x 0 = r` and `x (n + 1) = x n - 1 / a n` with `a n = ⌊(x n)⁻¹ + 1⌉`, the integer
nearest to `(x n)⁻¹ + 1`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definitions of the pseudo-greedy
expansion and its remainder sequence). -/
noncomputable def pseudoGreedyRemainder (r : ℝ) : ℕ → ℝ
  | 0 => r
  | n + 1 => pseudoGreedyRemainder r n -
      1 / (⌊(pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2⌋ : ℝ)

/-- The pseudo-greedy expansion `a_n = ⌊x_n⁻¹ + 1⌉ = ⌊x_n⁻¹ + 1 + 1/2⌋` of `r`, indexed
from `0`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the pseudo-greedy
expansion). -/
noncomputable def pseudoGreedyExpansion (r : ℝ) (n : ℕ) : ℤ :=
  ⌊(pseudoGreedyRemainder r n)⁻¹ + 1 + 1 / 2⌋

/-- The gap sequence `ε_n = x_n⁻¹ + 1 - a_n` of the pseudo-greedy expansion of `r`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the gap sequence). -/
noncomputable def pseudoGreedyGap (r : ℝ) (n : ℕ) : ℝ :=
  (pseudoGreedyRemainder r n)⁻¹ + 1 - pseudoGreedyExpansion r n

/-- The remainder recursion `x (n + 1) = x n - 1 / a n`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Section 2 (definition of the remainder
sequence). -/
theorem pseudoGreedyRemainder_succ (r : ℝ) (n : ℕ) :
    pseudoGreedyRemainder r (n + 1) =
      pseudoGreedyRemainder r n - 1 / (pseudoGreedyExpansion r n : ℝ) := rfl

/-- The pseudo-greedy expansion of `1` starts with `a 0 = 2` (first Sylvester number).

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (the expansion of `1` is the Sylvester
sequence). -/
theorem pseudoGreedyExpansion_one_zero : pseudoGreedyExpansion 1 0 = 2 := by
  rw [pseudoGreedyExpansion, pseudoGreedyRemainder, Int.floor_eq_iff]
  norm_num

/-- The pseudo-greedy expansion of `1` continues with `a 1 = 3` (remainder `1 - 1/2 = 1/2`).

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (the expansion of `1` is the Sylvester
sequence). -/
theorem pseudoGreedyExpansion_one_one : pseudoGreedyExpansion 1 1 = 3 := by
  have h : pseudoGreedyRemainder 1 1 = 1 / 2 := by
    rw [pseudoGreedyRemainder_succ, pseudoGreedyExpansion_one_zero]
    simp only [pseudoGreedyRemainder]
    norm_num
  rw [pseudoGreedyExpansion, h, Int.floor_eq_iff]
  norm_num

/-- The gap sequence of the expansion of `1` starts with `ε 0 = 1 + 1 - 2 = 0`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Example 1 (`ε_n = 0` for the expansion of `1`). -/
theorem pseudoGreedyGap_one_zero : pseudoGreedyGap 1 0 = 0 := by
  rw [pseudoGreedyGap, pseudoGreedyExpansion_one_zero]
  simp only [pseudoGreedyRemainder]
  norm_num

/-- **Main theorem.** Let `β ≥ 0` and let `a` be a sequence of positive integers with
`|a_n² / a_(n+1) - β| ≤ 1/3` for all `n` and `∑ 1 / a_n = r`. Then for every `n` with
`a_n ≥ 8 (β + 1/3)²`, `a_n` is the integer nearest to `(r - ∑_(k<n) 1/a_k)⁻¹ + β`. Moreover, if
`a_n² / a_(n+1) → β`, then `|(r - ∑_(k<n) 1/a_k)⁻¹ + β - a_n| → 0`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 1 (`integers-2026-A28-thm-1`). -/
public theorem_wanted eq_round_inv_remainder_add {β r : ℝ} (hβ : 0 ≤ β) {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hratio : ∀ n, |(a n : ℝ) ^ 2 / a (n + 1) - β| ≤ 1 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) r) :
    (∀ n, 8 * (β + 1 / 3) ^ 2 ≤ (a n : ℝ) →
      (a n : ℤ) = ⌊(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β + 1 / 2⌋) ∧
    (Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 β) →
      Tendsto (fun n => |(r - ∑ k ∈ Finset.range n, 1 / (a k : ℝ))⁻¹ + β - a n|) atTop (𝓝 0))

/-- A sequence of positive integers with `2/3 ≤ a_n² / a_(n+1) ≤ 4/3` and `∑ 1 / a_n = 1` is
the Sylvester sequence `2, 3, 7, 43, …`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 1 (`integers-2026-A28-cor-1`). -/
public theorem_wanted eq_sylvester_of_ratio_mem_of_hasSum_one {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n)
    (hratio : ∀ n, 2 / 3 ≤ (a n : ℝ) ^ 2 / a (n + 1) ∧ (a n : ℝ) ^ 2 / a (n + 1) ≤ 4 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) 1) :
    ∀ n, a n = Nat.generalizedSylvester 1 n

/-- A sequence of positive integers with `a_n² / a_(n+1) ≤ 2/3` and
`∑ 1 / a_n = (5 - √5) / 2` is `F_2, F_4, F_8, …` (the Millin series).

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 2 (`integers-2026-A28-cor-2`). -/
public theorem_wanted eq_fib_two_pow_of_ratio_le_of_hasSum_millin {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n) (hratio : ∀ n, (a n : ℝ) ^ 2 / a (n + 1) ≤ 2 / 3)
    (hsum : HasSum (fun n => 1 / (a n : ℝ)) ((5 - √5) / 2)) :
    ∀ n, a n = Nat.fib (2 ^ (n + 1))

/-- For all `α > 1` outside a countable set, `⌊α ^ (2 ^ n)⌋` is a Type 2 irrationality
sequence: for every sequence `b` of positive integers with `b_n / ⌊α ^ (2 ^ n)⌋ → 1`, the sum
`∑ 1 / b_n` is not a rational number.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 2 and the definition of Type 2
irrationality sequences preceding it (`integers-2026-A28-thm-2`). -/
public theorem_wanted countable_not_type2IrrationalitySequence_floor_pow_two_pow :
    Set.Countable {α : ℝ | 1 < α ∧ ¬∀ b : ℕ → ℕ, (∀ n, 0 < b n) →
      Tendsto (fun n => (b n : ℝ) / ⌊α ^ 2 ^ (n + 1)⌋₊) atTop (𝓝 1) →
        ∀ q : ℚ, ¬HasSum (fun n => 1 / (b n : ℝ)) q}

/-- The pseudo-greedy expansion of a positive real `r` sums to `r`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 1 (`integers-2026-A28-lem-1`). -/
public theorem_wanted hasSum_one_div_pseudoGreedyExpansion {r : ℝ} (hr : 0 < r) :
    HasSum (fun n => 1 / (pseudoGreedyExpansion r n : ℝ)) r

/-- The pseudo-greedy expansion and its gap sequence satisfy
`a_(n+1) = a_n² / (1 - ε_n) - a_n + (1 - ε_(n+1))`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 2 (`integers-2026-A28-lem-2`). -/
public theorem_wanted pseudoGreedyExpansion_succ_eq {r : ℝ} (hr : 0 < r) (n : ℕ) :
    (pseudoGreedyExpansion r (n + 1) : ℝ) =
      1 / (1 - pseudoGreedyGap r n) * (pseudoGreedyExpansion r n : ℝ) ^ 2 -
        pseudoGreedyExpansion r n + (1 - pseudoGreedyGap r (n + 1))

/-- If a gap `ε_n` of the pseudo-greedy expansion of a positive real vanishes, so does
`ε_(n+1)`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 3 (`integers-2026-A28-lem-3`). -/
public theorem_wanted pseudoGreedyGap_succ_eq_zero {r : ℝ} (hr : 0 < r) {n : ℕ}
    (h : pseudoGreedyGap r n = 0) : pseudoGreedyGap r (n + 1) = 0

/-- Let `r = p / q` with `p, q` positive integers and `d_n = q a_0 ⋯ a_(n-1)`. Then there are
positive integers `c_n` and integers `e_n` with `x_n = c_n / d_n` and `ε_n = e_n / c_n`, such
that `e_n ≡ d_n (mod c_n)`, `-c_n / 2 ≤ e_n < c_n / 2`, `a_n = (d_n - e_n) / c_n + 1`,
`c_(n+1) = c_n - e_n` and `d_(n+1) = d_n a_n`; moreover `c_n = O(a_0 ⋯ a_(n-1) / a_n)` and
`c_n = O(1.5 ^ n)`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Lemma 4 (`integers-2026-A28-lem-4`). -/
public theorem_wanted pseudoGreedyExpansion_rational_structure {p q : ℕ} (hp : 0 < p)
    (hq : 0 < q) :
    let r : ℝ := p / q
    let a : ℕ → ℤ := pseudoGreedyExpansion r
    let d : ℕ → ℤ := fun n => q * ∏ k ∈ Finset.range n, a k
    ∃ (c : ℕ → ℕ) (e : ℕ → ℤ),
      (∀ n, 0 < c n ∧ pseudoGreedyRemainder r n = (c n : ℝ) / d n ∧
        pseudoGreedyGap r n = (e n : ℝ) / c n) ∧
      (∀ n, e n ≡ d n [ZMOD c n] ∧ -(c n : ℝ) / 2 ≤ e n ∧ (e n : ℝ) < c n / 2 ∧
        (a n : ℝ) = (d n - e n : ℝ) / c n + 1 ∧ (c (n + 1) : ℤ) = c n - e n ∧
        d (n + 1) = d n * a n) ∧
      (fun n => (c n : ℝ)) =O[atTop] (fun n => (∏ k ∈ Finset.range n, (a k : ℝ)) / a n) ∧
      (fun n => (c n : ℝ)) =O[atTop] (fun n => (1.5 : ℝ) ^ n)

/-- Let `r` be a positive rational with gap sequence `ε`. If
`liminf ε_n ∏_(k<n) (1 - ε_k) ≥ 0`, or if `ε_n ≥ 0` for `n ≫ 0`, then `ε_n = 0` for `n ≫ 0`.
The `liminf` condition is written as: for every `δ > 0`, eventually
`-δ ≤ ε_n ∏_(k<n) (1 - ε_k)`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Proposition 1 (`integers-2026-A28-prop-1`). -/
public theorem_wanted eventually_pseudoGreedyGap_eq_zero {r : ℚ} (hr : 0 < r)
    (h : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        -δ ≤ pseudoGreedyGap r n * ∏ k ∈ Finset.range n, (1 - pseudoGreedyGap r k)) ∨
      ∀ᶠ n in atTop, 0 ≤ pseudoGreedyGap r n) :
    ∀ᶠ n in atTop, pseudoGreedyGap r n = 0

/-- If `a` is a sequence of positive integers with `a_n² / a_(n+1) → 1` and
`∑ 1 / a_n < ∞`, then some tail `(a_(N+n))_n` is the pseudo-greedy expansion of its own
reciprocal sum, and the gap sequence of that expansion tends to `0`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 3 (`integers-2026-A28-cor-3`). -/
public theorem_wanted exists_tail_eq_pseudoGreedyExpansion {a : ℕ → ℕ} (hpos : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1))
    (hsum : Summable fun n => 1 / (a n : ℝ)) :
    ∃ N : ℕ,
      (∀ n, (a (N + n) : ℤ) = pseudoGreedyExpansion (∑' k, 1 / (a (N + k) : ℝ)) n) ∧
      Tendsto (pseudoGreedyGap (∑' k, 1 / (a (N + k) : ℝ))) atTop (𝓝 0)

/-- **Erdős–Straus; Badea.** Let `a` be a sequence of positive integers with
`a_n² / a_(n+1) → 1` and rational reciprocal sum. If
`liminf (a_0 ⋯ a_(n-1) / a_n)(1 - a_n² / a_(n+1)) ≥ 0`, or if `a_(n+1) ≥ a_n² - a_n + 1` for
`n ≫ 0`, then `a_(n+1) = a_n² - a_n + 1` for `n ≫ 0`. The `liminf` condition is written as:
for every `δ > 0`, eventually the quantity is `≥ -δ`.

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Corollary 4 (`integers-2026-A28-cor-4`). -/
public theorem_wanted eventually_sylvester_recurrence_of_rational_sum {a : ℕ → ℕ}
    (hpos : ∀ n, 0 < a n)
    (hratio : Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1))
    (hrat : ∃ q : ℚ, HasSum (fun n => 1 / (a n : ℝ)) q)
    (h : (∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
        -δ ≤ (∏ k ∈ Finset.range n, (a k : ℝ)) / a n * (1 - (a n : ℝ) ^ 2 / a (n + 1))) ∨
      ∀ᶠ n in atTop, a n ^ 2 - a n + 1 ≤ a (n + 1)) :
    ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1

/-- Koizumi's Conjecture 1 (for every positive rational `r` whose pseudo-greedy gap sequence
tends to `0`, the gaps vanish eventually) holds if and only if the Erdős–Graham question has an
affirmative answer (every sequence of positive integers with `a_n² / a_(n+1) → 1` and rational
reciprocal sum eventually satisfies `a_(n+1) = a_n² - a_n + 1`).

Source: Junnosuke Koizumi, *Irrationality of the Reciprocal Sum of Doubly Exponential
Sequences*, INTEGERS 26 (2026), Article A28, Theorem 3, with Conjecture 1 and Question 1
(`integers-2026-A28-thm-3`). -/
public theorem_wanted pseudoGreedy_conjecture_iff_erdos_graham_question :
    (∀ r : ℚ, 0 < r → Tendsto (pseudoGreedyGap r) atTop (𝓝 0) →
        ∀ᶠ n in atTop, pseudoGreedyGap r n = 0) ↔
      ∀ a : ℕ → ℕ, (∀ n, 0 < a n) →
        Tendsto (fun n => (a n : ℝ) ^ 2 / a (n + 1)) atTop (𝓝 1) →
        (∃ q : ℚ, HasSum (fun n => 1 / (a n : ℝ)) q) →
        ∀ᶠ n in atTop, a (n + 1) = a n ^ 2 - a n + 1

end

end MetaMathlibExt
