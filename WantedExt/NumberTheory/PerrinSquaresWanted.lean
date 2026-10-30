/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.ContinuedFractions.Computation.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Real.Irrational
public import MathlibExt.NumberTheory.PerrinSequence

namespace MetaMathlibExt

@[expose] public section

/-- The Perrin sequence at negative indices: `perrinNeg n = R_{-n}`, the unique
backward extension of the Perrin recurrence `R_{k+3} = R_{k+1} + R_k` from
`R_0 = 3`, `R_1 = 0`, `R_2 = 2`, i.e. `R_{-n-3} = R_{-n} - R_{-n-2}`, with
`R_0 = 3`, `R_{-1} = R_2 - R_0 = -1`, `R_{-2} = R_1 - R_{-1} = 1`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public def perrinNeg : ℕ → ℤ
  | 0 => 3
  | 1 => -1
  | 2 => 1
  | n + 3 => perrinNeg n - perrinNeg (n + 2)

/-- The backward extension agrees with the Perrin sequence at index `0` and
satisfies the Perrin recurrence across `0`: `R_2 = R_0 + R_{-1}` and
`R_1 = R_{-1} + R_{-2}`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public theorem perrinNeg_bridge :
    perrinNeg 0 = (perrinSequence 0 : ℤ) ∧
      (perrinSequence 2 : ℤ) = perrinSequence 0 + perrinNeg 1 ∧
        (perrinSequence 1 : ℤ) = perrinNeg 1 + perrinNeg 2 := by
  decide

/-- The Perrin recurrence `R_{-n} = R_{-n-2} + R_{-n-3}` at negative indices.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2–4. -/
public theorem perrinNeg_rec (n : ℕ) :
    perrinNeg n = perrinNeg (n + 2) + perrinNeg (n + 3) := by
  rw [perrinNeg]; ring

/-- Small values quoted in Theorems 2 and 4: `R_{-5} = 4`, `R_{-18} = 25`,
`R_{-1} = R_{-7} = R_{-11} = R_{-29} = -1`, `R_{-2} = 1`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorems 2 and 4. -/
public theorem perrinNeg_small_values :
    perrinNeg 5 = 4 ∧ perrinNeg 18 = 25 ∧ perrinNeg 1 = -1 ∧ perrinNeg 7 = -1 ∧
      perrinNeg 11 = -1 ∧ perrinNeg 29 = -1 ∧ perrinNeg 2 = 1 := by
  decide

/-- Theorem 1: the only solution of `R_n = R_m ^ 2` in positive integers is
`R_1 = 0 = R_1 ^ 2`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 1
(`integers-2025-A70-thm-1`). -/
public theorem_wanted perrinSequence_eq_sq_iff {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    perrinSequence n = perrinSequence m ^ 2 ↔ n = 1 ∧ m = 1

/-- Theorem 2: the solutions of `R_{-n} = ± R_m ^ 2` in positive integers are
exactly `R_{-5} = 4 = R_2 ^ 2 = R_4 ^ 2` and `R_{-18} = 25 = R_5 ^ 2 = R_6 ^ 2`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 2
(`integers-2025-A70-thm-2`). -/
public theorem_wanted perrinNeg_eq_pm_perrinSequence_sq :
    {nm : ℕ × ℕ | 0 < nm.1 ∧ 0 < nm.2 ∧
      (perrinNeg nm.1 = (perrinSequence nm.2 : ℤ) ^ 2 ∨
        perrinNeg nm.1 = -((perrinSequence nm.2 : ℤ) ^ 2))} =
      {(5, 2), (5, 4), (18, 5), (18, 6)}

/-- Theorem 3: `R_n = R_{-m} ^ 2` has no solutions in positive integers.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 3
(`integers-2025-A70-thm-3`). -/
public theorem_wanted perrinSequence_ne_perrinNeg_sq {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    (perrinSequence n : ℤ) ≠ perrinNeg m ^ 2

/-- Theorem 4: the solutions of `R_{-n} = ± R_{-m} ^ 2` in positive integers
are exactly the pairs with `n, m ∈ {1, 2, 7, 11, 29}` (where `R_{-m} = ± 1`),
together with `R_{-5} = 4 = R_{-3} ^ 2 = R_{-6} ^ 2 = R_{-20} ^ 2` and
`R_{-18} = 25 = R_{-8} ^ 2 = R_{-16} ^ 2`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 4
(`integers-2025-A70-thm-4`). -/
public theorem_wanted perrinNeg_eq_pm_perrinNeg_sq :
    {nm : ℕ × ℕ | 0 < nm.1 ∧ 0 < nm.2 ∧
      (perrinNeg nm.1 = perrinNeg nm.2 ^ 2 ∨ perrinNeg nm.1 = -(perrinNeg nm.2 ^ 2))} =
      ({1, 2, 7, 11, 29} : Set ℕ) ×ˢ ({1, 2, 7, 11, 29} : Set ℕ) ∪
        {(5, 3), (5, 6), (5, 20), (18, 8), (18, 16)}

/-- Theorem 5: the two-sided Perrin sequence `(R_k)_{k ∈ ℤ}` has exactly one
zero, `R_1 = 0`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 5
(`integers-2025-A70-thm-5`). -/
public theorem_wanted perrin_zero_unique :
    (∀ n : ℕ, perrinSequence n = 0 ↔ n = 1) ∧ ∀ n : ℕ, perrinNeg n ≠ 0

/-- Lemma 1 (quoted from Bravo, Bravo and Luca): with `α` the real zero of
`X ^ 3 - X - 1`, for every integer `k ≥ 6`,
`α ^ (k / 2 - 3 × 10 ^ 15 log k) < |R_{-k}| < 2.01 α ^ (k / 2)`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Lemma 1
(`integers-2025-A70-lem-1`). -/
public theorem_wanted perrinNeg_abs_bounds {α : ℝ} (hα : α ^ 3 = α + 1) {k : ℕ} (hk : 6 ≤ k) :
    α ^ ((k : ℝ) / 2 - 3 * 10 ^ 15 * Real.log k) < |(perrinNeg k : ℝ)| ∧
      |(perrinNeg k : ℝ)| < 2.01 * α ^ ((k : ℝ) / 2)

/-- Theorem 6 (Matveev, two logarithms, complex case, as quoted): let `K` be a
number field of degree `D` embedded in `ℂ`, `η₁, η₂ ∈ K` nonzero, `b₁, b₂`
integers, `Λ = η₁ ^ b₁ η₂ ^ b₂ - 1`, `B ≥ max (|b₁|, |b₂|)` and
`A_j ≥ max (D h(η_j), |log η_j|, 0.16)`. If `Λ ≠ 0` then
`|Λ| > exp (-9.20483 × 10 ^ 11 D ^ 2 A₁ A₂ (1 + log D) (1 + log (2 B)))`.
Here `h` is Mathlib's absolute logarithmic height and `log` the principal
complex logarithm of the embedded value; the paper prints `|log η^{(j)}|`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 6
(`integers-2025-A70-thm-6`). -/
public theorem_wanted matveev_two_logs_complex_lower_bound
    {K : Type*} [Field K] [NumberField K] (f : K →+* ℂ)
    {η₁ η₂ : K} (h₁ : η₁ ≠ 0) (h₂ : η₂ ≠ 0) (b₁ b₂ : ℤ) {B A₁ A₂ : ℝ}
    (hB₁ : |(b₁ : ℝ)| ≤ B) (hB₂ : |(b₂ : ℝ)| ≤ B)
    (hA₁ : max (max ((Module.finrank ℚ K : ℝ) * NumberField.absLogHeight₁ η₁)
      ‖Complex.log (f η₁)‖) 0.16 ≤ A₁)
    (hA₂ : max (max ((Module.finrank ℚ K : ℝ) * NumberField.absLogHeight₁ η₂)
      ‖Complex.log (f η₂)‖) 0.16 ≤ A₂)
    (hΛ : f η₁ ^ b₁ * f η₂ ^ b₂ - 1 ≠ 0) :
    Real.exp (-(9.20483 * 10 ^ 11 * (Module.finrank ℚ K : ℝ) ^ 2 * A₁ * A₂ *
        (1 + Real.log (Module.finrank ℚ K : ℝ)) * (1 + Real.log (2 * B)))) <
      ‖f η₁ ^ b₁ * f η₂ ^ b₂ - 1‖

/-- Lemma 3: let `x` be irrational with convergents `p_n / q_n` and partial
quotients `a_0 = ⌊x⌋, a_1, …`. Let `M ≥ 1` and `N` with `q_N ≤ M < q_{N+1}`,
and let `a_M ≥ a_j` for all `j ∈ [0, N + 1]` (the paper takes the maximum;
any upper bound is equivalent since the bound weakens as `a_M` grows). Then
`|x - p / q| > 1 / ((a_M + 2) q ^ 2)` for all integers `p, q` with
`0 < q < M`. Here `a_{j+1}` is the `j`-th entry of Mathlib's `partDens`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Lemma 3
(`integers-2025-A70-lem-3`). -/
public theorem_wanted one_div_partialQuotient_bound_lt_abs_sub {x : ℝ} (hx : Irrational x)
    {M N : ℕ} (hM : 0 < M) (hNM : (GenContFract.of x).dens N ≤ M)
    (hMN : (M : ℝ) < (GenContFract.of x).dens (N + 1)) {aM : ℝ} (ha0 : (⌊x⌋ : ℝ) ≤ aM)
    (ha : ∀ j ≤ N, ∀ b : ℝ, (GenContFract.of x).partDens.get? j = some b → b ≤ aM)
    {p q : ℤ} (hq : 0 < q) (hqM : q < M) :
    1 / ((aM + 2) * (q : ℝ) ^ 2) < |x - p / q|

/-- Theorem 10 (Hardy–Wright, Theorem 182): for an irrational `x` with
convergents `p_n / q_n`, if `n > 1`, `0 < q ≤ q_n` and `p / q ≠ p_n / q_n`,
then `|p_n - q_n x| < |p - q x|`.

Source: Karen J. Sacanamboy, Eric F. Bravo, and Jhon J. Bravo, *Perrin Squares
Which Are Again Perrin*, INTEGERS 25 (2025), Article A70, Theorem 10
(`integers-2025-A70-thm-10`). -/
public theorem_wanted abs_convergent_num_sub_lt_of_le_den {x : ℝ} (hx : Irrational x)
    {n : ℕ} (hn : 1 < n) {p q : ℤ} (hq : 0 < q) (hqn : (q : ℝ) ≤ (GenContFract.of x).dens n)
    (hne : (p : ℝ) / q ≠ (GenContFract.of x).nums n / (GenContFract.of x).dens n) :
    |(GenContFract.of x).nums n - (GenContFract.of x).dens n * x| < |p - q * x|

end

end MetaMathlibExt
