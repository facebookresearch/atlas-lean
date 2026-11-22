/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Split families of Thue equations with linear recurrence factors

Statements from Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence
Sequences as Factors*, INTEGERS 25 (2025), Article A35.

The integer sequences `G 1, …, G d` are simple linear recurrences, written through their
closed formulas `G i n = ∑_{r ∈ R i} c i r * r ^ n` (distinct complex roots, nonzero
coefficients). `γ i` is the dominant root of `G i` (real and nonnegative, as the paper
assumes), and `δ (d - 1)`, `δ d` are the second dominant roots of `G (d - 1)`, `G d`.

The roots `α⁽ⁱ⁾ = α n i` of `fₙ(x, 1) = ∏ (x - G k n) - 1` are labelled as in the paper,
`α⁽ⁱ⁾` being the root close to `G i n`: an admissible labelling is any `α : ℕ → ℕ → ℝ`
such that, for all large `n`, every `α n i` is a root with `|α n i - G i n| < 1` (for large
`n` this determines the labelling, since the `G i n` are far apart).
-/

namespace MetaMathlibExt

@[expose] public section

/-- The hypotheses of Hilgart's Theorem 1 on `d ≥ 3` integer sequences `G 1, …, G d`:
each `G i` is a simple linear recurrence `G i n = ∑_{r ∈ R i} c i r * r ^ n` with
dominant root `γ i` (all other roots of smaller modulus);
`0 ≤ γ 1 < ⋯ < γ (d - 2) < γ (d - 1) = γ d`; the constant terms of the dominant roots of
`G (d - 1)` and `G d` agree; `G (d - 1)` and `G d` have second dominant roots `δ (d - 1)`,
`δ d` with `|δ (d - 1)| < |δ d| < γ (d - 2)` and `γ (d - 2) ^ 2 < γ |δ d|`.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (conditions 1-3); dominant roots taken real and
nonnegative as in
the paper's standing assumption after Corollary 1. -/
public def IsSplitThueRecurrenceFamily (d : ℕ) (G : ℕ → ℕ → ℤ) (γ : ℕ → ℝ) (δ : ℕ → ℂ) :
    Prop :=
  3 ≤ d ∧ ∃ (R : ℕ → Finset ℂ) (c : ℕ → ℂ → ℂ),
    (∀ i ∈ Finset.Icc 1 d, (∀ r ∈ R i, c i r ≠ 0) ∧
      ∀ n, (G i n : ℂ) = ∑ r ∈ R i, c i r * r ^ n) ∧
    (∀ i ∈ Finset.Icc 1 d, ((γ i : ℝ) : ℂ) ∈ R i ∧ ∀ r ∈ R i, r ≠ γ i → ‖r‖ < γ i) ∧
    0 ≤ γ 1 ∧ StrictMonoOn γ (Set.Icc 1 (d - 1)) ∧ γ (d - 1) = γ d ∧
    c (d - 1) (γ (d - 1)) = c d (γ d) ∧
    (∀ i ∈ ({d - 1, d} : Finset ℕ), δ i ∈ R i ∧ δ i ≠ γ i ∧
      ∀ r ∈ R i, r ≠ γ i → r ≠ δ i → ‖r‖ < ‖δ i‖) ∧
    ‖δ (d - 1)‖ < ‖δ d‖ ∧ ‖δ d‖ < γ (d - 2) ∧ γ (d - 2) ^ 2 < γ d * ‖δ d‖

/-- The hypotheses force `d ≥ 3`.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (the conditions mention `γ (d - 2)`). -/
public theorem IsSplitThueRecurrenceFamily.three_le {d : ℕ} {G : ℕ → ℕ → ℤ} {γ : ℕ → ℝ}
    {δ : ℕ → ℂ} (h : IsSplitThueRecurrenceFamily d G γ δ) : 3 ≤ d :=
  h.1

/-- Characteristic example: `G 1 n = 3 ^ n`, `G 2 n = 5 ^ n + 1`, `G 3 n = 5 ^ n + 2 ^ n`
(dominant roots `3, 5, 5`; second dominant roots `1, 2`) satisfy the hypotheses with
`d = 3`.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (conditions 1-3). -/
public theorem isSplitThueRecurrenceFamily_example :
    IsSplitThueRecurrenceFamily 3
      (fun i n => if i = 1 then 3 ^ n else if i = 2 then 5 ^ n + 1 else 5 ^ n + 2 ^ n)
      (fun i => if i = 1 then 3 else 5) (fun i => if i = 2 then 1 else 2) := by
  refine ⟨le_rfl, fun i => if i = 1 then {3} else if i = 2 then {5, 1} else {5, 2},
    fun _ _ => 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    have : i = 1 ∨ i = 2 ∨ i = 3 := by simp only [Finset.mem_Icc] at hi; omega
    rcases this with rfl | rfl | rfl <;> refine ⟨fun _ _ => one_ne_zero, fun n => ?_⟩ <;>
      norm_num [Finset.sum_pair]
  · intro i hi
    have : i = 1 ∨ i = 2 ∨ i = 3 := by simp only [Finset.mem_Icc] at hi; omega
    rcases this with rfl | rfl | rfl <;> norm_num
  · norm_num
  · intro a ha b hb hab
    simp only [Set.mem_Icc] at ha hb
    obtain ⟨rfl, rfl⟩ : a = 1 ∧ b = 2 := by omega
    norm_num
  · norm_num
  · norm_num
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> norm_num
  · norm_num
  · norm_num
  · norm_num

/-- Main theorem: under the hypotheses, every integer solution of
`(x - G 1 n * y) ⋯ (x - G d n * y) - y ^ d = ±1` with `|y| ≥ 2` has
`max (log |x|, log |y|, n) ≤ κ` for a constant `κ` depending only on the sequences.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Theorem 1 (`integers-2025-A35-thm-1`). The computability
of `κ` is not
recorded. -/
public theorem_wanted splitThue_recurrence_solutions_bounded {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ) :
    ∃ κ : ℝ, ∀ (n : ℕ) (x y : ℤ), 2 ≤ |y| →
      ((∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = 1 ∨
        (∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = -1) →
      Real.log |(x : ℝ)| ≤ κ ∧ Real.log |(y : ℝ)| ≤ κ ∧ (n : ℝ) ≤ κ

/-- For all large `n`, the only integer solutions of
`(x - G 1 n * y) ⋯ (x - G d n * y) - y ^ d = ±1` are `(±1, 0)` and `±(G i n, 1)`.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Corollary 1 (`integers-2025-A35-cor-1`). The
computability of `n₀` is not
recorded. -/
public theorem_wanted splitThue_recurrence_solutions_eventually_trivial {d : ℕ}
    {G : ℕ → ℕ → ℤ} {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x y : ℤ,
      ((∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = 1 ∨
        (∏ i ∈ Finset.Icc 1 d, (x - G i n * y)) - y ^ d = -1) ↔
      ((x = 1 ∨ x = -1) ∧ y = 0) ∨
        ∃ i ∈ Finset.Icc 1 d, (x = G i n ∧ y = 1) ∨ (x = -G i n ∧ y = -1)

/-- Roots of `fₙ(x, 1)`: for large `n` all roots of `∏ (x - G k n) - 1` are real, an
admissible labelling `α⁽ⁱ⁾` exists, and every admissible labelling satisfies
`α⁽ⁱ⁾ = G i n + (1 + O(γ_ε⁻ⁿ)) / ∏_{k ≠ i} (G i n - G k n)`, where
`γ_ε = γ i ^ (i - 1) * ∏_{k = i+1}^{d-2} γ k * γ ^ 2` for `i ≤ d - 2` and
`γ_ε = γ ^ (d - 2) * |δ d|` for `i ∈ {d - 1, d}` (`γ = γ d`).

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Lemma 1 (`integers-2025-A35-lem-1`). The `O`-term is
written as
`|(α⁽ⁱ⁾ - G i n) * ∏_{k ≠ i} (G i n - G k n) - 1| ≤ C * γ_ε⁻ⁿ`; `δ d` enters through its
modulus. -/
public theorem_wanted splitThue_recurrence_roots_asymptotic {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ) :
    (∃ N : ℕ, ∀ n ≥ N, ∀ z : ℂ, ∏ k ∈ Finset.Icc 1 d, (z - G k n) = 1 → z.im = 0) ∧
    (∃ α : ℕ → ℕ → ℝ, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) ∧
    ∀ α : ℕ → ℕ → ℝ, (∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) →
      ∀ i ∈ Finset.Icc 1 d, ∃ (C : ℝ) (N : ℕ), ∀ n ≥ N,
        |(α n i - G i n) * ∏ k ∈ (Finset.Icc 1 d).erase i, ((G i n : ℝ) - G k n) - 1| ≤
          C * ((if i ≤ d - 2 then γ i ^ (i - 1) * (∏ k ∈ Finset.Icc (i + 1) (d - 2), γ k) *
            γ d ^ 2 else γ d ^ (d - 2) * ‖δ d‖)⁻¹) ^ n

/-- Growth of the roots: for an admissible labelling, `|α⁽ⁱ⁾| = Ω(γ i ^ n)`, and for
`i ≠ j`, `|α⁽ⁱ⁾ - α⁽ʲ⁾|` and `|α⁽ⁱ⁾ - G j n|` are `Ω(|δ d| ^ n)` when `{i, j} = {d - 1, d}`
and `Ω(max (γ i) (γ j) ^ n)` otherwise.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Lemma 2 (`integers-2025-A35-lem-2`), including its last
sentence (the same
bounds with `α⁽ʲ⁾` replaced by `G j n`). `Ω` is the paper's lower bound
`|f n| ≥ c * g n` for large `n`. -/
public theorem_wanted splitThue_recurrence_roots_growth {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ)
    (α : ℕ → ℕ → ℝ) (hα : ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      c * γ i ^ n ≤ |α n i| ∧ ∀ j ∈ Finset.Icc 1 d, j ≠ i →
        (({i, j} : Finset ℕ) = {d - 1, d} →
          c * ‖δ d‖ ^ n ≤ |α n i - α n j| ∧ c * ‖δ d‖ ^ n ≤ |α n i - G j n|) ∧
        (({i, j} : Finset ℕ) ≠ {d - 1, d} →
          c * max (γ i) (γ j) ^ n ≤ |α n i - α n j| ∧
            c * max (γ i) (γ j) ^ n ≤ |α n i - G j n|)

/-- The `k × k` matrix `B_k = (log η_j⁽ⁱ⁾)_{i, j ≤ k}`, `η_j⁽ⁱ⁾ = α⁽ⁱ⁾ - G j n`, has
`det B_k = Θ(n ^ k)` for every `1 ≤ k ≤ d - 1`.

Source: Tobias Hilgart, *On Split Families of Thue Equations with Linear Recurrence Sequences as
Factors*, INTEGERS 25 (2025), Article A35, Lemma 3 (`integers-2025-A35-lem-3`). `Real.log` is the
logarithm of the
absolute value; `Θ` is the paper's two-sided bound `c₁ n ^ k ≤ |det B_k| ≤ c₂ n ^ k` for
large `n`. -/
public theorem_wanted splitThue_recurrence_logUnitDet_asymptotic {d : ℕ} {G : ℕ → ℕ → ℤ}
    {γ : ℕ → ℝ} {δ : ℕ → ℂ} (hF : IsSplitThueRecurrenceFamily d G γ δ)
    (α : ℕ → ℕ → ℝ) (hα : ∃ N : ℕ, ∀ n ≥ N, ∀ i ∈ Finset.Icc 1 d,
      ∏ k ∈ Finset.Icc 1 d, (α n i - G k n) = 1 ∧ |α n i - G i n| < 1) (k : ℕ) (hk : 1 ≤ k) (hkd : k
          ≤ d - 1) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∃ N : ℕ, ∀ n ≥ N,
      c₁ * (n : ℝ) ^ k ≤
          |(Matrix.of fun a b : Fin k => Real.log (α n ((a : ℕ) + 1) - G ((b : ℕ) + 1) n)).det| ∧
        |(Matrix.of fun a b : Fin k => Real.log (α n ((a : ℕ) + 1) - G ((b : ℕ) + 1) n)).det| ≤
          c₂ * (n : ℝ) ^ k

end

end MetaMathlibExt
