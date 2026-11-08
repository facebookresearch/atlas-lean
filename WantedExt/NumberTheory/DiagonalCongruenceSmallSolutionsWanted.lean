/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Pointwise.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SmoothNumbers

namespace MetaMathlibExt

open Pointwise

@[expose] public section

/-- Sumset-product covering in `ℤ/pℤ`: if `A₁, A₂, A₃, D ⊆ ℤ/pℤ` satisfy
`|A₁| |A₂| |A₃| |D| > p³`, then `A₁ D + A₂ + A₃ = ℤ/pℤ`.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 3
(`integers-2026-A14-lem-3`), quoting Lemma 8.3 of their reference [5] (a consequence of
Sárközy's Corollary A). -/
public theorem_wanted product_add_add_eq_univ_of_card_mul_gt (p : ℕ) [Fact p.Prime]
    (A₁ A₂ A₃ D : Finset (ZMod p))
    (h : p ^ 3 < A₁.card * A₂.card * A₃.card * D.card) :
    A₁ * D + A₂ + A₃ = Finset.univ

/-! Notation for the statements below. The paper's set of `B^η`-smooth numbers
`A(B, B^η) = {x ∈ [1, B] ∩ ℤ : every prime q ∣ x has q ≤ B^η}` is
`Nat.smoothNumbersUpTo B (⌊(B : ℝ) ^ η⌋₊ + 1)` (Mathlib's smooth numbers use a strict
bound, and a prime `q` satisfies `q ≤ B^η` iff `q < ⌊B^η⌋₊ + 1`). The threshold
`s_0(k)` of Theorem 2 is `5` for `k = 2`, `8` for `k = 3`, and
`k (log k + log log k + 2 + g k)` for `k ≥ 4`, where `g k = O(log log k / log k)`; the
function `g` is existentially quantified in each statement. -/

/-- Lemma 2 (quoting Lemma 8.1 of Cochrane, Ostergaard and Spencer): `Γ(k, p) ≤ k`, where
`Γ(k, p)` is the least `n` such that every congruence
`a_1 x_1^k + ⋯ + a_n x_n^k ≡ c (mod p)` with `p ∤ a_i` is solvable. Since solvability with
`n` variables gives solvability with more (set the extra variables to `0`), this is stated
as: every such congruence in exactly `k` variables is solvable.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 2 (`integers-2026-A14-lem-2`). -/
public theorem_wanted diagonal_congruence_solvable_of_card_eq_exponent (p : ℕ) [Fact p.Prime]
    {k : ℕ} (hk : 1 ≤ k) (a : Fin k → ℤ) (ha : ∀ i, ¬ (p : ℤ) ∣ a i) (c : ℤ) :
    ∃ x : Fin k → ℤ, ∑ i, a i * x i ^ k ≡ c [ZMOD p]

/-- Theorem 2 (Chow, Lindqvist and Prendiville, Theorem B.1): for `k ≥ 2` there is
`η_0(k) > 0` such that, for nonzero integers `c_1, …, c_s` with a nonempty zero
subsum, `s ≥ s_0(k)` and `0 < η ≤ η_0(k)`, the number of `x ∈ A(N, N^η)^s` with
`∑ c_i x_i^k = 0` is `≍_{c,η,k} N^{s-k}` for all `N ≥ N_0(c, η, k)`; moreover
`s_0(2) = 5`, `s_0(3) = 8` and `s_0(k) = k (log k + log log k + 2 + O(log log k / log k))`.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Theorem 2 (`integers-2026-A14-thm-2`), quoting Chow, Lindqvist and Prendiville,
*Rado's criterion over squares and higher powers*, J. Eur. Math. Soc. 23 (2021),
Theorem B.1. -/
public theorem_wanted smooth_diagonal_solution_count_asymp :
    ∃ g : ℕ → ℝ, (g =O[Filter.atTop] fun k : ℕ => Real.log (Real.log k) / Real.log k) ∧
      ∀ k : ℕ, 2 ≤ k → ∃ η₀ : ℝ, 0 < η₀ ∧
        ∀ (s : ℕ) (c : Fin s → ℤ), (∀ i, c i ≠ 0) →
          (∃ I : Finset (Fin s), I.Nonempty ∧ ∑ i ∈ I, c i = 0) →
          (k = 2 → 5 ≤ s) → (k = 3 → 8 ≤ s) →
          (4 ≤ k → (k : ℝ) * (Real.log k + Real.log (Real.log k) + 2 + g k) ≤ s) →
          ∀ η : ℝ, 0 < η → η ≤ η₀ →
            ∃ (N₀ : ℕ) (C₁ C₂ : ℝ), 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, N₀ ≤ N →
              C₁ * (N : ℝ) ^ ((s : ℝ) - k) ≤
                (((Fintype.piFinset fun _ : Fin s =>
                    Nat.smoothNumbersUpTo N (⌊(N : ℝ) ^ η⌋₊ + 1)).filter
                  fun x => ∑ i, c i * (x i : ℤ) ^ k = 0).card : ℝ) ∧
              (((Fintype.piFinset fun _ : Fin s =>
                    Nat.smoothNumbersUpTo N (⌊(N : ℝ) ^ η⌋₊ + 1)).filter
                  fun x => ∑ i, c i * (x i : ℤ) ^ k = 0).card : ℝ) ≤
                C₂ * (N : ℝ) ^ ((s : ℝ) - k)

/-- Lemma 1: for `k ≥ 2`, `0 < η ≤ η_0(k)`, `n ≥ 1` with `2n ≥ s_0(k)`, there is
`C = C(k, n, η) > 0` such that for every prime `p`, every `B ≥ 1` with `n B^k ≤ p` and all
integers `a_i` prime to `p`, the set
`S_{A^n} = {∑ a_i x_i^k mod p : x ∈ A(B, B^η)^n}` has at least `C B^k` elements.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Lemma 1 (`integers-2026-A14-lem-1`). -/
public theorem_wanted card_smooth_diagonal_values_ge :
    ∃ g : ℕ → ℝ, (g =O[Filter.atTop] fun k : ℕ => Real.log (Real.log k) / Real.log k) ∧
      ∀ k : ℕ, 2 ≤ k → ∃ η₀ : ℝ, 0 < η₀ ∧
        ∀ η : ℝ, 0 < η → η ≤ η₀ → ∀ n : ℕ, 1 ≤ n →
          (k = 2 → 5 ≤ 2 * n) → (k = 3 → 8 ≤ 2 * n) →
          (4 ≤ k → (k : ℝ) * (Real.log k + Real.log (Real.log k) + 2 + g k) ≤ 2 * n) →
          ∃ C : ℝ, 0 < C ∧ ∀ (p : ℕ) [Fact p.Prime] (B : ℕ), 1 ≤ B → n * B ^ k ≤ p →
            ∀ a : Fin n → ℤ, (∀ i, ¬ (p : ℤ) ∣ a i) →
              C * (B : ℝ) ^ k ≤
                (((Fintype.piFinset fun _ : Fin n =>
                    Nat.smoothNumbersUpTo B (⌊(B : ℝ) ^ η⌋₊ + 1)).image
                  fun x => ∑ i, (a i : ZMod p) * (x i : ZMod p) ^ k).card : ℝ)

/-- Theorem 1: for `k ≥ 2` there is `C = C(k) > 0` such that for every `n` with `n ≥ 9`
(`k = 2`), `n ≥ 12` (`k = 3`), or `n ≥ (3/2) k (log k + log log k + 2 + O(log log k / log k))`
(`k ≥ 4`), every prime `p`, integer `c` and integers `a_i` with `p ∤ a_i`, the congruence
`a_1 x_1^k + ⋯ + a_n x_n^k ≡ c (mod p)` has a solution with `1 ≤ x_i ≤ C p^{1/k}`.

Source: Todd Cochrane, Misty Ostergaard, Craig Spencer, and Kathryn Wilson, *A Note on Small
Solutions to Diagonal Congruences*, INTEGERS 26 (2026), Article A14, Theorem 1 (`integers-2026-A14-thm-1`). -/
public theorem_wanted exists_small_solution_diagonal_congruence :
    ∃ g : ℕ → ℝ, (g =O[Filter.atTop] fun k : ℕ => Real.log (Real.log k) / Real.log k) ∧
      ∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, (k = 2 → 9 ≤ n) → (k = 3 → 12 ≤ n) →
          (4 ≤ k → 3 / 2 * (k : ℝ) * (Real.log k + Real.log (Real.log k) + 2 + g k) ≤ n) →
          ∀ (p : ℕ) [Fact p.Prime] (c : ℤ) (a : Fin n → ℤ), (∀ i, ¬ (p : ℤ) ∣ a i) →
            ∃ x : Fin n → ℕ, (∀ i, 1 ≤ x i ∧ (x i : ℝ) ≤ C * (p : ℝ) ^ ((1 : ℝ) / k)) ∧
              ∑ i, a i * (x i : ℤ) ^ k ≡ c [ZMOD p]

end

end MetaMathlibExt
