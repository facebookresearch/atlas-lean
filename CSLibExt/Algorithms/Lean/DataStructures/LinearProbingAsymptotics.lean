/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingAnalysis
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# Limits of Knuth's sums for linear probing

Section 8 of Knuth's note (D. E. Knuth, *Notes on "open" addressing*, 22 July 1963, typeset by
H. Prodinger in 1997) approximates his sums by
`E_r(N, k) ≈ 1 + C(r + 1, r) α + C(r + 2, r) α ^ 2 + ⋯ = (1 - α) ^ -(r + 1)` with
`α = (k - 1) / N`, and states that the approximation becomes exact as `N → ∞` for fixed `α`.

## Main result

* `tendsto_knuthE`: if `n N / N → α` with `0 ≤ α < 1`, then
  `E_r(N, n N + 1) → 1 / (1 - α) ^ (r + 1)`. The proof is Tannery's theorem (dominated
  convergence for series): the `j`-th term `C(j + r, r) ∏_{i < j} (n N - i) / N` tends to
  `C(j + r, r) α ^ j` and is eventually dominated by `C(j + r, r) β ^ j` for any `β` with
  `α < β < 1`; the limit series is summed by `tsum_choose_mul_geometric_of_norm_lt_one`.

Combined with Knuth's exact formulas (`insertionCost_eq` and `successfulSearchCost_eq`, recorded in
`WantedExt.ComputerScience.LinearProbingAnalysisWanted`), this gives the fixed-load-factor limits
`(1 + 1 / (1 - α) ^ 2) / 2` and `(1 + 1 / (1 - α)) / 2` of the mean costs.
-/

@[expose] public section

set_option autoImplicit false

open Filter Topology

namespace Cslib.Algorithms.Lean.LinearProbing

/-- `(a : ℝ) - b ≤ ((a - b : ℕ) : ℝ)` for natural numbers, with truncated subtraction. -/
private theorem cast_sub_le_cast_tsub (a b : ℕ) : (a : ℝ) - b ≤ ((a - b : ℕ) : ℝ) := by
  rcases le_total b a with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith

/-- **Limit of Knuth's sums at a fixed load factor** (Knuth, *Notes on "open" addressing*, 1963,
Section 8). Let `r` be a natural number and `0 ≤ α < 1`. If `n N / N → α` as `N → ∞`, then
`E_r(N, n N + 1) → 1 / (1 - α) ^ (r + 1)`, where
`E_r(N, k) = ∑_{j < k} C(r + j, r) (k - 1)(k - 2)⋯(k - j) / N ^ j` is `knuthE r N k`. -/
theorem tendsto_knuthE (r : ℕ) {α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1) (n : ℕ → ℕ)
    (hlim : Tendsto (fun N : ℕ => (n N : ℝ) / N) atTop (𝓝 α)) :
    Tendsto (fun N : ℕ => (knuthE r N (n N + 1) : ℝ)) atTop (𝓝 (1 / (1 - α) ^ (r + 1))) := by
  set f : ℕ → ℕ → ℝ := fun N j =>
    ((j + r).choose r : ℝ) * ∏ i ∈ Finset.range j, (((n N - i : ℕ) : ℝ) / N) with hf
  -- `E_r(N, n N + 1)` is the full series `∑' j, f N j`, whose terms vanish for `j > n N`.
  have hrepr : ∀ N, (knuthE r N (n N + 1) : ℝ) = ∑' j, f N j := by
    intro N
    have hzero : ∀ j ∉ Finset.range (n N + 1), f N j = 0 := by
      intro j hj
      simp only [Finset.mem_range, not_lt] at hj
      simp only [hf]
      apply mul_eq_zero_of_right
      apply Finset.prod_eq_zero (i := n N) (Finset.mem_range.mpr (by omega))
      simp
    rw [tsum_eq_sum hzero]
    simp only [knuthE, Nat.add_sub_cancel]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
    simp only [hf]
    rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_range, add_comm r j]
    ring
  -- Each factor `(n N - i) / N` tends to `α`.
  have hfac : ∀ i : ℕ, Tendsto (fun N : ℕ => (((n N - i : ℕ) : ℝ) / N)) atTop (𝓝 α) := by
    intro i
    have hlow : Tendsto (fun N : ℕ => (n N : ℝ) / N - (i : ℝ) / N) atTop (𝓝 α) := by
      simpa using hlim.sub (tendsto_const_div_atTop_nhds_zero_nat (i : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hlim (fun N => ?_) (fun N => ?_)
    · rw [← sub_div]
      exact div_le_div_of_nonneg_right (cast_sub_le_cast_tsub _ _) (Nat.cast_nonneg _)
    · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _)) (Nat.cast_nonneg _)
  have hpoint : ∀ j : ℕ, Tendsto (fun N => f N j) atTop
      (𝓝 (((j + r).choose r : ℝ) * α ^ j)) := by
    intro j
    have hprod := tendsto_finsetProd (Finset.range j) (fun i _ => hfac i)
    rw [Finset.prod_const, Finset.card_range] at hprod
    exact hprod.const_mul _
  -- Domination by `C(j + r, r) β ^ j` with `β = (1 + α) / 2`.
  set β : ℝ := (1 + α) / 2 with hβ
  have hαβ : α < β := by rw [hβ]; linarith
  have hβ₀ : 0 ≤ β := by rw [hβ]; linarith
  have hβ₁ : β < 1 := by rw [hβ]; linarith
  have hnorm : ‖β‖ < 1 := by rwa [Real.norm_of_nonneg hβ₀]
  have hsum : Summable (fun j : ℕ => ((j + r).choose r : ℝ) * β ^ j) :=
    summable_choose_mul_geometric_of_norm_lt_one r hnorm
  have hev : ∀ᶠ N in atTop, (n N : ℝ) / N ≤ β := hlim.eventually (Iic_mem_nhds hαβ)
  have hbound : ∀ᶠ N in atTop, ∀ j, ‖f N j‖ ≤ ((j + r).choose r : ℝ) * β ^ j := by
    filter_upwards [hev] with N hN j
    have hnn : ∀ i ∈ Finset.range j, 0 ≤ (((n N - i : ℕ) : ℝ) / N) := fun i _ => by positivity
    have hle : ∀ i ∈ Finset.range j, (((n N - i : ℕ) : ℝ) / N) ≤ β := fun i _ =>
      le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Nat.sub_le _ _))
        (Nat.cast_nonneg _)) hN
    have hprod_le : ∏ i ∈ Finset.range j, (((n N - i : ℕ) : ℝ) / N) ≤ β ^ j := by
      calc ∏ i ∈ Finset.range j, (((n N - i : ℕ) : ℝ) / N)
          ≤ ∏ _i ∈ Finset.range j, β := Finset.prod_le_prod₀ hnn hle
        _ = β ^ j := by rw [Finset.prod_const, Finset.card_range]
    have hprod_nn : 0 ≤ ∏ i ∈ Finset.range j, (((n N - i : ℕ) : ℝ) / N) :=
      Finset.prod_nonneg hnn
    rw [hf, Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) hprod_nn)]
    exact mul_le_mul_of_nonneg_left hprod_le (Nat.cast_nonneg _)
  have hlimit := tendsto_tsum_of_dominated_convergence hsum hpoint hbound
  have hval : ∑' j : ℕ, ((j + r).choose r : ℝ) * α ^ j = 1 / (1 - α) ^ (r + 1) := by
    have hα : ‖α‖ < 1 := by rwa [Real.norm_of_nonneg hα₀]
    exact tsum_choose_mul_geometric_of_norm_lt_one r hα
  rw [hval] at hlimit
  exact hlimit.congr fun N => (hrepr N).symm

end Cslib.Algorithms.Lean.LinearProbing
