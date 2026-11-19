/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Sigma
public import MathlibExt.Biology.PopulationGenetics.Selection
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# The multilevel Price equation

For a finite population partitioned into groups `k`, with all moments taken
as population (rather than sample) moments and each group weighted in
proportion to its size, the multilevel Price equation is

`w̄ Δz̄ = Cov_k(W_k, Z_k) + E_k[Cov_j(w_kj, z_kj)] + E[w (z' - z)]`.

Here individuals are elements `⟨k, j⟩` of `Σ k, α k`; `W_k` and `Z_k` are the
within-group population means of fitness and trait. This is Frank's recursive
substitution of the within-group Price equation into the population-level
Price equation. The key algebraic step is the law of total covariance for a
nested finite population.

## Main results

* `cov_eq_between_add_within`: total covariance is the between-group
  covariance of group means plus the size-weighted mean of within-group
  covariances.
* `multilevel_price`: the two-level Price equation, obtained from Atlas's
  one-level `Selection.price` and the law of total covariance.

## References

* S. A. Frank, *Natural selection. IV. The Price equation*, Journal of
  Evolutionary Biology 25 (2012), 1002–1019.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Classical.MultilevelPrice

open scoped BigOperators

set_option linter.style.haveILetI false in
private theorem expect_cov_eq {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    𝔼 i, (f i - 𝔼 j, f j) * (g i - 𝔼 j, g j)
      = 𝔼 i, f i * g i - (𝔼 j, f j) * 𝔼 j, g j := by
  by_cases hne : Nonempty ι
  · haveI := hne
    have hpt : ∀ i, (f i - 𝔼 j, f j) * (g i - 𝔼 j, g j)
        = f i * g i - (𝔼 j, f j) * g i
          - ((𝔼 j, g j) * f i - (𝔼 j, f j) * 𝔼 j, g j) := fun i => by ring
    have hEq : (fun i => (f i - 𝔼 j, f j) * (g i - 𝔼 j, g j))
        = (fun i => f i * g i - (𝔼 j, f j) * g i
          - ((𝔼 j, g j) * f i - (𝔼 j, f j) * 𝔼 j, g j)) := funext hpt
    rw [hEq]
    simp only [Finset.expect_sub_distrib, ← Finset.mul_expect, Fintype.expect_const]
    ring
  · haveI : IsEmpty ι := not_nonempty_iff.mp hne
    simp

set_option linter.style.haveILetI false in
/-- **Law of total covariance for a nested finite population** (key lemma of the multilevel
Price equation). Individuals are the elements `⟨k, j⟩` of `Σ k, α k`: group `k : κ` has members
`j : α k`. All moments are population (not sample) moments with every individual weighted
equally, so group `k` has weight `q k = |α k| / |Σ k, α k|` (proportional to its size) and
group means `X k = 𝔼 j, x ⟨k, j⟩`, `Y k = 𝔼 j, y ⟨k, j⟩`. Then the population covariance of
`x` and `y` splits into the size-weighted covariance of the group means (between groups) plus
the size-weighted mean of the within-group population covariances:

`Cov(x, y) = ∑ k, q k (X k - ∑ l, q l X l) (Y k - ∑ l, q l Y l)
  + ∑ k, q k 𝔼 j, (x ⟨k, j⟩ - X k) (y ⟨k, j⟩ - Y k)`.

No hypothesis is needed: an empty group has weight `0`, and an empty population makes both
sides `0`. -/
theorem cov_eq_between_add_within {κ : Type*} [Fintype κ] {α : κ → Type*}
    [∀ k, Fintype (α k)] (x y : (Σ k, α k) → ℝ) (q X Y : κ → ℝ)
    (hq : ∀ k, q k = (Fintype.card (α k) : ℝ) / Fintype.card (Σ k, α k))
    (hX : ∀ k, X k = 𝔼 j, x ⟨k, j⟩) (hY : ∀ k, Y k = 𝔼 j, y ⟨k, j⟩) :
    𝔼 i, (x i - 𝔼 j, x j) * (y i - 𝔼 j, y j) =
      ∑ k, q k * (X k - ∑ l, q l * X l) * (Y k - ∑ l, q l * Y l) +
        ∑ k, q k * 𝔼 j, (x ⟨k, j⟩ - X k) * (y ⟨k, j⟩ - Y k) := by
  have hsumdiv : ∀ (f : κ → ℝ) (a : ℝ), (∑ i, f i) / a = ∑ i, f i / a := by
    intro f a
    rw [div_eq_mul_inv, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [div_eq_mul_inv]
  have hmean : ∀ F : (Σ k, α k) → ℝ, ∑ l, q l * 𝔼 j, F ⟨l, j⟩ = 𝔼 i, F i := by
    intro F
    have h1 : ∀ l, q l * 𝔼 j, F ⟨l, j⟩
        = (∑ j, F ⟨l, j⟩) / Fintype.card (Σ k, α k) := fun l => by
      rw [hq, Fintype.expect_eq_sum_div_card]
      by_cases hn : Fintype.card (α l) = 0
      · haveI : IsEmpty (α l) := Fintype.card_eq_zero_iff.mp hn
        simp
      · have hn' : (Fintype.card (α l) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
        rw [div_mul_eq_mul_div, mul_div_cancel₀ _ hn']
    have hEq : (fun l => q l * 𝔼 j, F ⟨l, j⟩)
        = (fun l => (∑ j, F ⟨l, j⟩) / Fintype.card (Σ k, α k)) := funext h1
    rw [hEq, ← hsumdiv, ← Fintype.sum_sigma, Fintype.expect_eq_sum_div_card]
  by_cases hN : Fintype.card (Σ k, α k) = 0
  · haveI : IsEmpty (Σ k, α k) := Fintype.card_eq_zero_iff.mp hN
    have hq0 : ∀ k, q k = 0 := fun k => by simp [hq]
    simp [hq0]
  · have hXw : ∑ l, q l * X l = 𝔼 j, x j := by
      simp_rw [hX]
      exact hmean x
    have hYw : ∑ l, q l * Y l = 𝔼 j, y j := by
      simp_rw [hY]
      exact hmean y
    have hXYw : ∑ k, q k * 𝔼 j, x ⟨k, j⟩ * y ⟨k, j⟩ = 𝔼 i, x i * y i :=
      hmean (fun i => x i * y i)
    have hq1 : ∑ k, q k = 1 := by
      simp_rw [hq, ← hsumdiv, ← Nat.cast_sum]
      have hcard : (∑ k, Fintype.card (α k)) = Fintype.card (Σ k, α k) :=
        Fintype.card_sigma.symm
      rw [hcard]
      exact div_self (Nat.cast_ne_zero.mpr hN)
    have hcov : 𝔼 i, (x i - 𝔼 j, x j) * (y i - 𝔼 j, y j)
        = 𝔼 i, x i * y i - (𝔼 j, x j) * 𝔼 j, y j :=
      expect_cov_eq x y
    have hcovk : ∀ k, 𝔼 j, (x ⟨k, j⟩ - X k) * (y ⟨k, j⟩ - Y k)
        = 𝔼 j, x ⟨k, j⟩ * y ⟨k, j⟩ - X k * Y k := fun k => by
      rw [hX k, hY k]
      exact expect_cov_eq (fun j => x ⟨k, j⟩) (fun j => y ⟨k, j⟩)
    rw [hXw, hYw, hcov]
    have hbet : (∑ k, q k * (X k - 𝔼 j, x j) * (Y k - 𝔼 j, y j))
        = ∑ k, q k * X k * Y k - (𝔼 j, x j) * 𝔼 j, y j := by
      have hpt : ∀ k, q k * (X k - 𝔼 j, x j) * (Y k - 𝔼 j, y j)
          = q k * X k * Y k - (𝔼 j, x j) * (q k * Y k)
            - ((𝔼 j, y j) * (q k * X k) - (𝔼 j, x j) * (𝔼 j, y j) * q k) :=
        fun k => by ring
      have hEq : (fun k => q k * (X k - 𝔼 j, x j) * (Y k - 𝔼 j, y j))
          = (fun k => q k * X k * Y k - (𝔼 j, x j) * (q k * Y k)
            - ((𝔼 j, y j) * (q k * X k) - (𝔼 j, x j) * (𝔼 j, y j) * q k)) :=
        funext hpt
      rw [hEq]
      simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hXw, hYw, hq1]
      ring
    have hwit : (∑ k, q k * 𝔼 j, (x ⟨k, j⟩ - X k) * (y ⟨k, j⟩ - Y k))
        = 𝔼 i, x i * y i - ∑ k, q k * X k * Y k := by
      have hpt : ∀ k, q k * 𝔼 j, (x ⟨k, j⟩ - X k) * (y ⟨k, j⟩ - Y k)
          = q k * 𝔼 j, x ⟨k, j⟩ * y ⟨k, j⟩ - q k * X k * Y k := fun k => by
        rw [hcovk k]
        ring
      have hEq : (fun k => q k * 𝔼 j, (x ⟨k, j⟩ - X k) * (y ⟨k, j⟩ - Y k))
          = (fun k => q k * 𝔼 j, x ⟨k, j⟩ * y ⟨k, j⟩ - q k * X k * Y k) :=
        funext hpt
      rw [hEq, Finset.sum_sub_distrib, hXYw]
    rw [hbet, hwit]
    ring

/-- **Multilevel Price equation.** For individuals `⟨k, j⟩` in groups `k`,
with group weights proportional to group size and group mean fitness/trait
`W k`, `Z k`, the population-level change satisfies

`w̄ Δz̄ = Cov_k(W_k, Z_k) + E_k[Cov_j(w_kj, z_kj)] + E[w (z' - z)]`,

where all covariances and expectations are population moments. Only the
global hypothesis `∑ i, w i ≠ 0` is required. -/
theorem multilevel_price {κ : Type*} [Fintype κ] {α : κ → Type*} [∀ k, Fintype (α k)]
    (w z z' : (Σ k, α k) → ℝ) (q W Z : κ → ℝ)
    (hq : ∀ k, q k = (Fintype.card (α k) : ℝ) / Fintype.card (Σ k, α k))
    (hW : ∀ k, W k = 𝔼 j, w ⟨k, j⟩) (hZ : ∀ k, Z k = 𝔼 j, z ⟨k, j⟩)
    (hw : ∑ i, w i ≠ 0) :
    (𝔼 i, w i) * ((∑ i, w i * z' i) / ∑ i, w i - 𝔼 i, z i) =
      ∑ k, q k * (W k - ∑ l, q l * W l) * (Z k - ∑ l, q l * Z l) +
        ∑ k, q k * 𝔼 j, (w ⟨k, j⟩ - W k) * (z ⟨k, j⟩ - Z k) +
        𝔼 i, w i * (z' i - z i) := by
  rw [MathlibExt.Biology.PopulationGenetics.Selection.price w z z' hw,
    cov_eq_between_add_within w z q W Z hq hW hZ]

end MathlibExt.Biology.PopulationGenetics.Classical.MultilevelPrice
