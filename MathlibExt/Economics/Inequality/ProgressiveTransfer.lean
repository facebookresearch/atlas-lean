/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic

@[expose] public section

/-!
# Progressive transfers and separable convex inequality indices

The chosen inequality index is additively separable, `(∑ i, φ (x i)) / n` with `φ` convex on
a domain `s` (at a fixed mean, `φ y = y ^ 2` gives the variance and `φ y = y log y` the Theil
index, up to constants). A transfer of `δ` from individual `j` to individual `i` preserves
total income (`sum_transfer`); it is progressive (Pigou–Dalton) when `0 ≤ δ ≤ x j - x i`.

A progressive transfer moves the pair `(x i, x j)` to a pair of convex combinations of the two
incomes with complementary weights, so convexity of `φ` gives the Pigou–Dalton principle: the
index weakly decreases (`separableIndex_transfer_le`). The bound `δ ≤ x j - x i` is needed; a
larger transfer can increase the index.

## Main results

* `MathlibExt.Economics.Inequality.sum_transfer`
* `MathlibExt.Economics.Inequality.separableIndex_transfer_le`

Atlas roadmap target AP05.T02.
-/

namespace MathlibExt.Economics.Inequality

open Finset

/-- Additively separable inequality index `(∑ i, φ (x i)) / n` of the income distribution
`x` over the population `ι` (`n = card ι`), for a convex evaluation function `φ`. At a fixed
mean, `φ y = y ^ 2` gives the variance up to a constant and `φ y = y * log y` gives the Theil
index up to a constant. -/
noncomputable def separableIndex {ι : Type*} [Fintype ι] (φ : ℝ → ℝ) (x : ι → ℝ) : ℝ :=
  (∑ i, φ (x i)) / Fintype.card ι

/-- Transfer of the amount `δ` from individual `j` to individual `i`; all other incomes are
unchanged. It is a progressive (Pigou–Dalton) transfer when `0 ≤ δ ≤ x j - x i`. -/
def transfer {ι : Type*} [DecidableEq ι] (x : ι → ℝ) (i j : ι) (δ : ℝ) : ι → ℝ :=
  Function.update (Function.update x i (x i + δ)) j (x j - δ)

/-- A transfer between two distinct individuals preserves total (hence mean) income. -/
theorem sum_transfer {ι : Type*} [Fintype ι] [DecidableEq ι] (x : ι → ℝ) {i j : ι}
    (hij : i ≠ j) (δ : ℝ) :
    ∑ k, transfer x i j δ k = ∑ k, x k := by
  have htj : transfer x i j δ j = x j - δ := by
    simp [transfer, Function.update_apply]
  have hti : transfer x i j δ i = x i + δ := by
    simp [transfer, Function.update_apply, hij]
  have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have e1 : transfer x i j δ j + ∑ k ∈ Finset.univ.erase j, transfer x i j δ k
      = ∑ k, transfer x i j δ k :=
    Finset.add_sum_erase _ _ (Finset.mem_univ j)
  have e2 : transfer x i j δ i + ∑ k ∈ (Finset.univ.erase j).erase i, transfer x i j δ k
      = ∑ k ∈ Finset.univ.erase j, transfer x i j δ k :=
    Finset.add_sum_erase _ _ hmem
  have e3 : x j + ∑ k ∈ Finset.univ.erase j, x k = ∑ k, x k :=
    Finset.add_sum_erase _ _ (Finset.mem_univ j)
  have e4 : x i + ∑ k ∈ (Finset.univ.erase j).erase i, x k
      = ∑ k ∈ Finset.univ.erase j, x k :=
    Finset.add_sum_erase _ _ hmem
  have erest : (∑ k ∈ (Finset.univ.erase j).erase i, transfer x i j δ k)
      = ∑ k ∈ (Finset.univ.erase j).erase i, x k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hki, hk⟩ := hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkj, -⟩ := hk
    simp [transfer, Function.update_apply, hki, hkj]
  rw [htj] at e1
  rw [hti] at e2
  linarith

/-- **Pigou–Dalton principle for separable convex indices.** A progressive transfer
(`0 ≤ δ ≤ x j - x i`, from the richer `j` to the poorer `i`) weakly reduces the separable
inequality index of any `φ` convex on a set `s` containing both incomes. -/
theorem separableIndex_transfer_le {ι : Type*} [Fintype ι] [DecidableEq ι] {φ : ℝ → ℝ}
    {s : Set ℝ} (hφ : ConvexOn ℝ s φ) (x : ι → ℝ) {i j : ι} (hij : i ≠ j) {δ : ℝ}
    (hxi : x i ∈ s) (hxj : x j ∈ s) (hδ0 : 0 ≤ δ) (hδ : δ ≤ x j - x i) :
    separableIndex φ (transfer x i j δ) ≤ separableIndex φ x := by
  have htj : transfer x i j δ j = x j - δ := by
    simp [transfer, Function.update_apply]
  have hti : transfer x i j δ i = x i + δ := by
    simp [transfer, Function.update_apply, hij]
  have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have e1 : φ (transfer x i j δ j) + ∑ k ∈ Finset.univ.erase j, φ (transfer x i j δ k)
      = ∑ k, φ (transfer x i j δ k) :=
    Finset.add_sum_erase _ (fun k => φ (transfer x i j δ k)) (Finset.mem_univ j)
  have e2 : φ (transfer x i j δ i)
        + ∑ k ∈ (Finset.univ.erase j).erase i, φ (transfer x i j δ k)
      = ∑ k ∈ Finset.univ.erase j, φ (transfer x i j δ k) :=
    Finset.add_sum_erase _ (fun k => φ (transfer x i j δ k)) hmem
  have e3 : φ (x j) + ∑ k ∈ Finset.univ.erase j, φ (x k) = ∑ k, φ (x k) :=
    Finset.add_sum_erase _ (fun k => φ (x k)) (Finset.mem_univ j)
  have e4 : φ (x i) + ∑ k ∈ (Finset.univ.erase j).erase i, φ (x k)
      = ∑ k ∈ Finset.univ.erase j, φ (x k) :=
    Finset.add_sum_erase _ (fun k => φ (x k)) hmem
  have erest : (∑ k ∈ (Finset.univ.erase j).erase i, φ (transfer x i j δ k))
      = ∑ k ∈ (Finset.univ.erase j).erase i, φ (x k) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hki, hk⟩ := hk
    rw [Finset.mem_erase] at hk
    obtain ⟨hkj, -⟩ := hk
    have htk : transfer x i j δ k = x k := by
      simp [transfer, Function.update_apply, hki, hkj]
    rw [htk]
  rw [htj] at e1
  rw [hti] at e2
  have h2pt : φ (x i + δ) + φ (x j - δ) ≤ φ (x i) + φ (x j) := by
    by_cases hδeq : δ = 0
    · subst hδeq
      simp
    · have hpos : 0 < δ := lt_of_le_of_ne hδ0 (Ne.symm hδeq)
      have hlt : x i < x j := by linarith
      have hgap : 0 < x j - x i := sub_pos.mpr hlt
      have hgapne : x j - x i ≠ 0 := ne_of_gt hgap
      set lam : ℝ := δ / (x j - x i) with hlam
      have hlam0 : 0 < lam := by
        rw [hlam]
        exact div_pos hpos hgap
      have hlam1 : lam ≤ 1 := by
        rw [hlam]
        exact (div_le_one hgap).mpr hδ
      have h1lam0 : 0 ≤ 1 - lam := by linarith
      have hsum1 : (1 - lam) + lam = 1 := by ring
      have hsum2 : lam + (1 - lam) = 1 := by ring
      have hkey : lam * (x j - x i) = δ := by
        rw [hlam]
        exact div_mul_cancel₀ δ hgapne
      have hp1 : x i + δ = (1 - lam) * x i + lam * x j := by
        have h : (1 - lam) * x i + lam * x j = x i + lam * (x j - x i) := by ring
        rw [h, hkey]
      have hp2 : x j - δ = lam * x i + (1 - lam) * x j := by
        have h : lam * x i + (1 - lam) * x j = x j - lam * (x j - x i) := by ring
        rw [h, hkey]
      have hc1 : φ ((1 - lam) • x i + lam • x j)
          ≤ (1 - lam) • φ (x i) + lam • φ (x j) :=
        hφ.2 hxi hxj h1lam0 hlam0.le hsum1
      have hc2 : φ (lam • x i + (1 - lam) • x j)
          ≤ lam • φ (x i) + (1 - lam) • φ (x j) :=
        hφ.2 hxi hxj hlam0.le h1lam0 hsum2
      simp only [smul_eq_mul] at hc1 hc2
      rw [← hp1] at hc1
      rw [← hp2] at hc2
      have h := add_le_add hc1 hc2
      have hrhs : ((1 - lam) * φ (x i) + lam * φ (x j))
          + (lam * φ (x i) + (1 - lam) * φ (x j)) = φ (x i) + φ (x j) := by ring
      rwa [hrhs] at h
  have hsum : (∑ k, φ (transfer x i j δ k)) ≤ ∑ k, φ (x k) := by linarith
  unfold separableIndex
  exact div_le_div_of_nonneg_right hsum (Nat.cast_nonneg _)

end MathlibExt.Economics.Inequality
