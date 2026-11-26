/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LaurentSeriesConvergentProperties

/-!
# Distance from an irrational Laurent series to its convergents

This module proves that the convergents of an irrational Laurent series approximate it: if
$|\alpha| \ge 1$ then $|\alpha - P_n / Q_n| < |\alpha|$ for all $n \ge 0$, and if
$|\alpha| < 1$ then $|\alpha - P_0 / Q_0| = |\alpha|$ and
$|\alpha - P_n / Q_n| < |\alpha|$ for all $n \ge 1$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 4 (`integers-2026-A57-lem-4`).
-/

namespace MetaMathlibExt

@[expose] public noncomputable section

section LaurentContinuedFraction

private theorem exists_polyPart {K : Type*} [Field K] (x : LaurentSeries K) :
    ∃ B : Polynomial K, polyToLaurentInv B = laurentPolyPart x := by
  classical
  refine ⟨∑ i ∈ Finset.Icc x.order 0, Polynomial.monomial (-i).toNat (x.coeff i), ?_⟩
  unfold polyToLaurentInv
  rw [map_sum]
  have hterm (i : ℤ) (hi : i ∈ Finset.Icc x.order 0) :
      Polynomial.aeval (laurentInvVar K) (Polynomial.monomial (-i).toNat (x.coeff i)) =
        HahnSeries.single i (x.coeff i) := by
    have hi' := (Finset.mem_Icc.mp hi).2
    rw [Polynomial.aeval_monomial, LaurentSeries.algebraMap_apply, HahnSeries.C_apply]
    simp [laurentInvVar, HahnSeries.single_pow, HahnSeries.single_mul_single,
      Int.toNat_of_nonneg (show 0 ≤ -i by omega)]
  rw [Finset.sum_congr rfl hterm]
  ext j
  simp only [HahnSeries.coeff_sum, HahnSeries.coeff_single, laurentPolyPart_coeff]
  by_cases hj : j ≤ 0
  · rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj'
      have hlt : j < x.order := by
        simp only [Finset.mem_Icc, hj, and_true, not_le] at hj'
        exact hj'
      simp [HahnSeries.coeff_eq_zero_of_lt_order hlt]
  · rw [Finset.sum_eq_zero]
    · simp [hj]
    · intro i hi
      have hi' := (Finset.mem_Icc.mp hi).2
      simp [show j ≠ i by omega]

private theorem order_inv {K : Type*} [Field K] (x : LaurentSeries K) (hx : x ≠ 0) :
    x⁻¹.order = -x.order := by
  have h := HahnSeries.order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, HahnSeries.order_one] at h
  omega

private theorem polyPart_eq_zero {K : Type*} [Field K] {y : LaurentSeries K}
    (hy : 0 < y.order) : laurentPolyPart y = 0 := by
  ext n
  rw [laurentPolyPart_coeff]
  split_ifs with h
  · rw [HahnSeries.coeff_eq_zero_of_lt_order (h.trans_lt hy), HahnSeries.coeff_zero]
  · rw [HahnSeries.coeff_zero]

private theorem polyPart_order {K : Type*} [Field K] {y : LaurentSeries K}
    (hy : y.order ≤ 0) : (laurentPolyPart y).order = y.order := by
  by_cases hy0 : y = 0
  · subst hy0
    have h0 : laurentPolyPart (0 : LaurentSeries K) = 0 := by
      ext n
      rw [laurentPolyPart_coeff]
      split_ifs with h
      · rfl
      · rw [HahnSeries.coeff_zero]
    rw [h0]
  · have hc : (laurentPolyPart y).coeff y.order ≠ 0 := by
      simp only [laurentPolyPart_coeff, hy, ↓reduceIte]
      exact HahnSeries.coeff_order_eq_zero.not.mpr hy0
    refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
    by_contra! hlt
    have hz := HahnSeries.coeff_order_eq_zero.not.mpr
      (HahnSeries.ne_zero_of_coeff_ne_zero hc)
    apply hz
    rw [laurentPolyPart_coeff]
    split_ifs with hle
    · exact HahnSeries.coeff_eq_zero_of_lt_order hlt
    · rfl

private theorem sub_polyPart_order {K : Type*} [Field K] {α : LaurentSeries K}
    (hα : LaurentIsIrrational α) (h0 : α.order ≤ 0) :
    α.order < (α - laurentPolyPart α).order := by
  obtain ⟨B, hB⟩ := exists_polyPart α
  have hr : α - laurentPolyPart α ≠ 0 := sub_ne_zero.mpr fun h =>
    not_laurentIsIrrational_polyToLaurentInv B (h.trans hB.symm ▸ hα)
  have hvan (m : ℤ) (hm : m ≤ α.order) : (α - laurentPolyPart α).coeff m = 0 := by
    have hm0 : m ≤ 0 := hm.trans h0
    simp only [HahnSeries.coeff_sub, laurentPolyPart_coeff, hm0, ↓reduceIte, sub_self]
  by_contra! hlt
  exact HahnSeries.coeff_order_eq_zero.not.mpr hr (hvan _ hlt)

private theorem partialQuotient_one_order {K : Type*} [Field K] {α : LaurentSeries K}
    (hpos : 0 < α.order) : (laurentPartialQuotient α 1).order = -α.order := by
  have hA1 : laurentCompleteQuotient α 1 = α⁻¹ := by
    have h := (laurentPartialQuotient_zero α).2
    rw [polyPart_eq_zero hpos, sub_zero] at h
    exact h
  have hα0 : α ≠ 0 := by
    rintro rfl
    simp [HahnSeries.order_zero] at hpos
  have hA1ord : (laurentCompleteQuotient α 1).order = -α.order := by
    rw [hA1, order_inv α hα0]
  have hb1 : laurentPartialQuotient α 1 =
      laurentPolyPart (laurentCompleteQuotient α 1) := rfl
  rw [hb1, polyPart_order (by omega : (laurentCompleteQuotient α 1).order ≤ 0), hA1ord]

private theorem conv_zero {K : Type*} [Field K] (α : LaurentSeries K) :
    laurentConvNum α 1 / laurentConvDen α 1 = laurentPolyPart α := by
  have eN : laurentConvNum α 1 = laurentPartialQuotient α 0 := rfl
  have eD : laurentConvDen α 1 = 1 := rfl
  rw [eN, eD, div_one, (laurentPartialQuotient_zero α).1]

private theorem convDen_order_neg {K : Type*} [Field K] {α : LaurentSeries K}
    (hα : LaurentIsIrrational α) (n : ℕ) (hn : 1 ≤ n) :
    (laurentConvDen α (n + 1)).order < 0 := by
  have hden := (laurentConvergent_properties α hα).2.2.1
  have h1 : (laurentConvDen α 2).order < 0 := by
    have h := (hden 1 le_rfl).2
    rwa [show laurentConvDen α 1 = 1 from rfl, HahnSeries.order_one] at h
  have aux : ∀ k : ℕ, (laurentConvDen α (k + 2)).order < 0 := by
    intro k
    induction k with
    | zero => exact h1
    | succ k ih =>
      have h := (hden (k + 2) (by omega)).2
      have h' : k + 2 + 1 = (k + 1) + 2 := by omega
      rw [h'] at h
      exact h.trans ih
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h' : k + 1 + 1 = k + 2 := by omega
  rw [h']
  exact aux k

private theorem convDen_order_le_two {K : Type*} [Field K] {α : LaurentSeries K}
    (hα : LaurentIsIrrational α) (n : ℕ) (hn : 1 ≤ n) :
    (laurentConvDen α (n + 1)).order ≤ (laurentConvDen α 2).order := by
  have hden := (laurentConvergent_properties α hα).2.2.1
  have aux : ∀ k : ℕ, (laurentConvDen α (k + 2)).order ≤ (laurentConvDen α 2).order := by
    intro k
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have h := (hden (k + 2) (by omega)).2
      have h' : k + 2 + 1 = (k + 1) + 2 := by omega
      rw [h'] at h
      exact h.le.trans ih
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have h' : k + 1 + 1 = k + 2 := by omega
  rw [h']
  exact aux k

private theorem partialQuotient_order_neg {K : Type*} [Field K] {α : LaurentSeries K}
    (hα : LaurentIsIrrational α) (n : ℕ) (hn : 1 ≤ n) :
    (laurentPartialQuotient α (n + 1)).order < 0 := by
  have hden := (laurentConvergent_properties α hα).2.2.1
  have hsum := (laurentConvergent_properties α hα).2.2.2.1
  have h1 := hsum (n + 1) (by omega)
  have heq : n + 1 + 1 = n + 2 := by omega
  rw [heq] at h1
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)] at h1
  have h0 := hsum n hn
  have hlt := (hden (n + 1) (by omega)).2
  rw [heq] at hlt
  omega

/-- **Distance from an irrational Laurent series to its convergents.** Let $K$ be a field, let
$\alpha \in K((x^{-1}))$ be irrational with convergents $P_n/Q_n$ ($n \ge 0$), and for nonzero
$y \in K((x^{-1}))$ let $|y| = |x|^{\deg y}$, where $\deg y$ is the largest exponent of $x$
occurring in $y$ and $|x| > 1$ is fixed. (i) If $|\alpha| \ge 1$, then
$|\alpha - P_n/Q_n| < |\alpha|$ for all $n \ge 0$. (ii) If $|\alpha| < 1$, then
$|\alpha - P_0/Q_0| = |\alpha|$ and $|\alpha - P_n/Q_n| < |\alpha|$ for all $n \ge 1$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 4 (`integers-2026-A57-lem-4`). -/
public theorem laurent_sub_convergent_order {K : Type*} [Field K] (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) :
    (α.order ≤ 0 → ∀ n : ℕ,
        α.order < (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order) ∧
      (0 < α.order →
        (α - laurentConvNum α 1 / laurentConvDen α 1).order = α.order ∧
          ∀ n : ℕ, 1 ≤ n →
            α.order < (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order) := by
  have herr := (laurentConvergent_properties α hα).2.2.2.2.1
  constructor
  · intro h0 n
    by_cases hn : n = 0
    · subst hn
      change α.order < (α - laurentConvNum α 1 / laurentConvDen α 1).order
      rw [conv_zero α]
      exact sub_polyPart_order hα h0
    · have hn1 : 1 ≤ n := by omega
      rw [herr n hn1]
      have hb := partialQuotient_order_neg hα n hn1
      have hq := convDen_order_neg hα n hn1
      omega
  · intro hpos
    refine ⟨?_, ?_⟩
    · rw [conv_zero α, polyPart_eq_zero hpos, sub_zero]
    · intro n hn
      rw [herr n hn]
      have hb := partialQuotient_order_neg hα n hn
      have hq := convDen_order_le_two hα n hn
      have hb1 := partialQuotient_one_order hpos
      have hQ2 := congrArg HahnSeries.order (laurentConv_two α).2
      omega

end LaurentContinuedFraction

end

end MetaMathlibExt
