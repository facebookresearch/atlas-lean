/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LaurentSeriesConvergentProperties
public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Degree identities at convergents of a Möbius–Frobenius fixed point

We prove the two order identities for the linear forms arising from a Möbius–Frobenius
fixed point evaluated at convergents of an irrational Laurent series.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 7, (3.7) and (3.8) (`integers-2026-A57-lem-7`).
-/

namespace MetaMathlibExt

@[expose] public noncomputable section

section LaurentContinuedFraction

variable {K : Type*} [Field K]

open HahnSeries

private theorem order_inv_aux (x : LaurentSeries K) (hx : x ≠ 0) : x⁻¹.order = -x.order := by
  have h := order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, order_one] at h
  omega

private theorem order_div_aux (x y : LaurentSeries K) (hx : x ≠ 0) (hy : y ≠ 0) :
    (x / y).order = x.order - y.order := by
  rw [div_eq_mul_inv, order_mul hx (inv_ne_zero hy), order_inv_aux y hy]
  ring

private theorem order_add_eq_left_of_lt (x y : LaurentSeries K) (hx : x ≠ 0)
    (hlt : x.order < y.order) : (x + y).order = x.order := by
  have hxTop : (x.order : WithTop ℤ) = x.orderTop := order_eq_orderTop_of_ne_zero hx
  have hltTop : x.orderTop < y.orderTop := by
    by_cases hy : y = 0
    · subst hy
      rw [orderTop_zero, ← hxTop]
      exact WithTop.coe_lt_top _
    · rw [← hxTop, ← order_eq_orderTop_of_ne_zero hy]
      exact WithTop.coe_lt_coe.mpr hlt
  have hadd := orderTop_add_eq_left hltTop
  have hne : x + y ≠ 0 := orderTop_ne_top.mp (hadd.trans_ne hltTop.ne_top)
  have h := order_eq_orderTop_of_ne_zero hne
  rw [hadd, ← hxTop] at h
  exact WithTop.coe_eq_coe.mp h

private theorem aeval_monomial_single (n : ℕ) (c : K) :
    (Polynomial.aeval (laurentInvVar K)) (Polynomial.monomial n c) =
      single (-(n : ℤ)) c := by
  rw [Polynomial.aeval_monomial, LaurentSeries.algebraMap_apply, C_apply]
  simp [laurentInvVar, single_pow, single_mul_single]

private theorem coeff_polyToLaurentInv (T : Polynomial K) (m : ℤ) :
    (polyToLaurentInv T).coeff m = if m ≤ 0 then T.coeff (-m).toNat else 0 := by
  have hsum : polyToLaurentInv T =
      ∑ i ∈ Finset.range (T.natDegree + 1), single (-(i : ℤ)) (T.coeff i) := by
    conv_lhs => rw [Polynomial.as_sum_range T]
    unfold polyToLaurentInv
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [aeval_monomial_single]
  rw [hsum, coeff_sum]
  by_cases hm : m ≤ 0
  · have hnonneg : 0 ≤ -m := by omega
    set k := (-m).toNat with hk
    have hkm : (-(k : ℤ)) = m := by
      rw [hk, Int.toNat_of_nonneg hnonneg]
      omega
    have hmk : m = (-(k : ℤ)) := hkm.symm
    rw [Finset.sum_eq_single k]
    · simp only [coeff_single, hmk, ↓reduceIte]
      simp [hm, hk]
    · intro b _ hb
      simp only [coeff_single]
      have hne : m ≠ (-(b : ℤ)) := by
        intro h
        apply hb
        have h2 : (b : ℤ) = (k : ℤ) := by omega
        exact Nat.cast_injective h2
      simp [hne]
    · intro hk_mem
      simp only [coeff_single]
      have hlt : T.natDegree < k := by
        simp only [Finset.mem_range, not_lt] at hk_mem
        omega
      have hcoeff : T.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hlt
      simp [hcoeff]
  · simp only [hm, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro i _
    simp only [coeff_single]
    have hne : m ≠ (-(i : ℤ)) := by omega
    simp [hne]

private theorem order_polyToLaurentInv (T : Polynomial K) :
    (polyToLaurentInv T).order = -(T.natDegree : ℤ) := by
  by_cases hT : T = 0
  · subst hT
    simp [polyToLaurentInv]
  · have hcoeff : T.coeff T.natDegree ≠ 0 := by
      rw [Polynomial.coeff_natDegree]
      exact Polynomial.leadingCoeff_ne_zero.mpr hT
    have ha0 : (-(T.natDegree : ℤ)) ≤ 0 := by omega
    have htoNat : (-(-(T.natDegree : ℤ))).toNat = T.natDegree := by
      simp [Int.toNat_natCast]
    have hne_coeff : (polyToLaurentInv T).coeff (-(T.natDegree : ℤ)) ≠ 0 := by
      simp only [coeff_polyToLaurentInv, ha0, ↓reduceIte, htoNat]
      exact hcoeff
    have hne : polyToLaurentInv T ≠ 0 := ne_zero_of_coeff_ne_zero hne_coeff
    apply le_antisymm
    · exact order_le_of_coeff_ne_zero hne_coeff
    · by_contra! hlt
      have hz := coeff_order_eq_zero.not.mpr hne
      apply hz
      simp only [coeff_polyToLaurentInv]
      by_cases hm0 : (polyToLaurentInv T).order ≤ 0
      · simp only [hm0, ↓reduceIte]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hnonneg : 0 ≤ -((polyToLaurentInv T).order) := by omega
        have h2 : (((-((polyToLaurentInv T).order)).toNat : ℕ) : ℤ) =
            -((polyToLaurentInv T).order) := Int.toNat_of_nonneg hnonneg
        omega
      · simp [hm0]

private theorem polyToLaurentInv_ne_zero (T : Polynomial K) (hT : T ≠ 0) :
    polyToLaurentInv T ≠ 0 := by
  have hcoeff : T.coeff T.natDegree ≠ 0 := by
    rw [Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hT
  have ha0 : (-(T.natDegree : ℤ)) ≤ 0 := by omega
  have htoNat : (-(-(T.natDegree : ℤ))).toNat = T.natDegree := by
    simp [Int.toNat_natCast]
  have hne_coeff : (polyToLaurentInv T).coeff (-(T.natDegree : ℤ)) ≠ 0 := by
    simp only [coeff_polyToLaurentInv, ha0, ↓reduceIte, htoNat]
    exact hcoeff
  exact ne_zero_of_coeff_ne_zero hne_coeff

private theorem polyToLaurentInv_injective : Function.Injective (polyToLaurentInv (K := K)) := by
  intro T1 T2 h
  have hsub : polyToLaurentInv (T1 - T2) = 0 := by
    unfold polyToLaurentInv at h ⊢
    rw [map_sub, h, sub_self]
  have hzero : T1 - T2 = 0 := by
    by_contra hne
    exact polyToLaurentInv_ne_zero _ hne hsub
  exact sub_eq_zero.mp hzero

private theorem exists_polyPart_aux (x : LaurentSeries K) :
    ∃ B : Polynomial K, polyToLaurentInv B = laurentPolyPart x := by
  classical
  refine ⟨∑ i ∈ Finset.Icc x.order 0, Polynomial.monomial (-i).toNat (x.coeff i), ?_⟩
  unfold polyToLaurentInv
  rw [map_sum]
  have hterm (i : ℤ) (hi : i ∈ Finset.Icc x.order 0) :
      Polynomial.aeval (laurentInvVar K) (Polynomial.monomial (-i).toNat (x.coeff i)) =
        single i (x.coeff i) := by
    have hi' := (Finset.mem_Icc.mp hi).2
    rw [Polynomial.aeval_monomial, LaurentSeries.algebraMap_apply, C_apply]
    simp [laurentInvVar, single_pow, single_mul_single, Int.toNat_of_nonneg (show 0 ≤ -i by omega)]
  rw [Finset.sum_congr rfl hterm]
  ext j
  simp only [coeff_sum, coeff_single, laurentPolyPart_coeff]
  by_cases hj : j ≤ 0
  · rw [Finset.sum_eq_single j]
    · simp [hj]
    · intro i _ hij
      simp [Ne.symm hij]
    · intro hj'
      have hlt : j < x.order := by
        simp only [Finset.mem_Icc, hj, and_true, not_le] at hj'
        exact hj'
      simp [coeff_eq_zero_of_lt_order hlt]
  · rw [Finset.sum_eq_zero]
    · simp [hj]
    · intro i hi
      have hi' := (Finset.mem_Icc.mp hi).2
      simp [show j ≠ i by omega]

private theorem convNum_in_image (α : LaurentSeries K) (n : ℕ) :
    ∃ P : Polynomial K, polyToLaurentInv P = laurentConvNum α n := by
  have h2 : ∀ n : ℕ, (∃ P : Polynomial K, polyToLaurentInv P = laurentConvNum α n) ∧
      (∃ P : Polynomial K, polyToLaurentInv P = laurentConvNum α (n + 1)) := by
    intro n
    induction n with
    | zero =>
      constructor
      · exact ⟨1, by simp [polyToLaurentInv, laurentConvNum]⟩
      · obtain ⟨B, hB⟩ := exists_polyPart_aux (laurentCompleteQuotient α 0)
        exact ⟨B, by simpa [laurentConvNum, laurentPartialQuotient] using hB⟩
    | succ n ih =>
      obtain ⟨⟨P0, hP0⟩, ⟨P1, hP1⟩⟩ := ih
      constructor
      · exact ⟨P1, hP1⟩
      · obtain ⟨B, hB⟩ := exists_polyPart_aux (laurentCompleteQuotient α (n + 1))
        refine ⟨B * P1 + P0, ?_⟩
        unfold polyToLaurentInv at hB hP1 hP0 ⊢
        rw [map_add, map_mul, hB, hP1, hP0]
        simp [laurentConvNum, laurentPartialQuotient]
  exact (h2 n).1

private theorem convDen_in_image (α : LaurentSeries K) (n : ℕ) :
    ∃ Q : Polynomial K, polyToLaurentInv Q = laurentConvDen α n := by
  have h2 : ∀ n : ℕ, (∃ Q : Polynomial K, polyToLaurentInv Q = laurentConvDen α n) ∧
      (∃ Q : Polynomial K, polyToLaurentInv Q = laurentConvDen α (n + 1)) := by
    intro n
    induction n with
    | zero =>
      constructor
      · exact ⟨0, by simp [polyToLaurentInv, laurentConvDen]⟩
      · exact ⟨1, by simp [polyToLaurentInv, laurentConvDen]⟩
    | succ n ih =>
      obtain ⟨⟨Q0, hQ0⟩, ⟨Q1, hQ1⟩⟩ := ih
      constructor
      · exact ⟨Q1, hQ1⟩
      · obtain ⟨B, hB⟩ := exists_polyPart_aux (laurentCompleteQuotient α (n + 1))
        refine ⟨B * Q1 + Q0, ?_⟩
        unfold polyToLaurentInv at hB hQ1 hQ0 ⊢
        rw [map_add, map_mul, hB, hQ1, hQ0]
        simp [laurentConvDen, laurentPartialQuotient]
  exact (h2 n).1

private theorem convDen_succ_ne_zero (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (n : ℕ) : laurentConvDen α (n + 1) ≠ 0 := by
  have h3 := (laurentConvergent_properties α hα).2.2.1
  exact (h3 (n + 1) (by omega)).1

private theorem order_denom_step_aux (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (n : ℕ) : (laurentConvDen α (n + 2)).order =
      (laurentPartialQuotient α (n + 1)).order + (laurentConvDen α (n + 1)).order := by
  by_cases hn : n = 0
  · subst hn
    have hQ2 : laurentConvDen α 2 = laurentPartialQuotient α 1 := by
      simp [laurentConvDen]
    have hQ1 : laurentConvDen α 1 = 1 := by simp [laurentConvDen]
    rw [hQ2, hQ1, order_one, add_zero]
  · have hn1 : 1 ≤ n := by omega
    have h4 := (laurentConvergent_properties α hα).2.2.2.1
    have h_n := h4 n hn1
    have h_n1 := h4 (n + 1) (by omega)
    rw [h_n1]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), h_n]
    ring

private theorem order_approx_zero_aux (α : LaurentSeries K) (hα : LaurentIsIrrational α) :
    (α - laurentConvNum α 1 / laurentConvDen α 1).order =
      -(laurentPartialQuotient α 1).order - 2 * (laurentConvDen α 1).order := by
  have hQ1 : laurentConvDen α 1 = 1 := by simp [laurentConvDen]
  have hP1 : laurentConvNum α 1 = laurentPartialQuotient α 0 := by simp [laurentConvNum]
  have hb0 : laurentPartialQuotient α 0 = laurentPolyPart α := rfl
  rw [hQ1, hP1, hb0, div_one, order_one, mul_zero, sub_zero]
  obtain ⟨B, hB⟩ := exists_polyPart_aux α
  have hr : α - laurentPolyPart α ≠ 0 := by
    intro h
    have halpha : α = polyToLaurentInv B := by
      have h2 : α = laurentPolyPart α := sub_eq_zero.mp h
      rw [h2, ← hB]
    exact hα B 1 one_ne_zero (by
      simp only [polyToLaurentInv] at halpha ⊢
      rw [map_one, one_mul]
      exact halpha)
  have hpos : 0 < (α - laurentPolyPart α).order := by
    by_contra! h
    apply hr
    apply coeff_order_eq_zero.mp
    simp [coeff_sub, laurentPolyPart_coeff, h]
  have hy : (laurentCompleteQuotient α 1).order < 0 := by
    change ((α - laurentPolyPart α)⁻¹).order < 0
    rw [order_inv_aux _ hr]
    omega
  have hc : (laurentPolyPart (laurentCompleteQuotient α 1)).coeff
      (laurentCompleteQuotient α 1).order ≠ 0 := by
    simp only [laurentPolyPart_coeff, hy.le, ↓reduceIte]
    exact coeff_order_eq_zero.not.mpr (inv_ne_zero hr)
  have heq : (laurentPartialQuotient α 1).order = (laurentCompleteQuotient α 1).order := by
    apply le_antisymm
    · exact order_le_of_coeff_ne_zero hc
    · by_contra! h
      change (laurentPolyPart (laurentCompleteQuotient α 1)).order <
        (laurentCompleteQuotient α 1).order at h
      have hz := coeff_order_eq_zero.not.mpr (ne_zero_of_coeff_ne_zero hc)
      apply hz
      simp only [laurentPolyPart_coeff]
      rw [coeff_eq_zero_of_lt_order h]
      split_ifs <;> rfl
  have hinv : (laurentCompleteQuotient α 1).order = -((α - laurentPolyPart α).order) := by
    change ((α - laurentPolyPart α)⁻¹).order = _
    exact order_inv_aux _ hr
  omega

private theorem order_approx_all (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (n : ℕ) : (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order =
      -(laurentPartialQuotient α (n + 1)).order - 2 * (laurentConvDen α (n + 1)).order := by
  by_cases hn : n = 0
  · subst hn
    exact order_approx_zero_aux α hα
  · have hn1 : 1 ≤ n := by omega
    exact (laurentConvergent_properties α hα).2.2.2.2.1 n hn1

private theorem conv_coprime_aux (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (n : ℕ) (P' Q' : Polynomial K)
    (hP' : polyToLaurentInv P' = laurentConvNum α (n + 1))
    (hQ' : polyToLaurentInv Q' = laurentConvDen α (n + 1)) :
    IsCoprime P' Q' := by
  obtain ⟨P'', hP''⟩ := convNum_in_image α n
  obtain ⟨Q'', hQ''⟩ := convDen_in_image α n
  have hdet := (laurentConvergent_properties α hα).2.1 n
  rw [← hP', ← hQ', ← hP'', ← hQ''] at hdet
  have hpoly : P' * Q'' - P'' * Q' = (-1 : Polynomial K) ^ (n + 1) := by
    apply polyToLaurentInv_injective
    unfold polyToLaurentInv at hdet ⊢
    rw [map_sub, map_mul, map_mul, map_pow, map_neg, map_one]
    simpa using hdet
  set s : Polynomial K := (-1 : Polynomial K) ^ (n + 1) with hs
  have hs2 : s * s = 1 := by
    simp only [hs, ← mul_pow]
    simp
  have h1 : (P' * Q'' - P'' * Q') * s = 1 := by rw [hpoly, hs2]
  exact ⟨Q'' * s, -P'' * s, by linear_combination h1⟩

private theorem degQ_eq_aux (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (n : ℕ) (P Q P' Q' : Polynomial K)
    (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hP' : polyToLaurentInv P' = laurentConvNum α (n + 1))
    (hQ' : polyToLaurentInv Q' = laurentConvDen α (n + 1))
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1)) :
    Q.natDegree = Q'.natDegree := by
  have he : polyToLaurentInv P * polyToLaurentInv Q' =
      polyToLaurentInv Q * polyToLaurentInv P' := by
    rw [← hQ', ← hP'] at hconv
    exact hconv
  have hmul : P * Q' = Q * P' := by
    apply polyToLaurentInv_injective
    simp only [polyToLaurentInv, map_mul]
    exact he
  have hQ'ne : Q' ≠ 0 := by
    intro hz
    subst hz
    simp only [polyToLaurentInv, map_zero] at hQ'
    exact convDen_succ_ne_zero α hα n hQ'.symm
  have hP'Q' : IsCoprime P' Q' := conv_coprime_aux α hα n P' Q' hP' hQ'
  have hdvd1 : Q ∣ Q' := by
    have hdiv : Q ∣ P * Q' := by rw [hmul]; exact dvd_mul_right Q P'
    exact hPQ.symm.dvd_of_dvd_mul_left hdiv
  have hdvd2 : Q' ∣ Q := by
    have hdiv : Q' ∣ Q * P' := by rw [← hmul]; exact dvd_mul_left Q' P
    exact hP'Q'.symm.dvd_of_dvd_mul_right hdiv
  apply le_antisymm
  · exact Polynomial.natDegree_le_of_dvd hdvd1 hQ'ne
  · exact Polynomial.natDegree_le_of_dvd hdvd2 hQ

private theorem alpha_sub_frac_ne_zero (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (P Q : Polynomial K) (hQ : Q ≠ 0) : α - polyToLaurentInv P / polyToLaurentInv Q ≠ 0 := by
  intro hz
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have heq : α = polyToLaurentInv P / polyToLaurentInv Q := sub_eq_zero.mp hz
  have hmul : polyToLaurentInv Q * α = polyToLaurentInv P := by
    rw [heq, mul_div_cancel₀ _ hQe]
  exact hα P Q hQ hmul

private theorem order_alpha_sub_frac (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (n : ℕ) (P Q : Polynomial K) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1)) :
    (α - polyToLaurentInv P / polyToLaurentInv Q).order =
      -(laurentPartialQuotient α (n + 1)).order -
        2 * (laurentConvDen α (n + 1)).order := by
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have hQn : laurentConvDen α (n + 1) ≠ 0 := convDen_succ_ne_zero α hα n
  have hfrac : polyToLaurentInv P / polyToLaurentInv Q =
      laurentConvNum α (n + 1) / laurentConvDen α (n + 1) := by
    apply (div_eq_div_iff hQe hQn).mpr
    calc polyToLaurentInv P * laurentConvDen α (n + 1)
        = polyToLaurentInv Q * laurentConvNum α (n + 1) := hconv
      _ = laurentConvNum α (n + 1) * polyToLaurentInv Q := mul_comm _ _
  rw [hfrac]
  exact order_approx_all α hα n

private theorem S1_identity [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (hS₁ : -C * P + A * Q ≠ 0) :
    polyToLaurentInv (-C * P + A * Q) * α ^ Fintype.card K -
        polyToLaurentInv (D * P - B * Q) =
      polyToLaurentInv (A * D - B * C) * (polyToLaurentInv Q * α - polyToLaurentInv P) /
        (polyToLaurentInv A - polyToLaurentInv C * α) := by
  have hS₁e : polyToLaurentInv (-C * P + A * Q) ≠ 0 :=
    polyToLaurentInv_ne_zero _ hS₁
  have hinvDen := laurentMobius_invDen_ne_zero A B C D hΔ α hα hfix
  have hdiv := laurentMobius_pow_sub_identity A B C D hΔ α hα hfix P Q hS₁
  have hfac : polyToLaurentInv (-C * P + A * Q) * α ^ Fintype.card K -
      polyToLaurentInv (D * P - B * Q) =
      polyToLaurentInv (-C * P + A * Q) *
        (α ^ Fintype.card K -
          polyToLaurentInv (D * P - B * Q) / polyToLaurentInv (-C * P + A * Q)) := by
    rw [mul_sub, mul_div_cancel₀ _ hS₁e]
  rw [hfac, hdiv]
  field_simp

private theorem S2_identity [Fintype K] (A B C D : Polynomial K)
    (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K)
    (hS₂ : C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0) :
    polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) * α -
        polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K) =
      polyToLaurentInv (A * D - B * C) *
          (polyToLaurentInv Q * α - polyToLaurentInv P) ^ Fintype.card K /
        (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D) := by
  have hS₂e : polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) ≠ 0 :=
    polyToLaurentInv_ne_zero _ hS₂
  have hden := laurentMobius_den_ne_zero A B C D α hα hfix
  have hdiv := laurentMobius_sub_identity A B C D α hα hfix P Q hS₂
  have hfac : polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) * α -
      polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K) =
      polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) *
        (α - polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K) /
          polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K)) := by
    rw [mul_sub, mul_div_cancel₀ _ hS₂e]
  rw [hfac, hdiv]
  field_simp

private theorem S1_ne_zero_of_close (α : LaurentSeries K)
    (A C P Q : Polynomial K) (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hclose : (α - polyToLaurentInv A / polyToLaurentInv C).order <
      (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    -C * P + A * Q ≠ 0 := by
  intro hS1
  have hCe : polyToLaurentInv C ≠ 0 := polyToLaurentInv_ne_zero C hC
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have heS1 : polyToLaurentInv (-C * P + A * Q) = 0 := by
    rw [hS1]
    simp [polyToLaurentInv]
  simp only [polyToLaurentInv, map_add, map_mul, map_neg] at heS1
  have hACPQ : polyToLaurentInv A / polyToLaurentInv C =
      polyToLaurentInv P / polyToLaurentInv Q := by
    apply (div_eq_div_iff hCe hQe).mpr
    simp only [polyToLaurentInv] at hCe hQe ⊢
    linear_combination heS1
  have heq : (α - polyToLaurentInv A / polyToLaurentInv C) =
      (α - polyToLaurentInv P / polyToLaurentInv Q) := by rw [hACPQ]
  have hord_eq : (α - polyToLaurentInv A / polyToLaurentInv C).order =
      (α - polyToLaurentInv P / polyToLaurentInv Q).order := by rw [heq]
  exact (ne_of_lt hclose) hord_eq

private theorem S2_ne_zero_of_close [Fintype K] (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) (C D P Q : Polynomial K) (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hclose : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
      Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0 := by
  intro hS2
  have hCe : polyToLaurentInv C ≠ 0 := polyToLaurentInv_ne_zero C hC
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have hQq : (polyToLaurentInv Q) ^ Fintype.card K ≠ 0 := pow_ne_zero _ hQe
  have heS2 : polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) = 0 := by
    rw [hS2]
    simp [polyToLaurentInv]
  simp only [polyToLaurentInv, map_add, map_mul, map_pow] at heS2
  have hfrac_pow : (polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K =
      -polyToLaurentInv D / polyToLaurentInv C := by
    rw [div_pow]
    apply (div_eq_div_iff hQq hCe).mpr
    simp only [polyToLaurentInv] at hCe hQe hQq ⊢
    linear_combination heS2
  have hpow : (α - polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K =
      α ^ Fintype.card K - (polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K :=
    map_sub (FiniteField.frobeniusAlgHom K (LaurentSeries K)) _ _
  have heq : α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C =
      (α - polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K := by
    rw [hpow, hfrac_pow]
    ring
  have hαPQ : α - polyToLaurentInv P / polyToLaurentInv Q ≠ 0 :=
    alpha_sub_frac_ne_zero α hα P Q hQ
  have hord : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order =
      Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order := by
    rw [heq, HahnSeries.order_pow, nsmul_eq_mul]
  exact (ne_of_lt hclose) hord

private theorem alpha_pow_frac_ne_zero [Fintype K] (A B C D : Polynomial K)
    (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (hC : C ≠ 0) : α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C ≠ 0 := by
  have hCe : polyToLaurentInv C ≠ 0 := polyToLaurentInv_ne_zero C hC
  have hden := laurentMobius_den_ne_zero A B C D α hα hfix
  have heq : α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C =
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D) / polyToLaurentInv C := by
    field_simp
  rw [heq]
  exact div_ne_zero hden hCe

private theorem order_ACPQ_eq (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (A C P Q : Polynomial K) (hC : C ≠ 0)
    (hclose : (α - polyToLaurentInv A / polyToLaurentInv C).order <
      (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    (polyToLaurentInv A / polyToLaurentInv C - polyToLaurentInv P / polyToLaurentInv Q).order =
      (α - polyToLaurentInv A / polyToLaurentInv C).order := by
  have hAC : α - polyToLaurentInv A / polyToLaurentInv C ≠ 0 :=
    alpha_sub_frac_ne_zero α hα A C hC
  have hx : -(α - polyToLaurentInv A / polyToLaurentInv C) ≠ 0 := neg_ne_zero.mpr hAC
  have hord : (-(α - polyToLaurentInv A / polyToLaurentInv C)).order <
      (α - polyToLaurentInv P / polyToLaurentInv Q).order := by
    rw [order_neg]
    exact hclose
  have heq : polyToLaurentInv A / polyToLaurentInv C - polyToLaurentInv P / polyToLaurentInv Q =
      -(α - polyToLaurentInv A / polyToLaurentInv C) +
        (α - polyToLaurentInv P / polyToLaurentInv Q) := by ring
  rw [heq, order_add_eq_left_of_lt _ _ hx hord, order_neg]

private theorem order_alpha_AC_eq (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (A C P Q : Polynomial K) (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hS1 : -C * P + A * Q ≠ 0)
    (hclose : (α - polyToLaurentInv A / polyToLaurentInv C).order <
      (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    (α - polyToLaurentInv A / polyToLaurentInv C).order =
      -(((-C * P + A * Q).natDegree : ℤ)) + (Q.natDegree : ℤ) + (C.natDegree : ℤ) := by
  have hCe : polyToLaurentInv C ≠ 0 := polyToLaurentInv_ne_zero C hC
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have hS1e : polyToLaurentInv (-C * P + A * Q) ≠ 0 :=
    polyToLaurentInv_ne_zero _ hS1
  have heq : polyToLaurentInv (-C * P + A * Q) = polyToLaurentInv C * polyToLaurentInv Q *
      (polyToLaurentInv A / polyToLaurentInv C - polyToLaurentInv P / polyToLaurentInv Q) := by
    simp only [polyToLaurentInv, map_add, map_mul, map_neg] at hCe hQe ⊢
    field_simp
    ring
  have hACPQ_ne : polyToLaurentInv A / polyToLaurentInv C -
      polyToLaurentInv P / polyToLaurentInv Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at heq
    exact hS1e heq
  have hCQ : polyToLaurentInv C * polyToLaurentInv Q ≠ 0 := mul_ne_zero hCe hQe
  have h1 : (polyToLaurentInv C * polyToLaurentInv Q *
      (polyToLaurentInv A / polyToLaurentInv C - polyToLaurentInv P / polyToLaurentInv Q)).order =
      (polyToLaurentInv C * polyToLaurentInv Q).order +
        (polyToLaurentInv A / polyToLaurentInv C - polyToLaurentInv P / polyToLaurentInv Q).order :=
    order_mul hCQ hACPQ_ne
  have h2 : (polyToLaurentInv C * polyToLaurentInv Q).order =
      (polyToLaurentInv C).order + (polyToLaurentInv Q).order := order_mul hCe hQe
  have hACPQ_ord := order_ACPQ_eq α hα A C P Q hC hclose
  have hS1_ord := order_polyToLaurentInv (-C * P + A * Q)
  have hC_ord := order_polyToLaurentInv C
  have hQ_ord := order_polyToLaurentInv Q
  have h3 : (polyToLaurentInv (-C * P + A * Q)).order =
      (polyToLaurentInv C).order + (polyToLaurentInv Q).order +
        (α - polyToLaurentInv A / polyToLaurentInv C).order := by
    rw [heq, h1, h2, hACPQ_ord]
  rw [hS1_ord, hC_ord, hQ_ord] at h3
  omega

private theorem order_PQqDC_eq [Fintype K] (A B C D : Polynomial K)
    (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hclose : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
      Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    ((polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K +
      polyToLaurentInv D / polyToLaurentInv C).order =
      (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order := by
  have hpow : (α - polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K =
      α ^ Fintype.card K - (polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K :=
    map_sub (FiniteField.frobeniusAlgHom K (LaurentSeries K)) _ _
  have hx_ne := alpha_pow_frac_ne_zero A B C D α hα hfix hC
  have hαPQ := alpha_sub_frac_ne_zero α hα P Q hQ
  have hord_y : (-(α - polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K).order =
      Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order := by
    rw [order_neg, HahnSeries.order_pow, nsmul_eq_mul]
  have hlt : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
      (-(α - polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K).order := by
    rw [hord_y]
    exact hclose
  have heq : (polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K +
      polyToLaurentInv D / polyToLaurentInv C =
      (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C) +
        (-(α - polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K) := by
    rw [hpow]
    ring
  rw [heq, order_add_eq_left_of_lt _ _ hx_ne hlt]

private theorem order_alphaq_DC_eq [Fintype K] (A B C D : Polynomial K)
    (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (P Q : Polynomial K) (hC : C ≠ 0) (hQ : Q ≠ 0)
    (hS2 : C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0)
    (hclose : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
      Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order =
      -(((C * P ^ Fintype.card K + D * Q ^ Fintype.card K).natDegree : ℤ)) +
        (Fintype.card K : ℤ) * (Q.natDegree : ℤ) + (C.natDegree : ℤ) := by
  have hCe : polyToLaurentInv C ≠ 0 := polyToLaurentInv_ne_zero C hC
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have hQq : (polyToLaurentInv Q) ^ Fintype.card K ≠ 0 := pow_ne_zero _ hQe
  have hS2e : polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) ≠ 0 :=
    polyToLaurentInv_ne_zero _ hS2
  have heq : polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) =
      (polyToLaurentInv Q) ^ Fintype.card K * polyToLaurentInv C *
        ((polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K +
          polyToLaurentInv D / polyToLaurentInv C) := by
    simp only [polyToLaurentInv, map_add, map_mul, map_pow, div_pow] at hCe hQq ⊢
    field_simp
  have hfrac_ne : (polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K +
      polyToLaurentInv D / polyToLaurentInv C ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at heq
    exact hS2e heq
  have hCQq : (polyToLaurentInv Q) ^ Fintype.card K * polyToLaurentInv C ≠ 0 :=
    mul_ne_zero hQq hCe
  have h1 : ((polyToLaurentInv Q) ^ Fintype.card K * polyToLaurentInv C *
      ((polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K +
        polyToLaurentInv D / polyToLaurentInv C)).order =
      ((polyToLaurentInv Q) ^ Fintype.card K * polyToLaurentInv C).order +
        ((polyToLaurentInv P / polyToLaurentInv Q) ^ Fintype.card K +
          polyToLaurentInv D / polyToLaurentInv C).order :=
    order_mul hCQq hfrac_ne
  have h2 : ((polyToLaurentInv Q) ^ Fintype.card K * polyToLaurentInv C).order =
      ((polyToLaurentInv Q) ^ Fintype.card K).order + (polyToLaurentInv C).order :=
    order_mul hQq hCe
  have hQq_ord : ((polyToLaurentInv Q) ^ Fintype.card K).order =
      (Fintype.card K : ℤ) * (polyToLaurentInv Q).order := by
    rw [HahnSeries.order_pow, nsmul_eq_mul]
  have hfrac_ord := order_PQqDC_eq A B C D α hα hfix P Q hC hQ hclose
  have hS2_ord := order_polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K)
  have hC_ord := order_polyToLaurentInv C
  have hQ_ord := order_polyToLaurentInv Q
  have h3 : (polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K)).order =
      ((polyToLaurentInv Q) ^ Fintype.card K).order + (polyToLaurentInv C).order +
        (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order := by
    rw [heq, h1, h2, hfrac_ord]
  rw [hS2_ord, hC_ord, hQq_ord, hQ_ord] at h3
  have hq : (Fintype.card K : ℤ) * (-(Q.natDegree : ℤ)) =
      -((Fintype.card K : ℤ) * (Q.natDegree : ℤ)) := by ring
  rw [hq] at h3
  omega

private theorem mobius_order_first_aux [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1))
    (hclose : (α - polyToLaurentInv A / polyToLaurentInv C).order <
        (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    (polyToLaurentInv (-C * P + A * Q) * α ^ Fintype.card K -
          polyToLaurentInv (D * P - B * Q)).order =
        ((-C * P + A * Q).natDegree : ℤ) - (A * D - B * C).natDegree -
          (laurentPartialQuotient α (n + 1)).order := by
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have hCe : polyToLaurentInv C ≠ 0 := polyToLaurentInv_ne_zero C hC
  have hΔe : polyToLaurentInv (A * D - B * C) ≠ 0 :=
    polyToLaurentInv_ne_zero _ hΔ
  have hS1 : -C * P + A * Q ≠ 0 := S1_ne_zero_of_close α A C P Q hC hQ hclose
  have hQαP : polyToLaurentInv Q * α - polyToLaurentInv P ≠ 0 := by
    have h := hα P Q hQ
    exact sub_ne_zero.mpr h
  have hinvDen := laurentMobius_invDen_ne_zero A B C D hΔ α hα hfix
  have hS1_id := S1_identity A B C D hΔ α hα hfix P Q hS1
  have hαPQ_ne := alpha_sub_frac_ne_zero α hα P Q hQ
  have hαAC_ne := alpha_sub_frac_ne_zero α hα A C hC
  obtain ⟨P', hP'⟩ := convNum_in_image α (n + 1)
  obtain ⟨Q', hQ'⟩ := convDen_in_image α (n + 1)
  have hdegQ : Q.natDegree = Q'.natDegree :=
    degQ_eq_aux α hα n P Q P' Q' hPQ hQ hP' hQ' hconv
  have hQn_ord : (laurentConvDen α (n + 1)).order = -(Q.natDegree : ℤ) := by
    rw [← hQ', order_polyToLaurentInv, hdegQ]
  have hαPQ_ord := order_alpha_sub_frac α hα n P Q hQ hconv
  have hαAC_ord := order_alpha_AC_eq α hα A C P Q hC hQ hS1 hclose
  have hfac1 : polyToLaurentInv Q * α - polyToLaurentInv P =
      polyToLaurentInv Q * (α - polyToLaurentInv P / polyToLaurentInv Q) := by
    rw [mul_sub, mul_div_cancel₀ _ hQe]
  have hfac2 : polyToLaurentInv A - polyToLaurentInv C * α =
      -polyToLaurentInv C * (α - polyToLaurentInv A / polyToLaurentInv C) := by
    field_simp
    ring
  rw [hS1_id]
  have hnum_ne : polyToLaurentInv (A * D - B * C) *
      (polyToLaurentInv Q * α - polyToLaurentInv P) ≠ 0 :=
    mul_ne_zero hΔe hQαP
  rw [order_div_aux _ _ hnum_ne hinvDen,
    order_mul hΔe hQαP, hfac1, order_mul hQe hαPQ_ne, hfac2,
    order_mul (neg_ne_zero.mpr hCe) hαAC_ne, order_neg]
  rw [order_polyToLaurentInv, order_polyToLaurentInv, order_polyToLaurentInv,
    hαPQ_ord, hαAC_ord, hQn_ord]
  omega

private theorem mobius_order_second_aux [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1))
    (hclose : (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
        Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order) :
    (polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) * α -
            polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K)).order =
          ((C * P ^ Fintype.card K + D * Q ^ Fintype.card K).natDegree : ℤ) -
            (A * D - B * C).natDegree -
            Fintype.card K * (laurentPartialQuotient α (n + 1)).order := by
  have hQe : polyToLaurentInv Q ≠ 0 := polyToLaurentInv_ne_zero Q hQ
  have hCe : polyToLaurentInv C ≠ 0 := polyToLaurentInv_ne_zero C hC
  have hΔe : polyToLaurentInv (A * D - B * C) ≠ 0 :=
    polyToLaurentInv_ne_zero _ hΔ
  have hS2 : C * P ^ Fintype.card K + D * Q ^ Fintype.card K ≠ 0 :=
    S2_ne_zero_of_close α hα C D P Q hC hQ hclose
  have hQαP : polyToLaurentInv Q * α - polyToLaurentInv P ≠ 0 := by
    have h := hα P Q hQ
    exact sub_ne_zero.mpr h
  have hQαPq : (polyToLaurentInv Q * α - polyToLaurentInv P) ^ Fintype.card K ≠ 0 :=
    pow_ne_zero _ hQαP
  have hden := laurentMobius_den_ne_zero A B C D α hα hfix
  have hS2_id := S2_identity A B C D α hα hfix P Q hS2
  have hαPQ_ne := alpha_sub_frac_ne_zero α hα P Q hQ
  have hαqDC_ne := alpha_pow_frac_ne_zero A B C D α hα hfix hC
  obtain ⟨P', hP'⟩ := convNum_in_image α (n + 1)
  obtain ⟨Q', hQ'⟩ := convDen_in_image α (n + 1)
  have hdegQ : Q.natDegree = Q'.natDegree :=
    degQ_eq_aux α hα n P Q P' Q' hPQ hQ hP' hQ' hconv
  have hQn_ord : (laurentConvDen α (n + 1)).order = -(Q.natDegree : ℤ) := by
    rw [← hQ', order_polyToLaurentInv, hdegQ]
  have hαPQ_ord := order_alpha_sub_frac α hα n P Q hQ hconv
  have hαqDC_ord := order_alphaq_DC_eq A B C D α hα hfix P Q hC hQ hS2 hclose
  have hfac1 : polyToLaurentInv Q * α - polyToLaurentInv P =
      polyToLaurentInv Q * (α - polyToLaurentInv P / polyToLaurentInv Q) := by
    rw [mul_sub, mul_div_cancel₀ _ hQe]
  have hfac3 : polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D =
      polyToLaurentInv C * (α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C) := by
    rw [mul_add, mul_div_cancel₀ _ hCe]
  rw [hS2_id]
  have hnum_ne : polyToLaurentInv (A * D - B * C) *
      (polyToLaurentInv Q * α - polyToLaurentInv P) ^ Fintype.card K ≠ 0 :=
    mul_ne_zero hΔe hQαPq
  rw [order_div_aux _ _ hnum_ne hden, order_mul hΔe hQαPq,
    HahnSeries.order_pow, nsmul_eq_mul, hfac1, order_mul hQe hαPQ_ne, hfac3, order_mul hCe hαqDC_ne]
  rw [order_polyToLaurentInv, order_polyToLaurentInv, order_polyToLaurentInv,
    hαPQ_ord, hαqDC_ord, hQn_ord]
  ring

/-- **Degree identities at convergents of a Möbius–Frobenius fixed point.** Let $K$ be a finite
field with $q$ elements, let $A, B, C, D \in K[x]$ with $\Delta = AD - BC \ne 0$ and $C \ne 0$,
and let $\alpha \in K((x^{-1}))$ be irrational with $\alpha = (A \alpha^q + B) / (C \alpha^q + D)$.
Let $b_0, b_1, \dots$ be the partial quotients of $\alpha$ and $P_n / Q_n$ its convergents, where
$P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$, $Q_0 = 1$, $P_{n+1} = b_{n+1} P_n + P_{n-1}$ and
$Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. For a Laurent series $y = \sum_m c_m x^{-m}$ let $v(y)$ be its
order, the least $m$ with $c_m \ne 0$, and let $v(0) = 0$; thus $|y| = |x|^{-v(y)}$ for
$y \ne 0$. Let $n \ge 0$, let $P, Q \in K[x]$ be coprime with $Q \ne 0$ and $P Q_n = Q P_n$,
and put $R_1 = DP - BQ$, $S_1 = -CP + AQ$, $R_2 = AP^q + BQ^q$ and $S_2 = CP^q + DQ^q$, with
the degree of the zero polynomial taken to be $0$. Then:
(i) if $v(\alpha - A/C) < v(\alpha - P/Q)$, then
$v(S_1 \alpha^q - R_1) = \deg S_1 - \deg \Delta - v(b_{n+1})$;
(ii) if $v(\alpha^q + D/C) < q \, v(\alpha - P/Q)$, then
$v(S_2 \alpha - R_2) = \deg S_2 - \deg \Delta - q \, v(b_{n+1})$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 7, (3.7) and (3.8) (`integers-2026-A57-lem-7`). -/
public theorem laurentMobius_order_identities [Fintype K] (A B C D : Polynomial K)
    (hΔ : A * D - B * C ≠ 0) (hC : C ≠ 0) (α : LaurentSeries K) (hα : LaurentIsIrrational α)
    (hfix : α = (polyToLaurentInv A * α ^ Fintype.card K + polyToLaurentInv B) /
      (polyToLaurentInv C * α ^ Fintype.card K + polyToLaurentInv D))
    (n : ℕ) (P Q : Polynomial K) (hPQ : IsCoprime P Q) (hQ : Q ≠ 0)
    (hconv : polyToLaurentInv P * laurentConvDen α (n + 1) =
      polyToLaurentInv Q * laurentConvNum α (n + 1)) :
    ((α - polyToLaurentInv A / polyToLaurentInv C).order <
        (α - polyToLaurentInv P / polyToLaurentInv Q).order →
      (polyToLaurentInv (-C * P + A * Q) * α ^ Fintype.card K -
          polyToLaurentInv (D * P - B * Q)).order =
        ((-C * P + A * Q).natDegree : ℤ) - (A * D - B * C).natDegree -
          (laurentPartialQuotient α (n + 1)).order) ∧
      ((α ^ Fintype.card K + polyToLaurentInv D / polyToLaurentInv C).order <
          Fintype.card K * (α - polyToLaurentInv P / polyToLaurentInv Q).order →
        (polyToLaurentInv (C * P ^ Fintype.card K + D * Q ^ Fintype.card K) * α -
            polyToLaurentInv (A * P ^ Fintype.card K + B * Q ^ Fintype.card K)).order =
          ((C * P ^ Fintype.card K + D * Q ^ Fintype.card K).natDegree : ℤ) -
            (A * D - B * C).natDegree -
            Fintype.card K * (laurentPartialQuotient α (n + 1)).order)
    := by
  constructor
  · intro hclose
    exact mobius_order_first_aux A B C D hΔ hC α hα hfix n P Q hPQ hQ hconv hclose
  · intro hclose
    exact mobius_order_second_aux A B C D hΔ hC α hα hfix n P Q hPQ hQ hconv hclose

end LaurentContinuedFraction

end

end MetaMathlibExt
