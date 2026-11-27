/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LaurentSeriesBoundedPartialQuotients

/-!
# Convergents of Laurent series

We prove the finite-tail and determinant identities for convergents, and compute the orders of
their denominators and approximation errors for an irrational Laurent series.
-/

namespace MetaMathlibExt

noncomputable section

variable {K : Type*} [Field K]

namespace laurentConvergent_properties

open HahnSeries

private theorem exists_polyPart (x : LaurentSeries K) :
    ∃ B : Polynomial K, polyToLaurentInv B = laurentPolyPart x := by
  classical
  -- The exponents retained by the polynomial part lie between the order and zero.
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

private theorem completeQuotient_irrational {α : LaurentSeries K} (hα : LaurentIsIrrational α)
    (n : ℕ) : LaurentIsIrrational (laurentCompleteQuotient α n) := by
  induction n with
  | zero => exact hα
  | succ n ih =>
    let x := laurentCompleteQuotient α n
    let e : Polynomial K →ₐ[K] LaurentSeries K := Polynomial.aeval (laurentInvVar K)
    obtain ⟨B, hB⟩ := exists_polyPart x
    change e B = laurentPolyPart x at hB
    have hd : x - e B ≠ 0 := sub_ne_zero.mpr fun h =>
      not_laurentIsIrrational_polyToLaurentInv B (show LaurentIsIrrational (e B) from h ▸ ih)
    intro P Q hQ h
    change e Q * (x - laurentPolyPart x)⁻¹ = e P at h
    rw [← hB, mul_inv_eq_iff_eq_mul₀ hd] at h
    have hP : P ≠ 0 := by
      rintro rfl
      simp only [map_zero, zero_mul] at h
      exact ih 0 Q hQ (by change e Q * x = e 0; rw [h, zero_mul, map_zero])
    apply ih (Q + P * B) P hP
    change e P * x = e (Q + P * B)
    rw [map_add, map_mul, h]
    ring

private theorem order_inv (x : LaurentSeries K) (hx : x ≠ 0) : x⁻¹.order = -x.order := by
  have h := order_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, order_one] at h
  omega

private theorem quotient_orders {α : LaurentSeries K} (hα : LaurentIsIrrational α) (n : ℕ) :
    (laurentCompleteQuotient α (n + 1)).order < 0 ∧
      (laurentPartialQuotient α (n + 1)).order = (laurentCompleteQuotient α (n + 1)).order := by
  let x := laurentCompleteQuotient α n
  let r := x - laurentPolyPart x
  obtain ⟨B, hB⟩ := exists_polyPart x
  have hr : r ≠ 0 := sub_ne_zero.mpr fun h =>
    not_laurentIsIrrational_polyToLaurentInv B
      ((h.trans hB.symm) ▸ completeQuotient_irrational hα n)
  have hpos : 0 < r.order := by
    by_contra! h
    apply hr
    apply coeff_order_eq_zero.mp
    change (x - laurentPolyPart x).coeff r.order = 0
    simp [coeff_sub, laurentPolyPart_coeff, h]
  let y := laurentCompleteQuotient α (n + 1)
  have hy : y.order < 0 := by
    change r⁻¹.order < 0
    rw [order_inv r hr]
    omega
  have hc : (laurentPolyPart y).coeff y.order ≠ 0 := by
    simp only [laurentPolyPart_coeff, hy.le, ↓reduceIte]
    exact coeff_order_eq_zero.not.mpr (inv_ne_zero hr)
  refine ⟨hy, le_antisymm (order_le_of_coeff_ne_zero hc) ?_⟩
  by_contra! h
  change (laurentPolyPart y).order < y.order at h
  have hz := coeff_order_eq_zero.not.mpr (ne_zero_of_coeff_ne_zero hc)
  apply hz
  rw [laurentPolyPart_coeff, coeff_eq_zero_of_lt_order h, ite_self]

variable (α : LaurentSeries K)

local notation "P" => laurentConvNum α
local notation "Q" => laurentConvDen α
local notation "b" => laurentPartialQuotient α
local notation "A" => laurentCompleteQuotient α

private theorem finite_tail (n : ℕ) (β : LaurentSeries K) (hβ : β ≠ 0)
    (ht : ∀ k, 1 ≤ k → k ≤ n →
      ((List.range' k (n + 1 - k)).map b).foldr (fun a t => a + t⁻¹) β ≠ 0) :
    (β * P (n + 1) + P n) / (β * Q (n + 1) + Q n) =
      ((List.range (n + 1)).map b).foldr (fun a t => a + t⁻¹) β := by
  induction n generalizing β with
  | zero =>
    simp [laurentConvNum, laurentConvDen, List.range_succ, add_div, hβ]
  | succ n ih =>
    let γ := b (n + 1) + β⁻¹
    have hγ : γ ≠ 0 := by
      simpa [γ, List.range'_succ] using ht (n + 1) (by omega) le_rfl
    have hs (k : ℕ) (hk : k ≤ n) :
        List.range' k (n + 2 - k) = List.range' k (n + 1 - k) ++ [n + 1] := by
      rw [show n + 2 - k = (n + 1 - k) + 1 by omega, List.range'_concat]
      simp [show k + (n + 1 - k) = n + 1 by omega]
    have ht' (k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n) := ht k hk (by omega)
    rw [List.range_succ, List.map_append, List.foldr_append]
    change _ = ((List.range (n + 1)).map b).foldr (fun a t => a + t⁻¹) γ
    rw [← ih γ hγ (fun k hk hkn => by simpa [hs k hkn, γ] using ht' k hk hkn)]
    conv_rhs => rw [← mul_div_mul_left _ _ hβ]
    congr 1 <;>
      simp only [laurentConvNum, laurentConvDen, γ, mul_add, add_mul, ← mul_assoc,
        mul_inv_cancel₀ hβ, one_mul] <;> ring

private theorem determinant (n : ℕ) :
    P (n + 1) * Q n - P n * Q (n + 1) = (-1) ^ (n + 1) := by
  induction n with
  | zero => simp [laurentConvNum, laurentConvDen]
  | succ n ih =>
    rw [pow_succ, ← ih]
    simp only [laurentConvNum, laurentConvDen]
    ring

private theorem denominator_step (hα : LaurentIsIrrational α) (n : ℕ) :
    Q (n + 1) ≠ 0 ∧ Q (n + 2) ≠ 0 ∧ (Q (n + 2)).order < (Q (n + 1)).order ∧
      (Q (n + 2)).order = (b (n + 1)).order + (Q (n + 1)).order := by
  have hneg (i : ℕ) : (b (i + 1)).order < 0 := by
    obtain ⟨h, he⟩ := quotient_orders hα i
    exact he.trans_lt h
  have hbn (i : ℕ) : b (i + 1) ≠ 0 := by
    intro hz
    simpa [hz] using hneg i
  induction n with
  | zero => simp [laurentConvDen, hbn, hneg]
  | succ n ih =>
    obtain ⟨hprev, hq, hlt, _⟩ := ih
    have hb := hneg (n + 1)
    have hb' := hbn (n + 1)
    have hmul := order_mul hb' hq
    have hlt' : (b (n + 2) * Q (n + 2)).orderTop < (Q (n + 1)).orderTop := by
      rw [← order_eq_orderTop_of_ne_zero (mul_ne_zero hb' hq),
        ← order_eq_orderTop_of_ne_zero hprev, WithTop.coe_lt_coe, hmul]
      omega
    have hadd := orderTop_add_eq_left hlt'
    have hnz : Q (n + 3) ≠ 0 := orderTop_ne_top.mp (hadd.trans_ne hlt'.ne_top)
    change (Q (n + 3)).orderTop = _ at hadd
    rw [← order_eq_orderTop_of_ne_zero hnz,
      ← order_eq_orderTop_of_ne_zero (mul_ne_zero hb' hq), WithTop.coe_eq_coe] at hadd
    rw [hmul] at hadd
    exact ⟨hq, hnz, hadd.trans_lt (by simpa using hb), hadd⟩

private def residual (n : ℕ) : LaurentSeries K := Q n * α - P n

local notation "E" => residual α

private theorem residual_step (hα : LaurentIsIrrational α) (n : ℕ) :
    E (n + 1) = -E n * (A (n + 1))⁻¹ := by
  have hinv (i : ℕ) : (A (i + 1))⁻¹ = A i - b i := by
    simp [laurentCompleteQuotient, laurentPartialQuotient]
  induction n with
  | zero =>
    simp [residual, laurentConvNum, laurentConvDen, laurentCompleteQuotient, laurentPartialQuotient]
  | succ n ih =>
    have ha : A (n + 1) ≠ 0 := by
      intro hz
      simpa [hz] using (quotient_orders hα n).1
    have hprev : E n = -E (n + 1) * A (n + 1) := by
      rw [ih]
      simp [ha]
    rw [hinv]
    calc
      E (n + 2) = b (n + 1) * E (n + 1) + E n := by
        simp only [residual, laurentConvDen, laurentConvNum]
        ring
      _ = _ := by rw [hprev]; ring

private theorem residual_order (hα : LaurentIsIrrational α) (n : ℕ) :
    E n ≠ 0 ∧ (E n).order = -(Q (n + 1)).order := by
  induction n with
  | zero => simp [residual, laurentConvNum, laurentConvDen]
  | succ n ih =>
    obtain ⟨hneg, heq⟩ := quotient_orders hα n
    have ha : A (n + 1) ≠ 0 := by
      intro hz
      simp [hz] at hneg
    rw [residual_step α hα n]
    refine ⟨mul_ne_zero (neg_ne_zero.mpr ih.1) (inv_ne_zero ha), ?_⟩
    rw [order_mul (neg_ne_zero.mpr ih.1) (inv_ne_zero ha), order_neg, order_inv _ ha,
      ih.2, (denominator_step α hα n).2.2.2, heq]
    omega

end laurentConvergent_properties

open laurentConvergent_properties HahnSeries in
/-- **Basic properties of the convergents of a Laurent series.** Let $K$ be a field and let
$\alpha \in K((x^{-1}))$ be irrational, with partial quotients $b_0, b_1, \dots$ and convergents
$P_n / Q_n$, where $P_{-1} = 1$, $Q_{-1} = 0$, $P_0 = b_0$, $Q_0 = 1$,
$P_{n+1} = b_{n+1} P_n + P_{n-1}$ and $Q_{n+1} = b_{n+1} Q_n + Q_{n-1}$. For a Laurent series
$y = \sum_m c_m x^{-m}$ let $v(y)$ be its order, the least $m$ with $c_m \ne 0$, and let
$v(0) = 0$; thus $|y| = |x|^{-v(y)}$ for $y \ne 0$. For $\beta \in K((x^{-1}))$ write
$[b_k, \dots, b_n, \beta] = b_k + 1/(b_{k+1} + 1/(\cdots + 1/(b_n + 1/\beta)))$. Then:
(i) for every $n \ge 0$ and every $\beta \ne 0$ such that $[b_k, \dots, b_n, \beta] \ne 0$ for
all $1 \le k \le n$, $(\beta P_n + P_{n-1}) / (\beta Q_n + Q_{n-1}) = [b_0, \dots, b_n, \beta]$;
(ii) $P_n Q_{n-1} - P_{n-1} Q_n = (-1)^{n+1}$ for every $n \ge 0$;
(iii) $Q_{n-1} \ne 0$ and $v(Q_n) < v(Q_{n-1})$ for every $n \ge 1$;
(iv) $v(Q_n) = v(b_1) + \dots + v(b_n)$ for every $n \ge 1$;
(v) $v(\alpha - P_n / Q_n) = -v(b_{n+1}) - 2 v(Q_n)$ for every $n \ge 1$;
(vi) $v(Q_n \alpha - P_n) < v(Q_{n+1} \alpha - P_{n+1})$ for every $n \ge 1$.

Part (iii) fails at $n = 0$ because $Q_{-1} = 0$.

Source: Tuangrat Chaichana, Natthaphong Chitmung, and Vichian Laohakosol, *Certain Algebraic
Formal Laurent Series with Bounded Partial Quotients*, INTEGERS 26 (2026), Article A57,
Lemma 1 (`integers-2026-A57-lem-1`). -/
public theorem laurentConvergent_properties (α : LaurentSeries K)
    (hα : LaurentIsIrrational α) :
    (∀ n : ℕ, ∀ β : LaurentSeries K, β ≠ 0 →
        (∀ k, 1 ≤ k → k ≤ n → ((List.range' k (n + 1 - k)).map (laurentPartialQuotient α)).foldr
          (fun b t => b + t⁻¹) β ≠ 0) →
        (β * laurentConvNum α (n + 1) + laurentConvNum α n) /
            (β * laurentConvDen α (n + 1) + laurentConvDen α n) =
          ((List.range (n + 1)).map (laurentPartialQuotient α)).foldr (fun b t => b + t⁻¹) β) ∧
      (∀ n : ℕ, laurentConvNum α (n + 1) * laurentConvDen α n -
          laurentConvNum α n * laurentConvDen α (n + 1) = (-1) ^ (n + 1)) ∧
      (∀ n : ℕ, 1 ≤ n → laurentConvDen α n ≠ 0 ∧
          (laurentConvDen α (n + 1)).order < (laurentConvDen α n).order) ∧
      (∀ n : ℕ, 1 ≤ n → (laurentConvDen α (n + 1)).order =
          ∑ i ∈ Finset.Icc 1 n, (laurentPartialQuotient α i).order) ∧
      (∀ n : ℕ, 1 ≤ n → (α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1)).order =
          -(laurentPartialQuotient α (n + 1)).order - 2 * (laurentConvDen α (n + 1)).order) ∧
      (∀ n : ℕ, 1 ≤ n → (laurentConvDen α (n + 1) * α - laurentConvNum α (n + 1)).order <
          (laurentConvDen α (n + 2) * α - laurentConvNum α (n + 2)).order) := by
  have hs (n : ℕ) : (laurentConvDen α (n + 1)).order =
      ∑ i ∈ Finset.Icc 1 n, (laurentPartialQuotient α i).order := by
    induction n with
    | zero => simp [laurentConvDen]
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), (denominator_step α hα n).2.2.2, ih, add_comm]
  refine ⟨finite_tail α, determinant α, ?_, fun n _ => hs n, ?_, ?_⟩
  · rintro (_ | n) hn
    · omega
    · obtain ⟨hq, _, hlt, _⟩ := denominator_step α hα n
      exact ⟨hq, hlt⟩
  · intro n _
    obtain ⟨he, ho⟩ := residual_order α hα (n + 1)
    obtain ⟨hq, _, _, hd⟩ := denominator_step α hα n
    have h : α - laurentConvNum α (n + 1) / laurentConvDen α (n + 1) =
        residual α (n + 1) * (laurentConvDen α (n + 1))⁻¹ := by
      rw [laurentConvergent_properties.residual, sub_mul, mul_comm _ α, mul_assoc,
        mul_inv_cancel₀ hq, mul_one, div_eq_mul_inv]
    rw [h, order_mul he (inv_ne_zero hq), ho, order_inv _ hq, hd]
    omega
  · intro n _
    change (residual α (n + 1)).order < (residual α (n + 2)).order
    rw [(residual_order α hα (n + 1)).2, (residual_order α hα (n + 2)).2, neg_lt_neg_iff]
    exact (denominator_step α hα (n + 1)).2.2.1

end

end MetaMathlibExt
