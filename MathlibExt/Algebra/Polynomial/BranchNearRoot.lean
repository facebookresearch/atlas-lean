/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Polynomial_exists_branch_near_root.lean`
and
`P2M/Sol/S_Polynomial_exists_branch_near_root.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Analysis.Complex.Basic

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section


set_option autoImplicit false

open Polynomial Finset

namespace M4cP1D1

private noncomputable def bnd (p : ℂ[X]) (d : ℕ) : ℝ := ∑ i ∈ range (d + 1), ‖p.coeff i‖

private theorem bnd_nonneg (p : ℂ[X]) (d : ℕ) : 0 ≤ bnd p d := sum_nonneg fun _ _ => norm_nonneg _

private theorem norm_eval_le_bnd (p : ℂ[X]) {d : ℕ} (hp : p.natDegree ≤ d) {t : ℂ} (ht : 1 ≤ ‖t‖) :
    ‖p.eval t‖ ≤ bnd p d * ‖t‖ ^ d := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hp), bnd, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht (Nat.lt_succ_iff.mp (mem_range.mp hi)))
    (norm_nonneg _)

private theorem norm_eval_ge (q : ℂ[X]) {w : ℕ} (hq : q.natDegree ≤ w) {t : ℂ} (ht : 1 ≤ ‖t‖) :
    ‖q.coeff w‖ * ‖t‖ ^ w - bnd (q - C (q.coeff w) * X ^ w) (w - 1) * ‖t‖ ^ (w - 1) ≤ ‖q.eval t‖ :=
      by
  set q' := q - C (q.coeff w) * X ^ w with hq'
  have hq'deg : q'.natDegree ≤ w - 1 := by
    rcases Nat.eq_zero_or_pos w with hw | hw
    · subst hw
      have : q' = 0 := by
        rw [hq', eq_C_of_natDegree_le_zero hq, coeff_C_zero, pow_zero, mul_one, sub_self]
      rw [this, natDegree_zero]
    · rw [Nat.le_sub_one_iff_lt hw]
      refine lt_of_le_of_lt (natDegree_le_iff_coeff_eq_zero.mpr fun i hi => ?_) (Nat.sub_one_lt
        hw.ne')
      have hi' : w - 1 < i := by exact_mod_cast hi
      rw [hq', coeff_sub, coeff_C_mul, coeff_X_pow]
      have hwi : w ≤ i := by lia
      rcases hwi.lt_or_eq with hlt | heq
      · rw [ite_eq_right hlt.ne', mul_zero, sub_zero]
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hq hlt)
      · subst heq; simp
  have hdecomp : q.eval t = q.coeff w * t ^ w + q'.eval t := by
    rw [hq', eval_sub, eval_mul, eval_C, eval_pow, eval_X]; ring
  have h1 := norm_eval_le_bnd q' hq'deg ht
  rw [hdecomp]
  have h2 : ‖q.coeff w * t ^ w‖ - ‖q'.eval t‖ ≤ ‖q.coeff w * t ^ w + q'.eval t‖ := by
    have := norm_sub_norm_le (q.coeff w * t ^ w) (-q'.eval t)
    rwa [norm_neg, sub_neg_eq_add] at this
  rw [norm_mul, norm_pow] at h2
  linarith

private theorem eval_map_eval (H : ℂ[X][X]) (t x : ℂ) :
    (H.map (evalRingHom t)).eval x = ∑ k ∈ range (H.natDegree + 1), (H.coeff k).eval t * x ^ k := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le natDegree_map_le)]
  simp only [coeff_map, coe_evalRingHom]

private theorem eval_map_factorization (F : ℂ[X][X]) (c : ℂ) {n : ℕ} (P : Fin n → ℂ[X]) (t x : ℂ) :
    (F.map (evalRingHom t)).eval x = c * ∏ i, (x - (P i).eval t) +
      ((F - C (C c) * ∏ i, (X - C (P i))).map (evalRingHom t)).eval x := by
  have : F = C (C c) * ∏ i, (X - C (P i)) + (F - C (C c) * ∏ i, (X - C (P i))) := by ring
  conv_lhs => rw [this]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_prod, Polynomial.map_sub, map_C,
    map_X, coe_evalRingHom, eval_C, eval_add, eval_mul, eval_prod, eval_sub, eval_X]

private theorem root_bound {n : ℕ} (hn : 0 < n) {c : ℂ} (hc : c ≠ 0) (f : ℕ → ℂ) (hf : f n = c) {M
  : ℝ}
    (hM : 0 ≤ M) (hfk : ∀ k, k < n → ‖f k‖ ≤ ‖c‖ * M ^ (n - k)) {x : ℂ}
    (hx : ∑ k ∈ range (n + 1), f k * x ^ k = 0) : ‖x‖ ≤ 2 * n * M := by
  by_contra hxM
  push Not at hxM
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (by positivity) hxM
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hMx : M ≤ ‖x‖ := by nlinarith
  rw [sum_range_succ, hf] at hx
  have heq : ‖c‖ * ‖x‖ ^ n = ‖∑ k ∈ range n, f k * x ^ k‖ := by
    rw [← norm_pow, ← norm_mul, ← norm_neg, show -(c * x ^ n) = ∑ k ∈ range n, f k * x ^ k by
      rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, hx]]
  have hterm : ∀ k ∈ range n, ‖f k * x ^ k‖ ≤ ‖c‖ * (M * ‖x‖ ^ (n - 1)) := by
    intro k hk
    have hkn := mem_range.mp hk
    rw [norm_mul, norm_pow]
    obtain ⟨m, hm, hmk⟩ : ∃ m, n - k = m + 1 ∧ m + k = n - 1 := ⟨n - k - 1, by lia, by lia⟩
    calc ‖f k‖ * ‖x‖ ^ k ≤ ‖c‖ * M ^ (n - k) * ‖x‖ ^ k :=
          mul_le_mul_of_nonneg_right (hfk k hkn) (by positivity)
      _ = ‖c‖ * (M * (M ^ m * ‖x‖ ^ k)) := by
          rw [hm, pow_succ]; ring
      _ ≤ ‖c‖ * (M * (‖x‖ ^ m * ‖x‖ ^ k)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hM hMx _) (by positivity)) hM) hcpos.le
      _ = ‖c‖ * (M * ‖x‖ ^ (n - 1)) := by
          rw [← pow_add, hmk]
  have hsum : ‖∑ k ∈ range n, f k * x ^ k‖ ≤ n * (‖c‖ * (M * ‖x‖ ^ (n - 1))) := by
    refine (norm_sum_le _ _).trans ?_
    have := sum_le_sum hterm
    rwa [sum_const, card_range, nsmul_eq_mul] at this
  have hlt : n * (‖c‖ * (M * ‖x‖ ^ (n - 1))) < ‖c‖ * ‖x‖ ^ n := by
    have : ‖x‖ ^ n = ‖x‖ * ‖x‖ ^ (n - 1) := by
      rw [← pow_succ', show n - 1 + 1 = n by lia]
    rw [this]
    have h1 : 0 < ‖x‖ ^ (n - 1) := by positivity
    have h2 : (n : ℝ) * M < ‖x‖ := by nlinarith
    calc (n : ℝ) * (‖c‖ * (M * ‖x‖ ^ (n - 1))) = ‖c‖ * ‖x‖ ^ (n - 1) * (n * M) := by ring
      _ < ‖c‖ * ‖x‖ ^ (n - 1) * ‖x‖ := mul_lt_mul_of_pos_left h2 (by positivity)
      _ = ‖c‖ * (‖x‖ * ‖x‖ ^ (n - 1)) := by ring
  linarith

private theorem exists_branch_near_root {n w : ℕ} (F : ℂ[X][X]) (hF : F.natDegree ≤ n)
    (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : ℂ) (hc : c ≠ 0)
    (hlead : F.coeff n = C c) (P : Fin n → ℂ[X]) (hP : ∀ i, (P i).natDegree ≤ w)
    (hPinj : Function.Injective fun i => (P i).coeff w)
    (hR : ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i,
      (X - C (P i))).coeff k).coeff j = 0) :
    ∃ C₀ T : ℝ, 0 < C₀ ∧ ∀ t : ℂ, T ≤ ‖t‖ → ∀ x : ℂ, (F.map (Polynomial.evalRingHom t)).IsRoot x →
      ∃ i, ‖x - (P i).eval t‖ ≤ C₀ / ‖t‖ := by
  classical
  set R := F - C (C c) * ∏ i, (X - C (P i)) with hRdef

  by_cases hR0 : R = 0
  · refine ⟨1, 1, one_pos, fun t ht x hx => ?_⟩
    have h := eval_map_factorization F c P t x
    rw [← hRdef, hR0, Polynomial.map_zero, eval_zero, add_zero, hx.eq_zero] at h
    obtain ⟨i, _, hi⟩ := prod_eq_zero_iff.mp ((mul_eq_zero.mp h.symm).resolve_left hc)
    exact ⟨i, by rw [sub_eq_zero.mp hi, sub_self, norm_zero]; positivity⟩

  obtain ⟨k₁, j₁, hne₁⟩ : ∃ k j, (R.coeff k).coeff j ≠ 0 := by
    by_contra h; push Not at h
    exact hR0 (Polynomial.ext fun k => Polynomial.ext fun j => by rw [h k j]; simp)
  have hslot₁ : j₁ + w < w * (n - k₁) := not_le.mp fun h => hne₁ (hR k₁ j₁ h)
  have hn2 : 2 ≤ n := by
    by_contra h; push Not at h
    have : n - k₁ ≤ 1 := by lia
    have := Nat.mul_le_mul_left w this; lia
  have hw1 : 1 ≤ w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp at hslot₁
    · exact h
  have hn : 0 < n := by lia
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc

  have hRcoeff : ∀ k, n - 1 ≤ k → R.coeff k = 0 := fun k hk =>
    Polynomial.ext fun j => by
      rw [coeff_zero]; exact hR k j (by have : n - k ≤ 1 := by lia
                                        have := Nat.mul_le_mul_left w this; lia)
  have hRnat : R.natDegree < n := by
    have : R.natDegree ≤ n - 1 := natDegree_le_iff_coeff_eq_zero.mpr fun k hk => hRcoeff k hk.le
    lia
  have hRdeg : ∀ k, k + 2 ≤ n → (R.coeff k).natDegree ≤ w * (n - k) - w - 1 := by
    intro k hk
    refine natDegree_le_iff_coeff_eq_zero.mpr fun j hj => hR k j ?_
    have hj' : w * (n - k) - w - 1 < j := by exact_mod_cast hj
    lia

  set L : ℝ := 1 + ∑ k ∈ range n, bnd (F.coeff k) (w * (n - k)) / ‖c‖ with hL
  have hL1 : 1 ≤ L := by
    rw [hL]; refine le_add_of_nonneg_right (sum_nonneg fun k _ => div_nonneg (bnd_nonneg _ _)
      hcpos.le)
  have hLk : ∀ k, k < n → bnd (F.coeff k) (w * (n - k)) ≤ ‖c‖ * L := by
    intro k hk
    have : bnd (F.coeff k) (w * (n - k)) / ‖c‖ ≤ ∑ k ∈ range n,
      bnd (F.coeff k) (w * (n - k)) / ‖c‖ :=
      single_le_sum (f := fun k => bnd (F.coeff k) (w * (n - k)) / ‖c‖)
        (fun k _ => div_nonneg (bnd_nonneg _ _) hcpos.le) (mem_range.mpr hk)
    rw [div_le_iff₀ hcpos] at this
    nlinarith [bnd_nonneg (F.coeff k) (w * (n - k))]

  set pairs := (univ : Finset (Fin n × Fin n)).filter fun p => p.1 ≠ p.2 with hpairs
  have hpairs_ne : pairs.Nonempty :=
    ⟨(⟨0, hn⟩, ⟨1, hn2⟩), by simp [hpairs, Fin.ext_iff]⟩
  set dif : Fin n × Fin n → ℂ[X] := fun p => P p.1 - P p.2 with hdif
  set κ : ℝ := pairs.inf' hpairs_ne fun p => ‖(dif p).coeff w‖ / 2 with hκ
  set T₁ : ℝ := pairs.sup' hpairs_ne fun p =>
    2 * bnd (dif p - C ((dif p).coeff w) * X ^ w) (w - 1) / ‖(dif p).coeff w‖ with hT₁
  have hdw : ∀ p ∈ pairs, (dif p).coeff w ≠ 0 := by
    intro p hp
    have hp' : p.1 ≠ p.2 := (mem_filter.mp hp).2
    rw [hdif]; dsimp only; rw [coeff_sub, sub_ne_zero]
    exact fun h => hp' (hPinj h)
  have hκpos : 0 < κ := by
    rw [hκ, Finset.lt_inf'_iff]
    intro p hp
    exact div_pos (norm_pos_iff.mpr (hdw p hp)) two_pos

  have hsep : ∀ t : ℂ, 1 ≤ ‖t‖ → T₁ ≤ ‖t‖ → ∀ i j, i ≠ j →
      κ * ‖t‖ ^ w ≤ ‖(P i).eval t - (P j).eval t‖ := by
    intro t ht1 htT i j hij
    have hp : (i, j) ∈ pairs := by simp [hpairs, hij]
    have hdeg : (dif (i, j)).natDegree ≤ w := (natDegree_sub_le _ _).trans (max_le (hP i) (hP j))
    have hlow := norm_eval_ge (dif (i, j)) hdeg ht1
    rw [show (dif (i, j)).eval t = (P i).eval t - (P j).eval t by simp [hdif]] at hlow
    set a := ‖(dif (i, j)).coeff w‖ with ha
    set Bq := bnd (dif (i, j) - C ((dif (i, j)).coeff w) * X ^ w) (w - 1) with hBq
    have hapos : 0 < a := norm_pos_iff.mpr (hdw _ hp)
    have hκle : κ ≤ a / 2 := Finset.inf'_le _ hp
    have hTle : 2 * Bq / a ≤ ‖t‖ := le_trans (Finset.le_sup' (f := fun p =>
      2 * bnd (dif p - C ((dif p).coeff w) * X ^ w) (w - 1) / ‖(dif p).coeff w‖) hp) htT
    have hBq0 : 0 ≤ Bq := bnd_nonneg _ _

    have hpow : ‖t‖ ^ w = ‖t‖ * ‖t‖ ^ (w - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel hw1]
    have h1 : Bq * ‖t‖ ^ (w - 1) ≤ a / 2 * ‖t‖ ^ w := by
      rw [hpow]
      have h2 : Bq ≤ a / 2 * ‖t‖ := by
        rw [div_le_iff₀ hapos] at hTle; linarith
      have h3 : 0 ≤ ‖t‖ ^ (w - 1) := by positivity
      nlinarith
    have h4 : κ * ‖t‖ ^ w ≤ a / 2 * ‖t‖ ^ w := mul_le_mul_of_nonneg_right hκle (by positivity)
    linarith

  set Λ : ℝ := 2 * n * L with hΛ
  have hΛ0 : 0 ≤ Λ := by positivity
  set C₂ : ℝ := ∑ k ∈ range n, bnd (R.coeff k) (w * (n - k) - w - 1) * Λ ^ k with hC₂
  have hC₂0 : 0 ≤ C₂ := sum_nonneg fun k _ => mul_nonneg (bnd_nonneg _ _) (by positivity)

  set C₀ : ℝ := C₂ / (‖c‖ * (κ / 2) ^ (n - 1)) + 1 with hC₀
  have hden : 0 < ‖c‖ * (κ / 2) ^ (n - 1) := by positivity
  have hC₀pos : 0 < C₀ := by rw [hC₀]; positivity
  refine ⟨C₀, max 1 T₁, hC₀pos, fun t ht x hx => ?_⟩
  have ht1 : 1 ≤ ‖t‖ := le_trans (le_max_left _ _) ht
  have htT : T₁ ≤ ‖t‖ := le_trans (le_max_right _ _) ht
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le one_pos ht1

  have hdegF : ∀ k, (F.coeff k).natDegree ≤ w * (n - k) := fun k =>
    natDegree_le_iff_coeff_eq_zero.mpr fun j hj => hwt k j (by exact_mod_cast hj)

  have hxroot : ∑ k ∈ range (n + 1), (F.coeff k).eval t * x ^ k = 0 := by
    have h : (F.map (evalRingHom t)).eval x = 0 := hx
    rw [eval_map_eval] at h
    rw [← h]
    symm
    refine sum_subset (range_subset_range.mpr (by lia)) fun k _ hk' => ?_
    rw [coeff_eq_zero_of_natDegree_lt (by simp at hk'; lia), eval_zero, zero_mul]
  have hxbd : ‖x‖ ≤ Λ * ‖t‖ ^ w := by
    have key := root_bound hn hc (fun k => (F.coeff k).eval t) (by simp [hlead])
      (M := L * ‖t‖ ^ w) (by positivity) ?_ hxroot
    · simpa [hΛ, mul_assoc] using key
    · intro k hk
      calc ‖(F.coeff k).eval t‖ ≤ bnd (F.coeff k) (w * (n - k)) * ‖t‖ ^ (w * (n - k)) :=
            norm_eval_le_bnd _ (hdegF k) ht1
        _ ≤ ‖c‖ * L * ‖t‖ ^ (w * (n - k)) :=
            mul_le_mul_of_nonneg_right (hLk k hk) (by positivity)
        _ ≤ ‖c‖ * L ^ (n - k) * ‖t‖ ^ (w * (n - k)) := by
            gcongr
            exact le_self_pow₀ hL1 (by lia)
        _ = ‖c‖ * (L * ‖t‖ ^ w) ^ (n - k) := by
            rw [mul_pow, ← pow_mul, mul_comm w (n - k)]; ring

  have hRx : ‖(R.map (evalRingHom t)).eval x‖ ≤ C₂ * ‖t‖ ^ (n * w - w - 1) := by
    rw [eval_map_eval]
    have hext : ∑ k ∈ range (R.natDegree + 1), (R.coeff k).eval t * x ^ k =
        ∑ k ∈ range n, (R.coeff k).eval t * x ^ k := by
      refine sum_subset (range_subset_range.mpr (by lia)) fun k _ hk' => ?_
      rw [coeff_eq_zero_of_natDegree_lt (by simp at hk'; lia), eval_zero, zero_mul]
    rw [hext, hC₂, sum_mul]
    refine (norm_sum_le _ _).trans (sum_le_sum fun k hk => ?_)
    have hkn := mem_range.mp hk
    rcases Nat.lt_or_ge k (n - 1) with hk2 | hk2
    · rw [norm_mul, norm_pow]
      have hwk : w * k + 2 * w ≤ w * n := by
        have := Nat.mul_le_mul_left w (show k + 2 ≤ n by lia); rw [Nat.mul_add] at this; lia
      have hexp : w * (n - k) - w - 1 + w * k = n * w - w - 1 := by
        rw [Nat.mul_sub, mul_comm n w]; lia
      calc ‖(R.coeff k).eval t‖ * ‖x‖ ^ k
          ≤ (bnd (R.coeff k) (w * (n - k) - w - 1) * ‖t‖ ^ (w * (n - k) - w - 1)) *
              (Λ * ‖t‖ ^ w) ^ k :=
            mul_le_mul (norm_eval_le_bnd _ (hRdeg k (by lia)) ht1)
              (pow_le_pow_left₀ (norm_nonneg _) hxbd k) (by positivity)
              (mul_nonneg (bnd_nonneg _ _) (by positivity))
        _ = bnd (R.coeff k) (w * (n - k) - w - 1) * Λ ^ k * ‖t‖ ^ (n * w - w - 1) := by
            rw [mul_pow, ← pow_mul, ← hexp, pow_add]; ring
    · rw [hRcoeff k hk2, eval_zero, zero_mul, norm_zero]
      exact mul_nonneg (mul_nonneg (bnd_nonneg _ _) (pow_nonneg hΛ0 k)) (by positivity)

  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨i₀, _, hi₀⟩ := exists_min_image univ (fun i => ‖x - (P i).eval t‖) univ_nonempty
  refine ⟨i₀, ?_⟩
  have hfar : ∀ i, i ≠ i₀ → κ * ‖t‖ ^ w / 2 ≤ ‖x - (P i).eval t‖ := by
    intro i hi
    have h1 := hsep t ht1 htT i₀ i (Ne.symm hi)
    have h2 : ‖(P i₀).eval t - (P i).eval t‖ ≤ ‖x - (P i₀).eval t‖ + ‖x - (P i).eval t‖ := by
      calc ‖(P i₀).eval t - (P i).eval t‖ = ‖(x - (P i).eval t) - (x - (P i₀).eval t)‖ := by
            congr 1; ring
        _ ≤ ‖x - (P i).eval t‖ + ‖x - (P i₀).eval t‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    have h3 := hi₀ i (mem_univ i)
    linarith

  have hprod : ‖c‖ * ∏ i, ‖x - (P i).eval t‖ = ‖(R.map (evalRingHom t)).eval x‖ := by
    have h := eval_map_factorization F c P t x
    rw [← hRdef, show (F.map (evalRingHom t)).eval x = 0 from hx] at h
    have h' : c * ∏ i, (x - (P i).eval t) = -((R.map (evalRingHom t)).eval x) :=
      eq_neg_of_add_eq_zero_left h.symm
    rw [← norm_neg ((R.map (evalRingHom t)).eval x), ← h', norm_mul, norm_prod]

  have hlow : ‖c‖ * (‖x - (P i₀).eval t‖ * (κ * ‖t‖ ^ w / 2) ^ (n - 1)) ≤
      ‖c‖ * ∏ i, ‖x - (P i).eval t‖ := by
    apply mul_le_mul_of_nonneg_left _ hcpos.le
    rw [← mul_prod_erase univ (fun i => ‖x - (P i).eval t‖) (mem_univ i₀)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc (κ * ‖t‖ ^ w / 2) ^ (n - 1) = ∏ _i ∈ univ.erase i₀, (κ * ‖t‖ ^ w / 2) := by
          rw [prod_const, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
      _ ≤ ∏ i ∈ univ.erase i₀, ‖x - (P i).eval t‖ :=
          prod_le_prod₀ (fun i _ => by positivity) fun i hi => hfar i (ne_of_mem_erase hi)

  set Dκ : ℝ := ‖c‖ * (κ / 2) ^ (n - 1) with hDκ
  have hpowsplit : (κ * ‖t‖ ^ w / 2) ^ (n - 1) = (κ / 2) ^ (n - 1) * ‖t‖ ^ (w * (n - 1)) := by
    rw [show κ * ‖t‖ ^ w / 2 = κ / 2 * ‖t‖ ^ w by ring, mul_pow, ← pow_mul]
  have hexp2 : w * (n - 1) = n * w - w - 1 + 1 := by
    rw [Nat.mul_sub, mul_one, mul_comm n w]
    have : 2 * w ≤ w * n := by nlinarith
    lia
  have hmain : ‖x - (P i₀).eval t‖ * Dκ * ‖t‖ * ‖t‖ ^ (n * w - w - 1) ≤
      C₂ * ‖t‖ ^ (n * w - w - 1) := by
    calc ‖x - (P i₀).eval t‖ * Dκ * ‖t‖ * ‖t‖ ^ (n * w - w - 1)
        = ‖c‖ * (‖x - (P i₀).eval t‖ * (κ * ‖t‖ ^ w / 2) ^ (n - 1)) := by
          rw [hpowsplit, hexp2, pow_succ, hDκ]; ring
      _ ≤ ‖c‖ * ∏ i, ‖x - (P i).eval t‖ := hlow
      _ = ‖(R.map (evalRingHom t)).eval x‖ := hprod
      _ ≤ C₂ * ‖t‖ ^ (n * w - w - 1) := hRx
  have htpow : 0 < ‖t‖ ^ (n * w - w - 1) := by positivity
  have hmain' : ‖x - (P i₀).eval t‖ * Dκ * ‖t‖ ≤ C₂ := le_of_mul_le_mul_right hmain htpow
  have hmain'' : ‖x - (P i₀).eval t‖ * ‖t‖ ≤ C₂ / Dκ := by
    rw [le_div_iff₀ hden]; linarith [hmain']
  rw [le_div_iff₀ htpos, hC₀]
  have : C₂ / Dκ ≤ C₂ / (‖c‖ * (κ / 2) ^ (n - 1)) + 1 := by rw [hDκ]; linarith
  linarith

end M4cP1D1

open Polynomial in
/-- Roots of a weighted bivariate polynomial lie uniformly close to one of the
prescribed polynomial branches at infinity: for all sufficiently large complex
parameters `t`, every root is within `C₀ / ‖t‖` of some branch evaluated at `t`. -/
theorem Polynomial.exists_branch_near_root {n w : ℕ} (F : Polynomial (Polynomial ℂ)) (hF :
  F.natDegree ≤ n)
    (hwt : ∀ k j : ℕ, w * (n - k) < j → (F.coeff k).coeff j = 0) (c : ℂ) (hc : c ≠ 0)
    (hlead : F.coeff n = C c) (P : Fin n → Polynomial ℂ) (hP : ∀ i, (P i).natDegree ≤ w)
    (hPinj : Function.Injective fun i => (P i).coeff w)
    (hR : ∀ k j : ℕ, w * (n - k) ≤ j + w → ((F - C (C c) * ∏ i,
      (X - C (P i))).coeff k).coeff j = 0) :
    ∃ C₀ T : ℝ, 0 < C₀ ∧ ∀ t : ℂ, T ≤ ‖t‖ → ∀ x : ℂ, (F.map (Polynomial.evalRingHom t)).IsRoot x →
      ∃ i, ‖x - (P i).eval t‖ ≤ C₀ / ‖t‖ :=
  M4cP1D1.exists_branch_near_root F hF hwt c hc hlead P hP hPinj hR
