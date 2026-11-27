/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean`
and
`P2M/Sol/S_PowerSeries_exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex.lean`
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

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.RingTheory.Algebraic.Defs
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

@[expose] public section

open Polynomial PowerSeries Finset

namespace EisensteinAlgSeries

private noncomputable def pn (N : ℕ) (x : ℝ) (f : ℂ⟦X⟧) : ℝ :=
  ∑ k ∈ range N, ‖PowerSeries.coeff k f‖ * x ^ k

private theorem pn_nonneg {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (f : ℂ⟦X⟧) : 0 ≤ pn N x f := by
  unfold pn
  exact sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hx k)

@[scoped simp] private theorem pn_zero (x : ℝ) (f : ℂ⟦X⟧) : pn 0 x f = 0 := by simp [pn]

private theorem pn_succ (N : ℕ) (x : ℝ) (f : ℂ⟦X⟧) :
    pn (N + 1) x f = pn N x f + ‖PowerSeries.coeff N f‖ * x ^ N := by
  simp [pn, sum_range_succ]

private theorem pn_add_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (f g : ℂ⟦X⟧) :
    pn N x (f + g) ≤ pn N x f + pn N x g := by
  unfold pn
  rw [← sum_add_distrib]
  refine sum_le_sum fun k _ => ?_
  rw [← add_mul, map_add]
  exact mul_le_mul_of_nonneg_right (norm_add_le _ _) (pow_nonneg hx k)

private theorem pn_sum_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) {ι : Type*} (s : Finset ι) (f : ι → ℂ⟦X⟧) :
    pn N x (∑ i ∈ s, f i) ≤ ∑ i ∈ s, pn N x (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pn]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (pn_add_le hx N _ _).trans (by linarith)

private theorem pn_mono {x : ℝ} (hx : 0 ≤ x) {N M : ℕ} (h : N ≤ M) (f : ℂ⟦X⟧) :
    pn N x f ≤ pn M x f := by
  unfold pn
  exact sum_le_sum_of_subset_of_nonneg (range_mono h)
    (fun k _ _ => mul_nonneg (norm_nonneg _) (pow_nonneg hx k))

private theorem norm_coeff_mul_pow_le_pn {x : ℝ} (hx : 0 ≤ x) {n N : ℕ} (h : n < N) (f : ℂ⟦X⟧) :
    ‖PowerSeries.coeff n f‖ * x ^ n ≤ pn N x f := by
  unfold pn
  exact single_le_sum (f := fun k => ‖PowerSeries.coeff k f‖ * x ^ k)
    (fun k _ => mul_nonneg (norm_nonneg _) (pow_nonneg hx k)) (mem_range.2 h)

private theorem pn_mul_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (f g : ℂ⟦X⟧) :
    pn N x (f * g) ≤ pn N x f * pn N x g := by
  unfold pn

  have h1 : ∀ k ∈ range N, ‖PowerSeries.coeff k (f * g)‖ * x ^ k ≤
      ∑ i ∈ range (k + 1), (‖PowerSeries.coeff i f‖ * x ^ i) *
        (‖PowerSeries.coeff (k - i) g‖ * x ^ (k - i)) := by
    intro k _
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i f * PowerSeries.coeff j g)]
    calc ‖∑ i ∈ range k.succ, PowerSeries.coeff i f * PowerSeries.coeff (k - i) g‖ * x ^ k
        ≤ (∑ i ∈ range k.succ, ‖PowerSeries.coeff i f * PowerSeries.coeff (k - i) g‖) * x ^ k :=
          mul_le_mul_of_nonneg_right (norm_sum_le _ _) (pow_nonneg hx k)
      _ = ∑ i ∈ range (k + 1), (‖PowerSeries.coeff i f‖ * x ^ i) *
            (‖PowerSeries.coeff (k - i) g‖ * x ^ (k - i)) := by
          rw [sum_mul]
          refine sum_congr rfl fun i hi => ?_
          have hik : i ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hi)
          rw [norm_mul]
          have : x ^ k = x ^ i * x ^ (k - i) := by
            rw [← pow_add, Nat.add_sub_cancel' hik]
          rw [this]; ring
  refine (sum_le_sum h1).trans ?_

  rw [sum_sigma']
  set F : ℕ → ℝ := fun i => ‖PowerSeries.coeff i f‖ * x ^ i with hF
  set G : ℕ → ℝ := fun j => ‖PowerSeries.coeff j g‖ * x ^ j with hG
  set S : Finset (Σ _ : ℕ, ℕ) := (range N).sigma fun k => range (k + 1) with hS
  have hinj : Set.InjOn (fun p : (Σ _ : ℕ, ℕ) => (p.2, p.1 - p.2)) ↑S := by
    intro p hp q hq hpq
    simp only [hS, coe_sigma, Set.mem_sigma_iff, coe_range, Set.mem_Iio] at hp hq
    simp only [Prod.mk.injEq] at hpq
    obtain ⟨h1, h2⟩ := hpq
    have : p.1 = q.1 := by omega
    exact Sigma.ext this (heq_of_eq h1)
  have hsub : S.image (fun p : (Σ _ : ℕ, ℕ) => (p.2, p.1 - p.2)) ⊆ range N ×ˢ range N := by
    intro q hq
    simp only [hS, mem_image, mem_sigma, mem_range] at hq
    obtain ⟨⟨k, i⟩, ⟨hk, hi⟩, rfl⟩ := hq
    simp only [mem_product, mem_range]
    dsimp only at hk hi ⊢
    omega
  calc ∑ p ∈ S, F p.2 * G (p.1 - p.2)
      = ∑ q ∈ S.image (fun p : (Σ _ : ℕ, ℕ) => (p.2, p.1 - p.2)), F q.1 * G q.2 := by
        rw [sum_image hinj]
    _ ≤ ∑ q ∈ range N ×ˢ range N, F q.1 * G q.2 :=
        sum_le_sum_of_subset_of_nonneg hsub fun q _ _ =>
          mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg hx _))
            (mul_nonneg (norm_nonneg _) (pow_nonneg hx _))
    _ = (∑ i ∈ range N, F i) * ∑ j ∈ range N, G j := by
        rw [sum_product, sum_mul_sum]

private theorem pn_one_le (x : ℝ) (N : ℕ) : pn N x (1 : ℂ⟦X⟧) ≤ 1 := by
  cases N with
  | zero => simp
  | succ N =>
    unfold pn
    rw [sum_range_succ']
    simp [PowerSeries.coeff_one]

private theorem pn_pow_le {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (f : ℂ⟦X⟧) (j : ℕ) :
    pn N x (f ^ j) ≤ pn N x f ^ j := by
  induction j with
  | zero => simpa using pn_one_le x N
  | succ j ih =>
    rw [pow_succ, pow_succ]
    exact (pn_mul_le hx N _ _).trans
      (mul_le_mul_of_nonneg_right ih (pn_nonneg hx N f))

private theorem pn_succ_X_mul (N : ℕ) (x : ℝ) (f : ℂ⟦X⟧) :
    pn (N + 1) x (PowerSeries.X * f) = x * pn N x f := by
  unfold pn
  rw [sum_range_succ', mul_sum]
  simp only [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul, norm_zero, zero_mul,
    add_zero]
  refine sum_congr rfl fun k _ => ?_
  ring

private theorem pn_succ_C (N : ℕ) {x : ℝ} (a : ℂ) :
    pn (N + 1) x (PowerSeries.C a) = ‖a‖ := by
  unfold pn
  rw [sum_range_succ']
  simp [PowerSeries.coeff_C]

private noncomputable def pabs (c : ℂ[X]) (x : ℝ) : ℝ := pn (c.natDegree + 1) x (c : ℂ⟦X⟧)

private theorem pabs_nonneg {x : ℝ} (hx : 0 ≤ x) (c : ℂ[X]) : 0 ≤ pabs c x := pn_nonneg hx _ _

private theorem pn_coe_le_pabs {x : ℝ} (hx : 0 ≤ x) (N : ℕ) (c : ℂ[X]) :
    pn N x (c : ℂ⟦X⟧) ≤ pabs c x := by
  unfold pabs
  rcases le_or_gt N (c.natDegree + 1) with h | h
  · exact pn_mono hx h _
  ·
    suffices H : ∀ M, c.natDegree + 1 ≤ M → pn M x (c : ℂ⟦X⟧) = pn (c.natDegree + 1) x (c : ℂ⟦X⟧) by
      exact (H N h.le).le
    intro M hM
    induction M, hM using Nat.le_induction with
    | base => rfl
    | succ M hM ih =>
      rw [pn_succ, ih, Polynomial.coeff_coe, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp

private theorem pabs_le_pabs_one {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (c : ℂ[X]) :
    pabs c x ≤ pabs c 1 := by
  unfold pabs pn
  refine sum_le_sum fun k _ => ?_
  rw [one_pow, mul_one]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hx hx1)

private theorem majorant {ψ : ℂ⟦X⟧} {c₀ : ℂ[X]} {d : ℕ} {e : ℕ → ℂ[X]}
    (hψ : ψ = (c₀ : ℂ⟦X⟧) + PowerSeries.X * ∑ j ∈ range d, (e j : ℂ⟦X⟧) * ψ ^ j) :
    ∃ C R : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n ψ‖ ≤ C * R ^ n := by

  set a : ℂ := c₀.coeff 0 with ha
  set c₀' : ℂ[X] := divX c₀ with hc₀'
  set G : ℂ⟦X⟧ := (c₀' : ℂ⟦X⟧) + ∑ j ∈ range d, (e j : ℂ⟦X⟧) * ψ ^ j with hG
  have hψ' : ψ = PowerSeries.C a + PowerSeries.X * G := by
    have hc : (c₀ : ℂ⟦X⟧) = PowerSeries.C a + PowerSeries.X * (c₀' : ℂ⟦X⟧) := by
      conv_lhs => rw [← X_mul_divX_add c₀]
      rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]
      ring
    rw [hψ, hc, hG]
    ring

  set ρ : ℝ := ‖a‖ + 1 with hρ
  let H : ℝ → ℝ → ℝ := fun x y => pabs c₀' x + ∑ j ∈ range d, pabs (e j) x * y ^ j
  set K : ℝ := H 1 ρ with hK
  have hρ0 : 0 ≤ ρ := by positivity
  have hK0 : 0 ≤ K := by
    show 0 ≤ pabs c₀' 1 + ∑ j ∈ range d, pabs (e j) 1 * ρ ^ j
    exact add_nonneg (pabs_nonneg zero_le_one _)
      (sum_nonneg fun j _ => mul_nonneg (pabs_nonneg zero_le_one _) (pow_nonneg hρ0 j))
  set x : ℝ := 1 / (K + 1) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one (by positivity)]
    linarith

  have hHy : ∀ {y y' : ℝ}, 0 ≤ y → y ≤ y' → H x y ≤ H x y' := by
    intro y y' hy hyy'
    show pabs c₀' x + ∑ j ∈ range d, pabs (e j) x * y ^ j ≤
      pabs c₀' x + ∑ j ∈ range d, pabs (e j) x * y' ^ j
    gcongr with j _
    exact pabs_nonneg hx0.le _
  have hHx : H x ρ ≤ K := by
    show pabs c₀' x + ∑ j ∈ range d, pabs (e j) x * ρ ^ j ≤
      pabs c₀' 1 + ∑ j ∈ range d, pabs (e j) 1 * ρ ^ j
    gcongr with j _
    · exact pabs_le_pabs_one hx0.le hx1 _
    · exact pabs_le_pabs_one hx0.le hx1 _

  have key : ∀ N, pn N x ψ ≤ ρ := by
    intro N
    induction N with
    | zero => simp [hρ0]
    | succ N ih =>
      have hGN : pn N x G ≤ H x (pn N x ψ) := by
        show pn N x G ≤ pabs c₀' x + ∑ j ∈ range d, pabs (e j) x * pn N x ψ ^ j
        refine (pn_add_le hx0.le N _ _).trans (add_le_add (pn_coe_le_pabs hx0.le N _) ?_)
        refine (pn_sum_le hx0.le N _ _).trans (sum_le_sum fun j _ => ?_)
        exact (pn_mul_le hx0.le N _ _).trans (mul_le_mul (pn_coe_le_pabs hx0.le N _)
          (pn_pow_le hx0.le N ψ j) (pn_nonneg hx0.le _ _) (pabs_nonneg hx0.le _))
      calc pn (N + 1) x ψ = pn (N + 1) x (PowerSeries.C a + PowerSeries.X * G) := by rw [← hψ']
        _ ≤ pn (N + 1) x (PowerSeries.C a) + pn (N + 1) x (PowerSeries.X * G) :=
            pn_add_le hx0.le _ _ _
        _ = ‖a‖ + x * pn N x G := by rw [pn_succ_C, pn_succ_X_mul]
        _ ≤ ‖a‖ + x * K := by
            gcongr
            exact hGN.trans ((hHy (pn_nonneg hx0.le _ _) ih).trans hHx)
        _ ≤ ‖a‖ + 1 := by
            gcongr
            rw [hx, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
            linarith

  refine ⟨ρ, K + 1, fun n => ?_⟩
  have h1 : ‖PowerSeries.coeff n ψ‖ * x ^ n ≤ ρ :=
    (norm_coeff_mul_pow_le_pn hx0.le (Nat.lt_succ_self n) ψ).trans (key (n + 1))
  have hxn : 0 < x ^ n := pow_pos hx0 n
  have h2 : x ^ n * (K + 1) ^ n = 1 := by
    rw [← mul_pow, hx, one_div, inv_mul_cancel₀ (by positivity), one_pow]
  calc ‖PowerSeries.coeff n ψ‖ = ‖PowerSeries.coeff n ψ‖ * x ^ n * (K + 1) ^ n := by
        rw [mul_assoc, h2, mul_one]
    _ ≤ ρ * (K + 1) ^ n := mul_le_mul_of_nonneg_right h1 (by positivity)

private theorem exists_annihilator_derivative_ne_zero {φ : ℂ⟦X⟧} (hφ : IsAlgebraic ℂ[X] φ) :
    ∃ P : ℂ[X][X], aeval φ P = 0 ∧ aeval φ (derivative P) ≠ 0 := by
  classical
  have hex : ∃ n, ∃ P : ℂ[X][X], P ≠ 0 ∧ aeval φ P = 0 ∧ P.natDegree = n := by
    obtain ⟨P, hP0, hP⟩ := hφ
    exact ⟨_, P, hP0, hP, rfl⟩
  obtain ⟨P, hP0, hP, hdeg⟩ := Nat.find_spec hex
  have hmin : ∀ Q : ℂ[X][X], Q ≠ 0 → aeval φ Q = 0 → P.natDegree ≤ Q.natDegree := by
    intro Q hQ0 hQ
    rw [hdeg]
    exact Nat.find_min' hex ⟨Q, hQ0, hQ, rfl⟩
  refine ⟨P, hP, fun hD => ?_⟩
  have hPdeg : P.natDegree ≠ 0 := by
    intro h0
    have hC := eq_C_of_natDegree_eq_zero h0
    rw [hC, aeval_C] at hP
    have h1 : ((P.coeff 0 : ℂ[X]) : ℂ⟦X⟧) = 0 := hP
    rw [Polynomial.coe_eq_zero_iff] at h1
    exact hP0 (by rw [hC, h1, map_zero])
  have hD0 : derivative P ≠ 0 := fun h => hPdeg (natDegree_eq_zero_of_derivative_eq_zero h)
  exact absurd (hmin _ hD0 hD) (not_le.mpr (natDegree_derivative_lt hPdeg))

private theorem aeval_taylor_powerSeries (P : ℂ[X][X]) (p : ℂ[X]) (z : ℂ⟦X⟧) :
    aeval z (taylor p P) = aeval (z + (p : ℂ⟦X⟧)) P := by
  rw [taylor_apply, aeval_comp]
  congr 1
  simp only [map_add, aeval_X, aeval_C]
  rfl

private theorem coe_aeval_eq (D : ℂ[X][X]) (p : ℂ[X]) :
    ((eval p D : ℂ[X]) : ℂ⟦X⟧) = aeval (p : ℂ⟦X⟧) D := by
  have h1 : (p : ℂ⟦X⟧) = algebraMap ℂ[X] ℂ⟦X⟧ p := rfl
  rw [h1, aeval_algebraMap_apply, coe_aeval_eq_eval]
  rfl

private theorem X_pow_dvd_aeval_sub {u v : ℂ⟦X⟧} {s : ℕ}
    (h : PowerSeries.X ^ s ∣ u - v) (D : ℂ[X][X]) :
    PowerSeries.X ^ s ∣ aeval u D - aeval v D := by
  rw [aeval_def, aeval_def, ← eval_map, ← eval_map]
  exact h.trans (sub_dvd_eval_sub u v _)

private theorem exists_prepared_tail {φ : ℂ⟦X⟧} {P : ℂ[X][X]} (hP : aeval φ P = 0)
    (hD : aeval φ (derivative P) ≠ 0) :
    ∃ (s : ℕ) (c₀ : ℂ[X]) (d : ℕ) (e : ℕ → ℂ[X]),
      (PowerSeries.mk fun n => PowerSeries.coeff (n + s) φ) =
        (c₀ : ℂ⟦X⟧) + PowerSeries.X * ∑ j ∈ range d,
          (e j : ℂ⟦X⟧) * (PowerSeries.mk fun n => PowerSeries.coeff (n + s) φ) ^ j := by
  classical
  set g : ℂ⟦X⟧ := aeval φ (derivative P) with hg

  have hexa : ∃ n, PowerSeries.coeff n g ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (PowerSeries.ext fun n => by simpa using h n)
  set a : ℕ := Nat.find hexa with ha_def
  have ha : PowerSeries.coeff a g ≠ 0 := Nat.find_spec hexa
  have hlt : ∀ i < a, PowerSeries.coeff i g = 0 := fun i hi => by
    have := Nat.find_min hexa (m := i) (by rwa [← ha_def])
    simpa using this

  set p : ℂ[X] := trunc (a + 1) φ with hp
  set ψ : ℂ⟦X⟧ := PowerSeries.mk fun n => PowerSeries.coeff (n + (a + 1)) φ with hψ
  have hsplit : φ = PowerSeries.X ^ (a + 1) * ψ + (p : ℂ⟦X⟧) := by
    ext n
    rw [map_add, PowerSeries.coeff_X_pow_mul', Polynomial.coeff_coe, hp, coeff_trunc]
    by_cases hn : a + 1 ≤ n
    · rw [ite_eq_left hn, ite_eq_right (by omega), hψ, PowerSeries.coeff_mk, Nat.sub_add_cancel hn,
        add_zero]
    · rw [ite_eq_right hn, ite_eq_left (by omega), zero_add]

  set T : ℂ[X][X] := taylor p P with hT
  set n : ℕ := P.natDegree + 1 with hn
  have hTdeg : T.natDegree < n + 2 := by
    rw [hT, natDegree_taylor]; omega
  set Y : ℂ⟦X⟧ := PowerSeries.X ^ (a + 1) * ψ with hY
  have hexp : (0 : ℂ⟦X⟧) = ((eval p P : ℂ[X]) : ℂ⟦X⟧) +
      ((eval p (derivative P) : ℂ[X]) : ℂ⟦X⟧) * Y +
      ∑ j ∈ range n, ((T.coeff (j + 2) : ℂ[X]) : ℂ⟦X⟧) * Y ^ (j + 2) := by
    have h1 : aeval Y T = 0 := by rw [aeval_taylor_powerSeries, ← hsplit, hP]
    rw [aeval_eq_sum_range' hTdeg, sum_range_succ', sum_range_succ'] at h1
    simp only [Algebra.smul_def, pow_zero, mul_one, zero_add, pow_one] at h1
    rw [← h1, hT, taylor_coeff_zero, taylor_coeff_one]
    show _ = _ + _ + ∑ j ∈ range n,
      algebraMap ℂ[X] ℂ⟦X⟧ ((taylor p P).coeff (j + 1 + 1)) * Y ^ (j + 1 + 1)
    have e1 : ∀ q : ℂ[X], (q : ℂ⟦X⟧) = algebraMap ℂ[X] ℂ⟦X⟧ q := fun q => rfl
    rw [e1, e1]
    ring

  set q1 : ℂ[X] := eval p (derivative P) with hq1
  have hq1g : PowerSeries.X ^ (a + 1) ∣ g - (q1 : ℂ⟦X⟧) := by
    rw [hg, hq1, coe_aeval_eq]
    refine X_pow_dvd_aeval_sub ?_ _
    exact ⟨ψ, by rw [hsplit]; ring⟩
  have hq1coeff : ∀ i < a + 1, q1.coeff i = PowerSeries.coeff i g := by
    intro i hi
    have := (PowerSeries.X_pow_dvd_iff.mp hq1g) i hi
    rw [map_sub, Polynomial.coeff_coe, sub_eq_zero] at this
    exact this.symm
  obtain ⟨u, hu⟩ : Polynomial.X ^ a ∣ q1 := by
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    rw [hq1coeff i (by omega), hlt i hi]
  have hu0 : u.coeff 0 ≠ 0 := by
    have h1 : q1.coeff a = u.coeff 0 := by
      rw [hu, Polynomial.coeff_X_pow_mul', ite_eq_left le_rfl, Nat.sub_self]
    rw [← h1, hq1coeff a (Nat.lt_succ_self a)]
    exact ha

  set q0 : ℂ[X] := eval p P with hq0
  set S2 : ℂ⟦X⟧ := ∑ j ∈ range n,
    ((T.coeff (j + 2) : ℂ[X]) : ℂ⟦X⟧) * PowerSeries.X ^ ((a + 1) * j) * ψ ^ (j + 2) with hS2
  set W : ℂ⟦X⟧ := (u : ℂ⟦X⟧) * ψ + PowerSeries.X * S2 with hW
  have hA : (q1 : ℂ⟦X⟧) * Y = PowerSeries.X ^ (a + 1 + a) * ((u : ℂ⟦X⟧) * ψ) := by
    rw [hu, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X, hY]
    ring
  have hB : ∑ j ∈ range n, ((T.coeff (j + 2) : ℂ[X]) : ℂ⟦X⟧) * Y ^ (j + 2) =
      PowerSeries.X ^ (a + 1 + a) * (PowerSeries.X * S2) := by
    rw [hS2, mul_sum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [hY]
    ring
  have hexp2 : (0 : ℂ⟦X⟧) = (q0 : ℂ⟦X⟧) + PowerSeries.X ^ (a + 1 + a) * W := by
    rw [hexp, add_assoc, hA, hB, hW]
    ring
  obtain ⟨r, hr⟩ : Polynomial.X ^ (a + 1 + a) ∣ q0 := by
    rw [Polynomial.X_pow_dvd_iff]
    intro i hi
    have hdvd : PowerSeries.X ^ (a + 1 + a) ∣ (q0 : ℂ⟦X⟧) :=
      ⟨-W, by linear_combination -hexp2⟩
    have := (PowerSeries.X_pow_dvd_iff.mp hdvd) i hi
    rwa [Polynomial.coeff_coe] at this
  have hexp3 : (r : ℂ⟦X⟧) + W = 0 := by
    have h1 : PowerSeries.X ^ (a + 1 + a) * ((r : ℂ⟦X⟧) + W) = 0 := by
      rw [hr, Polynomial.coe_mul, Polynomial.coe_pow, Polynomial.coe_X] at hexp2
      linear_combination -hexp2
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (pow_ne_zero _ PowerSeries.X_ne_zero)
    · exact h

  set V : ℂ⟦X⟧ := ((divX u : ℂ[X]) : ℂ⟦X⟧) * ψ + S2 with hV
  have hexp4 : (r : ℂ⟦X⟧) + PowerSeries.C (u.coeff 0) * ψ + PowerSeries.X * V = 0 := by
    rw [← hexp3, hW, hV]
    have hu' : (u : ℂ⟦X⟧) = PowerSeries.X * ((divX u : ℂ[X]) : ℂ⟦X⟧) +
        PowerSeries.C (u.coeff 0) := by
      conv_lhs => rw [← X_mul_divX_add u]
      rw [Polynomial.coe_add, Polynomial.coe_mul, Polynomial.coe_X, Polynomial.coe_C]
    rw [hu']
    ring

  have hkC : PowerSeries.C (u.coeff 0)⁻¹ * PowerSeries.C (u.coeff 0) = (1 : ℂ⟦X⟧) := by
    rw [← map_mul, inv_mul_cancel₀ hu0, map_one]
  let e : ℕ → ℂ[X] := fun j =>
    if j = 0 then 0 else if j = 1 then -(Polynomial.C (u.coeff 0)⁻¹ * divX u)
      else -(Polynomial.C (u.coeff 0)⁻¹ * T.coeff j * Polynomial.X ^ ((a + 1) * (j - 2)))
  have he0 : e 0 = 0 := by
    show (if (0 : ℕ) = 0 then (0 : ℂ[X]) else _) = 0
    rw [ite_eq_left rfl]
  have he1 : e 1 = -(Polynomial.C (u.coeff 0)⁻¹ * divX u) := by
    show (if (1 : ℕ) = 0 then (0 : ℂ[X]) else if (1 : ℕ) = 1 then _ else _) = _
    rw [ite_eq_right one_ne_zero, ite_eq_left rfl]
  have he2 : ∀ j : ℕ, e (j + 2) =
      -(Polynomial.C (u.coeff 0)⁻¹ * T.coeff (j + 2) * Polynomial.X ^ ((a + 1) * j)) := by
    intro j
    show (if j + 2 = 0 then (0 : ℂ[X]) else if j + 2 = 1 then _
      else -(Polynomial.C (u.coeff 0)⁻¹ * T.coeff (j + 2) *
        Polynomial.X ^ ((a + 1) * (j + 2 - 2)))) = _
    rw [ite_eq_right (by omega), ite_eq_right (by omega), Nat.add_sub_cancel]
  have hsum : ∑ j ∈ range (n + 2), (e j : ℂ⟦X⟧) * ψ ^ j =
      -(PowerSeries.C (u.coeff 0)⁻¹ * V) := by
    rw [sum_range_succ', sum_range_succ', he0, Polynomial.coe_zero, zero_mul, add_zero,
      zero_add, he1, pow_one, hV, mul_add, neg_add]
    conv_lhs => rw [add_comm]
    congr 1
    · rw [Polynomial.coe_neg, Polynomial.coe_mul, Polynomial.coe_C]
      ring
    · rw [hS2, mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun j _ => ?_
      rw [he2 j, Polynomial.coe_neg, Polynomial.coe_mul, Polynomial.coe_mul, Polynomial.coe_C,
        Polynomial.coe_pow, Polynomial.coe_X]
      ring
  refine ⟨a + 1, -(Polynomial.C (u.coeff 0)⁻¹ * r), n + 2, e, ?_⟩
  show ψ = ((-(Polynomial.C (u.coeff 0)⁻¹ * r) : ℂ[X]) : ℂ⟦X⟧) +
    PowerSeries.X * ∑ j ∈ range (n + 2), (e j : ℂ⟦X⟧) * ψ ^ j
  rw [hsum, Polynomial.coe_neg, Polynomial.coe_mul, Polynomial.coe_C]
  linear_combination (PowerSeries.C (u.coeff 0)⁻¹) * hexp4 - ψ * hkC

end EisensteinAlgSeries

/-- A complex formal power series that is algebraic over `ℂ[X]` has
coefficients growing at most exponentially: there are real `C` and `R`
with `‖coeff n φ‖ ≤ C * R ^ n` for every `n`.

No positivity condition on `C` or `R` is asserted. -/
public theorem PowerSeries.exists_norm_coeff_le_mul_pow_of_isAlgebraic_complex
    (φ : PowerSeries ℂ) (hφ : IsAlgebraic (Polynomial ℂ) φ) :
    ∃ C R : ℝ, ∀ n : ℕ, ‖PowerSeries.coeff n φ‖ ≤ C * R ^ n := by
  obtain ⟨P, hP, hD⟩ := EisensteinAlgSeries.exists_annihilator_derivative_ne_zero hφ
  obtain ⟨s, c₀, d, e, hψ⟩ := EisensteinAlgSeries.exists_prepared_tail hP hD
  obtain ⟨C, R, hCR⟩ := EisensteinAlgSeries.majorant hψ
  have hB0 : 0 ≤ ∑ i ∈ range s, ‖PowerSeries.coeff i φ‖ := sum_nonneg fun i _ => norm_nonneg _
  have hR1 : 1 ≤ max |R| 1 := le_max_right _ _
  refine ⟨(∑ i ∈ range s, ‖PowerSeries.coeff i φ‖) + |C|, max |R| 1, fun n => ?_⟩
  have h2 : ∑ i ∈ range s, ‖PowerSeries.coeff i φ‖ ≤
      (∑ i ∈ range s, ‖PowerSeries.coeff i φ‖) + |C| := le_add_of_nonneg_right (abs_nonneg C)
  by_cases hn : n < s
  · have h1 : ‖PowerSeries.coeff n φ‖ ≤ ∑ i ∈ range s, ‖PowerSeries.coeff i φ‖ :=
      single_le_sum (f := fun i => ‖PowerSeries.coeff i φ‖) (fun i _ => norm_nonneg _)
        (mem_range.mpr hn)
    exact h1.trans (h2.trans (le_mul_of_one_le_right (hB0.trans h2) (one_le_pow₀ hR1)))
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + s := ⟨n - s, by omega⟩
    have h1 : ‖PowerSeries.coeff (m + s) φ‖ ≤ C * R ^ m := by
      simpa only [PowerSeries.coeff_mk] using hCR m
    have h3 : C * R ^ m ≤ |C| * (max |R| 1) ^ (m + s) :=
      calc C * R ^ m ≤ |C * R ^ m| := le_abs_self _
        _ = |C| * |R| ^ m := by rw [abs_mul, abs_pow]
        _ ≤ |C| * (max |R| 1) ^ m := by
          gcongr
          exact le_max_left _ _
        _ ≤ |C| * (max |R| 1) ^ (m + s) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR1 (Nat.le_add_right m s))
            (abs_nonneg C)
    have h4 : |C| * (max |R| 1) ^ (m + s) ≤
        ((∑ i ∈ range s, ‖PowerSeries.coeff i φ‖) + |C|) * (max |R| 1) ^ (m + s) :=
      mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hB0) (by positivity)
    exact h1.trans (h3.trans h4)
