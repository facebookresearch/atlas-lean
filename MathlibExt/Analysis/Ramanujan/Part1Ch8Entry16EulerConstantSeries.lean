/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum.Parity

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry16Eulerconstantseries

open scoped BigOperators Real
open Topology

noncomputable section

private def Afun : ℕ → ℕ := fun k => (3 ^ k - 1) / 2
private def Hsum : ℕ → ℝ := fun n => ∑ i ∈ Finset.Icc 1 n, ((i : ℝ))⁻¹
private def gfun : ℕ → ℝ := fun j => (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ))
private def Tfun : ℕ → ℝ := fun k =>
  ((k + 1 : ℕ) : ℝ) *
    ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)),
      (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ))

private lemma one_le_pow3 (k : ℕ) : 1 ≤ 3 ^ k := Nat.one_le_pow k 3 (by norm_num)
private lemma two_dvd_pow3_sub_one (k : ℕ) : 2 ∣ (3 ^ k - 1) := by
  have hodd : Odd (3 ^ k) := Odd.pow (by norm_num)
  obtain ⟨m, hm⟩ := hodd
  have h1 : 1 ≤ 3 ^ k := one_le_pow3 k
  omega
private lemma two_mul_A_add_one (k : ℕ) : 2 * ((3 ^ k - 1) / 2) + 1 = 3 ^ k := by
  have h1 : 1 ≤ 3 ^ k := one_le_pow3 k
  have hdvd := two_dvd_pow3_sub_one k
  obtain ⟨t, ht⟩ := hdvd
  omega
private lemma A_succ (k : ℕ) : Afun (k + 1) = 3 * Afun k + 1 := by
  have h1 := two_mul_A_add_one k
  have h2 := two_mul_A_add_one (k + 1)
  have h3 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
  unfold Afun
  omega

private lemma Hsum_zero : Hsum 0 = 0 := by simp [Hsum]
private lemma Hsum_succ (n : ℕ) : Hsum (n + 1) = Hsum n + (((n + 1 : ℕ) : ℝ))⁻¹ := by
  unfold Hsum
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1)]

private lemma partial_frac (x : ℝ) (hx0 : x ≠ 0) (hx1 : x - 1 ≠ 0) (hx2 : x + 1 ≠ 0) :
    (1 : ℝ) / (x ^ 3 - x) = -1 / x + 1 / (2 * (x - 1)) + 1 / (2 * (x + 1)) := by
  have hx3 : x ^ 3 - x ≠ 0 := by
    have : x ^ 3 - x = x * (x - 1) * (x + 1) := by ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero hx0 hx1) hx2
  have hx4 : x ^ 2 - 1 ≠ 0 := by
    have : x ^ 2 - 1 = (x - 1) * (x + 1) := by ring
    rw [this]
    exact mul_ne_zero hx1 hx2
  field_simp
  ring

private lemma gfun_step (M : ℕ) :
    gfun (M + 1) =
      (((((3 * M + 2 : ℕ) : ℝ))⁻¹ + (((3 * M + 3 : ℕ) : ℝ))⁻¹ + (((3 * M + 4 : ℕ) : ℝ))⁻¹) -
        (((M + 1 : ℕ) : ℝ))⁻¹) / 2 := by
  have hcast1 : (1 : ℝ) ≤ (((M + 1 : ℕ) : ℝ)) := by
    have h : 1 ≤ M + 1 := Nat.succ_le_succ (Nat.zero_le M)
    exact_mod_cast h
  have hmR : (((M + 1 : ℕ) : ℝ)) ≠ 0 := by
    have hpos : (0 : ℝ) < (((M + 1 : ℕ) : ℝ)) := by linarith
    exact ne_of_gt hpos
  have hu0 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hmR
  have hu1 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) - 1 ≠ 0 := by
    have h3m : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) ≥ 3 := by nlinarith
    linarith
  have hu2 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) + 1 ≠ 0 := by positivity
  have hpf := partial_frac ((3 : ℝ) * (((M + 1 : ℕ) : ℝ))) hu0 hu1 hu2
  have e1 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) - 1 = (((3 * M + 2 : ℕ) : ℝ)) := by
    push_cast
    ring
  have e2 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) = (((3 * M + 3 : ℕ) : ℝ)) := by
    push_cast
    ring
  have e3 : (3 : ℝ) * (((M + 1 : ℕ) : ℝ)) + 1 = (((3 * M + 4 : ℕ) : ℝ)) := by
    push_cast
    ring
  unfold gfun
  rw [hpf, e3, e1, ← e2]
  field_simp
  ring

private lemma G_formula (M : ℕ) :
    ∑ j ∈ Finset.Icc 1 M, gfun j = (Hsum (3 * M + 1) - Hsum M - 1) / 2 := by
  induction M with
  | zero =>
    simp only [Nat.mul_zero, Nat.zero_add]
    rw [Finset.Icc_eq_empty (by norm_num : ¬ (1 : ℕ) ≤ 0)]
    simp only [Finset.sum_empty]
    have h1 : Hsum 1 = 1 := by
      have h := Hsum_succ 0
      simp [Hsum_zero] at h
      linarith [h]
    rw [Hsum_zero, h1]
    norm_num
  | succ M ih =>
    have hsum_g : ∑ j ∈ Finset.Icc 1 (M + 1), gfun j =
        (∑ j ∈ Finset.Icc 1 M, gfun j) + gfun (M + 1) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hH1 : Hsum (3 * M + 2) = Hsum (3 * M + 1) + (((3 * M + 2 : ℕ) : ℝ))⁻¹ := by
      have h : 3 * M + 2 = (3 * M + 1) + 1 := by omega
      rw [h]
      exact Hsum_succ (3 * M + 1)
    have hH2 : Hsum (3 * M + 3) = Hsum (3 * M + 2) + (((3 * M + 3 : ℕ) : ℝ))⁻¹ := by
      have h : 3 * M + 3 = (3 * M + 2) + 1 := by omega
      rw [h]
      exact Hsum_succ (3 * M + 2)
    have hH3 : Hsum (3 * M + 4) = Hsum (3 * M + 3) + (((3 * M + 4 : ℕ) : ℝ))⁻¹ := by
      have h : 3 * M + 4 = (3 * M + 3) + 1 := by omega
      rw [h]
      exact Hsum_succ (3 * M + 3)
    have hHM : Hsum (M + 1) = Hsum M + (((M + 1 : ℕ) : ℝ))⁻¹ := Hsum_succ M
    have h3M : 3 * (M + 1) + 1 = 3 * M + 4 := by omega
    rw [hsum_g, ih, gfun_step, h3M, hH3, hH2, hH1, hHM]
    ring

private lemma block_sum_id (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ j ∈ Finset.Icc (a + 1) b, f j =
      (∑ j ∈ Finset.Icc 1 b, f j) - (∑ j ∈ Finset.Icc 1 a, f j) := by
  have hunion : Finset.Icc 1 a ∪ Finset.Icc (a + 1) b = Finset.Icc 1 b := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc 1 a) (Finset.Icc (a + 1) b) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [Finset.mem_Icc] at hx1 hx2
    omega
  have hsum := Finset.sum_union hdisj (f := f)
  rw [hunion] at hsum
  linarith [hsum]

private lemma block_eq (k : ℕ) :
    ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j =
      ((Hsum (Afun (k + 2)) - Hsum (Afun (k + 1)) - 1) / 2) -
      ((Hsum (Afun (k + 1)) - Hsum (Afun k) - 1) / 2) := by
  have hmono : Afun k ≤ Afun (k + 1) := by
    have h := A_succ k
    unfold Afun at h ⊢
    omega
  have h1 : 3 * Afun k + 1 = Afun (k + 1) := (A_succ k).symm
  have h2 : 3 * Afun (k + 1) + 1 = Afun (k + 2) := (A_succ (k + 1)).symm
  have b1 := block_sum_id gfun (Afun k) (Afun (k + 1)) hmono
  rw [G_formula (Afun (k + 1)), G_formula (Afun k), h1, h2] at b1
  exact b1

private lemma gfun_nonneg (j : ℕ) (hj : 1 ≤ j) : 0 ≤ gfun j := by
  unfold gfun
  apply le_of_lt
  apply one_div_pos.mpr
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have h1 : (0 : ℝ) < (j : ℝ) := by linarith
  have h2 : (1 : ℝ) < (3 * (j : ℝ)) ^ 2 := by nlinarith [hjr]
  have hD : (3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ) = 3 * (j : ℝ) * (((3 * (j : ℝ)) ^ 2) - 1) := by ring
  rw [hD]
  apply mul_pos (by linarith)
  linarith

private lemma gfun_le_inv_cube (j : ℕ) (hj : 1 ≤ j) :
    gfun j ≤ 1 / (24 * ((j : ℝ)) ^ 3) := by
  unfold gfun
  have hjr : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  have h24pos : (0 : ℝ) < 24 * ((j : ℝ)) ^ 3 := by positivity
  apply one_div_le_one_div_of_le h24pos
  have hD : (3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ) - 24 * ((j : ℝ)) ^ 3 =
      3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by ring
  have hsq : (1 : ℝ) ≤ ((j : ℝ)) ^ 2 := by nlinarith [hjr]
  have hnn : (0 : ℝ) ≤ 3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by
    apply mul_nonneg
    · apply mul_nonneg (by norm_num)
      exact le_of_lt hjpos
    · linarith
  linarith [hD, hnn]

private lemma A_cast (k : ℕ) : ((Afun k : ℝ)) = ((((3 ^ k : ℕ) : ℝ)) - 1) / 2 := by
  have hdvd : 2 ∣ (3 ^ k - 1) := two_dvd_pow3_sub_one k
  have h1 : (1 : ℕ) ≤ 3 ^ k := one_le_pow3 k
  have hcast : ((((3 ^ k - 1) : ℕ) : ℝ)) = ((((3 ^ k : ℕ) : ℝ))) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  have hA : Afun k = (3 ^ k - 1) / 2 := rfl
  have h2 : ((Afun k : ℝ)) = ((((3 ^ k - 1 : ℕ) : ℝ))) / ((((2 : ℕ) : ℝ))) := by
    rw [hA]
    exact Nat.cast_div hdvd (by norm_num)
  rw [h2, hcast]
  norm_num

private lemma block_card (k : ℕ) :
    (Finset.Icc (Afun k + 1) (Afun (k + 1))).card = 3 ^ k := by
  have h1 := two_mul_A_add_one k
  have h2 := two_mul_A_add_one (k + 1)
  have h3 : 3 ^ (k + 1) = 3 ^ k * 3 := pow_succ 3 k
  have hA1 : Afun k = (3 ^ k - 1) / 2 := rfl
  have hA2 : Afun (k + 1) = (3 ^ (k + 1) - 1) / 2 := rfl
  rw [hA1, hA2, Nat.card_Icc]
  omega

private lemma block_sum_le (k : ℕ) :
    ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j ≤
      (((1 / 9 : ℝ)) ^ k) / 3 := by
  have hAlo : ((Afun k : ℝ)) = ((((3 ^ k : ℕ) : ℝ)) - 1) / 2 := A_cast k
  have h3k : (0 : ℝ) < (((3 ^ k : ℕ) : ℝ)) := by
    have hpos : 0 < 3 ^ k := Nat.pow_pos (by norm_num)
    exact_mod_cast hpos
  have hTne : ((((3 ^ k : ℕ) : ℝ))) ≠ 0 := ne_of_gt h3k
  have h3kR : ((((3 ^ k : ℕ) : ℝ))) = (3 : ℝ) ^ k := by push_cast; ring
  have h9t : (((1 / 9 : ℝ)) ^ k) = 1 / (((((3 ^ k : ℕ) : ℝ))) * ((((3 ^ k : ℕ) : ℝ)))) := by
    rw [div_pow, one_pow]
    congr 1
    rw [h3kR]
    have h9 : (9 : ℝ) = (3 : ℝ) ^ 2 := by norm_num
    rw [h9, ← pow_mul]
    have h2k : 2 * k = k + k := by ring
    rw [h2k, pow_add]
  have hjbound : ∀ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)),
      gfun j ≤ (((((1 / 9 : ℝ)) ^ k) / 3)) / ((((3 ^ k : ℕ) : ℝ))) := by
    intro j hj
    simp only [Finset.mem_Icc] at hj
    have hj1 : 1 ≤ j := by
      have hA0 : 0 ≤ Afun k := Nat.zero_le _
      omega
    have hle : ((Afun k + 1 : ℕ) : ℝ) ≤ ((j : ℝ)) := by exact_mod_cast hj.1
    have hAle : (((((3 ^ k : ℕ) : ℝ)) + 1) / 2) ≤ ((j : ℝ)) := by
      have hcast1 : ((Afun k + 1 : ℕ) : ℝ) = ((Afun k : ℝ)) + 1 := by
        push_cast; ring
      rw [hcast1, hAlo] at hle
      linarith [hle]
    have hle2 : (((((3 ^ k : ℕ) : ℝ))) / 2) ≤ ((j : ℝ)) := by linarith [hAle]
    have hcube : (((((3 ^ k : ℕ) : ℝ))) / 2) ^ 3 ≤ ((j : ℝ)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hle2 3
    have hstep := gfun_le_inv_cube j hj1
    have hden : (3 : ℝ) * (((((3 ^ k : ℕ) : ℝ))) * ((((3 ^ k : ℕ) : ℝ)))) * ((((3 ^ k : ℕ) : ℝ))) ≤
        24 * ((j : ℝ)) ^ 3 := by
      nlinarith [hcube, h3k]
    have hC : (((((1 / 9 : ℝ)) ^ k) / 3)) / ((((3 ^ k : ℕ) : ℝ))) =
        1 / (3 * (((((3 ^ k : ℕ) : ℝ))) * ((((3 ^ k : ℕ) : ℝ)))) * ((((3 ^ k : ℕ) : ℝ)))) := by
      rw [h9t]
      field_simp
    have hjr : (1 : ℝ) ≤ ((j : ℝ)) := by exact_mod_cast hj1
    have hjpos : (0 : ℝ) < ((j : ℝ)) := by linarith
    have hDge : (24 : ℝ) * ((j : ℝ)) ^ 3 ≤ (3 * ((j : ℝ))) ^ 3 - 3 * ((j : ℝ)) := by
      have hD : (3 * (j : ℝ)) ^ 3 - 3 * ((j : ℝ)) - 24 * ((j : ℝ)) ^ 3 =
          3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by ring
      have hsq : (1 : ℝ) ≤ ((j : ℝ)) ^ 2 := by nlinarith [hjr]
      have hnn : (0 : ℝ) ≤ 3 * ((j : ℝ)) * (((j : ℝ)) ^ 2 - 1) := by
        apply mul_nonneg
        · apply mul_nonneg (by norm_num)
          exact le_of_lt hjpos
        · linarith
      linarith [hD, hnn]
    rw [hC]
    apply one_div_le_one_div_of_le (by positivity)
    linarith [hden, hDge]
  have hle := Finset.sum_le_card_nsmul _ _ _ hjbound
  rw [block_card, nsmul_eq_mul] at hle
  have hcancel : ((((3 ^ k : ℕ) : ℝ))) * (((((1 / 9 : ℝ)) ^ k) / 3) / ((((3 ^ k : ℕ) : ℝ)))) =
      ((((1 / 9 : ℝ)) ^ k) / 3) := by
    rw [← mul_div_assoc]
    exact mul_div_cancel_left₀ _ hTne
  rwa [hcancel] at hle

private lemma majorant_summable :
    Summable (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 9 : ℝ) ^ n) / 3) := by
  have hnorm : ‖(1 / 9 : ℝ)‖ < 1 := by norm_num
  have hpow : Summable (fun n : ℕ => ((n : ℝ)) ^ 1 * (1 / 9 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hpow' : Summable (fun n : ℕ => ((n : ℝ)) * (1 / 9 : ℝ) ^ n) := by
    simpa [pow_one] using hpow
  have hgeo : Summable (fun n : ℕ => (1 / 9 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hadd : Summable (fun n : ℕ => (((n : ℝ)) * (1 / 9 : ℝ) ^ n + (1 / 9 : ℝ) ^ n)) :=
    hpow'.add hgeo
  have hmr := hadd.mul_right (1 / 3 : ℝ)
  have heq : (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 9 : ℝ) ^ n) / 3) =
      (fun n : ℕ => ((((n : ℝ)) * (1 / 9 : ℝ) ^ n + (1 / 9 : ℝ) ^ n)) * (1 / 3)) := by
    funext n
    ring
  rwa [heq]

private lemma Tfun_eq (k : ℕ) : Tfun k =
    ((k + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j := by
  unfold Tfun gfun
  rfl

private lemma Tfun_nonneg (k : ℕ) : 0 ≤ Tfun k := by
  rw [Tfun_eq]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro j hj
  simp only [Finset.mem_Icc] at hj
  have hA0 : 0 ≤ Afun k := Nat.zero_le _
  have hj1 : 1 ≤ j := by omega
  exact gfun_nonneg j hj1

private lemma Tfun_le (k : ℕ) :
    Tfun k ≤ ((((k : ℝ)) + 1) * (1 / 9 : ℝ) ^ k) / 3 := by
  rw [Tfun_eq]
  have hblk := block_sum_le k
  have hcast : (((k + 1 : ℕ) : ℝ)) = ((k : ℝ)) + 1 := by push_cast; ring
  rw [hcast]
  calc (((k : ℝ)) + 1) * ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)), gfun j
      ≤ (((k : ℝ)) + 1) * ((((1 / 9 : ℝ)) ^ k) / 3) := by
        apply mul_le_mul_of_nonneg_left hblk (by positivity)
    _ = ((((k : ℝ)) + 1) * (1 / 9 : ℝ) ^ k) / 3 := by ring

private lemma summable_tfun : Summable Tfun :=
  Summable.of_nonneg_of_le Tfun_nonneg Tfun_le majorant_summable

private lemma Hsum_cast : ∀ n : ℕ, ((((harmonic n : ℚ)) : ℝ)) = Hsum n := by
  intro n
  rw [harmonic_eq_sum_Icc]
  unfold Hsum
  push_cast
  rfl

private lemma H_rate (n : ℕ) (hn : 1 ≤ n) :
    |((Hsum n - Real.log ((n : ℝ))) - Real.eulerMascheroniConstant)| ≤ 1 / ((n : ℝ)) := by
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < ((n : ℝ)) := by exact_mod_cast hn
  have hcast := Hsum_cast n
  have hseq : Real.eulerMascheroniSeq n = Hsum n - Real.log (((n : ℝ)) + 1) := by
    unfold Real.eulerMascheroniSeq
    rw [hcast]
  have hseq' : Real.eulerMascheroniSeq' n = Hsum n - Real.log ((n : ℝ)) := by
    unfold Real.eulerMascheroniSeq'
    rw [ite_eq_right hn0, hcast]
  have h1 := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n
  have h2 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  rw [hseq] at h1
  rw [hseq'] at h2
  have hlog : Real.log (((n : ℝ)) + 1) - Real.log ((n : ℝ)) ≤ 1 / ((n : ℝ)) := by
    have hdiv : Real.log (((n : ℝ)) + 1) - Real.log ((n : ℝ)) =
        Real.log (1 + 1 / ((n : ℝ))) := by
      rw [← Real.log_div (by positivity) (ne_of_gt hnpos)]
      congr 1
      field_simp
    rw [hdiv]
    have hle := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + 1 / ((n : ℝ)))
    have heq : (1 + 1 / ((n : ℝ))) - 1 = 1 / ((n : ℝ)) := by ring
    rwa [heq] at hle
  rw [abs_le]
  constructor <;> linarith [h1, h2, hlog, hnpos]

private lemma key_decay :
    Filter.Tendsto (fun N : ℕ => (((N : ℝ)) + 1) * (1 / 3 : ℝ) ^ N) Filter.atTop (nhds 0) := by
  have hnorm : ‖(1 / 3 : ℝ)‖ < 1 := by norm_num
  have hpow : Summable (fun n : ℕ => ((n : ℝ)) ^ 1 * (1 / 3 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hpow' : Summable (fun n : ℕ => ((n : ℝ)) * (1 / 3 : ℝ) ^ n) := by
    simpa [pow_one] using hpow
  have hgeo : Summable (fun n : ℕ => (1 / 3 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hadd : Summable (fun n : ℕ => (((n : ℝ)) * (1 / 3 : ℝ) ^ n + (1 / 3 : ℝ) ^ n)) :=
    hpow'.add hgeo
  have hsum : Summable (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 3 : ℝ) ^ n)) := by
    have heq : (fun n : ℕ => ((((n : ℝ)) + 1) * (1 / 3 : ℝ) ^ n)) =
        (fun n : ℕ => ((((n : ℝ)) * (1 / 3 : ℝ) ^ n + (1 / 3 : ℝ) ^ n))) := by
      funext n
      rw [add_mul, one_mul]
    rwa [heq]
  exact hsum.tendsto_atTop_zero

private lemma geo_third :
    Filter.Tendsto (fun N : ℕ => (1 / 3 : ℝ) ^ N) Filter.atTop (nhds 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

private def Gfun : ℕ → ℝ := fun k => (Hsum (Afun (k + 1)) - Hsum (Afun k) - 1) / 2
private lemma hG (k : ℕ) : Gfun k = (Hsum (Afun (k + 1)) - Hsum (Afun k) - 1) / 2 := rfl
private lemma hT : ∀ k, Tfun k = ((k + 1 : ℕ) : ℝ) * (Gfun (k + 1) - Gfun k) := by
  intro k
  have e : k + 1 + 1 = k + 2 := by omega
  rw [Tfun_eq, block_eq, hG (k + 1), hG k, e]

private lemma key_identity (n : ℕ) :
    2 * ∑ k ∈ Finset.range n, Tfun k =
      ((n : ℝ)) * (Hsum (Afun (n + 1)) - Hsum (Afun n)) - Hsum (Afun n) := by
  induction n with
  | zero => simp [Hsum_zero, show Afun 0 = 0 from rfl]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih, hT n, hG n, hG (n + 1)]
    push_cast
    ring

private def err : ℕ → ℝ := fun n => Hsum n - Real.log ((n : ℝ)) - Real.eulerMascheroniConstant

private lemma herr (n : ℕ) (hn : 1 ≤ n) : |err n| ≤ 1 / ((n : ℝ)) := by
  have h := H_rate n hn
  have h2 : err n = (Hsum n - Real.log ((n : ℝ))) - Real.eulerMascheroniConstant := by
    unfold err; ring
  rwa [h2]

private lemma A_mono (k : ℕ) : Afun k ≤ Afun (k + 1) := by
  have h := A_succ k
  omega

private lemma A_ge (N : ℕ) : 3 ^ N ≤ Afun (N + 1) := by
  induction N with
  | zero => decide
  | succ N ih =>
    have hA := A_succ (N + 1)
    have h3 : 3 ^ (N + 1 + 1) = 3 * 3 ^ (N + 1) := by ring
    omega

private lemma A_one_le (m : ℕ) (hm : 1 ≤ m) : 1 ≤ Afun m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 1 := ⟨m - 1, by omega⟩
  exact le_trans (one_le_pow3 t) (A_ge t)

private lemma pow3R (m : ℕ) : (((3 ^ m : ℕ)) : ℝ) = (3:ℝ)^m := by push_cast; ring

private lemma Areal_ge (N : ℕ) : (3:ℝ)^N ≤ ((Afun (N+1) : ℝ)) := by
  have h := A_ge N
  have h3 : (((3 ^ N : ℕ)) : ℝ) = (3:ℝ)^N := pow3R N
  calc (3:ℝ)^N = (((3 ^ N : ℕ)) : ℝ) := h3.symm
    _ ≤ ((Afun (N+1) : ℝ)) := by exact_mod_cast h

private lemma Apos (m : ℕ) (hm : 1 ≤ m) : 0 < ((Afun m : ℝ)) := by
  have h1 : (1:ℝ) ≤ ((Afun m : ℝ)) := by exact_mod_cast A_one_le m hm
  linarith

private lemma errA (m : ℕ) (hm : 1 ≤ m) : |err (Afun m)| ≤ 1 / ((Afun m : ℝ)) :=
  herr (Afun m) (A_one_le m hm)

private lemma hlogbound (x : ℝ) (hx0 : 0 ≤ x) (hx12 : x ≤ 1 / 2) :
    |Real.log (1 - x)| ≤ 2 * x := by
  have h1x : (0 : ℝ) < 1 - x := by linarith
  have h1x_le : (1 : ℝ) - x ≤ 1 := by linarith
  have hlog_nonpos : Real.log (1 - x) ≤ 0 := Real.log_nonpos (by linarith) h1x_le
  rw [abs_of_nonpos hlog_nonpos]
  have h1 : -Real.log (1 - x) = Real.log (1 / (1 - x)) := by
    rw [Real.log_div (by norm_num) (ne_of_gt h1x)]
    simp [Real.log_one]
  rw [h1]
  have h2 : Real.log (1 / (1 - x)) ≤ 1 / (1 - x) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  have h3 : (1 : ℝ) / (1 - x) - 1 = x / (1 - x) := by
    field_simp
    ring
  have h4 : x / (1 - x) ≤ 2 * x := by
    rw [div_le_iff₀ h1x]
    nlinarith [hx0, hx12]
  linarith [h2, h3, h4]

private lemma rmem (m : ℕ) (hm : 1 ≤ m) : 0 ≤ (1/3:ℝ)^m ∧ (1/3:ℝ)^m ≤ 1/2 := by
  constructor
  · positivity
  · calc (1/3:ℝ)^m ≤ (1/3:ℝ)^1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1/3 := pow_one _
      _ ≤ 1/2 := by norm_num

private lemma logA (m : ℕ) (hm : 1 ≤ m) :
    Real.log ((Afun m : ℝ)) = (m : ℝ) * Real.log 3 - Real.log 2 + Real.log (1 - (1/3:ℝ)^m) := by
  have hA := A_cast m
  have h3 : (((3 ^ m : ℕ)) : ℝ) = (3:ℝ)^m := pow3R m
  have hmpos : (0:ℝ) < (3:ℝ)^m := by positivity
  have h3ne : (3:ℝ)^m ≠ 0 := ne_of_gt hmpos
  have hrm : (1/3:ℝ)^m ≤ 1/3 := by
    calc (1/3:ℝ)^m ≤ (1/3:ℝ)^1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ = 1/3 := pow_one _
  have h1r : (0:ℝ) < 1 - (1/3:ℝ)^m := by linarith
  have h1rne : (1:ℝ) - (1/3:ℝ)^m ≠ 0 := ne_of_gt h1r
  have hmul : (3:ℝ)^m * (1/3:ℝ)^m = 1 := by
    rw [← mul_pow]
    norm_num
  have hdecomp : ((Afun m : ℝ)) = (3:ℝ)^m * (1 - (1/3:ℝ)^m) / 2 := by
    rw [hA, h3]
    have h2 : (3:ℝ)^m * (1 - (1/3:ℝ)^m) = (3:ℝ)^m - 1 := by
      rw [mul_sub, mul_one, hmul]
    rw [h2]
  rw [hdecomp, Real.log_div (mul_ne_zero h3ne h1rne) (by norm_num),
    Real.log_mul h3ne h1rne, Real.log_pow]
  ring

private lemma L1lim : Filter.Tendsto
    (fun N : ℕ => (((N + 1 : ℕ) : ℝ)) *
        (Real.log ((Afun (N+1+1) : ℝ)) - Real.log ((Afun (N+1) : ℝ))) - Real.log ((Afun (N+1) : ℝ)))
    Filter.atTop (nhds (Real.log 2)) := by
  have hexpr : ∀ N : ℕ, ((((N+1:ℕ)):ℝ)) * (Real.log ((Afun (N+1+1):ℝ)) - Real.log ((Afun (N+1):ℝ)))
      - Real.log ((Afun (N+1):ℝ)) =
      Real.log 2 + (((((N+1:ℕ)):ℝ)) *
          (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
              (1 - (1/3:ℝ)^(N+1))) := by
    intro N
    have h1 := logA (N+1+1) (by omega)
    have h2 := logA (N+1) (by omega)
    rw [h1, h2]
    push_cast
    ring
  have hE : Filter.Tendsto (fun N : ℕ => ((((N+1:ℕ)):ℝ)) *
      (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
          (1 - (1/3:ℝ)^(N+1))) Filter.atTop (nhds 0) := by
    have hb : ∀ N : ℕ, ‖((((N+1:ℕ)):ℝ)) *
        (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
            (1 - (1/3:ℝ)^(N+1))‖ ≤
        2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1)) + 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1)) + 2 *
            (1/3:ℝ)^(N+1) := by
      intro N
      have hr1 := rmem (N+1+1) (by omega)
      have hr2 := rmem (N+1) (by omega)
      have hb1 : |Real.log (1 - (1/3:ℝ)^(N+1+1))| ≤ 2 * (1/3:ℝ)^(N+1+1) := hlogbound _ hr1.1 hr1.2
      have hb2 : |Real.log (1 - (1/3:ℝ)^(N+1))| ≤ 2 * (1/3:ℝ)^(N+1) := hlogbound _ hr2.1 hr2.2
      have hcast : (((N+1:ℕ)):ℝ) = ((N:ℝ)) + 1 := by push_cast; ring
      set la := Real.log (1 - (1/3:ℝ)^(N+1+1)) with hla
      set lb := Real.log (1 - (1/3:ℝ)^(N+1)) with hlb
      rw [Real.norm_eq_abs, hcast]
      have hPn : (0:ℝ) ≤ ((N:ℝ)) + 1 := by positivity
      have e1 : (((N:ℝ))+1) * |la| ≤ (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1+1)) :=
        mul_le_mul_of_nonneg_left hb1 hPn
      have e2 : (((N:ℝ))+1) * |lb| ≤ (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1)) :=
        mul_le_mul_of_nonneg_left hb2 hPn
      have hsub : |la - lb| ≤ |la| + |lb| := abs_sub _ _
      have hmul : (((N:ℝ))+1) * |la - lb| ≤ (((N:ℝ))+1) * |la| + (((N:ℝ))+1) * |lb| := by
        have h := mul_le_mul_of_nonneg_left hsub hPn
        rwa [mul_add] at h
      have h3 : |(((N:ℝ))+1) * (la - lb)| = (((N:ℝ))+1) * |la - lb| := by
        rw [abs_mul, abs_of_nonneg hPn]
      have hfin : |(((N:ℝ))+1) * (la - lb) - lb| ≤ (((N:ℝ))+1) * |la| + (((N:ℝ))+1) * |lb| +
          |lb| := by
        have h1 : |(((N:ℝ))+1) * (la - lb) - lb| ≤ |(((N:ℝ))+1) * (la - lb)| + |lb| := abs_sub _ _
        linarith [h1, hmul, h3]
      calc |(((N:ℝ))+1) * (la - lb) - lb|
          ≤ (((N:ℝ))+1) * |la| + (((N:ℝ))+1) * |lb| + |lb| := hfin
        _ ≤ (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1+1)) + (((N:ℝ))+1) * (2 * (1/3:ℝ)^(N+1)) + 2 *
            (1/3:ℝ)^(N+1) := by
            linarith [e1, e2, hb2]
        _ = 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1)) + 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1)) + 2 *
            (1/3:ℝ)^(N+1) := by
            ring
    have ht1 : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1))) Filter.atTop
        (nhds 0) := by
      have h0 := key_decay.const_mul (2*(1/3:ℝ)^(1+1))
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have ht2 : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1))) Filter.atTop
        (nhds 0) := by
      have h0 := key_decay.const_mul (2*(1/3:ℝ))
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have ht3 : Filter.Tendsto (fun N : ℕ => 2 * (1/3:ℝ)^(N+1)) Filter.atTop (nhds 0) := by
      have h0 := geo_third.const_mul (2*(1/3:ℝ))
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have hB : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^(N+1+1)) + 2 *
        ((((N:ℝ))+1) * (1/3:ℝ)^(N+1)) + 2 * (1/3:ℝ)^(N+1)) Filter.atTop (nhds 0) := by
      have h := (ht1.add ht2).add ht3
      simpa using h
    exact squeeze_zero_norm hb hB
  have hadd : Filter.Tendsto (fun N : ℕ => Real.log 2 +
      (((((N+1:ℕ)):ℝ)) * (Real.log (1 - (1/3:ℝ)^(N+1+1)) - Real.log (1 - (1/3:ℝ)^(N+1))) - Real.log
          (1 - (1/3:ℝ)^(N+1)))) Filter.atTop (nhds (Real.log 2 + 0)) :=
    tendsto_const_nhds.add hE
  rw [add_zero] at hadd
  refine hadd.congr (fun N => ?_)
  exact (hexpr N).symm

private lemma E2lim : Filter.Tendsto
    (fun N : ℕ => (((N + 1 : ℕ) : ℝ)) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1)))
    Filter.atTop (nhds 0) := by
  have hb : ∀ N : ℕ, ‖(((N+1:ℕ)):ℝ) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1))‖ ≤
      2 * ((((N:ℝ))+1) * (1/3:ℝ)^N) + (1/3:ℝ)^N := by
    intro N
    have e1 := errA (N+1) (by omega)
    have e2 := errA (N+1+1) (by omega)
    have hApos : (0:ℝ) < ((Afun (N+1) : ℝ)) := Apos _ (by omega)
    have h3pos : (0:ℝ) < (3:ℝ)^N := by positivity
    have hAge : (3:ℝ)^N ≤ ((Afun (N+1) : ℝ)) := Areal_ge N
    have hmono : ((Afun (N+1) : ℝ)) ≤ ((Afun (N+1+1) : ℝ)) := by
      have h := A_mono (N+1)
      exact_mod_cast h
    have h1A : 1 / ((Afun (N+1):ℝ)) ≤ 1 / (3:ℝ)^N := one_div_le_one_div_of_le h3pos hAge
    have h1A2 : 1 / ((Afun (N+1+1):ℝ)) ≤ 1 / ((Afun (N+1):ℝ)) := one_div_le_one_div_of_le hApos
        hmono
    have f1 : |err (Afun (N+1+1))| ≤ 1 / ((Afun (N+1):ℝ)) := le_trans e2 h1A2
    have hcast : (((N+1:ℕ)):ℝ) = ((N:ℝ)) + 1 := by push_cast; ring
    have hrw : (1/3:ℝ)^N = 1/(3:ℝ)^N := by rw [div_pow, one_pow]
    rw [Real.norm_eq_abs, hcast]
    set ea := err (Afun (N+1+1)) with hea
    set eb := err (Afun (N+1)) with heb
    have hPn : (0:ℝ) ≤ ((N:ℝ)) + 1 := by positivity
    have g1 : (((N:ℝ))+1) * |ea| ≤ (((N:ℝ))+1) * (1/(3:ℝ)^N) :=
      mul_le_mul_of_nonneg_left (le_trans f1 h1A) hPn
    have g2 : (((N:ℝ))+1) * |eb| ≤ (((N:ℝ))+1) * (1/(3:ℝ)^N) :=
      mul_le_mul_of_nonneg_left (le_trans e1 h1A) hPn
    have heb2 : |eb| ≤ (1/3:ℝ)^N := by rw [hrw]; exact le_trans e1 h1A
    have hsub : |ea - eb| ≤ |ea| + |eb| := abs_sub _ _
    have hmul : (((N:ℝ))+1) * |ea - eb| ≤ (((N:ℝ))+1) * |ea| + (((N:ℝ))+1) * |eb| := by
      have h := mul_le_mul_of_nonneg_left hsub hPn
      rwa [mul_add] at h
    have hfin : |(((N:ℝ))+1) * (ea - eb) - eb| ≤ (((N:ℝ))+1) * |ea| + (((N:ℝ))+1) * |eb| +
        |eb| := by
      have h1 : |(((N:ℝ))+1) * (ea - eb) - eb| ≤ |(((N:ℝ))+1) * (ea - eb)| + |eb| := abs_sub _ _
      have h3 : |(((N:ℝ))+1) * (ea - eb)| = (((N:ℝ))+1) * |ea - eb| := by
        rw [abs_mul, abs_of_nonneg hPn]
      linarith [h1, hmul, h3]
    have h1A' : (1/(3:ℝ)^N) = (1/3:ℝ)^N := hrw.symm
    rw [h1A'] at g1 g2
    linarith [hfin, g1, g2, heb2]
  have hB : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^N) + (1/3:ℝ)^N) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun N : ℕ => 2 * ((((N:ℝ))+1) * (1/3:ℝ)^N)) Filter.atTop
        (nhds 0) := by
      have h0 := key_decay.const_mul 2
      rw [mul_zero] at h0
      refine h0.congr (fun N => ?_)
      ring
    have h := h1.add geo_third
    simpa using h
  exact squeeze_zero_norm hb hB

private lemma hlim : Filter.Tendsto (fun N : ℕ => 2 * ∑ k ∈ Finset.range (N + 1), Tfun k)
    Filter.atTop (nhds (Real.log 2 - Real.eulerMascheroniConstant)) := by
  have e1 : ∀ N : ℕ, 2 * ∑ k ∈ Finset.range (N + 1), Tfun k =
      ((((N+1:ℕ)):ℝ) * (Real.log ((Afun (N+1+1):ℝ)) - Real.log ((Afun (N+1):ℝ))) - Real.log
          ((Afun (N+1):ℝ)) - Real.eulerMascheroniConstant) +
      ((((N+1:ℕ)):ℝ) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1))) := by
    intro N
    have hKI := key_identity (N + 1)
    have h2a : Hsum (Afun (N+1+1)) = Real.log ((Afun (N+1+1):ℝ)) + Real.eulerMascheroniConstant +
        err (Afun (N+1+1)) := by
      unfold err; ring
    have h2b : Hsum (Afun (N+1)) = Real.log ((Afun (N+1):ℝ)) + Real.eulerMascheroniConstant + err
        (Afun (N+1)) := by
      unfold err; ring
    rw [h2a, h2b] at hKI
    linear_combination hKI
  have hcomb : Filter.Tendsto
      (fun N : ℕ => ((((N+1:ℕ)):ℝ) * (Real.log ((Afun (N+1+1):ℝ)) - Real.log ((Afun (N+1):ℝ))) -
          Real.log ((Afun (N+1):ℝ)) - Real.eulerMascheroniConstant) +
        ((((N+1:ℕ)):ℝ) * (err (Afun (N+1+1)) - err (Afun (N+1))) - err (Afun (N+1))))
      Filter.atTop (nhds ((Real.log 2 - Real.eulerMascheroniConstant) + 0)) :=
    (L1lim.sub_const Real.eulerMascheroniConstant).add E2lim
  rw [add_zero] at hcomb
  refine hcomb.congr (fun N => ?_)
  exact (e1 N).symm

private lemma hS : Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1), Tfun k)
    Filter.atTop (nhds (∑' k, Tfun k)) := by
  have hP := summable_tfun.hasSum.tendsto_sum_nat
  have hT := summable_tfun.tendsto_atTop_zero
  have hPS : Filter.Tendsto (fun N : ℕ => (∑ k ∈ Finset.range N, Tfun k) + Tfun N)
      Filter.atTop (nhds ((∑' k, Tfun k) + 0)) := hP.add hT
  rw [add_zero] at hPS
  refine hPS.congr (fun N => ?_)
  exact (Finset.sum_range_succ Tfun N).symm

private lemma hfinal : 2 * ∑' k, Tfun k = Real.log 2 - Real.eulerMascheroniConstant := by
  have h2S : Filter.Tendsto (fun N : ℕ => 2 * ∑ k ∈ Finset.range (N + 1), Tfun k)
      Filter.atTop (nhds (2 * ∑' k, Tfun k)) :=
    tendsto_const_nhds.mul hS
  exact tendsto_nhds_unique h2S hlim

private lemma main_result : Summable Tfun ∧
    Real.eulerMascheroniConstant = Real.log 2 - 2 * ∑' k, Tfun k := by
  refine ⟨summable_tfun, ?_⟩
  linarith [hfinal]

/-- **Ramanujan's series for Euler's constant.** For $k \ge 0$ let $A_k = (3^k - 1)/2$. Then the
series
$$S = \sum_{k=0}^{\infty} (k+1) \sum_{j=A_k+1}^{A_{k+1}} \frac{1}{(3j)^3 - 3j}$$
converges, and $\gamma = \log 2 - 2S$, where $\gamma$ is Euler's constant.

Proves `Wanted` entry `ramanujan_part1_ch8_entry16_eulerconstantseries`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8, Entry 16.
-/
theorem ramanujan_part1_ch8_entry16_eulerconstantseries :
    let A : ℕ → ℕ := fun k => (3 ^ k - 1) / 2
    let term : ℕ → ℝ := fun k =>
      ((k + 1 : ℕ) : ℝ) *
        ∑ j ∈ Finset.Icc (A k + 1) (A (k + 1)),
          (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ))
    Summable term ∧
      Real.eulerMascheroniConstant = Real.log 2 - 2 * ∑' k : ℕ, term k := by
  exact main_result

end
end Entry16Eulerconstantseries
end MathlibExt.Analysis.Ramanujan.Part1Ch8
end
