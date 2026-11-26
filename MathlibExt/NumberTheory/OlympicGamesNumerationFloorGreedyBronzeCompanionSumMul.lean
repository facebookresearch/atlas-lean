/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.BronzeMetallicIdentities
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Floor of greedy bronze sums

This module proves the floor identity for greedy sums of bronze numbers and their companion
sequences multiplied by `(3 + Real.sqrt 13) / 2`.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (1).
-/

namespace MetaMathlibExt

@[expose] public section

open Finset

private noncomputable abbrev gamma : ℝ := (Real.sqrt 13 - 3) / 2
private noncomputable abbrev alpha : ℝ := (3 + Real.sqrt 13) / 2
private theorem gamma_bounds : 0 < gamma ∧ gamma < 1 / 2 ∧ gamma ^ 2 + 3 * gamma = 1 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  dsimp [gamma]
  constructor
  · nlinarith
  constructor <;> nlinarith
private theorem bronze_bounds (m : ℕ) :
    0 ≤ lucasU bronzeLucasParams (2 * m) ∧
      lucasU bronzeLucasParams (2 * m) < lucasU bronzeLucasParams (2 * m + 1) := by
  induction m with
  | zero => norm_num [lucasU]
  | succ m ih =>
    have h1 := lucasU_bronzeLucasParams_add_two (2 * m)
    have h2 := lucasU_bronzeLucasParams_add_two (2 * m + 1)
    simp only [Nat.add_assoc] at h2
    simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    norm_num only [Nat.reduceAdd] at h2 ⊢
    constructor <;> omega
private theorem digit_bounds (b p s x y z : ℤ) (hb : 0 < b) (hp : 0 ≤ p)
    (hpb : p < b) (hs : 0 ≤ s) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : s + x * b < 4 * b + p)
    (h2 : s + x * b + y * (4 * b + p) < 7 * b + 2 * p)
    (h3 : s + x * b + y * (4 * b + p) + z * (7 * b + 2 * p) < 10 * b + 3 * p) :
    x + y + z ≤ 4 ∧ (3 < x + y + z → s < p) := by
  have hxb : 0 ≤ x * b := mul_nonneg hx hb.le
  have hyb : 0 ≤ y * (4 * b + p) := mul_nonneg hy (by omega)
  have hz1 : z ≤ 1 := by
    by_contra h
    have hge : 2 ≤ z := by omega
    nlinarith [mul_nonneg (show 0 ≤ z - 2 by omega) (show 0 ≤ 7 * b + 2 * p by omega)]
  have hy1 : y ≤ 1 := by
    by_contra h
    have hge : 2 ≤ y := by omega
    nlinarith [mul_nonneg (show 0 ≤ y - 2 by omega) (show 0 ≤ 4 * b + p by omega)]
  have hx4 : x ≤ 4 := by
    by_contra h
    have hge : 5 ≤ x := by omega
    nlinarith [mul_nonneg (show 0 ≤ x - 5 by omega) hb.le]
  interval_cases y <;> interval_cases z <;> interval_cases x <;>
    norm_num at * <;> omega

private theorem weights (R : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3))) (m : ℕ) :
    let b := lucasU bronzeLucasParams (2 * m + 1)
    let p := lucasU bronzeLucasParams (2 * m)
    R (3 * m + 1) = b ∧ R (3 * m + 2) = 4 * b + p ∧
      R (3 * m + 3) = 7 * b + 2 * p ∧ R (3 * m + 4) = 10 * b + 3 * p := by
  dsimp only
  have h1 : (3 * m + 1) / 3 = m := by omega
  have h2 : (3 * m + 2) / 3 = m := by omega
  have h3 : (3 * m + 3) / 3 = m + 1 := by omega
  have h4 : (3 * m + 4) / 3 = m + 1 := by omega
  have hm1 : (3 * m + 1) % 3 = 1 := by omega
  have hm2 : (3 * m + 2) % 3 = 2 := by omega
  have hm3 : (3 * m + 3) % 3 = 0 := by omega
  have hm4 : (3 * m + 4) % 3 = 1 := by omega
  simp only [hR, hm1, hm2, hm3, hm4, h1, h2, h3, h4]
  norm_num
  simp only [bronzeCompanionFirst, bronzeCompanionSecond]
  rw [show 2 * (m + 1) = 2 * m + 2 by omega,
    show 2 * m + 2 + 1 = (2 * m + 1) + 2 by omega]
  simp only [lucasU_bronzeLucasParams_add_two]
  refine ⟨?_, ?_, ?_⟩ <;> ring
private theorem term_errors (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    (hR' : ∀ k, R' k =
      if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
      else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
      else bronzeCompanionFirst (2 * (k / 3) + 1)) (m : ℕ) :
    (R (3 * m + 1) : ℝ) * alpha - R' (3 * m + 2) = gamma ^ (2 * m + 1) ∧
      (R (3 * m + 2) : ℝ) * alpha - R' (3 * m + 3) =
        (1 - gamma) * gamma ^ (2 * m + 1) ∧
      (R (3 * m + 3) : ℝ) * alpha - R' (3 * m + 4) =
        (1 - 2 * gamma) * gamma ^ (2 * m + 1) := by
  have h1 : (3 * m + 1) / 3 = m := by omega
  have h2 : (3 * m + 2) / 3 = m := by omega
  have h3 : (3 * m + 3) / 3 = m + 1 := by omega
  have h4 : (3 * m + 4) / 3 = m + 1 := by omega
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hn : Real.sqrt (13 : ℝ) ≠ 0 := by positivity
  have hc : (13 + Real.sqrt 13) / (2 * Real.sqrt 13) * gamma = 1 - gamma := by
    dsimp [gamma]
    field_simp
    nlinarith
  have hd : (13 - Real.sqrt 13) / (2 * Real.sqrt 13) * gamma = 1 - 2 * gamma := by
    dsimp [gamma]
    field_simp
    nlinarith
  have hm1 : (3 * m + 1) % 3 = 1 := by omega
  have hm2 : (3 * m + 2) % 3 = 2 := by omega
  have hm3 : (3 * m + 3) % 3 = 0 := by omega
  have hm4 : (3 * m + 4) % 3 = 1 := by omega
  simp only [hR, hR', hm1, hm2, hm3, hm4, h1, h2, h3, h4]
  norm_num
  have hb := (bronze_mul_metallic_identities m).1
  have hC := (bronze_mul_metallic_identities (m + 1)).2.1
  have hD := (bronze_mul_metallic_identities (m + 1)).2.2.1
  have he : gamma ^ (2 * (m + 1)) = gamma * gamma ^ (2 * m + 1) := by
    rw [show 2 * (m + 1) = (2 * m + 1) + 1 by omega, pow_succ]
    ring
  rw [show 2 * (m + 1) = 2 * m + 2 by omega] at hC hD
  rw [show 2 * (m + 1) = 2 * m + 2 by omega] at he
  rw [he, ← mul_assoc, hc] at hC
  rw [he, ← mul_assoc, hd] at hD
  simp only [alpha, gamma, Nat.mul_add, Nat.mul_one, Nat.add_assoc, Nat.reduceAdd]
    at hb hC hD ⊢
  exact ⟨by linarith, by linarith, by linarith⟩
private def greedySum (R : ℕ → ℤ) (a : ℕ → ℕ) (n : ℕ) : ℤ :=
  ∑ k ∈ Ico 1 (n + 1), (a k : ℤ) * R k
private noncomputable def errorSum (R R' : ℕ → ℤ) (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  ∑ k ∈ Ico 1 (n + 1), (a k : ℝ) * ((R k : ℝ) * alpha - R' (k + 1))
private theorem prefix_succ (R : ℕ → ℤ) (a : ℕ → ℕ) (n : ℕ) :
    greedySum R a (n + 1) = greedySum R a n + (a (n + 1) : ℤ) * R (n + 1) := by
  unfold greedySum
  rw [sum_Ico_succ_top (by omega : 1 ≤ n + 1)]
private theorem errorSum_succ (R R' : ℕ → ℤ) (a : ℕ → ℕ) (n : ℕ) :
    errorSum R R' a (n + 1) = errorSum R R' a n +
      (a (n + 1) : ℝ) * ((R (n + 1) : ℝ) * alpha - R' (n + 1 + 1)) := by
  unfold errorSum
  rw [sum_Ico_succ_top (by omega : 1 ≤ n + 1)]

private theorem block_bound (b p s x y z : ℤ) (g e E : ℝ)
    (hb : 0 < b) (hp : 0 ≤ p) (hpb : p < b) (hs : 0 ≤ s)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : s + x * b < 4 * b + p)
    (h2 : s + x * b + y * (4 * b + p) < 7 * b + 2 * p)
    (h3 : s + x * b + y * (4 * b + p) + z * (7 * b + 2 * p) < 10 * b + 3 * p)
    (hg : 0 < g) (hg1 : g < 1 / 2) (hg2 : g ^ 2 + 3 * g = 1)
    (he : 0 ≤ e) (hA : E ≤ 1 - e) (hB : s < p → E ≤ 1 - (1 + g) * e) :
    E + ((x : ℝ) + (y : ℝ) * (1 - g) + (z : ℝ) * (1 - 2 * g)) * (e * g) ≤
        1 - e * g ^ 2 ∧
      (s + x * b + y * (4 * b + p) + z * (7 * b + 2 * p) < 3 * b + p →
        E + ((x : ℝ) + (y : ℝ) * (1 - g) + (z : ℝ) * (1 - 2 * g)) * (e * g) ≤
          1 - (1 + g) * (e * g ^ 2)) := by
  have hrx : (0 : ℝ) ≤ x := by exact_mod_cast hx
  have hry : (0 : ℝ) ≤ y := by exact_mod_cast hy
  have hrz : (0 : ℝ) ≤ z := by exact_mod_cast hz
  have heg : 0 ≤ e * g := mul_nonneg he hg.le
  have hδ : ((x : ℝ) + (y : ℝ) * (1 - g) + (z : ℝ) * (1 - 2 * g)) * (e * g) ≤
      ((x : ℝ) + y + z) * (e * g) := by
    apply mul_le_mul_of_nonneg_right _ heg
    nlinarith
  obtain ⟨hd, hdp⟩ := digit_bounds b p s x y z hb hp hpb hs hx hy hz h1 h2 h3
  constructor
  · by_cases hsmall : x + y + z ≤ 3
    · have hd3 : (x : ℝ) + y + z ≤ 3 := by exact_mod_cast hsmall
      have hmul := mul_le_mul_of_nonneg_right hd3 heg
      nlinarith [mul_nonneg he (sq_nonneg g)]
    · have hlow := hB (hdp (by omega))
      have hd4 : (x : ℝ) + y + z ≤ 4 := by exact_mod_cast hd
      have hmul := mul_le_mul_of_nonneg_right hd4 heg
      nlinarith [mul_nonneg he (sq_nonneg g)]
  · intro htotal
    have hxb := mul_nonneg hx hb.le
    have hyb := mul_nonneg hy (show 0 ≤ 4 * b + p by omega)
    have hz0 : z = 0 := by
      by_contra hne
      have hz1 : 1 ≤ z := by omega
      nlinarith [mul_nonneg (show 0 ≤ z - 1 by omega) (show 0 ≤ 7 * b + 2 * p by omega)]
    have hy0 : y = 0 := by
      by_contra hne
      have hy1 : 1 ≤ y := by omega
      nlinarith [mul_nonneg (show 0 ≤ y - 1 by omega) (show 0 ≤ 4 * b + p by omega)]
    subst y z
    norm_num at htotal ⊢
    have hx3 : x ≤ 3 := by
      by_contra hne
      have hx4 : 4 ≤ x := by omega
      nlinarith [mul_nonneg (show 0 ≤ x - 4 by omega) hb.le]
    have hbound : E + (x : ℝ) * (e * g) ≤ 1 - (1 - 2 * g) * e := by
      by_cases hx2 : x ≤ 2
      · have hxr : (x : ℝ) ≤ 2 := by exact_mod_cast hx2
        have hmul := mul_le_mul_of_nonneg_right hxr heg
        linarith
      · have hx_eq : x = 3 := by omega
        subst x
        have hlow := hB (by omega)
        norm_num
        linarith
    have hpoly : 0 ≤ (1 - 2 * g) - (1 + g) * g ^ 2 := by
      nlinarith [mul_pos hg (show 0 < 1 - 2 * g by linarith)]
    nlinarith [mul_nonneg he hpoly]

private theorem positive_weights (R : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3))) (k : ℕ) (hk : 1 ≤ k) : 0 < R k := by
  by_cases h1 : k % 3 = 1
  · have he : k = 3 * (k / 3) + 1 := by omega
    rw [he, (weights R hR (k / 3)).1]
    have h := bronze_bounds (k / 3)
    omega
  by_cases h2 : k % 3 = 2
  · have he : k = 3 * (k / 3) + 2 := by omega
    rw [he, (weights R hR (k / 3)).2.1]
    have h := bronze_bounds (k / 3)
    omega
  · have he : k = 3 * (k / 3 - 1) + 3 := by omega
    rw [he, (weights R hR (k / 3 - 1)).2.2.1]
    have h := bronze_bounds (k / 3 - 1)
    omega
private theorem nonnegative_errors (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    (hR' : ∀ k, R' k =
      if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
      else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
      else bronzeCompanionFirst (2 * (k / 3) + 1)) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ (R k : ℝ) * alpha - R' (k + 1) := by
  have hg := gamma_bounds
  by_cases h1 : k % 3 = 1
  · have he : k = 3 * (k / 3) + 1 := by omega
    rw [he]
    simpa only [Nat.add_assoc, Nat.reduceAdd,
      (term_errors R R' hR hR' (k / 3)).1] using
      (pow_nonneg hg.1.le (2 * (k / 3) + 1))
  by_cases h2 : k % 3 = 2
  · have he : k = 3 * (k / 3) + 2 := by omega
    rw [he]
    simpa only [Nat.add_assoc, Nat.reduceAdd,
      (term_errors R R' hR hR' (k / 3)).2.1] using
      (mul_nonneg (show 0 ≤ 1 - gamma by linarith [hg.2.1])
        (pow_nonneg hg.1.le (2 * (k / 3) + 1)))
  · have he : k = 3 * (k / 3 - 1) + 3 := by omega
    rw [he]
    simpa only [Nat.add_assoc, Nat.reduceAdd,
      (term_errors R R' hR hR' (k / 3 - 1)).2.2] using
      (mul_nonneg (show 0 ≤ 1 - 2 * gamma by linarith [hg.2.1])
        (pow_nonneg hg.1.le (2 * (k / 3 - 1) + 1)))
private theorem grouped_bound (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    (hR' : ∀ k, R' k =
      if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
      else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
      else bronzeCompanionFirst (2 * (k / 3) + 1))
    (a : ℕ → ℕ) (m : ℕ)
    (ha : ∀ j, 1 ≤ j → j ≤ 3 * m + 1 → greedySum R a (j - 1) < R j) :
    errorSum R R' a (3 * m) ≤ 1 - gamma ^ (2 * m) ∧
      (greedySum R a (3 * m) < lucasU bronzeLucasParams (2 * m) →
        errorSum R R' a (3 * m) ≤ 1 - (1 + gamma) * gamma ^ (2 * m)) := by
  induction m with
  | zero =>
    simp only [Nat.mul_zero, greedySum, errorSum, zero_add, Ico_self, sum_empty, pow_zero]
    norm_num [lucasU]
  | succ m ih =>
    have hprev := ih (fun j hj hjm => ha j hj (by omega))
    have hw := weights R hR m
    have ht := term_errors R R' hR hR' m
    dsimp only at hw
    let b := lucasU bronzeLucasParams (2 * m + 1)
    let p := lucasU bronzeLucasParams (2 * m)
    let s := greedySum R a (3 * m)
    let x : ℤ := a (3 * m + 1)
    let y : ℤ := a (3 * m + 2)
    let z : ℤ := a (3 * m + 3)
    have hS1 : greedySum R a (3 * m + 1) = s + x * b := by
      rw [prefix_succ, hw.1]
    have hS2 : greedySum R a (3 * m + 2) = s + x * b + y * (4 * b + p) := by
      rw [show 3 * m + 2 = (3 * m + 1) + 1 by omega, prefix_succ]
      simp only [Nat.add_assoc, Nat.reduceAdd, hS1, hw.2.1, y, b, p]
    have hS3 : greedySum R a (3 * (m + 1)) =
        s + x * b + y * (4 * b + p) + z * (7 * b + 2 * p) := by
      rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega, prefix_succ]
      simp only [Nat.add_assoc, Nat.reduceAdd, hS2, hw.2.2.1, z, b, p]
    have hE : errorSum R R' a (3 * (m + 1)) = errorSum R R' a (3 * m) +
        ((x : ℝ) + (y : ℝ) * (1 - gamma) + (z : ℝ) * (1 - 2 * gamma)) *
          (gamma ^ (2 * m) * gamma) := by
      rw [show 3 * (m + 1) = (3 * m + 2) + 1 by omega, errorSum_succ,
        show 3 * m + 2 = (3 * m + 1) + 1 by omega, errorSum_succ, errorSum_succ]
      simp only [Nat.add_assoc, Nat.reduceAdd, ht.1, ht.2.1, ht.2.2, pow_succ]
      dsimp [x, y, z]
      push_cast
      ring
    have hs : 0 ≤ s := by
      apply sum_nonneg
      intro k hk
      exact mul_nonneg (Int.natCast_nonneg _) (positive_weights R hR k (mem_Ico.mp hk).1).le
    have h1 : s + x * b < 4 * b + p := by
      have h := ha (3 * m + 2) (by omega) (by omega)
      simpa only [show 3 * m + 2 - 1 = 3 * m + 1 by omega, hS1, hw.2.1] using h
    have h2 : s + x * b + y * (4 * b + p) < 7 * b + 2 * p := by
      have h := ha (3 * m + 3) (by omega) (by omega)
      simpa only [show 3 * m + 3 - 1 = 3 * m + 2 by omega, hS2, hw.2.2.1] using h
    have h3 : s + x * b + y * (4 * b + p) + z * (7 * b + 2 * p) < 10 * b + 3 * p := by
      have h := ha (3 * m + 4) (by omega) (by omega)
      simpa only [show 3 * m + 4 - 1 = 3 * (m + 1) by omega, hS3, hw.2.2.2] using h
    have hbp := bronze_bounds m
    have hg := gamma_bounds
    have hblock := block_bound b p s x y z gamma (gamma ^ (2 * m))
      (errorSum R R' a (3 * m)) (by dsimp [b]; omega) hbp.1 hbp.2 hs
      (Int.natCast_nonneg _) (Int.natCast_nonneg _) (Int.natCast_nonneg _)
      h1 h2 h3 hg.1 hg.2.1 hg.2.2 (pow_nonneg hg.1.le _) hprev.1 hprev.2
    have hpow : gamma ^ (2 * (m + 1)) = gamma ^ (2 * m) * gamma ^ 2 := by
      rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
    rw [hE, hpow]
    refine ⟨hblock.1, ?_⟩
    intro hsmall
    apply hblock.2
    have hrec := lucasU_bronzeLucasParams_add_two (2 * m)
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, hrec, hS3] at hsmall
    exact hsmall

private theorem monotone_weights (R : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3))) : Monotone R := by
  apply monotone_nat_of_le_succ
  intro k
  by_cases hk : k = 0
  · subst k
    norm_num [hR, bronzeCompanionSecond, lucasU, bronzeLucasParams]
  by_cases h1 : k % 3 = 1
  · have he : k = 3 * (k / 3) + 1 := by omega
    rw [he]
    simp only [Nat.add_assoc, Nat.reduceAdd, (weights R hR (k / 3)).1,
      (weights R hR (k / 3)).2.1]
    have h := bronze_bounds (k / 3)
    omega
  by_cases h2 : k % 3 = 2
  · have he : k = 3 * (k / 3) + 2 := by omega
    rw [he]
    simp only [Nat.add_assoc, Nat.reduceAdd, (weights R hR (k / 3)).2.1,
      (weights R hR (k / 3)).2.2.1]
    have h := bronze_bounds (k / 3)
    omega
  · have he : k = 3 * (k / 3 - 1) + 3 := by omega
    rw [he]
    simp only [Nat.add_assoc, Nat.reduceAdd, (weights R hR (k / 3 - 1)).2.2.1,
      (weights R hR (k / 3 - 1)).2.2.2]
    have h := bronze_bounds (k / 3 - 1)
    omega
private theorem truncated_sum {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n j : ℕ) :
    (∑ k ∈ Ico 1 j, if k ≤ n then f k else 0) = ∑ k ∈ Ico 1 (min j (n + 1)), f k := by
  rw [← sum_filter]
  congr 1
  ext k
  simp only [mem_filter, mem_Ico]
  omega
private theorem errorSum_bounds (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    (hR' : ∀ k, R' k =
      if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
      else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
      else bronzeCompanionFirst (2 * (k / 3) + 1))
    (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ j, 1 ≤ j → j ≤ n + 1 → ∑ k ∈ Ico 1 j, (a k : ℤ) * R k < R j) :
    0 ≤ errorSum R R' a n ∧ errorSum R R' a n < 1 := by
  constructor
  · apply sum_nonneg
    intro k hk
    exact mul_nonneg (Nat.cast_nonneg _) (nonnegative_errors R R' hR hR' k (mem_Ico.mp hk).1)
  · let a' : ℕ → ℕ := fun k => if k ≤ n then a k else 0
    have hS (j : ℕ) : greedySum R a' j =
        ∑ k ∈ Ico 1 (min (j + 1) (n + 1)), (a k : ℤ) * R k := by
      unfold greedySum
      simp only [a', Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
      exact truncated_sum (fun k => (a k : ℤ) * R k) n (j + 1)
    have hpad : ∀ j, 1 ≤ j → j ≤ 3 * (n + 1) + 1 → greedySum R a' (j - 1) < R j := by
      intro j hj _
      rw [hS, Nat.sub_add_cancel hj]
      exact (ha (min j (n + 1)) (by omega) (by omega)).trans_le
        (monotone_weights R hR (min_le_left _ _))
    have hbound := (grouped_bound R R' hR hR' a' (n + 1) hpad).1
    have hE : errorSum R R' a' (3 * (n + 1)) = errorSum R R' a n := by
      unfold errorSum
      simp only [a', Nat.cast_ite, Nat.cast_zero, ite_mul, zero_mul]
      rw [truncated_sum, min_eq_right (by omega : n + 1 ≤ 3 * (n + 1) + 1)]
    rw [hE] at hbound
    have hpos : 0 < gamma ^ (2 * (n + 1)) := pow_pos gamma_bounds.1 _
    linarith

/-- **Floor of greedy bronze sums times $(3 + \sqrt{13})/2$.** Let $B_n$ be the bronze numbers
($B_0 = 0$, $B_1 = 1$, $B_{n+2} = 3B_{n+1} + B_n$, the Lucas sequence $U(3, -1)$), and let
$C_n = B_{n+1} - 2B_n$ and $D_n = B_{n+1} - B_n$ be the companion bronze numbers of the first and
second type. Let $R$ and $R'$ be the integer sequences with $R_{3m+1} = B_{2m+1}$,
$R_{3m+2} = C_{2m+2}$, $R_{3m} = D_{2m}$ and $R'_{3m+1} = D_{2m+1}$, $R'_{3m+2} = B_{2m+2}$,
$R'_{3m} = C_{2m+1}$ for all $m \ge 0$. Let $n$ be a natural number and $a_1, a_2, \dots$ natural
numbers such that $\sum_{k=1}^{m-1} a_k R_k < R_m$ for every $1 \le m \le n + 1$, and let
$t = \sum_{k=1}^{n} a_k R_k$. Then
$\lfloor t (3 + \sqrt{13})/2 \rfloor = \sum_{k=1}^{n} a_k R'_{k+1}$.

The hypothesis says that the $a_k$ are the digits of the greedy representation of Theorem 9;
$n$ need not be minimal.

Source: Michael Fisher, Keith Hazen, and Craig Tennenhouse, *Olympic Games: Three Impartial
Games with Infinite Octal Codes*, INTEGERS 24 (2024), Article G3, Theorem 10 (1). -/
public theorem floor_greedy_bronze_companion_sum_mul (R R' : ℕ → ℤ)
    (hR : ∀ k, R k =
      if k % 3 = 1 then lucasU bronzeLucasParams (2 * (k / 3) + 1)
      else if k % 3 = 2 then bronzeCompanionFirst (2 * (k / 3) + 2)
      else bronzeCompanionSecond (2 * (k / 3)))
    (hR' : ∀ k, R' k =
      if k % 3 = 1 then bronzeCompanionSecond (2 * (k / 3) + 1)
      else if k % 3 = 2 then lucasU bronzeLucasParams (2 * (k / 3) + 2)
      else bronzeCompanionFirst (2 * (k / 3) + 1))
    (n : ℕ) (a : ℕ → ℕ)
    (ha : ∀ m, 1 ≤ m → m ≤ n + 1 → ∑ k ∈ Ico 1 m, (a k : ℤ) * R k < R m) :
    ⌊((∑ k ∈ Icc 1 n, (a k : ℤ) * R k : ℤ) : ℝ) * ((3 + Real.sqrt 13) / 2)⌋ =
      ∑ k ∈ Icc 1 n, (a k : ℤ) * R' (k + 1)
    := by
  have hb := errorSum_bounds R R' hR hR' n a ha
  have he : errorSum R R' a n =
      ((∑ k ∈ Icc 1 n, (a k : ℤ) * R k : ℤ) : ℝ) * alpha -
        ((∑ k ∈ Icc 1 n, (a k : ℤ) * R' (k + 1) : ℤ) : ℝ) := by
    unfold errorSum
    rw [Ico_add_one_right_eq_Icc]
    push_cast
    simp_rw [mul_sub, ← mul_assoc]
    rw [sum_sub_distrib, sum_mul]
  apply Int.floor_eq_iff.mpr
  rw [he] at hb
  dsimp only [alpha] at hb
  exact ⟨by linarith [hb.1], by linarith [hb.2]⟩

end

end MetaMathlibExt
