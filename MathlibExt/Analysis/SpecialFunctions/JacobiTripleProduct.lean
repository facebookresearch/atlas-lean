/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Algebra.Group.Nat.Even
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import MathlibExt.Combinatorics.Enumerative.GaussianBinomial

@[expose] public section

/-!
# Jacobi triple product identity

The bilateral-series/product identity of Jacobi, as stated in the source below.
This is not supplied by `MetaMathlibExt.QPochhammer.jacobiThetaProduct`, which
only defines the product-side theta function and proves no triple-product
identity, so the full identity is proved here.
-/

namespace MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
open MathlibExt

section

open BigOperators

private lemma hexp_pos (n : ℕ) : (((n : ℤ) * (n : ℤ)).toNat = n * n) := by
  have h : ((((n : ℤ) * (n : ℤ)).toNat : ℕ) : ℤ) = ((n * n : ℕ) : ℤ) := by
    rw [Int.toNat_of_nonneg (mul_self_nonneg _), Nat.cast_mul]
  exact Nat.cast_injective h

private lemma hexp_neg (n : ℕ) : (((-(n : ℤ)) * (-(n : ℤ))).toNat = n * n) := by
  have h : (-(n : ℤ)) * (-(n : ℤ)) = (n : ℤ) * (n : ℤ) := by ring
  rw [h]
  exact hexp_pos n

private lemma summable_pow_mul_pow_sq (A r : ℝ) (hA : 0 ≤ A) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun n : ℕ => A ^ n * r ^ (n * n) := by
  have hB0 : (0:ℝ) < A + 1 := by linarith
  have h1B : (1:ℝ) ≤ A + 1 := by linarith
  have hAB : A ≤ A + 1 := by linarith
  have hρpos : (0:ℝ) < (r + 1) / 2 := by linarith
  have hρ0 : (0:ℝ) ≤ (r + 1) / 2 := by linarith
  have hρ1 : (r + 1) / 2 < 1 := by linarith
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one
    (show (0:ℝ) < (r + 1) / 2 / (A + 1) by positivity) hr1
  have hBN : (A + 1) * r ^ N < (r + 1) / 2 := by
    have h := (lt_div_iff₀ hB0).mp hN
    rwa [mul_comm (r ^ N) (A + 1)] at h
  have hBρ : (1:ℝ) ≤ (A + 1) / ((r + 1) / 2) := by
    rw [le_div_iff₀ hρpos]
    linarith
  have hK1 : (1:ℝ) ≤ ((A + 1) / ((r + 1) / 2)) ^ N := one_le_pow₀ hBρ
  have hρne : ((r + 1) / 2) ≠ 0 := ne_of_gt hρpos
  have h5 : ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ N = (A + 1) ^ N := by
    rw [← mul_pow, div_mul_cancel₀ _ hρne]
  have hb : ∀ n : ℕ, ‖A ^ n * r ^ (n * n)‖ ≤
      ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ n := by
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rcases le_total n N with hn | hn
    · have h1 : A ^ n ≤ (A + 1) ^ N :=
        le_trans (pow_le_pow_left₀ hA hAB n) (pow_le_pow_right₀ h1B hn)
      have h2 : r ^ (n * n) ≤ 1 := pow_le_one₀ hr0 hr1.le
      have h3 : A ^ n * r ^ (n * n) ≤ (A + 1) ^ N * 1 :=
        mul_le_mul h1 h2 (pow_nonneg hr0 _) (pow_nonneg (by linarith : (0:ℝ) ≤ A + 1) N)
      have h4 : ((r + 1) / 2) ^ N ≤ ((r + 1) / 2) ^ n :=
        pow_le_pow_of_le_one hρ0 hρ1.le hn
      have h6 : ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ N ≤
          ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ n :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
      calc A ^ n * r ^ (n * n) ≤ (A + 1) ^ N * 1 := h3
        _ = (A + 1) ^ N := mul_one _
        _ = ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ N := h5.symm
        _ ≤ ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ n := h6
    · have hm : n * N ≤ n * n := Nat.mul_le_mul_left n hn
      have h2 : r ^ (n * n) ≤ r ^ (n * N) := pow_le_pow_of_le_one hr0 hr1.le hm
      have h3 : A ^ n * r ^ (n * n) ≤ A ^ n * r ^ (n * N) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg hA n)
      have h4 : A ^ n * r ^ (n * N) = (A * r ^ N) ^ n := by ring
      have h5' : (A * r ^ N) ^ n ≤ ((r + 1) / 2) ^ n :=
        pow_le_pow_left₀ (by positivity)
          (le_of_lt (lt_of_le_of_lt
            (mul_le_mul_of_nonneg_right hAB (pow_nonneg hr0 N)) hBN)) n
      have h6 : ((r + 1) / 2) ^ n ≤
          ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ n :=
        le_mul_of_one_le_left (pow_nonneg hρ0 n) hK1
      calc A ^ n * r ^ (n * n) ≤ A ^ n * r ^ (n * N) := h3
        _ = (A * r ^ N) ^ n := h4
        _ ≤ ((r + 1) / 2) ^ n := h5'
        _ ≤ ((A + 1) / ((r + 1) / 2)) ^ N * ((r + 1) / 2) ^ n := h6
  exact Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hρ0 hρ1).mul_left
      (((A + 1) / ((r + 1) / 2)) ^ N)) hb

private lemma summable_pos (z q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => z ^ ((n : ℤ)) * q ^ (((n : ℤ) * (n : ℤ)).toNat) := by
  have key := summable_pow_mul_pow_sq ‖z‖ ‖q‖ (norm_nonneg _) (norm_nonneg _) hq
  refine Summable.of_norm_bounded key ?_
  intro n
  rw [hexp_pos n, zpow_natCast, norm_mul, norm_pow, norm_pow]

private lemma summable_neg (z q : ℂ) (hq : ‖q‖ < 1) :
    Summable fun n : ℕ => z ^ (-((n : ℤ))) * q ^ (((-(n : ℤ)) * (-(n : ℤ))).toNat) := by
  have key := summable_pow_mul_pow_sq ‖z‖⁻¹ ‖q‖ (inv_nonneg.mpr (norm_nonneg _))
    (norm_nonneg _) hq
  refine Summable.of_norm_bounded key ?_
  intro n
  rw [hexp_neg n, zpow_neg, zpow_natCast, ← inv_pow, norm_mul, norm_pow, norm_pow,
    norm_inv]

private lemma summable_int (z q : ℂ) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => z ^ n * q ^ (n * n).toNat) := by
  have h1 : Summable (fun n : ℕ => (fun m : ℤ => z ^ m * q ^ (m * m).toNat) (n : ℤ)) := by
    simpa only [Int.cast_natCast] using summable_pos z q hq
  have h2 : Summable (fun n : ℕ => (fun m : ℤ => z ^ m * q ^ (m * m).toNat) (-(n : ℤ))) := by
    simpa only [Int.cast_natCast] using summable_neg z q hq
  exact Summable.of_nat_of_neg h1 h2

private lemma multipliable_aux1 (q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => (1 - q ^ (2 * n + 2)) := by
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq2 : ‖q‖ ^ 2 < 1 := pow_lt_one₀ hq0 hq two_ne_zero
  have e : ∀ n : ℕ, ‖q ^ (2 * n + 2)‖ = (‖q‖ ^ 2) ^ n * ‖q‖ ^ 2 := by
    intro n
    rw [norm_pow]
    ring
  have key := (summable_geometric_of_lt_one (pow_nonneg hq0 2) hq2).mul_right (‖q‖ ^ 2)
  have hsumm : Summable fun n : ℕ => ‖q ^ (2 * n + 2)‖ := by
    simpa only [e] using key
  exact multipliable_one_sub_of_summable hsumm

private lemma multipliable_aux2 (z q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => (1 + z * q ^ (2 * n + 1)) := by
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq2 : ‖q‖ ^ 2 < 1 := pow_lt_one₀ hq0 hq two_ne_zero
  have e : ∀ n : ℕ, ‖-(z * q ^ (2 * n + 1))‖ = (‖q‖ ^ 2) ^ n * (‖z‖ * ‖q‖) := by
    intro n
    rw [norm_neg, norm_mul, norm_pow]
    ring
  have key := (summable_geometric_of_lt_one (pow_nonneg hq0 2) hq2).mul_right
    (‖z‖ * ‖q‖)
  have hsumm : Summable fun n : ℕ => ‖-(z * q ^ (2 * n + 1))‖ := by
    simpa only [e] using key
  simpa only [sub_neg_eq_add] using multipliable_one_sub_of_summable hsumm

private lemma multipliable_aux3 (z q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable fun n : ℕ => (1 + z⁻¹ * q ^ (2 * n + 1)) := by
  have hq0 : (0:ℝ) ≤ ‖q‖ := norm_nonneg _
  have hq2 : ‖q‖ ^ 2 < 1 := pow_lt_one₀ hq0 hq two_ne_zero
  have e : ∀ n : ℕ, ‖-(z⁻¹ * q ^ (2 * n + 1))‖ = (‖q‖ ^ 2) ^ n * (‖z‖⁻¹ * ‖q‖) := by
    intro n
    rw [norm_neg, norm_mul, norm_inv, norm_pow]
    ring
  have key := (summable_geometric_of_lt_one (pow_nonneg hq0 2) hq2).mul_right
    (‖z‖⁻¹ * ‖q‖)
  have hsumm : Summable fun n : ℕ => ‖-(z⁻¹ * q ^ (2 * n + 1))‖ := by
    simpa only [e] using key
  simpa only [sub_neg_eq_add] using multipliable_one_sub_of_summable hsumm

private lemma multipliable_triple (z q : ℂ) (hq : ‖q‖ < 1) :
    Multipliable (fun n : ℕ =>
      (1 - q ^ (2 * n + 2)) * (1 + z * q ^ (2 * n + 1)) *
        (1 + z⁻¹ * q ^ (2 * n + 1))) := by
  have h12 := (multipliable_aux1 q hq).mul (multipliable_aux2 z q hq)
  have h123 := h12.mul (multipliable_aux3 z q hq)
  simpa only [mul_assoc] using h123

section GaussBinom

open scoped BigOperators

variable {R : Type*} [CommRing R]

private lemma jtpChoose_add (k : ℕ) : (k + 1).choose 2 = k.choose 2 + k := by
  have h := Nat.choose_succ_succ' k 1
  have h2 : (1 : ℕ) + 1 = 2 := rfl
  rw [h2] at h
  rw [Nat.choose_one_right] at h
  omega

private lemma jtpChoose_pow (Q : R) (k : ℕ) :
    Q ^ ((k + 1).choose 2) = Q ^ (k.choose 2) * Q ^ k := by
  rw [jtpChoose_add k, pow_add]

/-- Termwise identity for Rothe's theorem. -/
private lemma jtpRothe_term (Q x : R) (M k : ℕ) :
    gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * (x * Q) ^ (k + 1) +
      x * (gaussBinom Q M k * Q ^ (k.choose 2) * (x * Q) ^ k) =
    gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ (k + 1) +
      Q ^ (k + 1) * gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * x ^ (k + 1) := by
  simp only [jtpChoose_pow Q k, mul_pow, pow_succ]
  ring

/-- Rothe's finite q-binomial theorem. -/
private lemma jtpRothe (Q x : R) : ∀ M : ℕ,
    (∏ j ∈ Finset.range M, (1 + x * Q ^ j)) =
    ∑ k ∈ Finset.range (M + 1),
      gaussBinom Q M k * Q ^ (k.choose 2) * x ^ k := by
  intro M
  induction M generalizing x with
  | zero =>
    have hch0 : Nat.choose 0 2 = 0 := by decide
    simp only [zero_add, Finset.prod_range_zero, Finset.sum_range_one,
      gaussBinom_zero_right, hch0, pow_zero, mul_one]
  | succ M IH =>
    have hprod : (∏ j ∈ Finset.range M, (1 + x * Q ^ (j + 1))) =
        ∏ j ∈ Finset.range M, (1 + (x * Q) * Q ^ j) := by
      apply Finset.prod_congr rfl
      intro j _
      rw [pow_succ]
      ring
    have hch0 : Nat.choose 0 2 = 0 := by decide
    have hB0 : gaussBinom Q (M + 1) 0 * Q ^ (Nat.choose 0 2) * x ^ 0 = 1 := by
      simp only [gaussBinom_zero_right, hch0, pow_zero, mul_one]
    have hA0 : gaussBinom Q M 0 * Q ^ (Nat.choose 0 2) * (x * Q) ^ 0 = 1 := by
      simp only [gaussBinom_zero_right, hch0, pow_zero, mul_one]
    have hAtop : gaussBinom Q M (M + 1) * Q ^ ((M + 1).choose 2) * (x * Q) ^ (M + 1) = 0 := by
      rw [gaussBinom_eq_zero_of_lt Q M (M + 1) (by omega)]
      simp only [zero_mul]
    have hBterm : ∀ k : ℕ,
        gaussBinom Q (M + 1) (k + 1) * Q ^ ((k + 1).choose 2) * x ^ (k + 1) =
        gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ (k + 1) +
        Q ^ (k + 1) * gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * x ^ (k + 1) := by
      intro k
      rw [gaussBinom_succ_succ]
      ring
    have hRHS : (∑ k ∈ Finset.range (M + 1 + 1),
          gaussBinom Q (M + 1) k * Q ^ (k.choose 2) * x ^ k) =
        (∑ k ∈ Finset.range (M + 1),
          gaussBinom Q (M + 1) (k + 1) * Q ^ ((k + 1).choose 2) * x ^ (k + 1)) + 1 := by
      rw [Finset.sum_range_succ']
      simp only [hB0]
    have hLHS : (∑ k ∈ Finset.range (M + 1),
          gaussBinom Q M k * Q ^ (k.choose 2) * (x * Q) ^ k) =
        (∑ k ∈ Finset.range (M + 1),
          gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * (x * Q) ^ (k + 1)) + 1 := by
      rw [Finset.sum_range_succ']
      simp only [hA0, hAtop, Finset.sum_range_succ, add_zero]
    have hsum : (∑ k ∈ Finset.range (M + 1),
          gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * (x * Q) ^ (k + 1)) +
        x * (∑ k ∈ Finset.range (M + 1),
          gaussBinom Q M k * Q ^ (k.choose 2) * (x * Q) ^ k) =
        ∑ k ∈ Finset.range (M + 1),
          (gaussBinom Q M k * Q ^ ((k + 1).choose 2) * x ^ (k + 1) +
          Q ^ (k + 1) * gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * x ^ (k + 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => jtpRothe_term Q x M k)
    have hS := hLHS.symm
    have hmain : ((∑ k ∈ Finset.range (M + 1),
          gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * (x * Q) ^ (k + 1)) + 1) * (1 + x) =
        ((∑ k ∈ Finset.range (M + 1),
          gaussBinom Q M (k + 1) * Q ^ ((k + 1).choose 2) * (x * Q) ^ (k + 1)) +
        x * (∑ k ∈ Finset.range (M + 1),
          gaussBinom Q M k * Q ^ (k.choose 2) * (x * Q) ^ k)) + 1 := by
      rw [← hS]
      ring
    simp only [Finset.prod_range_succ', pow_zero, mul_one, hprod, IH (x * Q), hRHS, hLHS, hBterm]
    rw [hmain, hsum]

end GaussBinom

section TriNum

open scoped BigOperators

/-- Triangular number `T(n) = n * (n - 1) / 2` for integers, via exact division. -/
private def jtpTri (n : ℤ) : ℤ := (n * (n - 1)) / 2

private lemma jtpTri_double (m : ℤ) : 2 * jtpTri m = m * (m - 1) := by
  obtain ⟨k, hk⟩ := Int.even_mul_pred_self m
  simp only [jtpTri]
  omega

private lemma jtpTri_nonneg (m : ℤ) : 0 ≤ jtpTri m := by
  have h := jtpTri_double m
  have hnn : 0 ≤ m * (m - 1) := by
    rcases le_total m 0 with hm | hm
    · have h1 : m - 1 ≤ 0 := by omega
      exact mul_nonneg_of_nonpos_of_nonpos hm h1
    · rcases eq_or_lt_of_le hm with rfl | hmpos
      · simp only [zero_mul, le_refl]
      · have h1 : 0 ≤ m - 1 := by omega
        exact mul_nonneg hm h1
  omega

private lemma jtpTri_succ (n : ℤ) : jtpTri (n + 1) = jtpTri n + n := by
  have e1 := jtpTri_double (n + 1)
  have e2 := jtpTri_double n
  have hrr : (n + 1) * ((n + 1) - 1) - n * (n - 1) = 2 * n := by ring
  omega

private lemma jtpTri_neg (n : ℤ) : jtpTri (-n) = jtpTri (n + 1) := by
  have e1 := jtpTri_double (-n)
  have e2 := jtpTri_double (n + 1)
  have hrr : (-n) * ((-n) - 1) = (n + 1) * ((n + 1) - 1) := by ring
  omega

private lemma jtpTwoChoose (n : ℕ) :
    2 * (((n.choose 2 : ℕ)) : ℤ) = (n : ℤ) * ((n : ℤ) - 1) := by
  have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
  obtain ⟨k, hk⟩ := heven
  have h2 : 2 * (n * (n - 1) / 2) = n * (n - 1) := by omega
  have hch : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n
  have hnat : 2 * n.choose 2 = n * (n - 1) := by rw [hch]; exact h2
  have hcast : ((2 * n.choose 2 : ℕ) : ℤ) = ((n * (n - 1) : ℕ) : ℤ) := by rw [hnat]
  rw [Nat.cast_mul, Nat.cast_two] at hcast
  rw [hcast]
  cases n with
  | zero => decide
  | succ n =>
    have hsub : Nat.succ n - 1 = n := by omega
    rw [hsub]
    push_cast
    ring

/-- The exponent identity for the finite JTP term: `C(k,2) - N*k + C(N+1,2) = T(k-N)`. -/
private lemma jtpTri_sub (k N : ℕ) :
    ((k.choose 2 : ℕ) : ℤ) - (N : ℤ) * (k : ℤ) + (((N + 1).choose 2 : ℕ) : ℤ) =
    jtpTri ((k : ℤ) - (N : ℤ)) := by
  have e1 := jtpTwoChoose k
  have e2 := jtpTwoChoose (N + 1)
  have e3 := jtpTri_double ((k : ℤ) - (N : ℤ))
  have hcast : ((N : ℤ) + 1) * (N : ℤ) =
      (((N + 1 : ℕ) : ℤ)) * ((((N + 1 : ℕ) : ℤ)) - 1) := by
    push_cast
    ring
  have hrr : (k : ℤ) * ((k : ℤ) - 1) - 2 * ((N : ℤ) * (k : ℤ)) + ((N : ℤ) + 1) * (N : ℤ) =
      ((k : ℤ) - (N : ℤ)) * (((k : ℤ) - (N : ℤ)) - 1) := by ring
  omega

/-- zpow negation for nonzero complex base. -/
private lemma jtpZpow_neg {a : ℂ} (ha : a ≠ 0) (n : ℤ) : a ^ (-n) = (a ^ n)⁻¹ := by
  have h : ((Units.mk0 a ha) ^ (-n) : ℂˣ) = ((Units.mk0 a ha) ^ n)⁻¹ :=
    zpow_neg (a := Units.mk0 a ha) (n := n)
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) h
  simp only [Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0] at h2
  exact h2

/-- zpow of a product for nonzero complex factors. -/
private lemma jtpMul_zpow {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) (n : ℤ) :
    (a * b) ^ n = a ^ n * b ^ n := by
  have h : (((Units.mk0 a ha) * (Units.mk0 b hb)) ^ n : ℂˣ) =
      (Units.mk0 a ha) ^ n * (Units.mk0 b hb) ^ n :=
    mul_zpow (a := Units.mk0 a ha) (b := Units.mk0 b hb) (n := n)
  have h2 := congrArg (fun u : ℂˣ => (u : ℂ)) h
  simp only [Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_mk0] at h2
  exact h2

/-- The hub summand `t(n) = (-1)^n * Q^(T n) * w^n` with zpow. -/
private noncomputable def jtpTheta (Q w : ℂ) (n : ℤ) : ℂ := (-1) ^ n * Q ^ (jtpTri n) * w ^ n

private lemma jtpNeg_ne_zero {a : ℂ} (ha : a ≠ 0) : -a ≠ 0 := by
  intro hcon
  rw [neg_eq_zero] at hcon
  exact ha hcon

private lemma jtpTheta_ne_zero {Q w : ℂ} (hQ : Q ≠ 0) (hw : w ≠ 0) (n : ℤ) :
    jtpTheta Q w n ≠ 0 := by
  have hneg1 : (-1 : ℂ) ≠ 0 := jtpNeg_ne_zero one_ne_zero
  have h1 : (-1 : ℂ) ^ n ≠ 0 := zpow_ne_zero n hneg1
  have h2 : Q ^ (jtpTri n) ≠ 0 := zpow_ne_zero _ hQ
  have h3 : w ^ n ≠ 0 := zpow_ne_zero n hw
  simp only [jtpTheta]
  exact mul_ne_zero (mul_ne_zero h1 h2) h3

private lemma jtpTheta_norm (Q w : ℂ) (n : ℤ) :
    ‖jtpTheta Q w n‖ = ‖Q‖ ^ (jtpTri n) * ‖w‖ ^ n := by
  have hunfold : jtpTheta Q w n = (-1) ^ n * Q ^ (jtpTri n) * w ^ n := rfl
  rw [hunfold, norm_mul, norm_mul, Complex.norm_zpow, Complex.norm_zpow,
    Complex.norm_zpow, norm_neg, norm_one, one_zpow, one_mul]

/-- The finite product `L(N)`. -/
private noncomputable def jtpProdL (Q w : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N, ((1 - w * Q ^ j) * (1 - w⁻¹ * Q ^ (j + 1)))

/-- The truncated summand `f_N(n)`. -/
private noncomputable def jtpFin (Q w : ℂ) (N : ℕ) (n : ℤ) : ℂ :=
  if n.natAbs ≤ N then gaussBinom Q (2 * N) (n + (N : ℤ)).toNat * jtpTheta Q w n else 0

end TriNum

section Reflect

open scoped BigOperators

/-- Reflection identity: the `2N`-product in terms of `L(N)`. -/
private lemma jtpReflect (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0) (N : ℕ) :
    (∏ j ∈ Finset.range (2 * N), (1 - w * (Q ^ N)⁻¹ * Q ^ j)) =
    (-w) ^ N * (Q ^ ((N + 1).choose 2))⁻¹ * jtpProdL Q w N := by
  have hQN : (Q : ℂ) ^ N ≠ 0 := pow_ne_zero N hQ
  have hsum : ∑ j ∈ Finset.range N, (j + 1) = (N + 1).choose 2 := by
    have h : (∑ k ∈ Finset.range (N + 1), k) =
        (∑ k ∈ Finset.range N, (k + 1)) + 0 :=
      Finset.sum_range_succ' _ N
    rw [Finset.sum_range_id] at h
    rw [Nat.choose_two_right]
    omega
  have hupper : ∀ j : ℕ, (1 - w * (Q ^ N)⁻¹ * Q ^ (N + j)) = (1 - w * Q ^ j) := by
    intro j
    have e : (Q ^ N)⁻¹ * (Q ^ N * Q ^ j) = Q ^ j := by
      rw [← mul_assoc, inv_mul_cancel₀ hQN, one_mul]
    have e2 : w * (Q ^ N)⁻¹ * Q ^ (N + j) = w * Q ^ j := by
      rw [pow_add]
      calc w * (Q ^ N)⁻¹ * (Q ^ N * Q ^ j)
          = w * ((Q ^ N)⁻¹ * (Q ^ N * Q ^ j)) := by ring
        _ = w * Q ^ j := by rw [e]
    rw [e2]
  have hlower : ∀ j : ℕ, j < N →
      (1 - w * (Q ^ N)⁻¹ * Q ^ (N - 1 - j)) =
      (-w) * (Q ^ (j + 1))⁻¹ * (1 - w⁻¹ * Q ^ (j + 1)) := by
    intro j hj
    have hQj : (Q : ℂ) ^ (j + 1) ≠ 0 := pow_ne_zero _ hQ
    have hQNj : (Q : ℂ) ^ (N - 1 - j) ≠ 0 := pow_ne_zero _ hQ
    have hexp : N - 1 - j + (j + 1) = N := by omega
    have hpow : Q ^ (N - 1 - j) * Q ^ (j + 1) = Q ^ N := by rw [← pow_add, hexp]
    have e1 : (-w) * (Q ^ (j + 1))⁻¹ * (1 - w⁻¹ * Q ^ (j + 1)) =
        1 - w * (Q ^ (j + 1))⁻¹ := by
      field_simp
      ring
    have e2 : (Q ^ N)⁻¹ * Q ^ (N - 1 - j) = (Q ^ (j + 1))⁻¹ := by
      rw [← hpow, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hQNj, mul_one]
    calc 1 - w * (Q ^ N)⁻¹ * Q ^ (N - 1 - j)
        = 1 - w * ((Q ^ N)⁻¹ * Q ^ (N - 1 - j)) := by ring
      _ = 1 - w * (Q ^ (j + 1))⁻¹ := by rw [e2]
      _ = (-w) * (Q ^ (j + 1))⁻¹ * (1 - w⁻¹ * Q ^ (j + 1)) := e1.symm
  have hsplit : (∏ j ∈ Finset.range (2 * N), (1 - w * (Q ^ N)⁻¹ * Q ^ j)) =
      (∏ j ∈ Finset.range N, (1 - w * (Q ^ N)⁻¹ * Q ^ j)) *
      (∏ j ∈ Finset.range N, (1 - w * (Q ^ N)⁻¹ * Q ^ (N + j))) := by
    rw [two_mul]
    exact Finset.prod_range_add _ N N
  have hrefl : (∏ j ∈ Finset.range N, (1 - w * (Q ^ N)⁻¹ * Q ^ j)) =
      ∏ j ∈ Finset.range N, ((-w) * (Q ^ (j + 1))⁻¹ * (1 - w⁻¹ * Q ^ (j + 1))) := by
    rw [← Finset.prod_range_reflect]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Finset.mem_range] at hj
    show (1 - w * (Q ^ N)⁻¹ * Q ^ (N - 1 - j)) =
      (-w) * (Q ^ (j + 1))⁻¹ * (1 - w⁻¹ * Q ^ (j + 1))
    exact hlower j hj
  have hupper_prod : (∏ j ∈ Finset.range N, (1 - w * (Q ^ N)⁻¹ * Q ^ (N + j))) =
      ∏ j ∈ Finset.range N, (1 - w * Q ^ j) := by
    apply Finset.prod_congr rfl
    intro j _
    exact hupper j
  have hconst : (∏ j ∈ Finset.range N,
        ((-w) * (Q ^ (j + 1))⁻¹ * (1 - w⁻¹ * Q ^ (j + 1)))) =
      (-w) ^ N * (Q ^ ((N + 1).choose 2))⁻¹ *
      (∏ j ∈ Finset.range N, (1 - w⁻¹ * Q ^ (j + 1))) := by
    have hA : (∏ j ∈ Finset.range N, (-w)) = (-w) ^ N := by
      rw [Finset.prod_const, Finset.card_range]
    have hB : (∏ j ∈ Finset.range N, ((Q ^ (j + 1))⁻¹)) =
        (Q ^ ((N + 1).choose 2))⁻¹ := by
      rw [Finset.prod_inv_distrib, Finset.prod_pow_eq_pow_sum, hsum]
    simp only [Finset.prod_mul_distrib]
    rw [hA, hB]
  rw [hsplit, hrefl, hupper_prod, hconst]
  simp only [jtpProdL, Finset.prod_mul_distrib]
  ring

end Reflect

section FiniteJTP

open scoped BigOperators

/-- Termwise zpow identity for the finite JTP sum. -/
private lemma jtpTermId (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0) (N k : ℕ) :
    ((-w) ^ N)⁻¹ * Q ^ ((N + 1).choose 2) * Q ^ (k.choose 2) *
      (-(w * (Q ^ N)⁻¹)) ^ k =
    jtpTheta Q w ((k : ℤ) - (N : ℤ)) := by
  have hN5b : ((k.choose 2 : ℕ) : ℤ) - (N : ℤ) * (k : ℤ) + (((N + 1).choose 2 : ℕ) : ℤ) =
      jtpTri ((k : ℤ) - (N : ℤ)) := jtpTri_sub k N
  have hneg1 : (-1 : ℂ) ≠ 0 := jtpNeg_ne_zero one_ne_zero
  have hnwm : -w ≠ 0 := jtpNeg_ne_zero hw
  have e1 : (((-w) ^ N : ℂ))⁻¹ = (-w) ^ (-(N : ℤ)) := by
    rw [jtpZpow_neg hnwm, zpow_natCast]
  have e2 : (Q ^ ((N + 1).choose 2) : ℂ) = Q ^ ((((N + 1).choose 2 : ℕ)) : ℤ) :=
    (zpow_natCast _ _).symm
  have e3 : (Q ^ (k.choose 2) : ℂ) = Q ^ (((k.choose 2 : ℕ)) : ℤ) :=
    (zpow_natCast _ _).symm
  have eX : (((Q ^ N)⁻¹ : ℂ)) ^ k = Q ^ (-(((N * k : ℕ)) : ℤ)) := by
    rw [inv_pow, ← pow_mul, ← zpow_natCast, ← jtpZpow_neg hQ]
  have e5 : ((-1 : ℂ) ^ k) = (-1) ^ ((k : ℤ)) := (zpow_natCast _ _).symm
  have e6 : (w ^ k : ℂ) = w ^ ((k : ℤ)) := (zpow_natCast _ _).symm
  have e1' : (-1 : ℂ) ^ (-(N : ℤ)) * (-1 : ℂ) ^ ((k : ℤ)) =
      (-1) ^ ((k : ℤ) - (N : ℤ)) := by
    rw [← zpow_add₀ hneg1]
    congr 1
    ring
  have e2' : (w : ℂ) ^ (-(N : ℤ)) * w ^ ((k : ℤ)) = w ^ ((k : ℤ) - (N : ℤ)) := by
    rw [← zpow_add₀ hw]
    congr 1
    ring
  have e3' : (Q : ℂ) ^ ((((N + 1).choose 2 : ℕ)) : ℤ) * Q ^ (((k.choose 2 : ℕ)) : ℤ) *
      Q ^ (-(((N * k : ℕ)) : ℤ)) = Q ^ (jtpTri ((k : ℤ) - (N : ℤ))) := by
    rw [← zpow_add₀ hQ, ← zpow_add₀ hQ]
    congr 1
    have hcast : (((N * k : ℕ)) : ℤ) = (N : ℤ) * (k : ℤ) := Nat.cast_mul _ _
    omega
  rw [e1]
  rw [show (-w : ℂ) = (-1) * w by ring]
  rw [jtpMul_zpow hneg1 hw]
  rw [e2, e3]
  rw [show (-(w * (Q ^ N)⁻¹) : ℂ) = (-1) * (w * (Q ^ N)⁻¹) by ring]
  rw [mul_pow, mul_pow]
  rw [eX, e5, e6]
  simp only [mul_assoc]
  have hre : (-1 : ℂ) ^ (-(N : ℤ)) * (w ^ (-(N : ℤ)) *
      (Q ^ ((((N + 1).choose 2 : ℕ)) : ℤ) * (Q ^ (((k.choose 2 : ℕ)) : ℤ) *
      ((-1) ^ ((k : ℤ)) * (w ^ ((k : ℤ)) * Q ^ (-(((N * k : ℕ)) : ℤ))))))) =
      ((-1) ^ (-(N : ℤ)) * (-1) ^ ((k : ℤ))) *
      ((w ^ (-(N : ℤ)) * w ^ ((k : ℤ))) *
      (Q ^ ((((N + 1).choose 2 : ℕ)) : ℤ) * Q ^ (((k.choose 2 : ℕ)) : ℤ) *
      Q ^ (-(((N * k : ℕ)) : ℤ)))) := by
    ring
  rw [hre, e1', e2', e3']
  simp only [jtpTheta, mul_assoc]
  ring

/-- Finite Jacobi triple product, `ℕ`-indexed. -/
private lemma jtpFiniteSum (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0) (N : ℕ) :
    jtpProdL Q w N =
    ∑ k ∈ Finset.range (2 * N + 1),
      gaussBinom Q (2 * N) k * jtpTheta Q w ((k : ℤ) - (N : ℤ)) := by
  have hN3 := jtpRothe Q (-(w * (Q ^ N)⁻¹)) (2 * N)
  have hN4 := jtpReflect Q w hQ hw N
  have hprod_eq : (∏ j ∈ Finset.range (2 * N), (1 + (-(w * (Q ^ N)⁻¹)) * Q ^ j)) =
      ∏ j ∈ Finset.range (2 * N), (1 - w * (Q ^ N)⁻¹ * Q ^ j) := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  have hSC : (∑ k ∈ Finset.range (2 * N + 1),
        gaussBinom Q (2 * N) k * Q ^ (k.choose 2) * (-(w * (Q ^ N)⁻¹)) ^ k) =
      (-w) ^ N * (Q ^ ((N + 1).choose 2))⁻¹ * jtpProdL Q w N := by
    rw [← hN3, hprod_eq]
    exact hN4
  have hC : (-w) ^ N * (Q ^ ((N + 1).choose 2))⁻¹ ≠ 0 := by
    apply mul_ne_zero
    · exact pow_ne_zero N (jtpNeg_ne_zero hw)
    · exact inv_ne_zero (pow_ne_zero _ hQ)
  have hL : jtpProdL Q w N = (((-w) ^ N * (Q ^ ((N + 1).choose 2))⁻¹)⁻¹) *
      (∑ k ∈ Finset.range (2 * N + 1),
        gaussBinom Q (2 * N) k * Q ^ (k.choose 2) * (-(w * (Q ^ N)⁻¹)) ^ k) := by
    rw [hSC]
    exact (inv_mul_cancel_left₀ hC _).symm
  have hCinv : (((-w) ^ N * (Q ^ ((N + 1).choose 2))⁻¹)⁻¹) =
      ((-w) ^ N)⁻¹ * Q ^ ((N + 1).choose 2) := by
    rw [mul_inv_rev, inv_inv]
    ring
  rw [hL, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [hCinv]
  have hre : (((-w) ^ N)⁻¹ * Q ^ ((N + 1).choose 2)) *
      (gaussBinom Q (2 * N) k * Q ^ (k.choose 2) * (-(w * (Q ^ N)⁻¹)) ^ k) =
      gaussBinom Q (2 * N) k *
      ((((-w) ^ N)⁻¹ * Q ^ ((N + 1).choose 2) * Q ^ (k.choose 2) *
      (-(w * (Q ^ N)⁻¹)) ^ k)) := by
    ring
  rw [hre, jtpTermId Q w hQ hw N k]

end FiniteJTP

section FinHasSum

open scoped BigOperators

private lemma jtpFin_hasSum (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0) (N : ℕ) :
    HasSum (jtpFin Q w N) (jtpProdL Q w N) := by
  have hN5 := jtpFiniteSum Q w hQ hw N
  have hsupp : ∀ n : ℤ, n ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → jtpFin Q w N n = 0 := by
    intro n hn
    have hneg : ¬ n.natAbs ≤ N := by
      rw [Finset.mem_Icc] at hn
      omega
    simp only [jtpFin]
    rw [ite_eq_right hneg]
  have hsum_eq : (∑ k ∈ Finset.range (2 * N + 1),
        gaussBinom Q (2 * N) k * jtpTheta Q w ((k : ℤ) - (N : ℤ))) =
      ∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), jtpFin Q w N n := by
    apply Finset.sum_nbij' (fun k : ℕ => (k : ℤ) - (N : ℤ))
      (fun n : ℤ => (n + (N : ℤ)).toNat)
    · intro k hk
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      constructor <;> omega
    · intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      have hnn : (0 : ℤ) ≤ n + (N : ℤ) := by omega
      have hval : ((n + (N : ℤ)).toNat : ℤ) = n + (N : ℤ) :=
        Int.toNat_of_nonneg hnn
      have hlt : ((n + (N : ℤ)).toNat : ℤ) < (((2 * N + 1 : ℕ)) : ℤ) := by
        rw [hval]
        push_cast
        omega
      exact_mod_cast hlt
    · intro k hk
      have hkk : ((k : ℤ) - (N : ℤ)) + (N : ℤ) = (k : ℤ) := by ring
      rw [hkk, Int.toNat_natCast]
    · intro n hn
      rw [Finset.mem_Icc] at hn
      have hnn : (0 : ℤ) ≤ n + (N : ℤ) := by omega
      have hval : ((n + (N : ℤ)).toNat : ℤ) = n + (N : ℤ) :=
        Int.toNat_of_nonneg hnn
      change ((n + (N : ℤ)).toNat : ℤ) - (N : ℤ) = n
      rw [hval]
      ring
    · intro k hk
      rw [Finset.mem_range] at hk
      have hle : ((k : ℤ) - (N : ℤ)).natAbs ≤ N := by
        have h1 : (-(N : ℤ)) ≤ (k : ℤ) - (N : ℤ) := by omega
        have h2 : (k : ℤ) - (N : ℤ) ≤ (N : ℤ) := by omega
        omega
      have hkk : ((k : ℤ) - (N : ℤ)) + (N : ℤ) = (k : ℤ) := by ring
      simp only [jtpFin]
      rw [ite_eq_left hle, hkk, Int.toNat_natCast]
  have hHS : HasSum (jtpFin Q w N)
      (∑ n ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), jtpFin Q w N n) :=
    hasSum_sum_of_ne_finset_zero hsupp
  rw [← hsum_eq, ← hN5] at hHS
  exact hHS

end FinHasSum

section ThetaSummable

open scoped BigOperators

private lemma jtpTheta_summable_norm (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0)
    (hq : ‖Q‖ < 1) : Summable (fun n : ℤ => ‖jtpTheta Q w n‖) := by
  have hQn : (‖Q‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hQ
  have hwn : (‖w‖ : ℝ) ≠ 0 := norm_ne_zero_iff.mpr hw
  have hr0 : (0 : ℝ) ≤ ‖Q‖ := norm_nonneg _
  have hpos : ∀ n : ℤ, jtpTheta Q w n ≠ 0 := jtpTheta_ne_zero hQ hw
  have hnorm_eq : ∀ m : ℤ, ‖(‖jtpTheta Q w m‖ : ℝ)‖ = ‖jtpTheta Q w m‖ := by
    intro m
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have hpow0 : Filter.Tendsto (fun n : ℕ => (‖Q‖ : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hq
  have hpos_half : Summable (fun n : ℕ => ‖jtpTheta Q w (n : ℤ)‖) := by
    refine summable_of_ratio_test_tendsto_lt_one zero_lt_one ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun n => norm_ne_zero_iff.mpr (hpos _))
    · have hratio : ∀ n : ℕ,
          (‖jtpTheta Q w (((n + 1 : ℕ)) : ℤ)‖) / (‖jtpTheta Q w (n : ℤ)‖) =
          ‖Q‖ ^ ((n : ℤ)) * ‖w‖ := by
        intro n
        have hcast : (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 := by
          simp only [Nat.cast_add, Nat.cast_one]
        have hT : jtpTri (((n + 1 : ℕ)) : ℤ) = jtpTri ((n : ℤ)) + (n : ℤ) := by
          rw [hcast]
          exact jtpTri_succ _
        rw [jtpTheta_norm, jtpTheta_norm, hT, hcast, zpow_add₀ hQn, zpow_add₀ hwn,
          zpow_one]
        have hQz : (‖Q‖ : ℝ) ^ (jtpTri (n : ℤ)) ≠ 0 := zpow_ne_zero _ hQn
        have hwz : (‖w‖ : ℝ) ^ ((n : ℤ)) ≠ 0 := zpow_ne_zero _ hwn
        have hden : (‖Q‖ : ℝ) ^ (jtpTri (n : ℤ)) * ‖w‖ ^ ((n : ℤ)) ≠ 0 :=
          mul_ne_zero hQz hwz
        rw [div_eq_iff hden]
        ring
      have hlim : Filter.Tendsto (fun n : ℕ => ‖Q‖ ^ ((n : ℤ)) * ‖w‖)
          Filter.atTop (nhds 0) := by
        have h1 : Filter.Tendsto (fun n : ℕ => (‖Q‖ : ℝ) ^ n * ‖w‖)
            Filter.atTop (nhds (0 * ‖w‖)) := hpow0.mul_const _
        rw [zero_mul] at h1
        simpa only [zpow_natCast] using h1
      have hEq : ∀ n : ℕ, ‖(‖jtpTheta Q w (((n + 1 : ℕ)) : ℤ)‖ : ℝ)‖ /
          ‖(‖jtpTheta Q w (n : ℤ)‖ : ℝ)‖ = ‖Q‖ ^ ((n : ℤ)) * ‖w‖ := by
        intro n
        rw [hnorm_eq, hnorm_eq, hratio]
      exact hlim.congr (fun n => (hEq n).symm)
  have hTneg : ∀ n : ℕ, jtpTri (-(((n + 1 : ℕ)) : ℤ)) =
      jtpTri (-((n : ℤ))) + (((n + 1 : ℕ)) : ℤ) := by
    intro n
    have hcast : (-(((n + 1 : ℕ)) : ℤ)) = -(((n : ℤ)) + 1) := by
      simp only [Nat.cast_add, Nat.cast_one]
    have h1 : jtpTri (-(((n + 1 : ℕ)) : ℤ)) = jtpTri (((n : ℤ)) + 1 + 1) := by
      rw [hcast]
      exact jtpTri_neg _
    have h2 : jtpTri (-((n : ℤ))) = jtpTri (((n : ℤ)) + 1) := jtpTri_neg _
    have h3 := jtpTri_succ ((n : ℤ) + 1)
    have hcast2 : (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
    rw [h1, h2, h3, hcast2]
  have hneg_half : Summable (fun n : ℕ => ‖jtpTheta Q w (-((n : ℤ)))‖) := by
    refine summable_of_ratio_test_tendsto_lt_one zero_lt_one ?_ ?_
    · exact Filter.Eventually.of_forall
        (fun n => norm_ne_zero_iff.mpr (hpos _))
    · have hratio : ∀ n : ℕ,
          (‖jtpTheta Q w (-(((n + 1 : ℕ)) : ℤ))‖) / (‖jtpTheta Q w (-((n : ℤ)))‖) =
          ‖Q‖ ^ ((((n + 1 : ℕ)) : ℤ)) * ‖w‖ ^ ((-1 : ℤ)) := by
        intro n
        have hT := hTneg n
        have hw_exp : (-(((n + 1 : ℕ)) : ℤ)) = (-((n : ℤ))) + (-1) := by
          simp only [Nat.cast_add, Nat.cast_one]
          ring
        rw [jtpTheta_norm, jtpTheta_norm, hT, hw_exp, zpow_add₀ hQn, zpow_add₀ hwn]
        have hQz : (‖Q‖ : ℝ) ^ (jtpTri (-((n : ℤ)))) ≠ 0 := zpow_ne_zero _ hQn
        have hwz : (‖w‖ : ℝ) ^ (-((n : ℤ))) ≠ 0 := zpow_ne_zero _ hwn
        have hden : (‖Q‖ : ℝ) ^ (jtpTri (-((n : ℤ)))) * ‖w‖ ^ (-((n : ℤ))) ≠ 0 :=
          mul_ne_zero hQz hwz
        rw [div_eq_iff hden]
        ring
      have hlim : Filter.Tendsto
          (fun n : ℕ => ‖Q‖ ^ ((((n + 1 : ℕ)) : ℤ)) * ‖w‖ ^ ((-1 : ℤ)))
          Filter.atTop (nhds 0) := by
        have h0 : Filter.Tendsto (fun n : ℕ => (‖Q‖ : ℝ) ^ (n + 1)) Filter.atTop
            (nhds 0) := by
          have hmul : Filter.Tendsto (fun n : ℕ => (‖Q‖ : ℝ) * ‖Q‖ ^ n)
              Filter.atTop (nhds (‖Q‖ * 0)) := hpow0.const_mul _
          rw [mul_zero] at hmul
          simpa only [pow_succ'] using hmul
        have h1 : Filter.Tendsto
            (fun n : ℕ => (‖Q‖ : ℝ) ^ (n + 1) * ‖w‖ ^ ((-1 : ℤ)))
            Filter.atTop (nhds (0 * ‖w‖ ^ ((-1 : ℤ)))) := h0.mul_const _
        rw [zero_mul] at h1
        simpa only [zpow_natCast] using h1
      have hEq : ∀ n : ℕ, ‖(‖jtpTheta Q w (-(((n + 1 : ℕ)) : ℤ))‖ : ℝ)‖ /
          ‖(‖jtpTheta Q w (-((n : ℤ)))‖ : ℝ)‖ =
          ‖Q‖ ^ ((((n + 1 : ℕ)) : ℤ)) * ‖w‖ ^ ((-1 : ℤ)) := by
        intro n
        rw [hnorm_eq, hnorm_eq, hratio]
      exact hlim.congr (fun n => (hEq n).symm)
  have hneg_half' : Summable (fun n : ℕ => (fun m : ℤ => ‖jtpTheta Q w m‖) (-(n : ℤ))) :=
    hneg_half
  have hpos_half' : Summable (fun n : ℕ => (fun m : ℤ => ‖jtpTheta Q w m‖) ((n : ℤ))) :=
    hpos_half
  exact Summable.of_nat_of_neg hpos_half' hneg_half'

private lemma jtpTheta_summable (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0)
    (hq : ‖Q‖ < 1) : Summable (jtpTheta Q w) :=
  (jtpTheta_summable_norm Q w hQ hw hq).of_norm

end ThetaSummable

section PochFacts

open scoped BigOperators

private lemma jtpPoch_factor_ne_zero (Q : ℂ) (hq : ‖Q‖ < 1) (j : ℕ) :
    (1 : ℂ) - Q ^ (j + 1) ≠ 0 := by
  intro hcon
  have h1 : Q ^ (j + 1) = 1 := (sub_eq_zero.mp hcon).symm
  have h2 : ‖Q ^ (j + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hq (by omega)
  rw [h1, norm_one] at h2
  exact lt_irrefl 1 h2

private lemma jtpPoch_ne_zero (Q : ℂ) (hq : ‖Q‖ < 1) (m : ℕ) :
    qPochFin Q m ≠ 0 := by
  simp only [qPochFin]
  rw [Finset.prod_ne_zero_iff]
  intro j _
  exact jtpPoch_factor_ne_zero Q hq j

private lemma jtpPoch_summable_norm (Q : ℂ) (hq : ‖Q‖ < 1) :
    Summable (fun j : ℕ => ‖Q ^ (j + 1)‖) := by
  have hgeo : Summable (fun j : ℕ => (‖Q‖ : ℝ) ^ j) :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hmul := hgeo.mul_left ‖Q‖
  refine hmul.congr (fun j => ?_)
  rw [norm_pow, pow_succ']

private lemma jtpPoch_multipliable (Q : ℂ) (hq : ‖Q‖ < 1) :
    Multipliable (fun j : ℕ => (1 : ℂ) - Q ^ (j + 1)) :=
  multipliable_one_sub_of_summable (jtpPoch_summable_norm Q hq)

/-- The infinite q-Pochhammer value `P∞`. -/
private noncomputable def jtpPochInf (Q : ℂ) : ℂ :=
  ∏' j : ℕ, ((1 : ℂ) - Q ^ (j + 1))

private lemma jtpPoch_tendsto (Q : ℂ) (hq : ‖Q‖ < 1) :
    Filter.Tendsto (fun m : ℕ => qPochFin Q m) Filter.atTop (nhds (jtpPochInf Q)) := by
  have h := (jtpPoch_multipliable Q hq).tendsto_prod_tprod_nat
  simpa only [qPochFin, jtpPochInf] using h

private lemma jtpPochInf_ne_zero (Q : ℂ) (hq : ‖Q‖ < 1) : jtpPochInf Q ≠ 0 := by
  have hfac : ∀ j : ℕ, (1 : ℂ) + (-Q ^ (j + 1)) ≠ 0 := by
    intro j
    have h := jtpPoch_factor_ne_zero Q hq j
    simpa only [sub_eq_add_neg] using h
  have hsum : Summable (fun j : ℕ => ‖(-Q ^ (j + 1) : ℂ)‖) := by
    have h := jtpPoch_summable_norm Q hq
    simpa only [norm_neg] using h
  have hne := tprod_one_add_ne_zero_of_summable hfac hsum
  have heq : jtpPochInf Q = ∏' j : ℕ, ((1 : ℂ) + (-Q ^ (j + 1))) := by
    simp only [jtpPochInf, sub_eq_add_neg]
  rw [heq]
  exact hne

end PochFacts

section GaussBound

open scoped BigOperators

private lemma jtpProd_le_prod {f g : ℕ → ℝ} : ∀ (s : Finset ℕ),
    (∀ i ∈ s, 0 ≤ f i) → (∀ i ∈ s, 0 ≤ g i) → (∀ i ∈ s, f i ≤ g i) →
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, g i := by
  intro s
  induction s using Finset.induction with
  | empty =>
    intro _ _ _
    simp only [Finset.prod_empty, le_refl]
  | insert a s has IH =>
    intro hf hg h
    rw [Finset.prod_insert has, Finset.prod_insert has]
    apply mul_le_mul
    · exact h a (Finset.mem_insert_self a s)
    · exact IH (fun i hi => hf i (Finset.mem_insert_of_mem hi))
        (fun i hi => hg i (Finset.mem_insert_of_mem hi))
        (fun i hi => h i (Finset.mem_insert_of_mem hi))
    · exact Finset.prod_nonneg (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    · exact hg a (Finset.mem_insert_self a s)

private lemma jtpGeom_partial (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ j ∈ Finset.range m, r ^ j ≤ (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  have hpos : (0 : ℝ) < 1 - r := by linarith
  have h1 : (1 : ℝ) - r ≠ 0 := ne_of_gt hpos
  have h2 : (r : ℝ) - 1 ≠ 0 := by
    intro hcon
    apply hne
    linarith
  have e : (r ^ m - 1) / (r - 1) = (1 - r ^ m) / (1 - r) := by
    rw [div_eq_div_iff h2 h1]
    ring
  rw [geom_sum_eq hne, e, div_le_iff₀ hpos, inv_mul_cancel₀ h1]
  have hnn : (0 : ℝ) ≤ r ^ m := pow_nonneg hr0 m
  linarith

private lemma jtpGeom_shift (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (m : ℕ) :
    ∑ j ∈ Finset.range m, r ^ (j + 1) ≤ r / (1 - r) := by
  have h1 : ∑ j ∈ Finset.range m, r ^ (j + 1) = r * ∑ j ∈ Finset.range m, r ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_succ']
  have h2 : ∑ j ∈ Finset.range m, r ^ j ≤ (1 - r)⁻¹ := jtpGeom_partial r hr0 hr1 m
  have h3 : r * ∑ j ∈ Finset.range m, r ^ j ≤ r * (1 - r)⁻¹ :=
    mul_le_mul_of_nonneg_left h2 hr0
  have heq : r * (1 - r)⁻¹ = r / (1 - r) := by rw [div_eq_mul_inv]
  rw [h1, ← heq]
  exact h3

private lemma jtpPoch_norm_le (Q : ℂ) (hq : ‖Q‖ < 1) (m : ℕ) :
    ‖qPochFin Q m‖ ≤ Real.exp (‖Q‖ / (1 - ‖Q‖)) := by
  have hr0 : (0 : ℝ) ≤ ‖Q‖ := norm_nonneg _
  have hfact : ∀ j : ℕ, ‖(1 : ℂ) - Q ^ (j + 1)‖ ≤
      Real.exp ((‖Q‖ : ℝ) ^ (j + 1)) := by
    intro j
    have h1 : ‖(1 : ℂ) - Q ^ (j + 1)‖ ≤ 1 + ‖Q ^ (j + 1)‖ := by
      have h := norm_sub_le (1 : ℂ) (Q ^ (j + 1))
      rwa [norm_one] at h
    have h2 : (1 : ℝ) + ‖Q ^ (j + 1)‖ = 1 + ‖Q‖ ^ (j + 1) := by rw [norm_pow]
    have h3 : (1 : ℝ) + ‖Q‖ ^ (j + 1) ≤ Real.exp (‖Q‖ ^ (j + 1)) := by
      have h := Real.add_one_le_exp ((‖Q‖ : ℝ) ^ (j + 1))
      linarith
    rw [h2] at h1
    exact le_trans h1 h3
  have hstep : ‖qPochFin Q m‖ ≤
      ∏ j ∈ Finset.range m, Real.exp ((‖Q‖ : ℝ) ^ (j + 1)) := by
    simp only [qPochFin, norm_prod]
    exact jtpProd_le_prod _ (fun j _ => norm_nonneg _)
      (fun j _ => le_of_lt (Real.exp_pos _)) (fun j _ => hfact j)
  have hexp : (∏ j ∈ Finset.range m, Real.exp ((‖Q‖ : ℝ) ^ (j + 1))) =
      Real.exp (∑ j ∈ Finset.range m, (‖Q‖ : ℝ) ^ (j + 1)) :=
    (Real.exp_sum _ _).symm
  rw [hexp] at hstep
  refine le_trans hstep (Real.exp_le_exp.mpr ?_)
  exact jtpGeom_shift ‖Q‖ hr0 hq m

private lemma jtpPoch_inv_norm_le (Q : ℂ) (hq : ‖Q‖ < 1) (m : ℕ) :
    (‖qPochFin Q m‖)⁻¹ ≤ Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) := by
  have hr0 : (0 : ℝ) ≤ ‖Q‖ := norm_nonneg _
  have h1r : (0 : ℝ) < 1 - ‖Q‖ := by linarith
  have hnorm_eq : ‖qPochFin Q m‖ =
      ∏ j ∈ Finset.range m, ‖(1 : ℂ) - Q ^ (j + 1)‖ := by
    simp only [qPochFin, norm_prod]
  have hfact : ∀ j : ℕ, (‖(1 : ℂ) - Q ^ (j + 1)‖)⁻¹ ≤
      Real.exp ((‖Q‖ : ℝ) ^ (j + 1) / (1 - ‖Q‖)) := by
    intro j
    have hsr : (‖Q‖ : ℝ) ^ (j + 1) ≤ ‖Q‖ := by
      have h1j : (1 : ℕ) ≤ j + 1 := by omega
      have h := pow_le_pow_of_le_one hr0 hq.le h1j
      rwa [pow_one] at h
    have h1s : (0 : ℝ) < 1 - ‖Q‖ ^ (j + 1) := by
      have hlt : (‖Q‖ : ℝ) ^ (j + 1) < 1 := pow_lt_one₀ hr0 hq (by omega)
      linarith
    have hfac_ge : (1 : ℝ) - ‖Q‖ ^ (j + 1) ≤ ‖(1 : ℂ) - Q ^ (j + 1)‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (Q ^ (j + 1))
      rwa [norm_one, norm_pow] at h
    have hfac_pos : (0 : ℝ) < ‖(1 : ℂ) - Q ^ (j + 1)‖ :=
      lt_of_lt_of_le h1s hfac_ge
    have hstep1 : (‖(1 : ℂ) - Q ^ (j + 1)‖)⁻¹ ≤ (1 - ‖Q‖ ^ (j + 1))⁻¹ :=
      (inv_le_inv₀ hfac_pos h1s).mpr hfac_ge
    have hstep2 : ((1 : ℝ) - ‖Q‖ ^ (j + 1))⁻¹ ≤
        Real.exp ((‖Q‖ : ℝ) ^ (j + 1) / (1 - ‖Q‖)) := by
      have hexp1 : (1 : ℝ) + (‖Q‖ ^ (j + 1) / (1 - ‖Q‖ ^ (j + 1))) ≤
          Real.exp (‖Q‖ ^ (j + 1) / (1 - ‖Q‖ ^ (j + 1))) := by
        have h := Real.add_one_le_exp (‖Q‖ ^ (j + 1) / (1 - ‖Q‖ ^ (j + 1)))
        linarith
      have heq : (1 : ℝ) + (‖Q‖ ^ (j + 1) / (1 - ‖Q‖ ^ (j + 1))) =
          (1 - ‖Q‖ ^ (j + 1))⁻¹ := by
        have hne : (1 : ℝ) - ‖Q‖ ^ (j + 1) ≠ 0 := ne_of_gt h1s
        field_simp
        ring
      have hmono : ‖Q‖ ^ (j + 1) / (1 - ‖Q‖ ^ (j + 1)) ≤
          ‖Q‖ ^ (j + 1) / (1 - ‖Q‖) := by
        have hle : (1 : ℝ) - ‖Q‖ ≤ 1 - ‖Q‖ ^ (j + 1) := by linarith [hsr]
        have hs0 : (0 : ℝ) ≤ ‖Q‖ ^ (j + 1) := pow_nonneg hr0 _
        rw [div_le_div_iff₀ h1s h1r]
        exact mul_le_mul_of_nonneg_left hle hs0
      calc ((1 : ℝ) - ‖Q‖ ^ (j + 1))⁻¹
          = 1 + (‖Q‖ ^ (j + 1) / (1 - ‖Q‖ ^ (j + 1))) := heq.symm
        _ ≤ Real.exp (‖Q‖ ^ (j + 1) / (1 - ‖Q‖ ^ (j + 1))) := hexp1
        _ ≤ Real.exp (‖Q‖ ^ (j + 1) / (1 - ‖Q‖)) :=
            Real.exp_le_exp.mpr hmono
    exact le_trans hstep1 hstep2
  have hstep : (‖qPochFin Q m‖)⁻¹ ≤
      ∏ j ∈ Finset.range m, Real.exp ((‖Q‖ : ℝ) ^ (j + 1) / (1 - ‖Q‖)) := by
    rw [hnorm_eq, ← Finset.prod_inv_distrib]
    exact jtpProd_le_prod _ (fun j _ => inv_nonneg.mpr (norm_nonneg _))
      (fun j _ => le_of_lt (Real.exp_pos _)) (fun j _ => hfact j)
  have hexp : (∏ j ∈ Finset.range m, Real.exp ((‖Q‖ : ℝ) ^ (j + 1) / (1 - ‖Q‖))) =
      Real.exp (∑ j ∈ Finset.range m, (‖Q‖ : ℝ) ^ (j + 1) / (1 - ‖Q‖)) :=
    (Real.exp_sum _ _).symm
  rw [hexp] at hstep
  refine le_trans hstep (Real.exp_le_exp.mpr ?_)
  have h1 : ∑ j ∈ Finset.range m, (‖Q‖ : ℝ) ^ (j + 1) / (1 - ‖Q‖) =
      (∑ j ∈ Finset.range m, (‖Q‖ : ℝ) ^ (j + 1)) / (1 - ‖Q‖) := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul]
  have h2 := jtpGeom_shift ‖Q‖ hr0 hq m
  have h3 : (∑ j ∈ Finset.range m, (‖Q‖ : ℝ) ^ (j + 1)) / (1 - ‖Q‖) ≤
      (‖Q‖ / (1 - ‖Q‖)) / (1 - ‖Q‖) := by
    rw [div_le_div_iff₀ h1r h1r]
    exact mul_le_mul_of_nonneg_right h2 (le_of_lt h1r)
  have heq : (‖Q‖ / (1 - ‖Q‖)) / (1 - ‖Q‖) = ‖Q‖ / (1 - ‖Q‖) ^ 2 := by
    rw [div_div, pow_two]
  rw [h1]
  exact le_trans h3 (le_of_eq heq)

/-- Uniform bound on Gaussian binomials. -/
private lemma jtpGauss_norm_le (Q : ℂ) (hq : ‖Q‖ < 1) (M k : ℕ) :
    ‖gaussBinom Q M k‖ ≤
    Real.exp (‖Q‖ / (1 - ‖Q‖)) * Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) *
      Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) := by
  by_cases hkM : k ≤ M
  · have hPk : qPochFin Q k ≠ 0 := jtpPoch_ne_zero Q hq k
    have hPm : qPochFin Q (M - k) ≠ 0 := jtpPoch_ne_zero Q hq (M - k)
    have hclosed := gaussBinom_mul_qPochFin_mul_qPochFin Q M k hkM
    have hG : gaussBinom Q M k =
        qPochFin Q M / (qPochFin Q k * qPochFin Q (M - k)) := by
      rw [eq_div_iff (mul_ne_zero hPk hPm)]
      have hassoc : gaussBinom Q M k * (qPochFin Q k * qPochFin Q (M - k)) =
          gaussBinom Q M k * qPochFin Q k * qPochFin Q (M - k) := by ring
      rw [hassoc]
      exact hclosed
    have hU : ‖qPochFin Q M‖ ≤ Real.exp (‖Q‖ / (1 - ‖Q‖)) :=
      jtpPoch_norm_le Q hq M
    have hV1 : (‖qPochFin Q k‖)⁻¹ ≤ Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) :=
      jtpPoch_inv_norm_le Q hq k
    have hV2 : (‖qPochFin Q (M - k)‖)⁻¹ ≤ Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) :=
      jtpPoch_inv_norm_le Q hq (M - k)
    have hnorm : ‖gaussBinom Q M k‖ =
        ‖qPochFin Q M‖ * (‖qPochFin Q k‖)⁻¹ * (‖qPochFin Q (M - k)‖)⁻¹ := by
      rw [hG, norm_div, norm_mul, div_eq_mul_inv, mul_inv_rev]
      ring
    have hn2 : (0 : ℝ) ≤ (‖qPochFin Q k‖)⁻¹ := inv_nonneg.mpr (norm_nonneg _)
    have he1 : (0 : ℝ) ≤ Real.exp (‖Q‖ / (1 - ‖Q‖)) := le_of_lt (Real.exp_pos _)
    have he2 : (0 : ℝ) ≤ Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) := le_of_lt (Real.exp_pos _)
    rw [hnorm]
    exact mul_le_mul (mul_le_mul hU hV1 hn2 he1) hV2
      (inv_nonneg.mpr (norm_nonneg _))
      (mul_nonneg he1 he2)
  · have hG0 : gaussBinom Q M k = 0 := gaussBinom_eq_zero_of_lt Q M k (by omega)
    rw [hG0, norm_zero]
    have he1 : (0 : ℝ) ≤ Real.exp (‖Q‖ / (1 - ‖Q‖)) := le_of_lt (Real.exp_pos _)
    have he2 : (0 : ℝ) ≤ Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) := le_of_lt (Real.exp_pos _)
    exact mul_nonneg (mul_nonneg he1 he2) he2

end GaussBound

section GaussLimit

open scoped BigOperators

private lemma jtpGauss_tendsto (Q : ℂ) (hq : ‖Q‖ < 1) (a b : ℕ → ℕ)
    (ha : Filter.Tendsto a Filter.atTop Filter.atTop)
    (hb : Filter.Tendsto b Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun N : ℕ => gaussBinom Q (a N + b N) (a N)) Filter.atTop
      (nhds (jtpPochInf Q)⁻¹) := by
  have hPne : jtpPochInf Q ≠ 0 := jtpPochInf_ne_zero Q hq
  have hform : ∀ N : ℕ, gaussBinom Q (a N + b N) (a N) =
      qPochFin Q (a N + b N) / (qPochFin Q (a N) * qPochFin Q (b N)) := by
    intro N
    have hclosed := gaussBinom_mul_qPochFin_mul_qPochFin Q (a N + b N) (a N) (Nat.le_add_right _ _)
    have hsub : a N + b N - a N = b N := Nat.add_sub_cancel_left _ _
    rw [hsub] at hclosed
    have hPa : qPochFin Q (a N) ≠ 0 := jtpPoch_ne_zero Q hq _
    have hPb : qPochFin Q (b N) ≠ 0 := jtpPoch_ne_zero Q hq _
    rw [eq_div_iff (mul_ne_zero hPa hPb)]
    have hassoc : gaussBinom Q (a N + b N) (a N) *
        (qPochFin Q (a N) * qPochFin Q (b N)) =
        gaussBinom Q (a N + b N) (a N) * qPochFin Q (a N) * qPochFin Q (b N) := by
      ring
    rw [hassoc]
    exact hclosed
  have hab : Filter.Tendsto (fun N : ℕ => a N + b N) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun N => Nat.le_add_right (a N) (b N)) ha
  have h1 : Filter.Tendsto (fun N : ℕ => qPochFin Q (a N + b N)) Filter.atTop
      (nhds (jtpPochInf Q)) :=
    (jtpPoch_tendsto Q hq).comp hab
  have h2 : Filter.Tendsto (fun N : ℕ => qPochFin Q (a N)) Filter.atTop
      (nhds (jtpPochInf Q)) :=
    (jtpPoch_tendsto Q hq).comp ha
  have h3 : Filter.Tendsto (fun N : ℕ => qPochFin Q (b N)) Filter.atTop
      (nhds (jtpPochInf Q)) :=
    (jtpPoch_tendsto Q hq).comp hb
  have h23 : Filter.Tendsto (fun N : ℕ => qPochFin Q (a N) * qPochFin Q (b N))
      Filter.atTop (nhds (jtpPochInf Q * jtpPochInf Q)) := h2.mul h3
  have hdiv : Filter.Tendsto
      (fun N : ℕ => qPochFin Q (a N + b N) / (qPochFin Q (a N) * qPochFin Q (b N)))
      Filter.atTop (nhds (jtpPochInf Q / (jtpPochInf Q * jtpPochInf Q))) :=
    h1.div h23 (mul_ne_zero hPne hPne)
  have heq : jtpPochInf Q / (jtpPochInf Q * jtpPochInf Q) = (jtpPochInf Q)⁻¹ := by
    rw [div_eq_mul_inv, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hPne, one_mul]
  rw [heq] at hdiv
  exact hdiv.congr (fun N => (hform N).symm)

end GaussLimit

section TanneryLimit

open scoped BigOperators

private lemma jtpToNat_tendsto (c : ℤ) :
    Filter.Tendsto (fun N : ℕ => (c + (N : ℤ)).toNat) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨b + c.natAbs, fun N hN => ?_⟩
  have h1 : (0 : ℤ) ≤ c + (N : ℤ) := by omega
  have h2 : (((c + (N : ℤ)).toNat : ℕ) : ℤ) = c + (N : ℤ) :=
    Int.toNat_of_nonneg h1
  have h3 : (b : ℤ) ≤ c + (N : ℤ) := by omega
  have h4 : (b : ℤ) ≤ (((c + (N : ℤ)).toNat : ℕ) : ℤ) := by rw [h2]; exact h3
  exact_mod_cast h4

private lemma jtpTannery (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0) (hq : ‖Q‖ < 1) :
    Filter.Tendsto (fun N : ℕ => ∑' n : ℤ, jtpFin Q w N n) Filter.atTop
      (nhds ((jtpPochInf Q)⁻¹ * ∑' n : ℤ, jtpTheta Q w n)) := by
  have hB : ∀ M k : ℕ, ‖gaussBinom Q M k‖ ≤
      Real.exp (‖Q‖ / (1 - ‖Q‖)) * Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) *
      Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) := jtpGauss_norm_le Q hq
  set B : ℝ := Real.exp (‖Q‖ / (1 - ‖Q‖)) * Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) *
      Real.exp (‖Q‖ / (1 - ‖Q‖) ^ 2) with hBdef
  have hBnn : (0 : ℝ) ≤ B := by
    rw [hBdef]
    exact mul_nonneg
      (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _)))
      (le_of_lt (Real.exp_pos _))
  have hsum_norm := jtpTheta_summable_norm Q w hQ hw hq
  have hbound_sum : Summable (fun n : ℤ => B * ‖jtpTheta Q w n‖) :=
    hsum_norm.mul_left B
  have hdom : ∀ᶠ N : ℕ in Filter.atTop,
      ∀ n : ℤ, ‖jtpFin Q w N n‖ ≤ B * ‖jtpTheta Q w n‖ := by
    apply Filter.Eventually.of_forall
    intro N n
    simp only [jtpFin]
    by_cases hn : n.natAbs ≤ N
    · rw [ite_eq_left hn, norm_mul]
      exact mul_le_mul_of_nonneg_right (hB _ _) (norm_nonneg _)
    · rw [ite_eq_right hn, norm_zero]
      exact mul_nonneg hBnn (norm_nonneg _)
  have hpt : ∀ n : ℤ, Filter.Tendsto (fun N : ℕ => jtpFin Q w N n) Filter.atTop
      (nhds ((jtpPochInf Q)⁻¹ * jtpTheta Q w n)) := by
    intro n
    have ha : Filter.Tendsto (fun N : ℕ => (n + (N : ℤ)).toNat) Filter.atTop
        Filter.atTop := jtpToNat_tendsto n
    have hb : Filter.Tendsto (fun N : ℕ => ((N : ℤ) - n).toNat) Filter.atTop
        Filter.atTop := by
      have h := jtpToNat_tendsto (-n)
      have heq : (fun N : ℕ => ((N : ℤ) - n).toNat) =
          fun N : ℕ => (-n + (N : ℤ)).toNat := by
        ext N
        congr 1
        ring
      rw [heq]
      exact h
    have hGlim := jtpGauss_tendsto Q hq (fun N : ℕ => (n + (N : ℤ)).toNat)
      (fun N : ℕ => ((N : ℤ) - n).toNat) ha hb
    have hlim : Filter.Tendsto
        (fun N : ℕ => gaussBinom Q ((n + (N : ℤ)).toNat + ((N : ℤ) - n).toNat)
          ((n + (N : ℤ)).toNat) * jtpTheta Q w n)
        Filter.atTop (nhds ((jtpPochInf Q)⁻¹ * jtpTheta Q w n)) :=
      hGlim.mul_const _
    have hev : (fun N : ℕ => gaussBinom Q ((n + (N : ℤ)).toNat + ((N : ℤ) - n).toNat)
          ((n + (N : ℤ)).toNat) * jtpTheta Q w n) =ᶠ[Filter.atTop]
        (fun N : ℕ => jtpFin Q w N n) := by
      filter_upwards [Filter.eventually_ge_atTop n.natAbs] with N hN
      simp only [jtpFin]
      have hle : n.natAbs ≤ N := hN
      rw [ite_eq_left hle]
      have h2N : 2 * N = (n + (N : ℤ)).toNat + ((N : ℤ) - n).toNat := by
        have hn1 : (0 : ℤ) ≤ n + (N : ℤ) := by
          have hle' : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
          omega
        have hn2 : (0 : ℤ) ≤ (N : ℤ) - n := by
          have hle' : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hle
          omega
        have hva : (((n + (N : ℤ)).toNat : ℕ) : ℤ) = n + (N : ℤ) :=
          Int.toNat_of_nonneg hn1
        have hvb : ((((N : ℤ) - n).toNat : ℕ) : ℤ) = (N : ℤ) - n :=
          Int.toNat_of_nonneg hn2
        have hcast : (((n + (N : ℤ)).toNat + ((N : ℤ) - n).toNat : ℕ) : ℤ) =
            ((2 * N : ℕ) : ℤ) := by
          push_cast
          rw [hva, hvb]
          ring
        exact (Nat.cast_injective hcast).symm
      rw [h2N]
    exact hlim.congr' hev
  have hTan := tendsto_tsum_of_dominated_convergence hbound_sum hpt hdom
  rw [tsum_mul_left] at hTan
  exact hTan

end TanneryLimit

section Hub

open scoped BigOperators

/-- The hub product family `h(m)`. -/
private noncomputable def jtpHub (Q w : ℂ) (m : ℕ) : ℂ :=
  (1 - Q ^ (m + 1)) * (1 - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1))

private lemma jtpHub_u1 (Q w : ℂ) (hq : ‖Q‖ < 1) :
    Multipliable (fun m : ℕ => (1 : ℂ) - w * Q ^ m) := by
  apply multipliable_one_sub_of_summable
  have hgeo : Summable (fun m : ℕ => (‖Q‖ : ℝ) ^ m) :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hmul := hgeo.mul_left ‖w‖
  refine hmul.congr (fun m => ?_)
  rw [norm_mul, norm_pow]

private lemma jtpHub_u2 (Q w : ℂ) (hq : ‖Q‖ < 1) :
    Multipliable (fun m : ℕ => (1 : ℂ) - w⁻¹ * Q ^ (m + 1)) := by
  apply multipliable_one_sub_of_summable
  have hgeo : Summable (fun m : ℕ => (‖Q‖ : ℝ) ^ m) :=
    summable_geometric_of_lt_one (norm_nonneg _) hq
  have hmul := hgeo.mul_left (‖w‖⁻¹ * ‖Q‖)
  refine hmul.congr (fun m => ?_)
  rw [norm_mul, norm_pow, norm_inv, pow_succ']
  ring

private lemma jtpHub_multipliable (Q w : ℂ) (hq : ‖Q‖ < 1) :
    Multipliable (jtpHub Q w) := by
  have hu1 := jtpHub_u1 Q w hq
  have hu2 := jtpHub_u2 Q w hq
  have hu : Multipliable
      (fun m : ℕ => ((1 : ℂ) - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1))) :=
    hu1.mul hu2
  have hP := jtpPoch_multipliable Q hq
  have hmul := hP.mul hu
  refine hmul.congr (fun m => ?_)
  simp only [jtpHub]
  ring

private lemma jtpHub_hasSum (Q w : ℂ) (hQ : Q ≠ 0) (hw : w ≠ 0) (hq : ‖Q‖ < 1) :
    HasSum (jtpTheta Q w) (∏' m : ℕ, jtpHub Q w m) := by
  have hu1 := jtpHub_u1 Q w hq
  have hu2 := jtpHub_u2 Q w hq
  have hu : Multipliable
      (fun m : ℕ => ((1 : ℂ) - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1))) :=
    hu1.mul hu2
  have hLlim : Filter.Tendsto (fun N : ℕ => jtpProdL Q w N) Filter.atTop
      (nhds (∏' m : ℕ, ((1 : ℂ) - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1)))) := by
    have h := hu.tendsto_prod_tprod_nat
    simpa only [jtpProdL] using h
  have hFeq : ∀ N : ℕ, (∑' n : ℤ, jtpFin Q w N n) = jtpProdL Q w N :=
    fun N => HasSum.tsum_eq (jtpFin_hasSum Q w hQ hw N)
  have hFlim := jtpTannery Q w hQ hw hq
  have hLlim2 : Filter.Tendsto (fun N : ℕ => jtpProdL Q w N) Filter.atTop
      (nhds ((jtpPochInf Q)⁻¹ * ∑' n : ℤ, jtpTheta Q w n)) :=
    hFlim.congr (fun N => hFeq N)
  have huniq := tendsto_nhds_unique hLlim hLlim2
  have hPne : jtpPochInf Q ≠ 0 := jtpPochInf_ne_zero Q hq
  have hPS : (∑' n : ℤ, jtpTheta Q w n) =
      jtpPochInf Q * (∏' m : ℕ, ((1 : ℂ) - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1))) := by
    calc (∑' n : ℤ, jtpTheta Q w n)
        = jtpPochInf Q * ((jtpPochInf Q)⁻¹ * ∑' n : ℤ, jtpTheta Q w n) := by
          rw [← mul_assoc, mul_inv_cancel₀ hPne, one_mul]
      _ = jtpPochInf Q * (∏' m : ℕ, ((1 : ℂ) - w * Q ^ m) *
          (1 - w⁻¹ * Q ^ (m + 1))) := by rw [← huniq]
  have hP := jtpPoch_multipliable Q hq
  have hprod_eq : (∏' m : ℕ, jtpHub Q w m) =
      jtpPochInf Q * (∏' m : ℕ, ((1 : ℂ) - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1))) := by
    have hcongr : (∏' m : ℕ, jtpHub Q w m) =
        ∏' m : ℕ, ((1 - Q ^ (m + 1)) *
          (((1 : ℂ) - w * Q ^ m) * (1 - w⁻¹ * Q ^ (m + 1)))) := by
      apply tprod_congr
      intro m
      simp only [jtpHub]
      ring
    have hteq := hP.tprod_mul hu
    rw [hcongr, hteq]
    simp only [jtpPochInf]
  have hS := jtpTheta_summable Q w hQ hw hq
  have htsum : (∑' n : ℤ, jtpTheta Q w n) = ∏' m : ℕ, jtpHub Q w m := by
    rw [hPS, hprod_eq]
  rw [← htsum]
  exact hS.hasSum

end Hub

/-- **Jacobi triple product identity.** For complex numbers $z \ne 0$ and $q$ with $|q| < 1$,
the bilateral series $\sum_{n \in \mathbb{Z}} z^n q^{n^2}$ is summable, the family of factors
$(1 - q^{2n+2})(1 + z q^{2n+1})(1 + z^{-1} q^{2n+1})$, $n \ge 0$, is multipliable, and

$$\sum_{n \in \mathbb{Z}} z^n q^{n^2} =
\prod_{n \ge 0} (1 - q^{2n+2})(1 + z q^{2n+1})(1 + z^{-1} q^{2n+1}).$$

Proves `Wanted` entry `jacobi_triple_product`.

Source: Aritram Dhar, Avi Mukhopadhyay, and Rishabh Sarma, "Generalization of
the Extended Minimal Excludant of Andrews and Newman," Journal of Integer
Sequences 26 (2023), Article 23.3.7, theorem at source lines 455-458 of
`https://cs.uwaterloo.ca/journals/JIS/VOL26/Sarma/sarma5.tex`.
-/
theorem jacobi_triple_product (z q : ℂ) (hz : z ≠ 0) (hq : ‖q‖ < 1) :
    Summable (fun n : ℤ => z ^ n * q ^ (n * n).toNat) ∧
    Multipliable (fun n : ℕ =>
      (1 - q ^ (2 * n + 2)) * (1 + z * q ^ (2 * n + 1)) *
        (1 + z⁻¹ * q ^ (2 * n + 1))) ∧
    (∑' n : ℤ, z ^ n * q ^ (n * n).toNat) =
      ∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + z * q ^ (2 * n + 1)) *
        (1 + z⁻¹ * q ^ (2 * n + 1)) := by
  refine ⟨summable_int z q hq, multipliable_triple z q hq, ?_⟩
  by_cases hq0 : q = 0
  · subst hq0
    have h0 : (z ^ (0 : ℤ) * (0 : ℂ) ^ (((0 : ℤ) * (0 : ℤ)).toNat)) = 1 := by
      simp only [mul_zero, Int.toNat_zero, pow_zero, zpow_zero, mul_one]
    have hsingle : ∀ n : ℤ, n ≠ 0 → z ^ n * (0 : ℂ) ^ ((n * n).toNat) = 0 := by
      intro n hn
      have hpos : 0 < n * n := by
        rcases lt_trichotomy n 0 with hneg | heq | hpos
        · exact mul_pos_of_neg_of_neg hneg hneg
        · exact absurd heq hn
        · exact mul_pos hpos hpos
      have hne : (n * n).toNat ≠ 0 := by
        intro hcon
        rw [Int.toNat_eq_zero] at hcon
        omega
      rw [zero_pow hne, mul_zero]
    have hsum1 : (∑' n : ℤ, z ^ n * (0 : ℂ) ^ ((n * n).toNat)) = 1 := by
      have h : (∑' n : ℤ, z ^ n * (0 : ℂ) ^ ((n * n).toNat)) =
          z ^ (0 : ℤ) * (0 : ℂ) ^ (((0 : ℤ) * (0 : ℤ)).toNat) :=
        tsum_eq_single 0 hsingle
      rw [h]
      exact h0
    have hprod_one : ∀ m : ℕ,
        (1 - (0 : ℂ) ^ (2 * m + 2)) * (1 + z * (0 : ℂ) ^ (2 * m + 1)) *
          (1 + z⁻¹ * (0 : ℂ) ^ (2 * m + 1)) = 1 := by
      intro m
      have e1 : (0 : ℂ) ^ (2 * m + 2) = 0 := zero_pow (by omega)
      have e2 : (0 : ℂ) ^ (2 * m + 1) = 0 := zero_pow (by omega)
      simp only [e1, e2, mul_zero, add_zero, sub_zero, mul_one]
    have hprod1 : (∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 2)) *
        (1 + z * (0 : ℂ) ^ (2 * n + 1)) *
        (1 + z⁻¹ * (0 : ℂ) ^ (2 * n + 1))) = 1 := by
      have h : (∏' n : ℕ, (1 - (0 : ℂ) ^ (2 * n + 2)) *
          (1 + z * (0 : ℂ) ^ (2 * n + 1)) *
          (1 + z⁻¹ * (0 : ℂ) ^ (2 * n + 1))) = ∏' _ : ℕ, 1 :=
        tprod_congr hprod_one
      rw [h, tprod_one]
    rw [hsum1, hprod1]
  · have hqne : q ≠ 0 := hq0
    have hQ : (q ^ 2 : ℂ) ≠ 0 := pow_ne_zero 2 hqne
    have hw : (-z * q : ℂ) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr hz) hqne
    have hQnorm : ‖(q ^ 2 : ℂ)‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) hq two_ne_zero
    have hHub := jtpHub_hasSum (q ^ 2) (-z * q) hQ hw hQnorm
    have hsum_eq : (∑' n : ℤ, jtpTheta (q ^ 2) (-z * q) n) =
        ∏' m : ℕ, jtpHub (q ^ 2) (-z * q) m := hHub.tsum_eq
    have hsum_congr : ∀ n : ℤ,
        jtpTheta (q ^ 2) (-z * q) n = z ^ n * q ^ ((n * n).toNat) := by
      intro n
      have hneg1 : (-1 : ℂ) ≠ 0 := jtpNeg_ne_zero one_ne_zero
      have hnz : (-z : ℂ) ≠ 0 := neg_ne_zero.mpr hz
      have h2T : 2 * jtpTri n = n * (n - 1) := jtpTri_double n
      have hTri_nn : 0 ≤ jtpTri n := jtpTri_nonneg n
      have hQpow : ((q ^ 2 : ℂ)) ^ (jtpTri n) = q ^ (n * (n - 1)) := by
        have hcast0 : ((((jtpTri n).toNat : ℕ)) : ℤ) = jtpTri n :=
          Int.toNat_of_nonneg hTri_nn
        have h1 : ((q ^ 2 : ℂ)) ^ (jtpTri n) =
            ((q ^ 2 : ℂ)) ^ ((jtpTri n).toNat) := by
          conv_lhs => rw [← hcast0]
          rw [zpow_natCast]
        have h2 : ((q ^ 2 : ℂ)) ^ ((jtpTri n).toNat) =
            q ^ (2 * ((jtpTri n).toNat)) :=
          (pow_mul q 2 ((jtpTri n).toNat)).symm
        have h3 : (q ^ (2 * ((jtpTri n).toNat)) : ℂ) =
            q ^ ((((2 * ((jtpTri n).toNat) : ℕ))) : ℤ) :=
          (zpow_natCast _ _).symm
        have hexp : ((((2 * ((jtpTri n).toNat) : ℕ))) : ℤ) = n * (n - 1) := by
          have h2e : ((((2 * ((jtpTri n).toNat) : ℕ))) : ℤ) =
              2 * ((((jtpTri n).toNat : ℕ)) : ℤ) := by
            push_cast
            ring
          rw [h2e, hcast0]
          exact h2T
        rw [h1, h2, h3, hexp]
      have hw_pow : ((-z * q : ℂ)) ^ n = (-1 : ℂ) ^ n * z ^ n * q ^ n := by
        have hw_eq : (-z * q : ℂ) = (-z) * q := by
          ring
        have hnz_eq : (-z : ℂ) = (-1) * z := by
          ring
        rw [hw_eq, jtpMul_zpow hnz hqne n, hnz_eq,
          jtpMul_zpow hneg1 hz n]
      have hneg_sq : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
        have h := (jtpMul_zpow hneg1 hneg1 n).symm
        have h11 : (-1 : ℂ) * (-1) = 1 := by
          ring
        rw [h, h11, one_zpow]
      have hq_add : q ^ (n * (n - 1)) * q ^ n = q ^ (n * n) := by
        have hexp2 : n * (n - 1) + n = n * n := by
          ring
        rw [← zpow_add₀ hqne, hexp2]
      have hnn : 0 ≤ n * n := mul_self_nonneg n
      have hcast : ((((n * n).toNat : ℕ)) : ℤ) = n * n :=
        Int.toNat_of_nonneg hnn
      have hq_nat : (q ^ (n * n) : ℂ) = q ^ ((n * n).toNat) := by
        conv_lhs => rw [← hcast]
        rw [zpow_natCast]
      have hTheta : jtpTheta (q ^ 2) (-z * q) n =
          (-1 : ℂ) ^ n * ((q ^ 2 : ℂ)) ^ (jtpTri n) * ((-z * q : ℂ)) ^ n :=
        rfl
      rw [hTheta, hQpow, hw_pow]
      have hre : (-1 : ℂ) ^ n * q ^ (n * (n - 1)) *
          ((-1 : ℂ) ^ n * z ^ n * q ^ n) =
          ((-1 : ℂ) ^ n * (-1 : ℂ) ^ n) * z ^ n *
            (q ^ (n * (n - 1)) * q ^ n) := by
        ring
      rw [hre, hneg_sq, one_mul, hq_add, hq_nat]
    have hprod_congr : ∀ m : ℕ,
        jtpHub (q ^ 2) (-z * q) m =
          (1 - q ^ (2 * m + 2)) * (1 + z * q ^ (2 * m + 1)) *
            (1 + z⁻¹ * q ^ (2 * m + 1)) := by
      intro m
      have hQm : ((q ^ 2 : ℂ)) ^ m = q ^ (2 * m) := by
        rw [← pow_mul]
      have hQm1 : ((q ^ 2 : ℂ)) ^ (m + 1) = q ^ (2 * m + 2) := by
        have hexp : 2 * (m + 1) = 2 * m + 2 := by
          omega
        rw [← pow_mul, hexp]
      have h2m1 : (q ^ (2 * m + 1) : ℂ) = q * q ^ (2 * m) :=
        pow_succ' q (2 * m)
      have h2m2 : (q ^ (2 * m + 2) : ℂ) = q * q ^ (2 * m + 1) := by
        have hexp : 2 * m + 2 = (2 * m + 1) + 1 := by
          omega
        rw [hexp]
        exact pow_succ' q (2 * m + 1)
      have hfac2 : (-z * q : ℂ) * (((q ^ 2 : ℂ)) ^ m) =
          -(z * q ^ (2 * m + 1)) := by
        rw [hQm, h2m1]
        ring
      have hfac3 : (-z * q : ℂ)⁻¹ * (((q ^ 2 : ℂ)) ^ (m + 1)) =
          -(z⁻¹ * q ^ (2 * m + 1)) := by
        have hw_inv : ((-z * q : ℂ))⁻¹ = -(z⁻¹ * q⁻¹) := by
          rw [mul_inv_rev, inv_neg]
          ring
        have hcancel : (q⁻¹ : ℂ) * q ^ (2 * m + 2) = q ^ (2 * m + 1) := by
          rw [h2m2, ← mul_assoc, inv_mul_cancel₀ hqne, one_mul]
        rw [hQm1, hw_inv]
        have hre2 : (-(z⁻¹ * q⁻¹) : ℂ) * q ^ (2 * m + 2) =
            -(z⁻¹ * (q⁻¹ * q ^ (2 * m + 2))) := by
          ring
        rw [hre2, hcancel]
      have hHubm : jtpHub (q ^ 2) (-z * q) m =
          (1 - ((q ^ 2 : ℂ)) ^ (m + 1)) *
            (1 - (-z * q) * (((q ^ 2 : ℂ)) ^ m)) *
            (1 - (-z * q)⁻¹ * (((q ^ 2 : ℂ)) ^ (m + 1))) :=
        rfl
      rw [hHubm, hfac2, hfac3, hQm1]
      simp only [sub_neg_eq_add]
    calc (∑' n : ℤ, z ^ n * q ^ ((n * n).toNat)) =
        ∑' n : ℤ, jtpTheta (q ^ 2) (-z * q) n :=
        tsum_congr (fun n => (hsum_congr n).symm)
      _ = ∏' m : ℕ, jtpHub (q ^ 2) (-z * q) m := hsum_eq
      _ = ∏' n : ℕ, (1 - q ^ (2 * n + 2)) * (1 + z * q ^ (2 * n + 1)) *
          (1 + z⁻¹ * q ^ (2 * n + 1)) :=
        tprod_congr hprod_congr

end
end MetaMathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
