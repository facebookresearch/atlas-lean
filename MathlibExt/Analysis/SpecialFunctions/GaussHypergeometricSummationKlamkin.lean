/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Gauss hypergeometric summation of Klamkin

The first Gamma quotient from U. Abel, "A Short Proof of the Binomial
Identities of Frisch and Klamkin," _Journal of Integer Sequences_ 23 (2020),
Article 20.7.1: `₂F₁(n, b + 1; b - a; 1)` equals a quotient of Gamma values.
-/

namespace MetaMathlibExt

section

/-- Coefficient shorthand: the k-th term of ₂F₁(j, b+1; b-a) at x = 1. -/
private noncomputable def klamCoeff (b a : ℝ) (m k : ℕ) : ℝ :=
  ordinaryHypergeometricCoefficient ((m : ℕ) : ℝ) (b + 1) (b - a) k

private noncomputable def klamF (b a : ℝ) (m : ℕ) : ℝ :=
  ∑' k, klamCoeff b a m k

private noncomputable def klamG (a b : ℝ) (m : ℕ) : ℝ :=
  Real.Gamma (-a - 1 - ((m : ℕ) : ℝ)) * Real.Gamma (b - a) /
    (Real.Gamma (b - a - ((m : ℕ) : ℝ)) * Real.Gamma (-a - 1))

private lemma C_add_ne (a b : ℝ) (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) (i : ℕ) :
    (b - a) + (i : ℝ) ≠ 0 := by
  intro h
  apply hadmissible (i + 1)
  push_cast
  linarith

private lemma B_add_ne (_a b : ℝ) (hb : ∀ k : ℕ, -b ≠ (k : ℝ)) (i : ℕ) :
    (b + 1) + (i : ℝ) ≠ 0 := by
  intro h
  apply hb (i + 1)
  push_cast
  linarith

private lemma pochC_ne (a b : ℝ) (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) (k : ℕ) :
    Polynomial.eval (b - a) (ascPochhammer ℝ k) ≠ 0 := by
  induction k with
  | zero => simp [ascPochhammer_zero]
  | succ k ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_ne_zero ih (C_add_ne a b hadmissible k)

private lemma pochB_ne (a b : ℝ) (hb : ∀ k : ℕ, -b ≠ (k : ℝ)) (k : ℕ) :
    Polynomial.eval (b + 1) (ascPochhammer ℝ k) ≠ 0 := by
  induction k with
  | zero => simp [ascPochhammer_zero]
  | succ k ih =>
    rw [ascPochhammer_succ_eval]
    exact mul_ne_zero ih (B_add_ne a b hb k)

private lemma pochNat_ne (m K : ℕ) (hm : 1 ≤ m) :
    Polynomial.eval ((m : ℕ) : ℝ) (ascPochhammer ℝ K) ≠ 0 := by
  induction K with
  | zero => simp [ascPochhammer_zero]
  | succ K ih =>
    rw [ascPochhammer_succ_eval]
    refine mul_ne_zero ih (ne_of_gt ?_)
    have hmR : (0 : ℝ) < (m : ℕ) := Nat.cast_pos.mpr hm
    have hK : (0 : ℝ) ≤ (K : ℕ) := Nat.cast_nonneg K
    linarith

private lemma klamCoeff_zero (b a : ℝ) (m : ℕ) : klamCoeff b a m 0 = 1 := by
  unfold klamCoeff ordinaryHypergeometricCoefficient
  simp [ascPochhammer_zero]

private lemma klamCoeff_zero_succ (b a : ℝ) (k : ℕ) :
    klamCoeff b a 0 (k + 1) = 0 := by
  have h0 : Polynomial.eval ((0 : ℕ) : ℝ) (ascPochhammer ℝ (k + 1)) = 0 := by
    rw [Nat.cast_zero, ascPochhammer_eval_zero]
    by_cases h : k + 1 = 0
    · omega
    · simp
  unfold klamCoeff ordinaryHypergeometricCoefficient
  rw [h0]
  simp

private lemma klamCoeff_succ_right (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) (m K : ℕ) :
    klamCoeff b a m (K + 1) =
      klamCoeff b a m K * ((((m : ℕ) : ℝ) + (K : ℝ)) * ((b + 1) + (K : ℝ)) /
        (((b - a) + (K : ℝ)) * ((K : ℝ) + 1))) := by
  have hK : ((K.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero K)
  have hK1 : ((K : ℝ) + 1) ≠ 0 := by positivity
  have hPC : Polynomial.eval (b - a) (ascPochhammer ℝ K) ≠ 0 :=
    pochC_ne a b hadmissible K
  have hPCK : ((b - a) + (K : ℝ)) ≠ 0 := C_add_ne a b hadmissible K
  have hK' : ((K : ℝ) + 1) * ((K.factorial : ℕ) : ℝ) ≠ 0 := mul_ne_zero hK1 hK
  have hPC' : Polynomial.eval (b - a) (ascPochhammer ℝ K) * ((b - a) + (K : ℝ)) ≠ 0 :=
    mul_ne_zero hPC hPCK
  have pC : Polynomial.eval (b - a) (ascPochhammer ℝ (K + 1)) =
      Polynomial.eval (b - a) (ascPochhammer ℝ K) * ((b - a) + (K : ℝ)) :=
    ascPochhammer_succ_eval K (b - a)
  have pB : Polynomial.eval (b + 1) (ascPochhammer ℝ (K + 1)) =
      Polynomial.eval (b + 1) (ascPochhammer ℝ K) * ((b + 1) + (K : ℝ)) :=
    ascPochhammer_succ_eval K (b + 1)
  have pM : Polynomial.eval ((m : ℕ) : ℝ) (ascPochhammer ℝ (K + 1)) =
      Polynomial.eval ((m : ℕ) : ℝ) (ascPochhammer ℝ K) * (((m : ℕ) : ℝ) + (K : ℝ)) :=
    ascPochhammer_succ_eval K ((m : ℕ) : ℝ)
  have fK : ((((K + 1).factorial : ℕ)) : ℝ) = ((K : ℝ) + 1) * ((K.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  unfold klamCoeff ordinaryHypergeometricCoefficient
  rw [pC, pB, pM, fK]
  field_simp

private lemma klamCoeff_poch_succ_left (j K : ℕ) :
    Polynomial.eval ((j : ℕ) : ℝ) (ascPochhammer ℝ (K + 1)) =
      (j : ℝ) * Polynomial.eval ((((j + 1 : ℕ))) : ℝ) (ascPochhammer ℝ K) := by
  have hcomp := ascPochhammer_succ_left ℝ K
  have e : Polynomial.eval ((j : ℕ) : ℝ) (Polynomial.X + 1) = ((((j + 1 : ℕ))) : ℝ) := by
    rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    push_cast
    ring
  rw [hcomp, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp, e]

private lemma klamCoeff_succ_left (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) (j K : ℕ) :
    klamCoeff b a j (K + 1) =
      klamCoeff b a (j + 1) K * (((j : ℝ) * ((b + 1) + (K : ℝ))) /
        (((b - a) + (K : ℝ)) * ((K : ℝ) + 1))) := by
  have hK : ((K.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero K)
  have hK1 : ((K : ℝ) + 1) ≠ 0 := by positivity
  have hPC : Polynomial.eval (b - a) (ascPochhammer ℝ K) ≠ 0 :=
    pochC_ne a b hadmissible K
  have hPCK : ((b - a) + (K : ℝ)) ≠ 0 := C_add_ne a b hadmissible K
  have hK' : ((K : ℝ) + 1) * ((K.factorial : ℕ) : ℝ) ≠ 0 := mul_ne_zero hK1 hK
  have hPC' : Polynomial.eval (b - a) (ascPochhammer ℝ K) * ((b - a) + (K : ℝ)) ≠ 0 :=
    mul_ne_zero hPC hPCK
  have pC : Polynomial.eval (b - a) (ascPochhammer ℝ (K + 1)) =
      Polynomial.eval (b - a) (ascPochhammer ℝ K) * ((b - a) + (K : ℝ)) :=
    ascPochhammer_succ_eval K (b - a)
  have pB : Polynomial.eval (b + 1) (ascPochhammer ℝ (K + 1)) =
      Polynomial.eval (b + 1) (ascPochhammer ℝ K) * ((b + 1) + (K : ℝ)) :=
    ascPochhammer_succ_eval K (b + 1)
  have pJ := klamCoeff_poch_succ_left j K
  have fK : ((((K + 1).factorial : ℕ)) : ℝ) = ((K : ℝ) + 1) * ((K.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  unfold klamCoeff ordinaryHypergeometricCoefficient
  rw [pC, pB, pJ, fK]
  field_simp

private lemma klam_step2_incr (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) (j K : ℕ) :
    ((b - a) - (j : ℝ) - 1 - (b + 1)) * klamCoeff b a (j + 1) (K + 1) -
      ((b - a) - (j : ℝ) - 1) * klamCoeff b a j (K + 1) =
      -((b + 1) + ((K : ℝ) + 1)) * klamCoeff b a (j + 1) (K + 1) +
        ((b + 1) + (K : ℝ)) * klamCoeff b a (j + 1) K := by
  have hK1 : ((K : ℝ) + 1) ≠ 0 := by positivity
  have hPCK : ((b - a) + (K : ℝ)) ≠ 0 := C_add_ne a b hadmissible K
  rw [klamCoeff_succ_right a b hadmissible (j + 1) K,
    klamCoeff_succ_left a b hadmissible j K]
  have eJ : ((((j + 1 : ℕ))) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [eJ]
  field_simp
  ring

private lemma klam_step2 (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) (j K : ℕ) :
    ((b - a) - (j : ℝ) - 1 - (b + 1)) *
        (∑ k ∈ Finset.range (K + 1), klamCoeff b a (j + 1) k) -
      ((b - a) - (j : ℝ) - 1) * (∑ k ∈ Finset.range (K + 1), klamCoeff b a j k) =
      -((b + 1) + (K : ℝ)) * klamCoeff b a (j + 1) K := by
  induction K with
  | zero =>
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      klamCoeff_zero]
    push_cast
    ring
  | succ K ih =>
    rw [Finset.sum_range_succ (fun k => klamCoeff b a (j + 1) k) (K + 1),
      Finset.sum_range_succ (fun k => klamCoeff b a j k) (K + 1)]
    have eK : ((((K + 1 : ℕ))) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
    rw [eK]
    have h := klam_step2_incr a b hadmissible j K
    linear_combination ih + h

private lemma prod_range_add_eq_poch (x : ℝ) (k : ℕ) :
    ∏ j ∈ Finset.range (k + 1), (x + (j : ℝ)) =
      Polynomial.eval x (ascPochhammer ℝ (k + 1)) := by
  induction k with
  | zero =>
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    rw [ascPochhammer_succ_eval, ascPochhammer_zero, Polynomial.eval_one]
    simp
  | succ k ih =>
    have h := ascPochhammer_succ_eval (k + 1) x
    rw [Finset.prod_range_succ, ih, h]

private lemma klamCoeff_eq_gammaSeq (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    klamCoeff b a j (k + 1) =
      (k : ℝ) ^ (((j : ℕ) : ℝ) + (b + 1) - (b - a)) / ((k : ℝ) + 1) *
        (Real.GammaSeq (b - a) k /
          (Real.GammaSeq ((j : ℕ) : ℝ) k * Real.GammaSeq (b + 1) k)) := by
  have hkr : (0 : ℝ) < (k : ℕ) := Nat.cast_pos.mpr hk
  have hK : ((k.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  have hRj : ((k : ℝ) ^ (((j : ℕ)) : ℝ)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hkr _)
  have hRB : ((k : ℝ) ^ (b + 1)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hkr _)
  have hRC : ((k : ℝ) ^ (b - a)) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hkr _)
  have hPj : Polynomial.eval ((j : ℕ) : ℝ) (ascPochhammer ℝ (k + 1)) ≠ 0 :=
    pochNat_ne j (k + 1) (by omega)
  have hPB : Polynomial.eval (b + 1) (ascPochhammer ℝ (k + 1)) ≠ 0 :=
    pochB_ne a b hb (k + 1)
  have hPC : Polynomial.eval (b - a) (ascPochhammer ℝ (k + 1)) ≠ 0 :=
    pochC_ne a b hadmissible (k + 1)
  have hK1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have gJ : Real.GammaSeq ((j : ℕ) : ℝ) k =
      (k : ℝ) ^ (((j : ℕ)) : ℝ) * ((k.factorial : ℕ) : ℝ) /
        Polynomial.eval ((j : ℕ) : ℝ) (ascPochhammer ℝ (k + 1)) := by
    simp only [Real.GammaSeq, prod_range_add_eq_poch]
  have gB : Real.GammaSeq (b + 1) k =
      (k : ℝ) ^ (b + 1) * ((k.factorial : ℕ) : ℝ) /
        Polynomial.eval (b + 1) (ascPochhammer ℝ (k + 1)) := by
    simp only [Real.GammaSeq, prod_range_add_eq_poch]
  have gC : Real.GammaSeq (b - a) k =
      (k : ℝ) ^ (b - a) * ((k.factorial : ℕ) : ℝ) /
        Polynomial.eval (b - a) (ascPochhammer ℝ (k + 1)) := by
    simp only [Real.GammaSeq, prod_range_add_eq_poch]
  have hGSj : Real.GammaSeq ((j : ℕ) : ℝ) k ≠ 0 := by
    rw [gJ]; exact div_ne_zero (mul_ne_zero hRj hK) hPj
  have hGSB : Real.GammaSeq (b + 1) k ≠ 0 := by
    rw [gB]; exact div_ne_zero (mul_ne_zero hRB hK) hPB
  have hGSC : Real.GammaSeq (b - a) k ≠ 0 := by
    rw [gC]; exact div_ne_zero (mul_ne_zero hRC hK) hPC
  have hGSJB : Real.GammaSeq ((j : ℕ) : ℝ) k * Real.GammaSeq (b + 1) k ≠ 0 :=
    mul_ne_zero hGSj hGSB
  have qJ : Polynomial.eval ((j : ℕ) : ℝ) (ascPochhammer ℝ (k + 1)) =
      (k : ℝ) ^ (((j : ℕ)) : ℝ) * ((k.factorial : ℕ) : ℝ) /
        Real.GammaSeq ((j : ℕ) : ℝ) k := by
    rw [eq_div_iff hGSj, gJ]
    field_simp
  have qB : Polynomial.eval (b + 1) (ascPochhammer ℝ (k + 1)) =
      (k : ℝ) ^ (b + 1) * ((k.factorial : ℕ) : ℝ) / Real.GammaSeq (b + 1) k := by
    rw [eq_div_iff hGSB, gB]
    field_simp
  have qC : Polynomial.eval (b - a) (ascPochhammer ℝ (k + 1)) =
      (k : ℝ) ^ (b - a) * ((k.factorial : ℕ) : ℝ) / Real.GammaSeq (b - a) k := by
    rw [eq_div_iff hGSC, gC]
    field_simp
  have rp : (k : ℝ) ^ (((j : ℕ) : ℝ) + (b + 1) - (b - a)) =
      (k : ℝ) ^ (((j : ℕ)) : ℝ) * (k : ℝ) ^ (b + 1) / (k : ℝ) ^ (b - a) := by
    rw [Real.rpow_sub hkr, Real.rpow_add hkr]
  have fK : ((((k + 1).factorial : ℕ)) : ℝ) = ((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hK' : ((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ) ≠ 0 := mul_ne_zero hK1 hK
  unfold klamCoeff ordinaryHypergeometricCoefficient
  rw [qJ, qB, qC, fK, rp]
  field_simp

private lemma klam_GammaB_ne (_a b : ℝ) (hb : ∀ k : ℕ, -b ≠ (k : ℝ)) :
    Real.Gamma (b + 1) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m hm
  apply hb (m + 1)
  push_cast
  linarith

private lemma klam_GammaC_ne (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) :
    Real.Gamma (b - a) ≠ 0 := by
  apply Real.Gamma_ne_zero
  intro m hm
  exact (C_add_ne a b hadmissible m) (by linarith)

private lemma klam_coeff_norm_bound (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (j : ℕ) (hj1 : 1 ≤ j) :
    ∃ M : ℝ, ∀ᶠ k in Filter.atTop,
      ‖klamCoeff b a j (k + 1)‖ ≤
        M * (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1)) - 1) := by
  have hjR : (0 : ℝ) < ((j : ℕ) : ℝ) := Nat.cast_pos.mpr hj1
  have hGj : Real.Gamma ((j : ℕ) : ℝ) ≠ 0 := by
    apply Real.Gamma_ne_zero
    intro m hm
    have h1 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) := Nat.cast_nonneg m
    linarith [hm]
  have hLim : Filter.Tendsto
      (fun k => Real.GammaSeq (b - a) k /
        (Real.GammaSeq ((j : ℕ) : ℝ) k * Real.GammaSeq (b + 1) k))
      Filter.atTop
      (nhds (Real.Gamma (b - a) /
        (Real.Gamma ((j : ℕ) : ℝ) * Real.Gamma (b + 1)))) :=
    Filter.Tendsto.div
      (Real.GammaSeq_tendsto_Gamma (b - a))
      ((Real.GammaSeq_tendsto_Gamma _).mul (Real.GammaSeq_tendsto_Gamma _))
      (mul_ne_zero hGj (klam_GammaB_ne a b hb))
  refine ⟨‖Real.Gamma (b - a) /
      (Real.Gamma ((j : ℕ) : ℝ) * Real.Gamma (b + 1))‖ + 1, ?_⟩
  have hM : ∀ᶠ k in Filter.atTop,
      ‖Real.GammaSeq (b - a) k /
        (Real.GammaSeq ((j : ℕ) : ℝ) k * Real.GammaSeq (b + 1) k)‖ <
        ‖Real.Gamma (b - a) /
          (Real.Gamma ((j : ℕ) : ℝ) * Real.Gamma (b + 1))‖ + 1 :=
    hLim.norm.eventually (Iio_mem_nhds (lt_add_one _))
  have hM' : ∀ᶠ k in Filter.atTop,
      ‖Real.GammaSeq (b - a) k /
        (Real.GammaSeq ((j : ℕ) : ℝ) k * Real.GammaSeq (b + 1) k)‖ ≤
        ‖Real.Gamma (b - a) /
          (Real.Gamma ((j : ℕ) : ℝ) * Real.Gamma (b + 1))‖ + 1 :=
    hM.mono (fun k hk => le_of_lt hk)
  filter_upwards [hM', Filter.eventually_ge_atTop 1] with k hkM hk1
  have hkr : (0 : ℝ) < (k : ℕ) := Nat.cast_pos.mpr hk1
  have hrep := klamCoeff_eq_gammaSeq a b hadmissible hb j k hj1 hk1
  have hp : ((j : ℕ) : ℝ) + (b + 1) - (b - a) = (((j : ℕ) : ℝ) - (-a - 1)) := by
    ring
  have hK1 : (0 : ℝ) < (k : ℕ) + 1 := by positivity
  have hpow_nn : (0 : ℝ) ≤ (k : ℕ) ^ ((((j : ℕ) : ℝ) - (-a - 1))) :=
    Real.rpow_nonneg (le_of_lt hkr) _
  have hAscal : (0 : ℝ) ≤ (k : ℕ) ^ ((((j : ℕ) : ℝ) - (-a - 1))) / ((k : ℕ) + 1) :=
    div_nonneg hpow_nn (le_of_lt hK1)
  have hexp : ((((j : ℕ) : ℝ) - (-a - 1))) =
      ((((j : ℕ) : ℝ) - (-a - 1)) - 1) + 1 := by ring
  have hle : (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1))) / ((k : ℕ) + 1) ≤
      (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1)) - 1) := by
    conv_lhs => rw [hexp]
    rw [Real.rpow_add hkr, Real.rpow_one, div_le_iff₀ hK1]
    exact mul_le_mul_of_nonneg_left (by linarith)
      (Real.rpow_nonneg (le_of_lt hkr) _)
  have n1 : ‖(k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1)))‖ =
      (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1))) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hpow_nn]
  have n2 : ‖(k : ℝ) + 1‖ = (k : ℝ) + 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hK1)]
  rw [hrep, hp, norm_mul, norm_div, n1, n2]
  calc (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1))) / ((k : ℕ) + 1) *
        ‖Real.GammaSeq (b - a) k /
          (Real.GammaSeq ((j : ℕ) : ℝ) k * Real.GammaSeq (b + 1) k)‖
      ≤ (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1))) / ((k : ℕ) + 1) *
        (‖Real.Gamma (b - a) /
          (Real.Gamma ((j : ℕ) : ℝ) * Real.Gamma (b + 1))‖ + 1) :=
        mul_le_mul_of_nonneg_left hkM hAscal
    _ ≤ (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1)) - 1) *
        (‖Real.Gamma (b - a) /
          (Real.Gamma ((j : ℕ) : ℝ) * Real.Gamma (b + 1))‖ + 1) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = (‖Real.Gamma (b - a) /
          (Real.Gamma ((j : ℕ) : ℝ) * Real.Gamma (b + 1))‖ + 1) *
        (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1)) - 1) := mul_comm _ _

private lemma klam_coeff_summable (n : ℕ) (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (hconv : a + 1 + n < 0)
    (j : ℕ) (hj1 : 1 ≤ j) (hjn : j ≤ n) :
    Summable (fun k => klamCoeff b a j k) := by
  obtain ⟨M, hM⟩ := klam_coeff_norm_bound a b hadmissible hb j hj1
  have hs : (n : ℝ) < -a - 1 := by linarith
  have hjR : ((j : ℕ) : ℝ) ≤ (n : ℕ) := by exact_mod_cast hjn
  have hq : ((((j : ℕ) : ℝ) - (-a - 1)) - 1) < -1 := by linarith
  have hsum : Summable
      (fun k : ℕ => M * (k : ℝ) ^ ((((j : ℕ) : ℝ) - (-a - 1)) - 1)) :=
    Summable.mul_left M (Real.summable_nat_rpow.mpr hq)
  have hshift : Summable (fun k => klamCoeff b a j (k + 1)) :=
    hsum.of_norm_bounded_eventually_nat hM
  exact (summable_nat_add_iff 1).mp hshift

private lemma klam_coeff_zero_summable (b a : ℝ) :
    Summable (fun k => klamCoeff b a 0 k) := by
  have h : (fun k => klamCoeff b a 0 k) =
      (fun k => if k = 0 then klamCoeff b a 0 0 else 0) := by
    funext k
    by_cases hk : k = 0
    · simp [hk]
    · simp only [hk, ↓reduceIte]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
      exact klamCoeff_zero_succ b a m
  rw [h]
  exact (hasSum_ite_eq 0 (klamCoeff b a 0 0)).summable

private lemma klam_boundary_tendsto (n : ℕ) (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (hconv : a + 1 + n < 0)
    (m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    Filter.Tendsto (fun (K : ℕ) => ((b + 1) + (K : ℝ)) * klamCoeff b a m K)
      Filter.atTop (nhds 0) := by
  obtain ⟨M, hMb⟩ := klam_coeff_norm_bound a b hadmissible hb m hm1
  have hs : (n : ℝ) < -a - 1 := by linarith
  have hmR : ((m : ℕ) : ℝ) ≤ (n : ℕ) := by exact_mod_cast hmn
  have hpneg : ((m : ℕ) : ℝ) - (-a - 1) < 0 := by linarith
  have key : Filter.Tendsto
      (fun (K : ℕ) => ((b + 1) + (K : ℝ) + 1) * klamCoeff b a m (K + 1))
      Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm'
      (a := fun (K : ℕ) => ((|b + 1| + 2) * M) *
        (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1)))) ?_ ?_
    · filter_upwards [hMb, Filter.eventually_ge_atTop 1] with K hQ hK1
      have hkr : (0 : ℝ) < (K : ℕ) := Nat.cast_pos.mpr hK1
      have hK1R : (1 : ℝ) ≤ (K : ℕ) := by exact_mod_cast hK1
      have hB : |(b + 1) + (K : ℝ) + 1| ≤ (|b + 1| + 2) * (K : ℝ) := by
        have h1 : |(b + 1) + (K : ℝ) + 1| ≤ |b + 1| + ((K : ℝ) + 1) := by
          have hassoc := abs_add_le (b + 1) ((K : ℝ) + 1)
          have reassoc : ((b + 1) + (K : ℝ) + 1) = (b + 1) + ((K : ℝ) + 1) := by
            ring
          rw [reassoc]
          calc |(b + 1) + ((K : ℝ) + 1)| ≤ |(b + 1)| + |((K : ℝ) + 1)| := hassoc
            _ = |b + 1| + ((K : ℝ) + 1) := by
                rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (K : ℝ) + 1)]
        have h2 : |b + 1| ≤ |b + 1| * (K : ℝ) := by
          calc |b + 1| = |b + 1| * 1 := (mul_one _).symm
            _ ≤ |b + 1| * (K : ℝ) :=
                mul_le_mul_of_nonneg_left hK1R (abs_nonneg _)
        linarith
      have hKp : (K : ℝ) * (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1)) - 1) =
          (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1))) := by
        have h1 : (K : ℝ) ^ ((1 : ℝ) + ((((m : ℕ) : ℝ) - (-a - 1)) - 1)) =
            (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1))) := by
          congr 1
          ring
        rw [Real.rpow_add hkr] at h1
        rw [Real.rpow_one] at h1
        exact h1
      have hAscal : ‖((b + 1) + (K : ℝ) + 1) * klamCoeff b a m (K + 1)‖ =
          |(b + 1) + (K : ℝ) + 1| * ‖klamCoeff b a m (K + 1)‖ := by
        rw [norm_mul, Real.norm_eq_abs]
      rw [hAscal]
      calc |(b + 1) + (K : ℝ) + 1| * ‖klamCoeff b a m (K + 1)‖
          ≤ ((|b + 1| + 2) * (K : ℝ)) *
            (M * (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1)) - 1)) :=
            mul_le_mul hB hQ (norm_nonneg _) (by positivity)
        _ = ((|b + 1| + 2) * M) * (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1))) := by
            have e : ((|b + 1| + 2) * (K : ℝ)) *
                (M * (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1)) - 1)) =
                ((|b + 1| + 2) * M) *
                ((K : ℝ) * (K : ℝ) ^ ((((m : ℕ) : ℝ) - (-a - 1)) - 1)) := by
              ring
            rw [e, hKp]
    · have hq : (0 : ℝ) < -((((m : ℕ) : ℝ) - (-a - 1))) := by linarith
      have h2 : Filter.Tendsto
          (fun K : ℕ => (K : ℝ) ^ (-(-((((m : ℕ) : ℝ) - (-a - 1))))))
          Filter.atTop (nhds 0) :=
        (tendsto_rpow_neg_atTop hq).comp tendsto_natCast_atTop_atTop
      rw [neg_neg] at h2
      simpa using h2.const_mul _
  have heq : (fun (K : ℕ) => ((b + 1) + (K : ℝ) + 1) * klamCoeff b a m (K + 1)) =
      (fun (K : ℕ) => ((b + 1) + ((((K + 1 : ℕ))) : ℝ)) *
        klamCoeff b a m (K + 1)) := by
    funext K
    have eK : ((((K + 1 : ℕ))) : ℝ) = (K : ℝ) + 1 := by push_cast; ring
    rw [eK]
    ring
  rw [heq] at key
  refine (Filter.tendsto_add_atTop_iff_nat 1).mp ?_
  exact key

private lemma klam_F_rec (n : ℕ) (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (hconv : a + 1 + n < 0)
    (j : ℕ) (hj : j + 1 ≤ n) :
    ((-a - 1) - (j : ℝ) - 1) * klamF b a (j + 1) =
      ((b - a) - (j : ℝ) - 1) * klamF b a j := by
  have hS1 : Summable (fun k => klamCoeff b a (j + 1) k) :=
    klam_coeff_summable n a b hadmissible hb hconv (j + 1) (by omega) hj
  have hS0 : Summable (fun k => klamCoeff b a j k) := by
    by_cases hj0 : j = 0
    · subst hj0; exact klam_coeff_zero_summable b a
    · exact klam_coeff_summable n a b hadmissible hb hconv j
        (by omega) (by omega)
  have hT1 : Filter.Tendsto
      (fun (K : ℕ) => ∑ k ∈ Finset.range (K + 1), klamCoeff b a (j + 1) k)
      Filter.atTop (nhds (klamF b a (j + 1))) :=
    (Filter.tendsto_add_atTop_iff_nat
      (f := fun n => ∑ k ∈ Finset.range n, klamCoeff b a (j + 1) k) 1).mpr
      hS1.hasSum.tendsto_sum_nat
  have hT0 : Filter.Tendsto
      (fun (K : ℕ) => ∑ k ∈ Finset.range (K + 1), klamCoeff b a j k)
      Filter.atTop (nhds (klamF b a j)) :=
    (Filter.tendsto_add_atTop_iff_nat
      (f := fun n => ∑ k ∈ Finset.range n, klamCoeff b a j k) 1).mpr
      hS0.hasSum.tendsto_sum_nat
  have hbound := klam_boundary_tendsto n a b hadmissible hb hconv (j + 1)
    (by omega) hj
  have hE : Filter.Tendsto
      (fun (K : ℕ) => -((((b + 1) + (K : ℝ)) * klamCoeff b a (j + 1) K)))
      Filter.atTop (nhds 0) := by
    simpa only [neg_zero] using hbound.neg
  have hC : Filter.Tendsto
      (fun (K : ℕ) => ((-a - 1) - (j : ℝ) - 1) *
          (∑ k ∈ Finset.range (K + 1), klamCoeff b a (j + 1) k) -
        ((b - a) - (j : ℝ) - 1) *
          (∑ k ∈ Finset.range (K + 1), klamCoeff b a j k))
      Filter.atTop
      (nhds (((-a - 1) - (j : ℝ) - 1) * klamF b a (j + 1) -
        ((b - a) - (j : ℝ) - 1) * klamF b a j)) :=
    (hT1.const_mul _).sub (hT0.const_mul _)
  have hfun : ∀ (K : ℕ), ((-a - 1) - (j : ℝ) - 1) *
        (∑ k ∈ Finset.range (K + 1), klamCoeff b a (j + 1) k) -
      ((b - a) - (j : ℝ) - 1) *
        (∑ k ∈ Finset.range (K + 1), klamCoeff b a j k) =
      -((((b + 1) + (K : ℝ)) * klamCoeff b a (j + 1) K)) := by
    intro K
    have h := klam_step2 a b hadmissible j K
    linear_combination h
  have hC' := hC.congr hfun
  have hV : ((-a - 1) - (j : ℝ) - 1) * klamF b a (j + 1) -
      ((b - a) - (j : ℝ) - 1) * klamF b a j = 0 :=
    tendsto_nhds_unique hC' hE
  exact sub_eq_zero.mp hV

private lemma klam_gamma_inv_succ (x : ℝ) :
    x / Real.Gamma (x + 1) = 1 / Real.Gamma x := by
  by_cases hx : x = 0
  · subst hx
    simp [Real.Gamma_zero, Real.Gamma_one]
  · rw [Real.Gamma_add_one hx]
    field_simp

private lemma klam_G_rec (n : ℕ) (a b : ℝ) (hconv : a + 1 + n < 0)
    (j : ℕ) (hj : j + 1 ≤ n) :
    ((-a - 1) - (j : ℝ) - 1) * klamG a b (j + 1) =
      ((b - a) - (j : ℝ) - 1) * klamG a b j := by
  have hs : (n : ℝ) < -a - 1 := by linarith
  have hjR : ((j : ℕ) : ℝ) + 1 ≤ (n : ℕ) := by exact_mod_cast hj
  have num : ((-a - 1) - (j : ℝ) - 1) *
      Real.Gamma (-a - 1 - (((j + 1 : ℕ)) : ℝ)) =
      Real.Gamma (-a - 1 - (j : ℝ)) := by
    have hne : (-a - 1 - (((j + 1 : ℕ)) : ℝ)) ≠ 0 := by
      have hpos2 : (0 : ℝ) < -a - 1 - (((j + 1 : ℕ)) : ℝ) := by
        have hj1 : ((((j + 1 : ℕ))) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
        rw [hj1]
        linarith
      exact ne_of_gt hpos2
    have h := Real.Gamma_add_one hne
    have e1 : ((-a - 1) - (j : ℝ) - 1) = (-a - 1 - (((j + 1 : ℕ)) : ℝ)) := by
      push_cast; ring
    have e2 : (-a - 1 - (((j + 1 : ℕ)) : ℝ)) + 1 = -a - 1 - (j : ℝ) := by
      push_cast; ring
    rw [e1, ← h, e2]
  have den : (((b - a) - (j : ℝ) - 1)) / Real.Gamma (((b - a) - (j : ℝ))) =
      1 / Real.Gamma (((b - a) - (((j + 1 : ℕ)) : ℝ))) := by
    have e0 : ((b - a) - (j : ℝ) - 1) = ((b - a) - (((j + 1 : ℕ)) : ℝ)) := by
      push_cast; ring
    have e : ((b - a) - (j : ℝ)) = (((b - a) - (((j + 1 : ℕ)) : ℝ))) + 1 := by
      push_cast; ring
    rw [e0, e]
    exact klam_gamma_inv_succ _
  have e1 : ((-a - 1) - (j : ℝ) - 1) * klamG a b (j + 1) =
      (Real.Gamma (b - a) / Real.Gamma (-a - 1) /
        Real.Gamma ((b - a) - (((j + 1 : ℕ)) : ℝ))) *
      (((-a - 1) - (j : ℝ) - 1) *
        Real.Gamma (-a - 1 - (((j + 1 : ℕ)) : ℝ))) := by
    unfold klamG
    ring
  have e2 : ((b - a) - (j : ℝ) - 1) * klamG a b j =
      (Real.Gamma (-a - 1 - (j : ℝ)) * Real.Gamma (b - a) / Real.Gamma (-a - 1)) *
      ((((b - a) - (j : ℝ) - 1)) / Real.Gamma (((b - a) - (j : ℝ)))) := by
    unfold klamG
    ring
  rw [e1, num, e2, den]
  ring

private lemma klam_FG_eq (n : ℕ) (a b : ℝ)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (hconv : a + 1 + n < 0)
    (_hn : 1 ≤ n) :
    ∀ j : ℕ, j ≤ n → klamF b a j = klamG a b j := by
  intro j
  induction j with
  | zero =>
    intro _
    have hF0 : klamF b a 0 = 1 := by
      unfold klamF
      rw [tsum_eq_single 0 (fun b' hb' => by
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb'
        exact klamCoeff_zero_succ b a m)]
      exact klamCoeff_zero b a 0
    have hG0 : klamG a b 0 = 1 := by
      have hGC : Real.Gamma (b - a) ≠ 0 := klam_GammaC_ne a b hadmissible
      have hGs : Real.Gamma (-a - 1) ≠ 0 := by
        have hs : (n : ℝ) < -a - 1 := by linarith
        have hspos : (0 : ℝ) < -a - 1 := by
          have hnR : (0 : ℝ) ≤ (n : ℕ) := Nat.cast_nonneg n
          linarith
        exact ne_of_gt (Real.Gamma_pos_of_pos hspos)
      unfold klamG
      simp only [Nat.cast_zero, sub_zero]
      rw [div_eq_one_iff_eq (mul_ne_zero hGC hGs)]
      ring
    rw [hF0, hG0]
  | succ m ih =>
    intro hle
    have hF := klam_F_rec n a b hadmissible hb hconv m (by omega)
    have hG := klam_G_rec n a b hconv m (by omega)
    have hne : ((-a - 1) - (m : ℝ) - 1) ≠ 0 := by
      have hs : (n : ℝ) < -a - 1 := by linarith
      have hmR : ((m : ℕ) : ℝ) + 1 ≤ (n : ℕ) := by
        exact_mod_cast (by omega : m + 1 ≤ n)
      have hpos : (0 : ℝ) < (-a - 1) - (m : ℝ) - 1 := by linarith
      exact ne_of_gt hpos
    rw [ih (by omega)] at hF
    have hcc : ((-a - 1) - (m : ℝ) - 1) * klamF b a (m + 1) =
        ((-a - 1) - (m : ℝ) - 1) * klamG a b (m + 1) := by
      rw [hF, hG]
    exact mul_left_cancel₀ hne hcc

set_option linter.unusedVariables false in
/--
**Klamkin's Gauss summation.** Let $n \ge 1$ be an integer and let $a$ and $b$ be real numbers
such that $-a$ and $-b$ are not nonnegative integers, $a + 1 + n < 0$, and $a - b + 1$ is not a
nonnegative integer. Then
$$
{}_2F_1(n, b + 1; b - a; 1) =
  \frac{\Gamma(-a - n - 1)\,\Gamma(b - a)}{\Gamma(b - a - n)\,\Gamma(-a - 1)},
$$
where ${}_2F_1(\alpha, \beta; \gamma; 1) =
\sum_{k \ge 0} \frac{(\alpha)_k (\beta)_k}{(\gamma)_k\, k!}$ and $(x)_k$ is the rising factorial.

The condition $a + 1 + n < 0$ makes the series converge. The Gamma function is taken to be $0$
at its poles and division by $0$ gives $0$, so the right side is $0$ when $b - a - n$ is a
nonpositive integer.

Source: U. Abel, "A Short Proof of the Binomial Identities of Frisch and
Klamkin," _Journal of Integer Sequences_ 23 (2020), Article 20.7.1.

Proves `Wanted` entry `gauss_hypergeometric_summation_klamkin`.
-/
theorem gauss_hypergeometric_summation_klamkin (n : ℕ) (a b : ℝ)
    (ha : ∀ k : ℕ, -a ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (hn : 1 ≤ n)
    (hconv : a + 1 + n < 0)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) :
    ordinaryHypergeometric (n : ℝ) (b + 1) (b - a) (1 : ℝ) =
      Real.Gamma (-a - n - 1) * Real.Gamma (b - a) /
        (Real.Gamma (b - a - n) * Real.Gamma (-a - 1)) := by
  have hLHS : ordinaryHypergeometric (n : ℝ) (b + 1) (b - a) (1 : ℝ) =
      klamF b a n := by
    have h : ordinaryHypergeometric ((n : ℕ) : ℝ) (b + 1) (b - a) =
        (fun x : ℝ => ∑' k, ordinaryHypergeometricCoefficient ((n : ℕ) : ℝ)
          (b + 1) (b - a) k • x ^ k) :=
      ordinaryHypergeometric_eq_tsum _ _ _
    unfold klamF klamCoeff
    calc ordinaryHypergeometric (n : ℝ) (b + 1) (b - a) (1 : ℝ)
        = ∑' k, ordinaryHypergeometricCoefficient ((n : ℕ) : ℝ) (b + 1)
            (b - a) k • (1 : ℝ) ^ k := by rw [h]
      _ = ∑' k, ordinaryHypergeometricCoefficient ((n : ℕ) : ℝ) (b + 1)
            (b - a) k := by
          apply tsum_congr
          intro k
          simp
  rw [hLHS]
  have hFG := klam_FG_eq n a b hadmissible hb hconv hn n le_rfl
  rw [hFG]
  unfold klamG
  have e : (-a - 1 - (((n : ℕ)) : ℝ)) = (-a - ((n : ℕ)) - 1) := by ring
  rw [e]

/--
**Klamkin's Gauss summation as a convergent series.** Let $n \ge 1$ be an integer and let $a$
and $b$ be real numbers such that $-a$ and $-b$ are not nonnegative integers, $a + 1 + n < 0$,
and $a - b + 1$ is not a nonnegative integer. Then the series
$$
\sum_{k \ge 0} \frac{(n)_k\,(b + 1)_k}{(b - a)_k\, k!}
$$
converges absolutely, with sum
$$
\frac{\Gamma(-a - n - 1)\,\Gamma(b - a)}{\Gamma(b - a - n)\,\Gamma(-a - 1)},
$$
where $(x)_k = x(x + 1) \cdots (x + k - 1)$ is the rising factorial.

The Gamma function is taken to be $0$ at its poles and division by $0$ gives $0$, so this sum is
$0$ when $b - a - n$ is a nonpositive integer.
-/
theorem hasSum_ordinaryHypergeometricCoefficient_klamkin (n : ℕ) (a b : ℝ)
    (ha : ∀ k : ℕ, -a ≠ (k : ℝ))
    (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
    (hn : 1 ≤ n)
    (hconv : a + 1 + n < 0)
    (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) :
    HasSum (fun k => ordinaryHypergeometricCoefficient (n : ℝ) (b + 1) (b - a) k)
      (Real.Gamma (-a - n - 1) * Real.Gamma (b - a) /
        (Real.Gamma (b - a - n) * Real.Gamma (-a - 1))) := by
  have hs : Summable (fun k =>
      ordinaryHypergeometricCoefficient (n : ℝ) (b + 1) (b - a) k) := by
    simpa only [klamCoeff] using
      klam_coeff_summable n a b hadmissible hb hconv n hn le_rfl
  have hvalue : ordinaryHypergeometric (n : ℝ) (b + 1) (b - a) (1 : ℝ) =
      ∑' k, ordinaryHypergeometricCoefficient (n : ℝ) (b + 1) (b - a) k := by
    rw [ordinaryHypergeometric_eq_tsum]
    apply tsum_congr
    intro k
    simp
  have hgauss := gauss_hypergeometric_summation_klamkin n a b ha hb hn hconv hadmissible
  have hsum := hs.hasSum
  rw [← hvalue, hgauss] at hsum
  exact hsum

end
end MetaMathlibExt
