/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import MathlibExt.Analysis.Asymptotics.WatsonLaplaceLemma
import Mathlib.Tactic.Continuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
namespace MetaMathlibExt

private theorem exp_logGammaSeq_eq_gammaSeq {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : n ≠ 0) :
    Real.exp (Real.BohrMollerup.logGammaSeq s n) = Real.GammaSeq s n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  unfold Real.BohrMollerup.logGammaSeq Real.GammaSeq
  rw [Real.exp_sub, Real.exp_add]
  have e1 : Real.exp (s * Real.log n) = (n : ℝ) ^ s := by
    rw [Real.rpow_def_of_pos hnR]; ring_nf
  have e2 : Real.exp (Real.log (n.factorial : ℝ)) = (n.factorial : ℝ) := by
    apply Real.exp_log
    exact_mod_cast Nat.factorial_pos n
  have e3 : Real.exp (∑ m ∈ Finset.range (n + 1), Real.log (s + (m : ℝ)))
      = ∏ j ∈ Finset.range (n + 1), (s + (j : ℝ)) := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro m _
    apply Real.exp_log
    have : (0 : ℝ) < s + (m : ℝ) := by
      have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact this
  rw [e1, e2, e3]

private theorem logGamma_fe :
    ∀ {y : ℝ}, 0 < y → (Real.log ∘ Real.Gamma) (y + 1)
      = (Real.log ∘ Real.Gamma) y + Real.log y := by
  intro y hy
  change Real.log (Real.Gamma (y + 1)) = Real.log (Real.Gamma y) + Real.log y
  rw [Real.Gamma_add_one (ne_of_gt hy)]
  rw [Real.log_mul (ne_of_gt hy) (ne_of_gt (Real.Gamma_pos_of_pos hy))]
  ring

private theorem gammaSeq_le_gamma {s : ℝ} (hs : 0 < s) {n : ℕ} (hn : n ≠ 0) :
    Real.GammaSeq s n ≤ Real.Gamma s := by
  have hGs : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have hge := Real.BohrMollerup.ge_logGammaSeq (f := Real.log ∘ Real.Gamma)
    Real.convexOn_log_Gamma logGamma_fe hs hn
  simp only [Function.comp_apply, Real.Gamma_one, Real.log_one, zero_add] at hge
  have hexp := Real.exp_le_exp.mpr hge
  rw [Real.exp_log hGs] at hexp
  rwa [exp_logGammaSeq_eq_gammaSeq hs hn] at hexp

private theorem gamma_le_one_add_inv_mul_gammaSeq {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1)
    {n : ℕ} (hn : n ≠ 0) :
    Real.Gamma s ≤ (1 + 1 / (n : ℝ)) * Real.GammaSeq s n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hn1R : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hGs : 0 < Real.Gamma s := Real.Gamma_pos_of_pos hs
  have hGS : 0 < Real.GammaSeq s n := by
    rw [← exp_logGammaSeq_eq_gammaSeq hs hn]; exact Real.exp_pos _
  have hle := Real.BohrMollerup.le_logGammaSeq (f := Real.log ∘ Real.Gamma)
    Real.convexOn_log_Gamma logGamma_fe hs hs1 n
  simp only [Function.comp_apply, Real.Gamma_one, Real.log_one, zero_add] at hle
  have hexp := Real.exp_le_exp.mpr hle
  rw [Real.exp_log hGs] at hexp
  have hsplit : Real.exp (s * Real.log ((n : ℝ) + 1) - s * Real.log (n : ℝ)
      + Real.BohrMollerup.logGammaSeq s n)
      = Real.exp (s * Real.log ((n : ℝ) + 1) - s * Real.log (n : ℝ))
        * Real.GammaSeq s n := by
    rw [Real.exp_add, exp_logGammaSeq_eq_gammaSeq hs hn]
  rw [hsplit] at hexp
  have hexp2 : Real.exp (s * Real.log ((n : ℝ) + 1) - s * Real.log (n : ℝ))
      = (((n : ℝ) + 1) / (n : ℝ)) ^ s := by
    rw [Real.div_rpow (le_of_lt hn1R) (le_of_lt hnR)]
    rw [Real.rpow_def_of_pos hn1R, Real.rpow_def_of_pos hnR]
    rw [← Real.exp_sub]
    congr 1
    ring
  rw [hexp2] at hexp
  have hbase : (1 : ℝ) ≤ ((n : ℝ) + 1) / (n : ℝ) := by
    rw [le_div_iff₀ hnR]
    linarith
  have hrpow : (((n : ℝ) + 1) / (n : ℝ)) ^ s ≤ ((n : ℝ) + 1) / (n : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hbase hs1
    rwa [Real.rpow_one] at h
  have h11 : ((n : ℝ) + 1) / (n : ℝ) = 1 + 1 / (n : ℝ) := by
    field_simp
  calc Real.Gamma s ≤ (((n : ℝ) + 1) / (n : ℝ)) ^ s * Real.GammaSeq s n := hexp
    _ ≤ (((n : ℝ) + 1) / (n : ℝ)) * Real.GammaSeq s n := by
        apply mul_le_mul_of_nonneg_right hrpow (le_of_lt hGS)
    _ = (1 + 1 / (n : ℝ)) * Real.GammaSeq s n := by rw [h11]

private theorem phi_mem {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ x * (Real.Gamma (1 - x))⁻¹ ∧ x * (Real.Gamma (1 - x))⁻¹ ≤ 2 := by
  by_cases hx : x = 1
  · subst hx
    simp [Real.Gamma_zero]
  · have hs : 0 < 1 - x := by
      have : x < 1 := lt_of_le_of_ne hx1 hx
      linarith
    have hs1 : 1 - x ≤ 1 := by linarith
    have hGs : 0 < Real.Gamma (1 - x) := Real.Gamma_pos_of_pos hs
    have hseq1 : Real.GammaSeq (1 - x) 1 = 1 / ((1 - x) * ((1 - x) + 1)) := by
      rw [Real.GammaSeq.eq_1]
      simp only [Nat.factorial_one, Nat.cast_one, Finset.prod_range_succ,
        Finset.prod_range_zero]
      rw [Real.one_rpow]
      ring
    have hfeq : ∀ {y : ℝ}, 0 < y → (Real.log ∘ Real.Gamma) (y + 1)
        = (Real.log ∘ Real.Gamma) y + Real.log y :=
      logGamma_fe
    have hge := Real.BohrMollerup.ge_logGammaSeq (f := Real.log ∘ Real.Gamma)
      Real.convexOn_log_Gamma hfeq hs (by norm_num : (1:ℕ) ≠ 0)
    simp only [Function.comp_apply, Real.Gamma_one, Real.log_one, zero_add] at hge
    have hexp := Real.exp_le_exp.mpr hge
    have hbridge : Real.exp (Real.BohrMollerup.logGammaSeq (1 - x) 1)
        = Real.GammaSeq (1 - x) 1 :=
      exp_logGammaSeq_eq_gammaSeq hs (by norm_num)
    rw [Real.exp_log hGs] at hexp
    rw [hbridge, hseq1] at hexp
    have hprod : (0 : ℝ) < (1 - x) * ((1 - x) + 1) := by positivity
    have hprod_le : (1 - x) * ((1 - x) + 1) ≤ 2 := by nlinarith
    have hG12 : (1 / 2 : ℝ) ≤ Real.Gamma (1 - x) :=
      le_trans (one_div_le_one_div_of_le hprod hprod_le) hexp
    constructor
    · apply mul_nonneg hx0
      exact le_of_lt (inv_pos.mpr hGs)
    · have hinv : (Real.Gamma (1 - x))⁻¹ ≤ 2 := by
        rw [inv_le_iff_one_le_mul₀ hGs]
        linarith
      calc x * (Real.Gamma (1 - x))⁻¹ ≤ 1 * 2 := by
            apply mul_le_mul hx1 hinv (le_of_lt (inv_pos.mpr hGs)) (by norm_num)
        _ = 2 := one_mul 2

private theorem prod_range_sub_mul_eq_prod_one_sub_add (n : ℕ) (x : ℝ) :
    (∏ j ∈ Finset.range n, (x - (j : ℝ))) * ((n : ℝ) + 1 - x) * ((n : ℝ) - x)
      = (-1 : ℝ) ^ (n + 1) * x * ∏ j ∈ Finset.range (n + 1), ((1 - x) + (j : ℝ)) := by
  induction n with
  | zero => simp; ring
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ]
    push_cast
    linear_combination (-((n : ℝ) + 2 - x)) * ih

private theorem integrand_eq (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    (n : ℝ) * (-1 : ℝ) ^ (n + 1) * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ)
      = (n : ℝ) ^ (-x) * (x * (Real.Gamma (1 - x))⁻¹)
        * ((n : ℝ) ^ 2 / (((n : ℝ) + 1 - x) * ((n : ℝ) - x)))
        * (Real.Gamma (1 - x) / Real.GammaSeq (1 - x) n) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hs : (0 : ℝ) < 1 - x := by linarith
  have hGs_ne : Real.Gamma (1 - x) ≠ 0 := ne_of_gt (Real.Gamma_pos_of_pos hs)
  have hQ : (0 : ℝ) < ∏ j ∈ Finset.range (n + 1), ((1 - x) + (j : ℝ)) := by
    apply Finset.prod_pos
    intro j _
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hQ_ne : (∏ j ∈ Finset.range (n + 1), ((1 - x) + (j : ℝ))) ≠ 0 := ne_of_gt hQ
  have hA : (0 : ℝ) < (n : ℝ) + 1 - x := by linarith
  have hB : (0 : ℝ) < (n : ℝ) - x := by linarith
  have hA_ne : ((n : ℝ) + 1 - x) ≠ 0 := ne_of_gt hA
  have hB_ne : ((n : ℝ) - x) ≠ 0 := ne_of_gt hB
  have hAB : (((n : ℝ) + 1 - x) * ((n : ℝ) - x)) ≠ 0 := mul_ne_zero hA_ne hB_ne
  have hfact : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hfact_ne : (n.factorial : ℝ) ≠ 0 := ne_of_gt hfact
  have hrpow_pos : (0 : ℝ) < (n : ℝ) ^ (-x) := Real.rpow_pos_of_pos hn0 _
  have hrpow_ne : (n : ℝ) ^ (-x) ≠ 0 := ne_of_gt hrpow_pos
  have hrpow1_pos : (0 : ℝ) < (n : ℝ) ^ ((1 : ℝ) - x) := Real.rpow_pos_of_pos hn0 _
  have hrpow1_ne : (n : ℝ) ^ ((1 : ℝ) - x) ≠ 0 := ne_of_gt hrpow1_pos
  have hGS_ne : Real.GammaSeq (1 - x) n ≠ 0 := by
    rw [Real.GammaSeq.eq_1]
    apply div_ne_zero
    · apply mul_ne_zero hrpow1_ne hfact_ne
    · exact hQ_ne
  have hN1 := prod_range_sub_mul_eq_prod_one_sub_add n x
  have hP : (∏ j ∈ Finset.range n, (x - (j : ℝ)))
      = (((-1 : ℝ) ^ (n + 1) * x * ∏ j ∈ Finset.range (n + 1), ((1 - x) + (j : ℝ)))
        / (((n : ℝ) + 1 - x) * ((n : ℝ) - x))) := by
    refine (eq_div_iff hAB).mpr ?_
    linear_combination hN1
  have hsign : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
    rw [← pow_add]
    have : Even ((n + 1) + (n + 1)) := ⟨n + 1, by ring⟩
    exact Even.neg_one_pow this
  have hrpow : (n : ℝ) ^ ((1 : ℝ) - x) = (n : ℝ) * (n : ℝ) ^ (-x) := by
    have h := Real.rpow_add hn0 (1 : ℝ) (-x)
    rwa [Real.rpow_one] at h
  rw [hP, Real.GammaSeq.eq_1, hrpow]
  field_simp
  have hsign2 : (((-1 : ℝ) ^ (n + 1)) ^ 2) = 1 := by rw [sq]; exact hsign
  rw [hsign2, one_mul]

private theorem abs_integrand_sub_le (n : ℕ) (hn : 2 ≤ n) (x : ℝ)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |(n:ℝ) * (-1 : ℝ) ^ (n + 1) * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ)
      - (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹)| ≤ 8 / (n:ℝ) := by
  obtain ⟨hx0, hx1⟩ := Set.mem_Icc.mp hx
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have hn1_ne : ((n : ℝ) + 1) ≠ 0 := ne_of_gt hn1
  have hnm1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hnm1_ne : ((n : ℝ) - 1) ≠ 0 := ne_of_gt hnm1
  by_cases hx1e : x = 1
  · subst hx1e
    have hprod : (∏ j ∈ Finset.range n, ((1:ℝ) - (j : ℝ))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : 1 < n)) (by norm_num)
    rw [hprod]
    simp [Real.Gamma_zero]
    have h8 : (0:ℝ) ≤ 8 / (n:ℝ) := by positivity
    simpa using h8
  · have hx1lt : x < 1 := lt_of_le_of_ne hx1 hx1e
    have hs : (0 : ℝ) < 1 - x := by linarith
    have hGs : (0 : ℝ) < Real.Gamma (1 - x) := Real.Gamma_pos_of_pos hs
    have hGs_ne : Real.Gamma (1 - x) ≠ 0 := ne_of_gt hGs
    have hGS : (0 : ℝ) < Real.GammaSeq (1 - x) n := by
      rw [Real.GammaSeq.eq_1]
      apply div_pos
      · apply mul_pos (Real.rpow_pos_of_pos hn0 _)
        exact_mod_cast Nat.factorial_pos n
      · apply Finset.prod_pos
        intro j _
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j; linarith
    have hGS_ne : Real.GammaSeq (1 - x) n ≠ 0 := ne_of_gt hGS
    have hN4 := integrand_eq n hn x hx0 hx1lt
    set D : ℝ := ((n : ℝ) + 1 - x) * ((n : ℝ) - x) with hD
    set A : ℝ := (n : ℝ) ^ 2 / D with hA
    set B : ℝ := Real.Gamma (1 - x) / Real.GammaSeq (1 - x) n with hB
    set φ : ℝ := x * (Real.Gamma (1 - x))⁻¹ with hφ
    set R : ℝ := (n : ℝ) ^ (-x) with hR
    have hDpos : 0 < D := by
      rw [hD]; apply mul_pos <;> linarith
    have hDhi : D ≤ ((n : ℝ) + 1) * (n : ℝ) := by
      rw [hD]
      apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hDlo : (n : ℝ) * ((n : ℝ) - 1) ≤ D := by
      rw [hD]
      apply mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
    have hBlo : (1 : ℝ) ≤ B := by
      rw [hB, le_div_iff₀ hGS]
      simpa using gammaSeq_le_gamma hs (n := n) (by omega : n ≠ 0)
    have hBhi : B ≤ 1 + 1 / (n : ℝ) := by
      rw [hB, div_le_iff₀ hGS]
      have hmem : 1 - x ≤ 1 := by linarith
      have := gamma_le_one_add_inv_mul_gammaSeq hs hmem (n := n) (by omega : n ≠ 0)
      linarith
    have hApos : 0 < A := by rw [hA]; positivity
    have hBpos : 0 < B := lt_of_lt_of_le (by norm_num) hBlo
    have hAno : 0 ≤ A := le_of_lt hApos
    have hBno : 0 ≤ B := le_of_lt hBpos
    have hA_lo : (n:ℝ)/((n:ℝ)+1) ≤ A := by
      rw [hA, le_div_iff₀ hDpos]
      have h1 : ((n:ℝ)/((n:ℝ)+1))*D ≤ ((n:ℝ)/((n:ℝ)+1))*(((n:ℝ)+1)*(n:ℝ)) :=
        mul_le_mul_of_nonneg_left hDhi
          (div_nonneg (le_of_lt hn0) (le_of_lt hn1))
      have h2 : ((n:ℝ)/((n:ℝ)+1))*(((n:ℝ)+1)*(n:ℝ)) = (n:ℝ)^2 := by
        field_simp
      linarith
    have hA_hi : A ≤ (n:ℝ)/((n:ℝ)-1) := by
      rw [hA, div_le_iff₀ hDpos]
      have h1 : ((n:ℝ)/((n:ℝ)-1))*((n:ℝ)*((n:ℝ)-1)) = (n:ℝ)^2 := by
        field_simp
      have h2 : ((n:ℝ)/((n:ℝ)-1))*((n:ℝ)*((n:ℝ)-1)) ≤ ((n:ℝ)/((n:ℝ)-1))*D :=
        mul_le_mul_of_nonneg_left hDlo
          (div_nonneg (le_of_lt hn0) (le_of_lt hnm1))
      linarith
    have hBhi2 : B ≤ ((n:ℝ)+1)/(n:ℝ) := by
      have heq : (1:ℝ) + 1/(n:ℝ) = ((n:ℝ)+1)/(n:ℝ) := by field_simp
      rwa [heq] at hBhi
    have hAB : |A*B - 1| ≤ 4/(n:ℝ) := by
      rw [abs_le]
      have hUB : A*B ≤ ((n:ℝ)/((n:ℝ)-1))*(((n:ℝ)+1)/(n:ℝ)) :=
        mul_le_mul hA_hi hBhi2 hBno
          (div_nonneg (le_of_lt hn0) (le_of_lt hnm1))
      have hUB2 : ((n:ℝ)/((n:ℝ)-1))*(((n:ℝ)+1)/(n:ℝ)) ≤ 1 + 4/(n:ℝ) := by
        field_simp
        nlinarith [hnR]
      have hLB : ((n:ℝ)/((n:ℝ)+1))*1 ≤ A*B :=
        mul_le_mul hA_lo hBlo (by norm_num) hAno
      have hLB2 : 1 - 4/(n:ℝ) ≤ ((n:ℝ)/((n:ℝ)+1))*1 := by
        field_simp
        nlinarith [hnR]
      constructor <;> linarith
    have hphi := phi_mem hx0 hx1
    have hR_nn : 0 ≤ R := by
      rw [hR]; exact le_of_lt (Real.rpow_pos_of_pos hn0 _)
    have hR_le : R ≤ 1 := by
      rw [hR]
      apply Real.rpow_le_one_of_one_le_of_nonpos
      · exact_mod_cast (show 1 ≤ n by omega)
      · exact neg_nonpos.mpr hx0
    have hdiff : (n:ℝ) * (-1 : ℝ) ^ (n + 1) * (∏ j ∈ Finset.range n, (x - (j : ℝ)))
        / (n.factorial : ℝ) - R*φ = (R*φ)*(A*B - 1) := by
      rw [hN4]; ring
    have hfin : |(n:ℝ) * (-1 : ℝ) ^ (n + 1) * (∏ j ∈ Finset.range n, (x - (j : ℝ)))
        / (n.factorial : ℝ) - R*φ| ≤ 8/(n:ℝ) := by
      rw [hdiff, abs_mul, abs_of_nonneg (mul_nonneg hR_nn hphi.1)]
      have h1 : R*φ ≤ 1*2 := mul_le_mul hR_le hphi.2 hphi.1 (by norm_num)
      have h2 : (R*φ)*|A*B-1| ≤ (1*2)*(4/(n:ℝ)) :=
        mul_le_mul h1 hAB (abs_nonneg _) (by norm_num)
      have e : (1*2)*(4/(n:ℝ)) = 8/(n:ℝ) := by ring
      linarith
    simpa [hR, hφ] using hfin

private theorem contDiff_inv_gamma (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun s : ℝ => (Real.Gamma s)⁻¹) := by
  have hC : ContDiff ℂ n (fun s : ℂ => (Complex.Gamma s)⁻¹) :=
    Complex.differentiable_one_div_Gamma.contDiff
  have hR := ContDiff.real_of_complex hC
  have heq : (fun x : ℝ => ((Complex.Gamma (x : ℂ))⁻¹).re)
      = (fun s : ℝ => (Real.Gamma s)⁻¹) := by
    funext x
    rw [Complex.Gamma_ofReal, ← Complex.ofReal_inv, Complex.ofReal_re]
  have hR' : ContDiff ℝ n (fun x : ℝ => ((Complex.Gamma (x : ℂ))⁻¹).re) := hR
  rw [heq] at hR'
  exact hR'

private theorem phi_eq_neg_inv_gamma_neg (x : ℝ) :
    x * (Real.Gamma (1 - x))⁻¹ = -((Real.Gamma (-x))⁻¹) := by
  by_cases hx : x = 0
  · subst hx; simp [Real.Gamma_zero]
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    have h := Real.Gamma_add_one hnx
    have heq : -x + 1 = 1 - x := by ring
    rw [heq] at h
    rw [h, mul_inv]
    have hxx : x * (-x)⁻¹ = -1 := by
      rw [inv_neg, mul_neg, mul_inv_cancel₀ hx]
    calc x * ((-x)⁻¹ * (Real.Gamma (-x))⁻¹)
        = (x * (-x)⁻¹) * (Real.Gamma (-x))⁻¹ := by ring
      _ = -1 * (Real.Gamma (-x))⁻¹ := by rw [hxx]
      _ = -((Real.Gamma (-x))⁻¹) := by ring

private theorem contDiff_phi (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹) := by
  have h1 : ContDiff ℝ n (fun s : ℝ => (Real.Gamma s)⁻¹) := contDiff_inv_gamma n
  have hneg : ContDiff ℝ n (fun x : ℝ => -x) := contDiff_neg
  have hcomp : ContDiff ℝ n (fun x : ℝ => (Real.Gamma (-x))⁻¹) :=
    h1.comp hneg
  have hphi : (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹)
      = (fun x : ℝ => -((Real.Gamma (-x))⁻¹)) := by
    funext x; exact phi_eq_neg_inv_gamma_neg x
  rw [hphi]
  exact hcomp.neg

private theorem phi_zero : (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹) (0 : ℝ) = 0 := by
  simp

private theorem phi_iteratedDeriv (k : ℕ) :
    iteratedDeriv (k + 1) (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹) (0 : ℝ)
      = (-1 : ℝ) ^ k * iteratedDeriv (k + 1) (fun s : ℝ => (Real.Gamma s)⁻¹) (0 : ℝ) := by
  have hphi : (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹)
      = (fun x : ℝ => -((Real.Gamma (-x))⁻¹)) := by
    funext x; exact phi_eq_neg_inv_gamma_neg x
  have h2 : (fun x : ℝ => -((Real.Gamma (-x))⁻¹))
      = -(fun x : ℝ => (Real.Gamma (-x))⁻¹) := by
    funext x; rfl
  have h3 : (fun x : ℝ => (Real.Gamma (-x))⁻¹)
      = (fun x : ℝ => (fun s : ℝ => (Real.Gamma s)⁻¹) (-x)) := by
    funext x; rfl
  rw [hphi, h2, iteratedDeriv_neg, h3,
    iteratedDeriv_comp_neg (k + 1) (fun s : ℝ => (Real.Gamma s)⁻¹) 0]
  simp only [neg_zero, smul_eq_mul]
  rw [pow_succ]
  ring

private theorem n_mul_b_sub_laplace_isBigO (b : ℕ → ℝ)
    (hb : ∀ n : ℕ, b n = (∫ x in (0 : ℝ)..1, ∏ j ∈ Finset.range n, (x - (j : ℝ))) /
      (Nat.factorial n : ℝ)) :
    (fun n : ℕ => (n:ℝ) * (-1 : ℝ)^(n+1) * b n
      - ∫ x in (0:ℝ)..1, (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹))
      =O[Filter.atTop] (fun n : ℕ => 1 / (n:ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 8
  rw [Filter.eventually_atTop]
  refine ⟨2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := hn
  have hnR : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
  have hn0 : (0:ℝ) < (n:ℝ) := by linarith
  have hn_ne : (n:ℝ) ≠ 0 := ne_of_gt hn0
  have hcontP : Continuous (fun x : ℝ => ∏ j ∈ Finset.range n, (x - (j:ℝ))) := by
    continuity
  have hcont1 : Continuous (fun x : ℝ => (n:ℝ) * (-1 : ℝ)^(n+1)
      * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ)) := by
    continuity
  have hR_cont : Continuous (fun x : ℝ => (n:ℝ)^(-x)) :=
    (Real.continuous_const_rpow hn_ne).comp continuous_neg
  have hcont2 : Continuous (fun x : ℝ => (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹)) :=
    hR_cont.mul (contDiff_phi ⊤).continuous
  have hint1 : IntervalIntegrable (fun x : ℝ => (n:ℝ) * (-1 : ℝ)^(n+1)
      * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ))
      MeasureTheory.volume 0 1 :=
    hcont1.intervalIntegrable 0 1
  have hint2 : IntervalIntegrable (fun x : ℝ => (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹))
      MeasureTheory.volume 0 1 :=
    hcont2.intervalIntegrable 0 1
  have hb_n : (n:ℝ) * (-1 : ℝ)^(n+1) * b n
      = ∫ x in (0:ℝ)..1, (n:ℝ) * (-1 : ℝ)^(n+1)
        * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ) := by
    rw [hb n]
    have hSP : (fun x : ℝ => (n:ℝ) * (-1 : ℝ)^(n+1)
          * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ))
        = (fun x : ℝ => ((n:ℝ) * (-1 : ℝ)^(n+1) / (n.factorial : ℝ))
          * (∏ j ∈ Finset.range n, (x - (j : ℝ)))) := by
      funext x; ring
    rw [hSP, intervalIntegral.integral_const_mul]
    ring
  have hdiff_int : (n:ℝ) * (-1 : ℝ)^(n+1) * b n
        - ∫ x in (0:ℝ)..1, (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹)
      = ∫ x in (0:ℝ)..1, ((n:ℝ) * (-1 : ℝ)^(n+1)
        * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ)
        - (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹)) := by
    rw [hb_n, ← intervalIntegral.integral_sub hint1 hint2]
  have hnorm : ∀ x ∈ Set.uIoc (0:ℝ) 1,
      ‖(n:ℝ) * (-1 : ℝ)^(n+1) * (∏ j ∈ Finset.range n, (x - (j : ℝ))) / (n.factorial : ℝ)
        - (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹)‖ ≤ 8/(n:ℝ) := by
    intro x hx
    rw [Real.norm_eq_abs]
    rw [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] at hx
    exact abs_integrand_sub_le n hn2 x (Set.Ioc_subset_Icc_self hx)
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hnorm
  rw [hdiff_int]
  have e0 : |(1:ℝ) - 0| = 1 := by norm_num
  rw [e0, mul_one] at hle
  have e1 : (8:ℝ) * ‖(1:ℝ)/(n:ℝ)‖ = 8/(n:ℝ) := by
    rw [Real.norm_eq_abs, abs_of_pos (div_pos one_pos hn0)]
    ring
  rw [e1]
  exact hle

private theorem one_div_n_isLittleO_one_div_log_pow (j : ℕ) :
    (fun n : ℕ => (1:ℝ)/(n:ℝ)) =o[Filter.atTop] (fun n : ℕ => 1/(Real.log (n:ℝ))^j) := by
  have h : (fun x : ℝ => (Real.log x)^j) =o[Filter.atTop] (fun x : ℝ => x) :=
    Real.isLittleO_pow_log_id_atTop
  have hc : Filter.Tendsto (fun n : ℕ => (n:ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have h2 : (fun n : ℕ => (Real.log (n:ℝ))^j) =o[Filter.atTop] (fun n : ℕ => (n:ℝ)) :=
    h.comp_tendsto hc
  have hside : ∀ᶠ n : ℕ in Filter.atTop,
      ((Real.log (n:ℝ))^j = 0 → (n:ℝ) = 0) := by
    rw [Filter.eventually_atTop]
    refine ⟨2, fun n hn => ?_⟩
    intro h0
    have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hlog : 0 < Real.log (n:ℝ) := Real.log_pos hn1
    exact absurd h0 (pow_ne_zero j (ne_of_gt hlog))
  have hinv := h2.inv_rev hside
  simpa only [inv_eq_one_div] using hinv

private theorem n_mul_b_sub_laplace_isLittleO (b : ℕ → ℝ)
    (hb : ∀ n : ℕ, b n = (∫ x in (0 : ℝ)..1, ∏ j ∈ Finset.range n, (x - (j : ℝ))) /
      (Nat.factorial n : ℝ)) (j : ℕ) :
    (fun n : ℕ => (n:ℝ) * (-1 : ℝ)^(n+1) * b n
      - ∫ x in (0:ℝ)..1, (n:ℝ)^(-x) * (x * (Real.Gamma (1 - x))⁻¹))
      =o[Filter.atTop] (fun n : ℕ => 1/(Real.log (n:ℝ))^j) :=
  (n_mul_b_sub_laplace_isBigO b hb).trans_isLittleO
    (one_div_n_isLittleO_one_div_log_pow j)

private theorem sub_taylor_isBigO (f : ℝ → ℝ) (hcont : ContDiff ℝ ⊤ f) (hf0 : f 0 = 0) (N : ℕ) :
    (fun s => f s - ∑ k ∈ Finset.range N,
      (iteratedDeriv (k+1) f 0 / ((k + 1).factorial : ℝ)) * s^(k+1))
      =O[nhdsWithin 0 (Set.Ioi 0)] (fun s => s^(N+1)) := by
  have hcontN : ContDiff ℝ ((N + 1 : ℕ) : WithTop ℕ∞) f := hcont.of_le le_top
  have htay := taylor_isLittleO_univ (f := f) (x₀ := (0:ℝ)) (n := N + 1) hcontN
  have htay' : (fun x => f x - taylorWithinEval f (N+1) Set.univ 0 x)
      =o[nhds (0:ℝ)] (fun x => x^(N+1)) := by
    simpa only [sub_zero] using htay
  have hterm : ∀ k : ℕ, ∀ x : ℝ,
      ((((k.factorial : ℝ))⁻¹ * (x - (0:ℝ))^k) • iteratedDerivWithin k f Set.univ (0:ℝ))
        = (iteratedDeriv k f 0 / ((k.factorial : ℝ))) * x^k := by
    intro k x
    rw [iteratedDerivWithin_univ, sub_zero, smul_eq_mul]
    ring
  have hc0 : ∀ x : ℝ,
      (iteratedDeriv 0 f 0 / ((0).factorial : ℝ)) * x^(0:ℕ) = 0 := by
    intro x; simp [hf0]
  have hT : ∀ x : ℝ, taylorWithinEval f (N+1) Set.univ 0 x
      = (∑ k ∈ Finset.range N,
          (iteratedDeriv (k+1) f 0 / ((k + 1).factorial : ℝ)) * x^(k+1))
        + (iteratedDeriv (N+1) f 0 / (((N + 1).factorial : ℕ) : ℝ)) * x^(N+1) := by
    intro x
    rw [taylor_within_apply]
    simp only [hterm]
    rw [Finset.sum_range_succ', hc0 x, add_zero, Finset.sum_range_succ]
  have ho_top : (fun s : ℝ => (iteratedDeriv (N+1) f 0 / (((N + 1).factorial : ℕ) : ℝ)) * s^(N+1))
      =O[nhds (0:ℝ)] (fun s => s^(N+1)) := by
    apply Asymptotics.IsBigO.of_bound ‖iteratedDeriv (N+1) f 0 / (((N + 1).factorial : ℕ) : ℝ)‖
    apply Filter.Eventually.of_forall
    intro s
    rw [norm_mul]
  have hcomb : (fun x => (f x - taylorWithinEval f (N+1) Set.univ 0 x)
        + (iteratedDeriv (N+1) f 0 / (((N + 1).factorial : ℕ) : ℝ)) * x^(N+1))
      =O[nhds (0:ℝ)] (fun x => x^(N+1)) :=
    Asymptotics.IsLittleO.add_isBigO htay' ho_top
  have heq : (fun s => f s - ∑ k ∈ Finset.range N,
        (iteratedDeriv (k+1) f 0 / ((k + 1).factorial : ℝ)) * s^(k+1))
      = (fun s => (f s - taylorWithinEval f (N+1) Set.univ 0 s)
        + (iteratedDeriv (N+1) f 0 / (((N + 1).factorial : ℕ) : ℝ)) * s^(N+1)) := by
    funext s; rw [hT s]; ring
  rw [heq]
  exact hcomb.mono nhdsWithin_le_nhds

private theorem watson_unit_interval (f : ℝ → ℝ) (hcont : ContDiff ℝ ⊤ f) (hf0 : f 0 = 0)
    (N : ℕ) :
    (fun M : ℝ => (∫ x in (0 : ℝ)..1, f x * Real.exp (-M * x))
      - ∑ k ∈ Finset.range N,
        (((k + 1).factorial : ℝ) * (iteratedDeriv (k + 1) f 0 / ((k + 1).factorial : ℝ))
          / M ^ (k + 2)))
      =O[Filter.atTop] (fun M : ℝ => 1 / M ^ (N + 2)) := by
  have hfun : ∀ m : ℝ,
      (fun s : ℝ => Set.indicator (Set.Ioc (0 : ℝ) 1) f s * Real.exp (-m * s))
      = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun s : ℝ => f s * Real.exp (-m * s)) := by
    intro m
    funext s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1
    · simp only [Set.indicator_of_mem hs]
    · simp only [Set.indicator_of_notMem hs, zero_mul]
  have hlocal : ∀ N' : ℕ, Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0))
      (fun s : ℝ => Set.indicator (Set.Ioc (0 : ℝ) 1) f s
        - ∑ k ∈ Finset.range N',
          (iteratedDeriv (k + 1) f 0 / ((k + 1).factorial : ℝ)) * s ^ (k + 1))
      (fun s : ℝ => s ^ (N' + 1)) := by
    intro N'
    have hbase := sub_taylor_isBigO f hcont hf0 N'
    refine hbase.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    unfold Filter.EventuallyEq
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff_ball]
    refine ⟨1, one_pos, fun s hs hpos => ?_⟩
    rw [Metric.mem_ball, dist_eq_norm, sub_zero, Real.norm_eq_abs] at hs
    have hlt : s < 1 := (abs_lt.mp hs).2
    have hmem : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hpos, le_of_lt hlt⟩
    simp only [Set.indicator_of_mem hmem]
  have hconv : ∃ m₀ : ℝ, ∀ m ≥ m₀, MeasureTheory.IntegrableOn
      (fun s : ℝ => Set.indicator (Set.Ioc (0 : ℝ) 1) f s * Real.exp (-m * s))
      (Set.Ioi 0) := by
    refine ⟨0, fun m _ => ?_⟩
    have hFcont : Continuous (fun s : ℝ => f s * Real.exp (-m * s)) :=
      hcont.continuous.mul
        (Real.continuous_exp.comp (continuous_const.mul continuous_id'))
    have hIoc : MeasureTheory.IntegrableOn (fun s : ℝ => f s * Real.exp (-m * s))
        (Set.Ioc (0 : ℝ) 1) :=
      hFcont.integrableOn_Ioc
    rw [hfun m]
    exact (hIoc.integrable_indicator measurableSet_Ioc).integrableOn
  have hW := watson_laplace_integral_asymptotic
    (Set.indicator (Set.Ioc (0 : ℝ) 1) f)
    (fun j : ℕ => iteratedDeriv j f 0 / (j.factorial : ℝ)) hlocal hconv N
  have hint : ∀ M : ℝ, (∫ s in Set.Ioi 0,
      Set.indicator (Set.Ioc (0 : ℝ) 1) f s * Real.exp (-M * s))
      = ∫ x in (0 : ℝ)..1, f x * Real.exp (-M * x) := by
    intro M
    rw [hfun M, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
      Set.inter_eq_self_of_subset_right Set.Ioc_subset_Ioi_self,
      intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  have hsums : ∀ M : ℝ, (∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℕ) : ℝ)
        * (fun j : ℕ => iteratedDeriv j f 0 / (j.factorial : ℝ)) (k + 1) / M ^ (k + 2))
      = ∑ k ∈ Finset.range N, ((k + 1).factorial : ℝ)
        * (iteratedDeriv (k + 1) f 0 / ((k + 1).factorial : ℝ)) / M ^ (k + 2) :=
    fun _ => rfl
  have e : ∀ M : ℝ, (∫ s in Set.Ioi 0,
        Set.indicator (Set.Ioc (0 : ℝ) 1) f s * Real.exp (-M * s))
        - ∑ k ∈ Finset.range N, ((Nat.factorial (k + 1) : ℕ) : ℝ)
          * (fun j : ℕ => iteratedDeriv j f 0 / (j.factorial : ℝ)) (k + 1) / M ^ (k + 2)
      = (∫ x in (0 : ℝ)..1, f x * Real.exp (-M * x))
        - ∑ k ∈ Finset.range N, ((k + 1).factorial : ℝ)
          * (iteratedDeriv (k + 1) f 0 / ((k + 1).factorial : ℝ)) / M ^ (k + 2) := by
    intro M
    rw [hint M, hsums M]
  exact hW.congr_left e

private theorem laplace_phi_log_asymptotic (β : ℕ → ℝ)
    (hβ : ∀ k : ℕ, β k = (-1 : ℝ) ^ k
      * iteratedDeriv (k + 1) (fun s : ℝ => (Real.Gamma s)⁻¹) (0 : ℝ))
    (m : ℕ) :
    (fun n : ℕ => (∫ x in (0 : ℝ)..1, (n : ℝ) ^ (-x) * (x * (Real.Gamma (1 - x))⁻¹))
      - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2))
      =o[Filter.atTop] (fun n : ℕ => 1 / (Real.log (n : ℝ)) ^ (m + 2)) := by
  have hcoeff : ∀ k : ℕ, ((k + 1).factorial : ℝ)
      * (iteratedDeriv (k + 1) (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹) 0
        / ((k + 1).factorial : ℝ)) = β k := by
    intro k
    have hne : ((k + 1).factorial : ℝ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero (k + 1)
    rw [mul_comm ((k + 1).factorial : ℝ), div_mul_cancel₀ _ hne,
      phi_iteratedDeriv k, ← hβ k]
  have hWβ : (fun M : ℝ => (∫ x in (0 : ℝ)..1,
            (x * (Real.Gamma (1 - x))⁻¹) * Real.exp (-M * x))
          - ∑ k ∈ Finset.range (m + 1), β k / M ^ (k + 2))
      =O[Filter.atTop] (fun M : ℝ => 1 / M ^ (m + 3)) := by
    have hsumM : ∀ M : ℝ, (∑ k ∈ Finset.range (m + 1),
            ((k + 1).factorial : ℝ)
              * (iteratedDeriv (k + 1) (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹) 0
                / ((k + 1).factorial : ℝ)) / M ^ (k + 2))
        = ∑ k ∈ Finset.range (m + 1), β k / M ^ (k + 2) := by
      intro M
      apply Finset.sum_congr rfl
      intro k _
      rw [hcoeff k]
    have hexp3 : m + 1 + 2 = m + 3 := by omega
    have hWred : (fun M : ℝ => (∫ x in (0 : ℝ)..1,
              (x * (Real.Gamma (1 - x))⁻¹) * Real.exp (-M * x))
            - ∑ k ∈ Finset.range (m + 1), ((k + 1).factorial : ℝ)
              * (iteratedDeriv (k + 1) (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹) 0
                / ((k + 1).factorial : ℝ)) / M ^ (k + 2))
        =O[Filter.atTop] (fun M : ℝ => 1 / M ^ (m + 1 + 2)) :=
      watson_unit_interval (fun x : ℝ => x * (Real.Gamma (1 - x))⁻¹)
        (contDiff_phi ⊤) phi_zero (m + 1)
    simp only [hexp3, hsumM] at hWred
    exact hWred
  have hlogtend : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ))
      Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmain : (fun n : ℕ => (∫ x in (0 : ℝ)..1,
            (x * (Real.Gamma (1 - x))⁻¹) * Real.exp (-(Real.log (n : ℝ)) * x))
          - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2))
      =O[Filter.atTop] (fun n : ℕ => 1 / (Real.log (n : ℝ)) ^ (m + 3)) :=
    hWβ.comp_tendsto hlogtend
  have hmain2 : (fun n : ℕ => (∫ x in (0 : ℝ)..1,
            (n : ℝ) ^ (-x) * (x * (Real.Gamma (1 - x))⁻¹))
          - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2))
      =O[Filter.atTop] (fun n : ℕ => 1 / (Real.log (n : ℝ)) ^ (m + 3)) := by
    refine hmain.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hx : ∀ x : ℝ, (x * (Real.Gamma (1 - x))⁻¹) * Real.exp (-(Real.log (n : ℝ)) * x)
        = (n : ℝ) ^ (-x) * (x * (Real.Gamma (1 - x))⁻¹) := by
      intro x
      have e : Real.log (n : ℝ) * (-x) = -(Real.log (n : ℝ)) * x := by ring
      rw [Real.rpow_def_of_pos hn0, e]
      ring
    change (∫ x in (0 : ℝ)..1,
            (x * (Real.Gamma (1 - x))⁻¹) * Real.exp (-(Real.log (n : ℝ)) * x))
          - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2)
        = (∫ x in (0 : ℝ)..1, (n : ℝ) ^ (-x) * (x * (Real.Gamma (1 - x))⁻¹))
          - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2)
    simp only [hx]
  have herr : (fun n : ℕ => (1 : ℝ) / (Real.log (n : ℝ)) ^ (m + 3))
      =o[Filter.atTop] (fun n : ℕ => 1 / (Real.log (n : ℝ)) ^ (m + 2)) := by
    refine Asymptotics.isLittleO_of_tendsto' ?hg ?ht
    · filter_upwards [Filter.eventually_ge_atTop 2] with n hn h0
      have hlog : (0 : ℝ) < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      exact absurd h0 (one_div_ne_zero (pow_ne_zero _ (ne_of_gt hlog)))
    · have heq : ∀ᶠ n : ℕ in Filter.atTop,
          ((1 : ℝ) / (Real.log (n : ℝ)) ^ (m + 3)) / (1 / (Real.log (n : ℝ)) ^ (m + 2))
            = 1 / Real.log (n : ℝ) := by
        filter_upwards [Filter.eventually_ge_atTop 2] with n hn
        have hL : Real.log (n : ℝ) ≠ 0 :=
          ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < n by omega)))
        have hLm2 : (Real.log (n : ℝ)) ^ (m + 2) ≠ 0 := pow_ne_zero _ hL
        have h1 : (1 : ℝ) / (Real.log (n : ℝ)) ^ (m + 2) ≠ 0 := one_div_ne_zero hLm2
        have hpow : (Real.log (n : ℝ)) ^ (m + 3)
            = (Real.log (n : ℝ)) ^ (m + 2) * Real.log (n : ℝ) := by
          rw [show m + 3 = (m + 2) + 1 from by omega, pow_succ]
        have hAL : (Real.log (n : ℝ)) ^ (m + 2) * Real.log (n : ℝ) ≠ 0 :=
          mul_ne_zero hLm2 hL
        rw [div_eq_div_iff h1 hL, one_mul, hpow, div_mul_eq_mul_div, one_mul,
          div_eq_iff hAL, div_mul_eq_mul_div, one_mul, mul_div_cancel_left₀ _ hLm2]
      have hlim : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / Real.log (n : ℝ))
          Filter.atTop (nhds 0) := by
        have h2 := hlogtend.inv_tendsto_atTop
        have heq2 : (fun n : ℕ => Real.log (n : ℝ))⁻¹
            = fun n : ℕ => (1 : ℝ) / Real.log (n : ℝ) := by
          funext n
          simp only [Pi.inv_apply, inv_eq_one_div]
        rw [heq2] at h2
        exact h2
      exact (Filter.tendsto_congr' heq).mpr hlim
  exact hmain2.trans_isLittleO herr

/-- **Asymptotic expansion of the Bernoulli numbers of the second kind.** For a natural number
$n$ let $b_n = \frac{1}{n!} \int_0^1 x (x - 1) \cdots (x - n + 1) dx$, and for a natural
number $k$ let $\beta_k$ be $(-1)^k$ times the $(k + 1)$-th derivative of $1 / \Gamma$ at $0$.
Then for every natural number $m$, as $n \to \infty$,
$$b_n - \frac{(-1)^{n+1}}{n (\log n)^2} \sum_{k=0}^{m} \frac{\beta_k}{(\log n)^k} =
o\left(\frac{1}{n (\log n)^{m+2}}\right).$$

The main term $(-1)^{n+1} / (n (\log n)^2)$ is Steffensen's approximation, as noted in the
source.

Proves `Wanted` entry `bernoulli_second_kind_asymptotic`.

Source: Gergő Nemes, "An Asymptotic Expansion for the Bernoulli
Numbers of the Second Kind," Journal of Integer Sequences 14 (2011),
Article 11.4.8, Theorem (label theorem), equations (eq1)–(eq2),
lines 124–133,
https://cs.uwaterloo.ca/journals/JIS/VOL14/Nemes/nemes4.tex
-/
theorem bernoulli_second_kind_asymptotic (b : ℕ → ℝ) (β : ℕ → ℝ)
  (hb : ∀ n : ℕ, b n = (∫ x in (0 : ℝ)..1, ∏ j ∈ Finset.range n, (x - (j : ℝ))) /
    (Nat.factorial n : ℝ))
  (hβ : ∀ k : ℕ, β k = (-1 : ℝ) ^ k * iteratedDeriv (k + 1) (fun s : ℝ => (Real.Gamma s)⁻¹)
    (0 : ℝ)) :
  ∀ m : ℕ, Asymptotics.IsLittleO Filter.atTop
    (fun n : ℕ => b n -
    (((-1 : ℝ) ^ (n + 1) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)) * ∑ k ∈ Finset.range (m + 1), β k /
    (Real.log (n : ℝ)) ^ k)) (fun n : ℕ => 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ (m + 2))) := by
  intro m
  have h11 := n_mul_b_sub_laplace_isLittleO b hb (m + 2)
  have h10 := laplace_phi_log_asymptotic β hβ m
  have hE : (fun n : ℕ => (n : ℝ) * (-1 : ℝ) ^ (n + 1) * b n
      - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2))
      =o[Filter.atTop] (fun n : ℕ => 1 / (Real.log (n : ℝ)) ^ (m + 2)) := by
    have hsum := h11.add h10
    refine hsum.congr' ?_ (Filter.Eventually.of_forall fun _ => rfl)
    apply Filter.Eventually.of_forall
    intro n
    change ((n : ℝ) * (-1 : ℝ) ^ (n + 1) * b n
          - ∫ x in (0 : ℝ)..1, (n : ℝ) ^ (-x) * (x * (Real.Gamma (1 - x))⁻¹))
          + ((∫ x in (0 : ℝ)..1, (n : ℝ) ^ (-x) * (x * (Real.Gamma (1 - x))⁻¹))
          - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2))
        = (n : ℝ) * (-1 : ℝ) ^ (n + 1) * b n
          - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2)
    ring
  have hscale : (fun n : ℕ => (-1 : ℝ) ^ (n + 1) / (n : ℝ))
      =O[Filter.atTop] (fun n : ℕ => 1 / (n : ℝ)) := by
    apply Asymptotics.isBigO_of_le
    intro n
    have h1 : |(-1 : ℝ) ^ (n + 1)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_div, abs_div, h1, abs_one]
  have hmul := hscale.mul_isLittleO hE
  refine hmul.congr' ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hN : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hL : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos hn1)
    have hsign : (-1 : ℝ) ^ (n + 1) * (-1 : ℝ) ^ (n + 1) = 1 := by
      rw [← pow_add]
      have hev : Even ((n + 1) + (n + 1)) := ⟨n + 1, by ring⟩
      exact Even.neg_one_pow hev
    have hmain : ((-1 : ℝ) ^ (n + 1) / (n : ℝ))
        * ((n : ℝ) * (-1 : ℝ) ^ (n + 1) * b n) = b n := by
      rw [div_mul_eq_mul_div, div_eq_iff hN]
      linear_combination (b n * (n : ℝ)) * hsign
    have hpow : ∀ k : ℕ, (Real.log (n : ℝ)) ^ (k + 2)
        = (Real.log (n : ℝ)) ^ k * (Real.log (n : ℝ)) ^ 2 := fun k => pow_add _ _ _
    have hS : ((-1 : ℝ) ^ (n + 1) / (n : ℝ))
          * ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2)
        = ((-1 : ℝ) ^ (n + 1) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2))
          * ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ k := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      have hLk : (Real.log (n : ℝ)) ^ k ≠ 0 := pow_ne_zero _ hL
      have hL2 : (Real.log (n : ℝ)) ^ 2 ≠ 0 := pow_ne_zero _ hL
      have hAB : (Real.log (n : ℝ)) ^ k * (Real.log (n : ℝ)) ^ 2 ≠ 0 :=
        mul_ne_zero hLk hL2
      have hNB : (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≠ 0 := mul_ne_zero hN hL2
      rw [hpow k]
      field_simp
    change ((-1 : ℝ) ^ (n + 1) / (n : ℝ))
          * ((n : ℝ) * (-1 : ℝ) ^ (n + 1) * b n
            - ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ (k + 2))
        = b n - (((-1 : ℝ) ^ (n + 1) / ((n : ℝ) * (Real.log (n : ℝ)) ^ 2))
          * ∑ k ∈ Finset.range (m + 1), β k / (Real.log (n : ℝ)) ^ k)
    rw [mul_sub, hmain, hS]
  · filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
    have hN : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
    have hL : Real.log (n : ℝ) ≠ 0 :=
      ne_of_gt (Real.log_pos hn1)
    have hM : (Real.log (n : ℝ)) ^ (m + 2) ≠ 0 := pow_ne_zero _ hL
    have hNM : (n : ℝ) * (Real.log (n : ℝ)) ^ (m + 2) ≠ 0 := mul_ne_zero hN hM
    change (1 / (n : ℝ)) * (1 / (Real.log (n : ℝ)) ^ (m + 2))
      = 1 / ((n : ℝ) * (Real.log (n : ℝ)) ^ (m + 2))
    rw [div_mul_eq_mul_div, one_mul, div_eq_div_iff hN hNM, one_mul,
      div_mul_eq_mul_div, one_mul, div_eq_iff hM]

end MetaMathlibExt
end
