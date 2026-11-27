/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Analysis.MellinTransform.Gaussian
public import MathlibExt.Analysis.MellinTransform.GaussianLaplaceSeries
public import MathlibExt.Analysis.SpecialFunctions.ParabolicCylinder.GammaProduct
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The Gaussian integral representation of U

For complex s,z with Re(s)>0, the convergent Mellin integral satisfies

∫₀∞ t^(s-1) exp(-t²/2-zt) dt = exp(z²/4) Γ(s) U(s-1/2,z).

Equivalently, for Re(a)>-1/2, U(a,z) is exp(-z²/4)/Γ(a+1/2) times the integral with exponent
t^(a-1/2). The complex argument z is arbitrary. Splitting the Gaussian moment series into even
and odd terms gives the two confluent series in the defining normalization.

## References

The integral representation is DLMF §12.5(i), equation 12.5.1. Its Mellin formulation is used in
Helfgott, *Major arcs for Goldbach's problem*, arXiv:1305.2897v4, §3.2, equation (3.8), with
`z=-2πiδ` for the oscillatory Gaussian. The complex argument `z` here is unrestricted; the
integral is asserted only for `Re(s)>0`.
-/

public section

noncomputable section

open Complex MeasureTheory Set

private lemma gamma_three_halves : Gamma (3 / 2 : ℂ) = (1 / 2 : ℂ) * Gamma (1 / 2) := by
  simpa only [show (1 / 2 : ℂ) + 1 = 3 / 2 by ring] using
    Gamma_add_one (1 / 2 : ℂ) (by norm_num)

private lemma factorial_even (k : ℕ) :
    ((2 * k).factorial : ℂ) * Gamma (1 / 2) =
      (2 : ℂ) ^ (2 * k) * (k.factorial : ℂ) * Gamma ((k : ℂ) + 1 / 2) := by
  have hhalf : (k : ℂ) + 1 / 2 + 1 / 2 = (k : ℂ) + 1 := by ring
  have htwice : 2 * ((k : ℂ) + 1 / 2) = ((2 * k : ℕ) : ℂ) + 1 := by push_cast; ring
  have hexponent : 1 - 2 * ((k : ℂ) + 1 / 2) = -((2 * k : ℕ) : ℂ) := by push_cast; ring
  have h := Gamma_mul_Gamma_add_half ((k : ℂ) + 1 / 2)
  have hhalfGamma : Gamma (1 / 2 : ℂ) = (Real.sqrt Real.pi : ℂ) := by
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat, Real.Gamma_one_half_eq] using
      Gamma_ofReal (1 / 2 : ℝ)
  rw [hhalf, hexponent, htwice, Gamma_nat_eq_factorial k, Gamma_nat_eq_factorial (2 * k),
    ← hhalfGamma, cpow_neg, cpow_natCast] at h
  have htwo : (2 : ℂ) ^ (2 * k) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc
    ((2 * k).factorial : ℂ) * Gamma (1 / 2) =
        (((2 * k).factorial : ℂ) * ((2 : ℂ) ^ (2 * k))⁻¹ * Gamma (1 / 2)) *
          (2 : ℂ) ^ (2 * k) := by field_simp [htwo]
    _ = (Gamma ((k : ℂ) + 1 / 2) * (k.factorial : ℂ)) * (2 : ℂ) ^ (2 * k) := by rw [← h]
    _ = _ := by ring

private lemma factorial_odd (k : ℕ) :
    ((2 * k + 1).factorial : ℂ) * Gamma (3 / 2) =
      (2 : ℂ) ^ (2 * k) * (k.factorial : ℂ) * Gamma ((k : ℂ) + 3 / 2) := by
  have hpos : 0 < ((k : ℂ) + 1 / 2).re := by
    simpa using (show (0 : ℝ) < (k : ℝ) + 1 / 2 by positivity)
  have hne : (k : ℂ) + 1 / 2 ≠ 0 := by
    apply ne_of_apply_ne re
    simpa only [zero_re] using hpos.ne'
  have hstep : Gamma ((k : ℂ) + 3 / 2) =
      ((k : ℂ) + 1 / 2) * Gamma ((k : ℂ) + 1 / 2) := by
    simpa only [show (k : ℂ) + 1 / 2 + 1 = (k : ℂ) + 3 / 2 by ring] using
      Gamma_add_one ((k : ℂ) + 1 / 2) hne
  calc
    ((2 * k + 1).factorial : ℂ) * Gamma (3 / 2) =
        ((k : ℂ) + 1 / 2) * (((2 * k).factorial : ℂ) * Gamma (1 / 2)) := by
      rw [Nat.factorial_succ, gamma_three_halves]
      push_cast
      ring
    _ = ((k : ℂ) + 1 / 2) *
        ((2 : ℂ) ^ (2 * k) * (k.factorial : ℂ) * Gamma ((k : ℂ) + 1 / 2)) := by
      rw [factorial_even]
    _ = _ := by rw [hstep]; ring

private lemma mellin_gaussian_half (s : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2)) s =
      (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) := by
  have h := (hasMellin_exp_neg_mul_sq (b := 1 / 2) (by norm_num) hs).2
  have hfun : (fun t : ℝ => (Real.exp (-(1 / 2) * t ^ 2) : ℂ)) =
      fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2) := by
    funext t
    rw [ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun] at h
  simp only [ofReal_div, ofReal_one, ofReal_ofNat] at h
  have hconstant : (1 / 2 : ℂ) * ((1 / (1 / 2) : ℂ) ^ (s / 2) * Gamma (s / 2)) =
      (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) := by
    norm_num
    rw [cpow_sub _ _ (by norm_num), cpow_one]
    ring
  exact h.trans hconstant

private def coefficient (s z : ℂ) (n : ℕ) : ℂ :=
  (-z) ^ n / (n.factorial : ℂ) * ((2 : ℂ) ^ ((s + n) / 2 - 1) * Gamma ((s + n) / 2))

private lemma coefficient_even (s z : ℂ) (hs : 0 < s.re) (k : ℕ) :
    coefficient s z (2 * k) =
      ((2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) * Gamma (1 / 2)) *
        (regularizedHGFunCoeff ({s / 2} : Multiset ℂ) ({1 / 2} : Multiset ℂ) k *
          (z ^ 2 / 2) ^ k) := by
  have hA : 0 < (s / 2).re := by simpa using (show (0 : ℝ) < s.re / 2 by linarith)
  have hGammaA : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hA
  have havoid : ∀ n : ℕ, s / 2 ≠ -n := by
    intro n h
    apply hGammaA
    rw [h, Gamma_neg_nat_eq_zero]
  have hratio : Gamma (s / 2 + k) = (ascPochhammer ℂ k).eval (s / 2) * Gamma (s / 2) :=
    (div_eq_iff hGammaA).mp (Gamma_add_nat_div_Gamma_eq (n := k) (s / 2) havoid)
  have hGammaK : Gamma ((k : ℂ) + 1 / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simpa using (show (0 : ℝ) < (k : ℝ) + 1 / 2 by positivity)
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hfacEven : ((2 * k).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k)
  have htwo : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hhalf : (s + ((2 * k : ℕ) : ℂ)) / 2 = s / 2 + k := by push_cast; ring
  have hexponent : (s + ((2 * k : ℕ) : ℂ)) / 2 - 1 = (s / 2 - 1) + k := by push_cast; ring
  have hz : (-z) ^ (2 * k) = (z ^ 2) ^ k := by rw [pow_mul, neg_sq]
  have hfactorial := factorial_even k
  rw [show (2 : ℂ) ^ (2 * k) = (2 : ℂ) ^ k * (2 : ℂ) ^ k by rw [Nat.two_mul, pow_add]] at hfactorial
  have hdenominator : (2 : ℂ) ^ k / ((2 * k).factorial : ℂ) =
      Gamma (1 / 2) / ((k.factorial : ℂ) * Gamma ((k : ℂ) + 1 / 2) * (2 : ℂ) ^ k) := by
    apply (div_eq_div_iff hfacEven (mul_ne_zero (mul_ne_zero hfac hGammaK) htwo)).mpr
    calc
      (2 : ℂ) ^ k * ((k.factorial : ℂ) * Gamma ((k : ℂ) + 1 / 2) * (2 : ℂ) ^ k) =
          (2 : ℂ) ^ k * (2 : ℂ) ^ k * (k.factorial : ℂ) * Gamma ((k : ℂ) + 1 / 2) := by ring
      _ = ((2 * k).factorial : ℂ) * Gamma (1 / 2) := hfactorial.symm
      _ = _ := by ring
  rw [coefficient, hz, hexponent, cpow_add _ _ (by norm_num), cpow_natCast, hhalf, hratio,
    regularizedHGFunCoeff_singleton_eq, show (1 / 2 : ℂ) + k = (k : ℂ) + 1 / 2 by ring, div_pow]
  calc
    (z ^ 2) ^ k / ((2 * k).factorial : ℂ) *
        (((2 : ℂ) ^ (s / 2 - 1) * (2 : ℂ) ^ k) *
          ((ascPochhammer ℂ k).eval (s / 2) * Gamma (s / 2))) =
        (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) * (ascPochhammer ℂ k).eval (s / 2) *
          (z ^ 2) ^ k * ((2 : ℂ) ^ k / ((2 * k).factorial : ℂ)) := by ring
    _ = (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) * (ascPochhammer ℂ k).eval (s / 2) *
        (z ^ 2) ^ k *
          (Gamma (1 / 2) / ((k.factorial : ℂ) * Gamma ((k : ℂ) + 1 / 2) * (2 : ℂ) ^ k)) := by
      rw [hdenominator]
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

private lemma coefficient_odd (s z : ℂ) (hs : 0 < s.re) (k : ℕ) :
    coefficient s z (2 * k + 1) =
      -((2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2) * z * Gamma (3 / 2)) *
        (regularizedHGFunCoeff ({(s + 1) / 2} : Multiset ℂ) ({3 / 2} : Multiset ℂ) k *
          (z ^ 2 / 2) ^ k) := by
  have hB : 0 < ((s + 1) / 2).re := by
    simpa using (show (0 : ℝ) < (s.re + 1) / 2 by linarith)
  have hGammaB : Gamma ((s + 1) / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hB
  have havoid : ∀ n : ℕ, (s + 1) / 2 ≠ -n := by
    intro n h
    apply hGammaB
    rw [h, Gamma_neg_nat_eq_zero]
  have hratio : Gamma ((s + 1) / 2 + k) =
      (ascPochhammer ℂ k).eval ((s + 1) / 2) * Gamma ((s + 1) / 2) :=
    (div_eq_iff hGammaB).mp (Gamma_add_nat_div_Gamma_eq (n := k) ((s + 1) / 2) havoid)
  have hGammaK : Gamma ((k : ℂ) + 3 / 2) ≠ 0 := by
    apply Gamma_ne_zero_of_re_pos
    simpa using (show (0 : ℝ) < (k : ℝ) + 3 / 2 by positivity)
  have hfac : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hfacOdd : ((2 * k + 1).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * k + 1)
  have htwo : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have hhalf : (s + ((2 * k + 1 : ℕ) : ℂ)) / 2 = (s + 1) / 2 + k := by push_cast; ring
  have hexponent : (s + ((2 * k + 1 : ℕ) : ℂ)) / 2 - 1 = (s / 2 - 1 / 2) + k := by
    push_cast
    ring
  have hz : (-z) ^ (2 * k + 1) = -(z * (z ^ 2) ^ k) := by
    rw [pow_succ, pow_mul, neg_sq]
    ring
  have hfactorial := factorial_odd k
  rw [show (2 : ℂ) ^ (2 * k) = (2 : ℂ) ^ k * (2 : ℂ) ^ k by rw [Nat.two_mul, pow_add]] at hfactorial
  have hdenominator : (2 : ℂ) ^ k / ((2 * k + 1).factorial : ℂ) =
      Gamma (3 / 2) / ((k.factorial : ℂ) * Gamma ((k : ℂ) + 3 / 2) * (2 : ℂ) ^ k) := by
    apply (div_eq_div_iff hfacOdd (mul_ne_zero (mul_ne_zero hfac hGammaK) htwo)).mpr
    calc
      (2 : ℂ) ^ k * ((k.factorial : ℂ) * Gamma ((k : ℂ) + 3 / 2) * (2 : ℂ) ^ k) =
          (2 : ℂ) ^ k * (2 : ℂ) ^ k * (k.factorial : ℂ) * Gamma ((k : ℂ) + 3 / 2) := by ring
      _ = ((2 * k + 1).factorial : ℂ) * Gamma (3 / 2) := hfactorial.symm
      _ = _ := by ring
  rw [coefficient, hz, hexponent, cpow_add _ _ (by norm_num), cpow_natCast, hhalf, hratio,
    regularizedHGFunCoeff_singleton_eq, show (3 / 2 : ℂ) + k = (k : ℂ) + 3 / 2 by ring, div_pow]
  calc
    -(z * (z ^ 2) ^ k) / ((2 * k + 1).factorial : ℂ) *
        (((2 : ℂ) ^ (s / 2 - 1 / 2) * (2 : ℂ) ^ k) *
          ((ascPochhammer ℂ k).eval ((s + 1) / 2) * Gamma ((s + 1) / 2))) =
        -((2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2) * z *
          (ascPochhammer ℂ k).eval ((s + 1) / 2) * (z ^ 2) ^ k) *
          ((2 : ℂ) ^ k / ((2 * k + 1).factorial : ℂ)) := by ring
    _ = -((2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2) * z *
        (ascPochhammer ℂ k).eval ((s + 1) / 2) * (z ^ 2) ^ k) *
          (Gamma (3 / 2) / ((k.factorial : ℂ) * Gamma ((k : ℂ) + 3 / 2) * (2 : ℂ) ^ k)) := by
      rw [hdenominator]
    _ = _ := by simp only [div_eq_mul_inv, mul_inv]; ring

private lemma even_normalization (s : ℂ) (hs : 0 < s.re) :
    Gamma s * (2 : ℂ) ^ (-s / 2) * ((Real.sqrt Real.pi : ℂ) / Gamma ((s + 1) / 2)) =
      (2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) := by
  have h := Gamma_mul_parabolicCylinderU_zero_of_re_pos s hs
  rw [parabolicCylinderU_zero,
    show -(s - 1 / 2) / 2 - 1 / 4 = -s / 2 by ring,
    show (s - 1 / 2) / 2 + 3 / 4 = (s + 1) / 2 by ring] at h
  calc
    Gamma s * (2 : ℂ) ^ (-s / 2) * ((Real.sqrt Real.pi : ℂ) / Gamma ((s + 1) / 2)) =
        Gamma s * ((2 : ℂ) ^ (-s / 2) * (Real.sqrt Real.pi : ℂ) / Gamma ((s + 1) / 2)) := by ring
    _ = _ := h

private lemma odd_normalization (s : ℂ) (hs : 0 < s.re) :
    Gamma s * (2 : ℂ) ^ (-s / 2) * ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (s / 2)) =
      (2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2) := by
  have hA : 0 < (s / 2).re := by simpa using (show (0 : ℝ) < s.re / 2 by linarith)
  have hGammaA : Gamma (s / 2) ≠ 0 := Gamma_ne_zero_of_re_pos hA
  have htwo : (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow]
    simpa only [ofReal_div, ofReal_one, ofReal_ofNat] using
      (ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (1 / 2)).symm
  have hsqrt : (Real.sqrt (2 * Real.pi) : ℂ) =
      (2 : ℂ) ^ (1 / 2 : ℂ) * (Real.sqrt Real.pi : ℂ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ofReal_mul, htwo]
  have hdup : Gamma (s / 2) * Gamma ((s + 1) / 2) =
      Gamma s * (2 : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ) := by
    simpa only [show 2 * (s / 2) = s by ring,
      show s / 2 + 1 / 2 = (s + 1) / 2 by ring] using Gamma_mul_Gamma_add_half (s / 2)
  have hpower : (2 : ℂ) ^ (-s / 2) * (2 : ℂ) ^ (1 / 2 : ℂ) =
      (2 : ℂ) ^ (s / 2 - 1 / 2) * (2 : ℂ) ^ (1 - s) := by
    rw [← cpow_add _ _ (by norm_num), ← cpow_add _ _ (by norm_num)]
    congr 1
    ring
  rw [← mul_div_assoc]
  apply (div_eq_iff hGammaA).mpr
  calc
    Gamma s * (2 : ℂ) ^ (-s / 2) * (Real.sqrt (2 * Real.pi) : ℂ) =
        ((2 : ℂ) ^ (-s / 2) * (2 : ℂ) ^ (1 / 2 : ℂ)) *
          Gamma s * (Real.sqrt Real.pi : ℂ) := by rw [hsqrt]; ring
    _ = ((2 : ℂ) ^ (s / 2 - 1 / 2) * (2 : ℂ) ^ (1 - s)) *
        Gamma s * (Real.sqrt Real.pi : ℂ) := by rw [hpower]
    _ = (2 : ℂ) ^ (s / 2 - 1 / 2) *
        (Gamma s * (2 : ℂ) ^ (1 - s) * (Real.sqrt Real.pi : ℂ)) := by ring
    _ = (2 : ℂ) ^ (s / 2 - 1 / 2) * (Gamma (s / 2) * Gamma ((s + 1) / 2)) := by rw [← hdup]
    _ = ((2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2)) * Gamma (s / 2) := by ring

private lemma hasSum_coefficient (s z : ℂ) (hs : 0 < s.re) :
    HasSum (coefficient s z)
      (mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) s) := by
  have h := hasSum_gaussian_laplace_mellin (s := s) (z := z) hs
  have hfunction : (fun n : ℕ => (-z) ^ n / (n.factorial : ℂ) *
      mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2)) (s + n)) = coefficient s z := by
    funext n
    have hpos : 0 < (s + n).re := by
      simpa only [add_re, natCast_re] using add_pos_of_pos_of_nonneg hs (Nat.cast_nonneg n)
    rw [mellin_gaussian_half (s + n) hpos]
    rfl
  rw [hfunction] at h
  exact h

private lemma mellin_two_series (s z : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) s =
      ((2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) * Gamma (1 / 2)) *
        regularizedHGFun ({s / 2} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2) +
      -((2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2) * z * Gamma (3 / 2)) *
        regularizedHGFun ({(s + 1) / 2} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2) := by
  have heven : HasSum (fun k : ℕ => coefficient s z (2 * k))
      (((2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) * Gamma (1 / 2)) *
        regularizedHGFun ({s / 2} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2)) := by
    have hf : (fun k : ℕ => coefficient s z (2 * k)) = fun k : ℕ =>
        ((2 : ℂ) ^ (s / 2 - 1) * Gamma (s / 2) * Gamma (1 / 2)) *
          (regularizedHGFunCoeff ({s / 2} : Multiset ℂ) ({1 / 2} : Multiset ℂ) k *
            (z ^ 2 / 2) ^ k) := funext (coefficient_even s z hs)
    rw [hf]
    exact (hasSum_regularizedHGFun_singleton (s / 2) (1 / 2) (z ^ 2 / 2)).mul_left _
  have hodd : HasSum (fun k : ℕ => coefficient s z (2 * k + 1))
      (-((2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2) * z * Gamma (3 / 2)) *
        regularizedHGFun ({(s + 1) / 2} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2)) := by
    have hf : (fun k : ℕ => coefficient s z (2 * k + 1)) = fun k : ℕ =>
        -((2 : ℂ) ^ (s / 2 - 1 / 2) * Gamma ((s + 1) / 2) * z * Gamma (3 / 2)) *
          (regularizedHGFunCoeff ({(s + 1) / 2} : Multiset ℂ) ({3 / 2} : Multiset ℂ) k *
            (z ^ 2 / 2) ^ k) := funext (coefficient_odd s z hs)
    rw [hf]
    exact (hasSum_regularizedHGFun_singleton ((s + 1) / 2) (3 / 2) (z ^ 2 / 2)).mul_left _
  exact (hasSum_coefficient s z hs).unique (HasSum.even_add_odd heven hodd)

namespace Complex

/-- For complex s,z with Re(s)>0, the positive-half-line Mellin integral
∫₀∞ t^(s-1) exp(-t²/2-zt) dt equals exp(z²/4) Γ(s) U(s-1/2,z).
The function U uses the normalization U(a,z)=D_(-a-1/2)(z). -/
theorem mellin_gaussian_laplace_eq_parabolicCylinderU (s z : ℂ) (hs : 0 < s.re) :
    mellin (fun t : ℝ => exp (-(t : ℂ) ^ 2 / 2 - z * (t : ℂ))) s =
      exp (z ^ 2 / 4) * Gamma s * parabolicCylinderU (s - 1 / 2) z := by
  have hpower : -(s - 1 / 2) / 2 - 1 / 4 = -s / 2 := by ring
  have hA : (s - 1 / 2) / 2 + 1 / 4 = s / 2 := by ring
  have hB : (s - 1 / 2) / 2 + 3 / 4 = (s + 1) / 2 := by ring
  have hexp : exp (z ^ 2 / 4) * exp (-(z ^ 2) / 4) = 1 := by
    rw [← exp_add, show z ^ 2 / 4 + -(z ^ 2) / 4 = 0 by ring, exp_zero]
  have hcanonical : exp (z ^ 2 / 4) * Gamma s * parabolicCylinderU (s - 1 / 2) z =
      (Gamma s * (2 : ℂ) ^ (-s / 2) * ((Real.sqrt Real.pi : ℂ) / Gamma ((s + 1) / 2))) *
        Gamma (1 / 2) *
        regularizedHGFun ({s / 2} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2) -
      (Gamma s * (2 : ℂ) ^ (-s / 2) * ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (s / 2))) *
        z * Gamma (3 / 2) *
        regularizedHGFun ({(s + 1) / 2} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2) := by
    rw [parabolicCylinderU, hpower, hA, hB]
    calc
      _ = (exp (z ^ 2 / 4) * exp (-(z ^ 2) / 4)) *
          ((Gamma s * (2 : ℂ) ^ (-s / 2) * ((Real.sqrt Real.pi : ℂ) / Gamma ((s + 1) / 2))) *
            Gamma (1 / 2) *
            regularizedHGFun ({s / 2} : Multiset ℂ) ({1 / 2} : Multiset ℂ) (z ^ 2 / 2) -
          (Gamma s * (2 : ℂ) ^ (-s / 2) * ((Real.sqrt (2 * Real.pi) : ℂ) / Gamma (s / 2))) *
            z * Gamma (3 / 2) *
            regularizedHGFun ({(s + 1) / 2} : Multiset ℂ) ({3 / 2} : Multiset ℂ) (z ^ 2 / 2)) := by
        ring
      _ = _ := by rw [hexp, one_mul]
  rw [even_normalization s hs, odd_normalization s hs] at hcanonical
  calc
    _ = _ := mellin_two_series s z hs
    _ = _ := by rw [hcanonical]; ring

end Complex
