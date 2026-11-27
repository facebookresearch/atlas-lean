/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.NumberTheory.IncompleteExponentialSum
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Weighted absolute sines and sine ratios

The Fourier coefficients of `|sin|` away from frequency zero are nonpositive. A lower bound on
finite cosine sums, obtained by integrating a finite geometric series, therefore gives the
weighted absolute-sine estimate. The pointwise cosecant bound then gives the ratio estimate.
-/

open scoped BigOperators Interval
open Complex Filter Finset MeasureTheory

namespace MetaMathlibExt

section

private theorem norm_sub_pow_le (z : ℂ) (hz : ‖z‖ = 1) (k : ℕ) :
    ‖1 - z ^ k‖ ≤ (k : ℝ) * ‖1 - z‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 1 - z ^ (k + 1) = (1 - z ^ k) + z ^ k * (1 - z) by ring]
    have hnorm : ‖z ^ k * (1 - z)‖ = ‖1 - z‖ := by
      rw [norm_mul, norm_pow, hz, one_pow, one_mul]
    rw [Nat.cast_succ, add_mul, one_mul]
    exact (norm_add_le _ _).trans (by rw [hnorm]; gcongr)

private theorem norm_sq_one_sub (z : ℂ) (hz : ‖z‖ = 1) (t : ℝ) :
    Complex.normSq (1 - (t : ℂ) * z) = 1 - 2 * t * z.re + t ^ 2 := by
  have h := Complex.normSq_eq_norm_sq z
  rw [hz, one_pow, Complex.normSq_apply] at h
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
    Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  linear_combination t ^ 2 * h

private theorem re_div_one_sub (z : ℂ) (hz : ‖z‖ = 1) (t : ℝ) :
    (z / (1 - (t : ℂ) * z)).re =
      (z.re - t) / (1 - 2 * t * z.re + t ^ 2) := by
  have h := Complex.normSq_eq_norm_sq z
  rw [hz, one_pow, Complex.normSq_apply] at h
  rw [Complex.div_re, norm_sq_one_sub z hz t, ← add_div]
  congr 1
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  linear_combination -t * h

private theorem norm_one_sub_scale_ge (z : ℂ) (hz : ‖z‖ = 1) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖1 - z‖ / 2 ≤ ‖1 - (t : ℂ) * z‖ := by
  have ht' : ‖(t : ℂ) * z‖ = t := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hrev := norm_sub_norm_le (1 : ℂ) ((t : ℂ) * z)
  rw [norm_one, ht'] at hrev
  have hadd := norm_sub_le (1 - (t : ℂ) * z) (((1 - t : ℝ) : ℂ) * z)
  have hnorm : ‖(((1 - t : ℝ) : ℂ) * z)‖ = 1 - t := by
    rw [norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr ht.2)]
  rw [hnorm, show (1 - (t : ℂ) * z) - (((1 - t : ℝ) : ℂ) * z) = 1 - z by push_cast; ring]
    at hadd
  linarith

private theorem weighted_re_eq_integral (z : ℂ) (K : ℕ) :
    (∑ j ∈ range K, (z ^ (j + 1)).re / ((j : ℝ) + 1)) =
      ∫ t in (0 : ℝ)..1, ∑ j ∈ range K, (z ^ (j + 1)).re * t ^ j := by
  rw [intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl
    intro j _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp [div_eq_mul_inv]
  · intro j _
    exact (continuous_const.mul (continuous_id.pow _)).intervalIntegrable _ _

private theorem weighted_re_integrand (z : ℂ) (K : ℕ) (t : ℝ)
    (ht : 1 - (t : ℂ) * z ≠ 0) :
    (∑ j ∈ range K, (z ^ (j + 1)).re * t ^ j) =
      (z / (1 - (t : ℂ) * z)).re - (((t : ℂ) ^ K * z ^ (K + 1)) /
        (1 - (t : ℂ) * z)).re := by
  have hcomplex : (∑ j ∈ range K, (z ^ (j + 1)) * (t : ℂ) ^ j) =
      z / (1 - (t : ℂ) * z) - ((t : ℂ) ^ K * z ^ (K + 1)) / (1 - (t : ℂ) * z) := by
    have hh : (t : ℂ) * z - 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm (sub_ne_zero.mp ht))
    calc
      _ = z * ∑ j ∈ range K, ((t : ℂ) * z) ^ j := by
        rw [mul_sum]
        apply sum_congr rfl
        intro j _
        rw [pow_succ, mul_pow]
        ring
      _ = _ := by
        rw [geom_sum_eq (sub_ne_zero.mp hh), mul_pow,
          show (t : ℂ) * z - 1 = -(1 - (t : ℂ) * z) by ring, div_neg]
        ring
  have h := congrArg Complex.reCLM hcomplex
  simpa only [map_sum, Complex.sub_re, Complex.mul_re, ← Complex.ofReal_pow,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Complex.reCLM_apply] using h

private theorem weighted_re_large (z : ℂ) (hz : ‖z‖ = 1) (K : ℕ)
    (hsmall : 1 / ((K : ℝ) + 1) < ‖1 - z‖ / 2) :
    -(Real.log 2 + 1 / ((K : ℝ) + 1)) ≤
      ∑ j ∈ range K, (z ^ (j + 1)).re / ((j : ℝ) + 1) := by
  let s := ‖1 - z‖ / 2
  have hs : 0 < s := lt_trans (by positivity) hsmall
  have hs1 : s ≤ 1 := by
    have h := norm_sub_le (1 : ℂ) z
    rw [norm_one, hz] at h
    dsimp [s]
    linarith
  let D (t : ℝ) := 1 - 2 * t * z.re + t ^ 2
  have hD (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 0 < D t := by
    rw [show D t = Complex.normSq (1 - (t : ℂ) * z) from (norm_sq_one_sub z hz t).symm,
      Complex.normSq_eq_norm_sq]
    have h := hs.trans_le (norm_one_sub_scale_ge z hz ht)
    positivity
  have hden (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : 1 - (t : ℂ) * z ≠ 0 :=
    norm_pos_iff.mp (hs.trans_le (norm_one_sub_scale_ge z hz ht))
  let main (t : ℝ) := (z.re - t) / D t
  have hcD : Continuous D := by dsimp [D]; fun_prop
  have hc : ContinuousOn main (Set.Icc (0 : ℝ) 1) :=
    (continuous_const.sub continuous_id).continuousOn.div hcD.continuousOn
      (fun t ht => (hD t ht).ne')
  have hint : IntervalIntegrable main volume (0 : ℝ) 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le zero_le_one] using hc
  have hmain : (∫ t in (0 : ℝ)..1, main t) = -Real.log (2 * s) := by
    have ha (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
        HasDerivAt (fun y => -(1 / 2 : ℝ) * Real.log (D y)) (main t) t := by
      have hpos := hD t (by simpa only [Set.uIcc_of_le zero_le_one] using ht)
      have hd : HasDerivAt D (-(2 * z.re) + 2 * t) t := by
        dsimp [D]
        convert ((hasDerivAt_const t (1 : ℝ)).sub
          (((hasDerivAt_id t).const_mul 2).mul_const z.re)).add ((hasDerivAt_id t).pow 2) using 1
        · ext u
          change 1 - 2 * u * z.re + u ^ 2 = 1 - 2 * u * z.re + u ^ 2
          rfl
        · norm_num [id]
      convert (hd.log hpos.ne').const_mul (-(1 / 2 : ℝ)) using 1
      dsimp [main]
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt ha hint]
    change -(1 / 2 : ℝ) * Real.log (D 1) - (-(1 / 2 : ℝ) * Real.log (D 0)) = _
    have hD0 : D 0 = 1 := by simp [D]
    have hD1 : D 1 = (2 * s) ^ 2 := by
      rw [show D 1 = Complex.normSq (1 - ((1 : ℝ) : ℂ) * z) from (norm_sq_one_sub z hz 1).symm,
        Complex.normSq_eq_norm_sq]
      simp [s]
      ring
    rw [hD0, hD1, Real.log_one, Real.log_pow]
    push_cast
    ring
  have hintpow : IntervalIntegrable (fun t : ℝ => t ^ K / s) volume 0 1 :=
    ((continuous_id.pow K).div_const s).intervalIntegrable _ _
  have hfin : IntervalIntegrable (fun t : ℝ => ∑ j ∈ range K, (z ^ (j + 1)).re * t ^ j)
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hle (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      main t - t ^ K / s ≤ ∑ j ∈ range K, (z ^ (j + 1)).re * t ^ j := by
    rw [weighted_re_integrand z K t (hden t ht), re_div_one_sub z hz t]
    change main t - t ^ K / s ≤ main t - _
    apply sub_le_sub_left
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_mul, norm_pow, norm_pow, hz, one_pow, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact div_le_div_of_nonneg_left (pow_nonneg ht.1 K) hs (norm_one_sub_scale_ge z hz ht)
  have hI := intervalIntegral.integral_mono_on zero_le_one (hint.sub hintpow) hfin hle
  rw [intervalIntegral.integral_sub hint hintpow, hmain,
    ← weighted_re_eq_integral z K] at hI
  have hpow : (∫ t in (0 : ℝ)..1, t ^ K / s) = 1 / (((K : ℝ) + 1) * s) := by
    simp_rw [div_eq_mul_inv, intervalIntegral.integral_mul_const, integral_pow]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm]
  rw [hpow, Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hs.ne'] at hI
  have hlog := Real.log_le_sub_one_of_pos hs
  have hN : 0 < (K : ℝ) + 1 := by positivity
  have hNs : 1 ≤ ((K : ℝ) + 1) * s := by
    have h := (div_le_iff₀ hN).mp hsmall.le
    simpa only [mul_comm] using h
  have hsbound : (1 - s) / (((K : ℝ) + 1) * s) ≤ 1 - s := by
    apply div_le_self (sub_nonneg.mpr hs1) hNs
  have he : 1 / (((K : ℝ) + 1) * s) - 1 / ((K : ℝ) + 1) =
      (1 - s) / (((K : ℝ) + 1) * s) := by
    field_simp
  linarith

private theorem weighted_re_small (z : ℂ) (hz : ‖z‖ = 1) (K : ℕ) (hK : 1 ≤ K)
    (hsmall : ‖1 - z‖ / 2 ≤ 1 / ((K : ℝ) + 1)) :
    -(Real.log 2 + 1 / ((K : ℝ) + 1)) ≤
      ∑ j ∈ range K, (z ^ (j + 1)).re / ((j : ℝ) + 1) := by
  let s := ‖1 - z‖ / 2
  let N : ℝ := (K : ℝ) + 1
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hN : 0 < N := by dsimp [N]; positivity
  have hs' : s ≤ 1 / N := hsmall
  have hnorm : ‖1 - z‖ = 2 * s := by dsimp [s]; ring
  have hterm (j : ℕ) : 1 / ((j : ℝ) + 1) - 2 * s ^ 2 * ((j : ℝ) + 1) ≤
      (z ^ (j + 1)).re / ((j : ℝ) + 1) := by
    let w := z ^ (j + 1)
    have hw : ‖w‖ = 1 := by simp [w, norm_pow, hz]
    have hsq := norm_sq_one_sub w hw 1
    rw [Complex.normSq_eq_norm_sq] at hsq
    simp only [Complex.ofReal_one, one_mul, one_pow] at hsq
    have hle : ‖1 - w‖ ≤ 2 * s * ((j : ℝ) + 1) := by
      simpa only [w, Nat.cast_succ, hnorm, mul_comm] using norm_sub_pow_le z hz (j + 1)
    have hpos : 0 < (j : ℝ) + 1 := by positivity
    have hsqle := pow_le_pow_left₀ (norm_nonneg (1 - w)) hle 2
    change 1 / ((j : ℝ) + 1) - 2 * s ^ 2 * ((j : ℝ) + 1) ≤ w.re / ((j : ℝ) + 1)
    have hr : 1 - 2 * s ^ 2 * ((j : ℝ) + 1) ^ 2 ≤ w.re := by nlinarith only [hsq, hsqle]
    calc
      _ = (1 - 2 * s ^ 2 * ((j : ℝ) + 1) ^ 2) / ((j : ℝ) + 1) := by
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hr hpos.le
  have hsum (k : ℕ) : ∑ j ∈ range k, ((j : ℝ) + 1) = (k : ℝ) * ((k : ℝ) + 1) / 2 := by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ, ih, Nat.cast_succ]; ring
  have hfirst : 1 ≤ ∑ j ∈ range K, 1 / ((j : ℝ) + 1) := by
    simpa using (single_le_sum (f := fun j : ℕ => 1 / ((j : ℝ) + 1))
      (s := range K) (fun j _ => by positivity) (mem_range.mpr (by omega : 0 < K)))
  have hscale : s * N ≤ 1 := (le_div_iff₀ hN).mp hs'
  have hsqscale : (s * N) ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (mul_nonneg hs hN.le) hscale 2
  have herror : s ^ 2 * (K : ℝ) * N ≤ 1 := by
    calc
      _ ≤ s ^ 2 * N * N := by gcongr; dsimp [N]; linarith
      _ = (s * N) ^ 2 := by ring
      _ ≤ 1 := hsqscale
  have hsumle := sum_le_sum (s := range K) (fun j _ => hterm j)
  rw [sum_sub_distrib, ← mul_sum, hsum] at hsumle
  change (∑ j ∈ range K, 1 / ((j : ℝ) + 1)) - 2 * s ^ 2 * ((K : ℝ) * N / 2) ≤ _ at hsumle
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hinv : 0 ≤ 1 / N := by positivity
  change -(Real.log 2 + 1 / N) ≤ _
  nlinarith only [hsumle, hfirst, herror, hlog, hinv]

private theorem weighted_cosine_lower (K : ℕ) (hK : 1 ≤ K) (θ : ℝ) :
    -(Real.log 2 + 1 / ((K : ℝ) + 1)) ≤ ∑ k ∈ Icc 1 K, Real.cos (k * θ) / k := by
  let z := Complex.exp ((θ : ℂ) * I)
  have hz : ‖z‖ = 1 := by simp [z, Complex.norm_exp, Complex.mul_re]
  have he (k : ℕ) : (z ^ k).re = Real.cos (k * θ) := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul, ← mul_assoc, ← Complex.ofReal_natCast, ← Complex.ofReal_mul,
      Complex.exp_ofReal_mul_I_re]
  have hsum (f : ℕ → ℝ) (n : ℕ) :
      ∑ j ∈ range n, f (j + 1) = ∑ j ∈ Icc 1 n, f j := by
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, sum_Icc_succ_top (by omega), ih]
  have h : -(Real.log 2 + 1 / ((K : ℝ) + 1)) ≤
      ∑ j ∈ range K, (z ^ (j + 1)).re / ((j : ℝ) + 1) := by
    by_cases hs : ‖1 - z‖ / 2 ≤ 1 / ((K : ℝ) + 1)
    · exact weighted_re_small z hz K hK hs
    · exact weighted_re_large z hz K (lt_of_not_ge hs)
  simp only [he, ← Nat.cast_succ] at h
  rw [hsum (fun j => Real.cos ((j : ℝ) * θ) / (j : ℝ))] at h
  simpa only [Nat.cast_succ] using h

end

noncomputable section

open Set

private local instance : Fact (0 < Real.pi) := ⟨Real.pi_pos⟩

private theorem absSin_periodic :
    Function.Periodic (fun x : ℝ => (↑|Real.sin x| : ℂ)) Real.pi := by
  intro x
  simp [Real.sin_add_pi]

private def absSinCircle : C(AddCircle Real.pi, ℂ) where
  toFun := absSin_periodic.lift
  continuous_toFun := continuous_quot_lift _
    (Complex.continuous_ofReal.comp Real.continuous_sin.abs)

@[simp] private theorem absSinCircle_coe (x : ℝ) :
    absSinCircle (x : AddCircle Real.pi) = (↑|Real.sin x| : ℂ) :=
  absSin_periodic.lift_coe x

private def sineCoeff (n : ℤ) : ℝ := 2 / (Real.pi * (1 - 4 * (n : ℝ)^2))

@[simp] private theorem sineCoeff_zero : sineCoeff 0 = 2 / Real.pi := by
  simp [sineCoeff]

private theorem one_le_intCast_sq (n : ℤ) (hn : n ≠ 0) : (1 : ℝ) ≤ (n : ℝ)^2 := by
  by_cases hp : 0 < n
  · have h : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ n by omega)
    nlinarith [sq_nonneg ((n : ℝ) - 1)]
  · have h : (n : ℝ) ≤ -1 := by exact_mod_cast (show n ≤ (-1 : ℤ) by omega)
    nlinarith [sq_nonneg ((n : ℝ) + 1)]

private theorem fourierCoeff_absSin_eq_on (n : ℤ) :
    fourierCoeff absSinCircle n =
      fourierCoeffOn Real.pi_pos (fun x => (↑(Real.sin x) : ℂ)) n := by
  rw [fourierCoeff_eq_intervalIntegral absSinCircle n 0, fourierCoeffOn_eq_integral]
  simp only [zero_add, sub_zero, absSinCircle_coe]
  refine congrArg (fun z : ℂ => (1 / Real.pi) • z) ?_
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le Real.pi_pos.le]
  intro x hx
  simp only [fourier_coe_apply, sub_zero,
    abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)]

private theorem fourierCoeff_absSin (n : ℤ) :
    fourierCoeff absSinCircle n = (sineCoeff n : ℂ) := by
  rw [fourierCoeff_absSin_eq_on]
  by_cases hn : n = 0
  · subst n
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, sub_zero, intervalIntegral.integral_ofReal,
      integral_sin, Real.cos_zero, Real.cos_pi, sineCoeff_zero]
    rw [Complex.real_smul]
    push_cast
    ring
  · let s : ℂ := fourierCoeffOn Real.pi_pos (fun x => (↑(Real.sin x) : ℂ)) n
    let c : ℂ := fourierCoeffOn Real.pi_pos (fun x => (↑(Real.cos x) : ℂ)) n
    let A : ℂ := -2 * Real.pi * Complex.I * n
    have hA : A ≠ 0 := by
      dsimp [A]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num)
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero) (by exact_mod_cast hn)
    have hs : s = 1 / A * (-(Real.pi : ℂ) * c) := by
      have h := fourierCoeffOn_of_hasDerivAt Real.pi_pos hn
        (f := fun x => (↑(Real.sin x) : ℂ)) (f' := fun x => (↑(Real.cos x) : ℂ))
        (fun x _ => (Real.hasDerivAt_sin x).ofReal_comp)
        ((Complex.continuous_ofReal.comp Real.continuous_cos).intervalIntegrable _ _)
      simpa [s, c, A, neg_mul] using h
    have hc : c = 1 / A * (-2 + (Real.pi : ℂ) * s) := by
      have h := fourierCoeffOn_of_hasDerivAt Real.pi_pos hn
        (f := fun x => (↑(Real.cos x) : ℂ)) (f' := fun x => -(↑(Real.sin x) : ℂ))
        (fun x _ => by simpa using (Real.hasDerivAt_cos x).ofReal_comp)
        ((Complex.continuous_ofReal.comp Real.continuous_sin).neg.intervalIntegrable _ _)
      have hneg : fourierCoeffOn Real.pi_pos (fun x => -(↑(Real.sin x) : ℂ)) n = -s := by
        simpa [s] using fourierCoeffOn.const_mul (fun x => (↑(Real.sin x) : ℂ)) (-1) n Real.pi_pos
      rw [hneg] at h
      simp only [sub_zero, AddCircle.coe_zero, fourier_eval_zero, one_mul, Real.cos_pi,
        Real.cos_zero, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero,
        mul_neg, sub_neg_eq_add] at h
      convert h using 2
      ring
    have hs' : s * A = -(Real.pi : ℂ) * c := by rw [hs]; field_simp
    have hc' : c * A = -2 + (Real.pi : ℂ) * s := by rw [hc]; field_simp
    have hAsq : A^2 = -4 * (Real.pi : ℂ)^2 * (n : ℂ)^2 := by
      dsimp [A]
      rw [mul_pow, mul_pow, mul_pow, Complex.I_sq]
      ring
    have hdenR : Real.pi * (1 - 4 * (n : ℝ)^2) ≠ 0 :=
      mul_ne_zero Real.pi_ne_zero (by linarith [one_le_intCast_sq n hn])
    have hden : (Real.pi : ℂ) * (1 - 4 * (n : ℂ)^2) ≠ 0 := by
      exact_mod_cast hdenR
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hprod : (Real.pi : ℂ) * (s * ((Real.pi : ℂ) * (1 - 4 * (n : ℂ)^2))) =
        (Real.pi : ℂ) * 2 := by
      linear_combination A * hs' - (Real.pi : ℂ) * hc' - s * hAsq
    change s = (sineCoeff n : ℂ)
    unfold sineCoeff
    push_cast
    exact (eq_div_iff hden).2 (mul_left_cancel₀ hπ hprod)

private theorem sineCoeff_nonpos (n : ℤ) (hn : n ≠ 0) : sineCoeff n ≤ 0 := by
  have h : 1 - 4 * (n : ℝ)^2 ≤ 0 := by linarith [one_le_intCast_sq n hn]
  exact div_nonpos_of_nonneg_of_nonpos (by norm_num)
    (mul_nonpos_of_nonneg_of_nonpos Real.pi_pos.le h)

private theorem fourierCoeff_absSin_summable : Summable (fourierCoeff absSinCircle) := by
  have hBound := (hasSum_ite_eq (0 : ℤ) (2 / Real.pi)).summable.add
    (((Real.summable_one_div_int_pow (p := 2)).2 (by decide)).mul_left (2 / Real.pi))
  apply Summable.of_norm_bounded hBound
  intro n
  rw [fourierCoeff_absSin, Complex.norm_real, Real.norm_eq_abs]
  by_cases hn : n = 0
  · subst n
    simp [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
  · simp only [hn, ite_false, zero_add, abs_of_nonpos (sineCoeff_nonpos n hn)]
    have hq := one_le_intCast_sq n hn
    calc
      -sineCoeff n = 2 / (Real.pi * (4 * (n : ℝ)^2 - 1)) := by
        rw [sineCoeff, ← div_neg, ← mul_neg]
        ring_nf
      _ ≤ 2 / (Real.pi * (n : ℝ)^2) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le)
      _ = (2 / Real.pi) * (1 / (n : ℝ)^2) := by ring

private theorem fourier_pi_re (n : ℤ) (x : ℝ) :
    (fourier n (x : AddCircle Real.pi)).re = Real.cos (2 * (n : ℝ) * x) := by
  rw [fourier_coe_apply, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

private theorem hasSum_sineCoeff_cos (x : ℝ) :
    HasSum (fun n : ℤ => sineCoeff n * Real.cos (2 * (n : ℝ) * x)) |Real.sin x| := by
  have h := Complex.reCLM.hasSum
    (has_pointwise_sum_fourier_series_of_summable fourierCoeff_absSin_summable
      (x : AddCircle Real.pi))
  convert h using 1
  · funext n
    simp only [Complex.reCLM_apply, smul_eq_mul, fourierCoeff_absSin,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, fourier_pi_re]
  · simp

/-- Nonnegative coefficients of the cosine series for `2 / π - |sin x|`, indexed by
    all integers. The two indices `n` and `-n` contribute equally. -/
private def absSinCosWeight (n : ℤ) : ℝ := if n = 0 then 0 else -sineCoeff n

private theorem absSinCosWeight_nonneg (n : ℤ) : 0 ≤ absSinCosWeight n := by
  by_cases hn : n = 0
  · simp [absSinCosWeight, hn]
  · simpa [absSinCosWeight, hn] using sineCoeff_nonpos n hn

private theorem hasSum_absSinCosWeight_mul_cos (x : ℝ) :
    HasSum (fun n : ℤ => absSinCosWeight n * Real.cos (2 * (n : ℝ) * x))
      (2 / Real.pi - |Real.sin x|) := by
  convert (hasSum_ite_eq (0 : ℤ) (2 / Real.pi)).sub (hasSum_sineCoeff_cos x) using 1
  funext n
  by_cases hn : n = 0
  · subst n
    simp [absSinCosWeight]
  · simp [absSinCosWeight, hn]

private theorem hasSum_absSinCosWeight : HasSum absSinCosWeight (2 / Real.pi) := by
  simpa using hasSum_absSinCosWeight_mul_cos 0

/-- A uniform lower bound for a finite cosine sum yields a corresponding upper bound
    for the weighted sum of absolute sines with the same frequencies. -/
private theorem weighted_abs_sin_le_of_cos_sum_lower_bound {ι : Type*} (s : Finset ι)
    (w f : ι → ℝ) (B ξ : ℝ)
    (hC : ∀ θ : ℝ, -B ≤ ∑ i ∈ s, w i * Real.cos (f i * θ)) :
    (∑ i ∈ s, w i * |Real.sin (f i * ξ)|) ≤ (2 / Real.pi) * ((∑ i ∈ s, w i) + B) := by
  have hlower := hasSum_absSinCosWeight.mul_right (-B)
  have hupper := hasSum_sum (s := s) fun i _ =>
    (hasSum_absSinCosWeight_mul_cos (f i * ξ)).mul_left (w i)
  have h := hlower.summable.tsum_le_tsum (g := fun n =>
      ∑ i ∈ s, w i * (absSinCosWeight n * Real.cos (2 * (n : ℝ) * (f i * ξ))))
    (fun n => by
      change absSinCosWeight n * (-B) ≤ _
      calc
        _ ≤ absSinCosWeight n * (∑ i ∈ s, w i * Real.cos (f i * (2 * (n : ℝ) * ξ))) :=
          mul_le_mul_of_nonneg_left (hC _) (absSinCosWeight_nonneg n)
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [show f i * (2 * (n : ℝ) * ξ) = 2 * (n : ℝ) * (f i * ξ) by ring]
          ring) hupper.summable
  rw [hlower.tsum_eq, hupper.tsum_eq] at h
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
  linarith only [h]

private theorem sum_Icc_one_div_eq_harmonic (K : ℕ) :
    (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / k) = (harmonic K : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le K)), harmonic_succ, Rat.cast_add,
      Rat.cast_inv, Rat.cast_natCast, ih, one_div]

/-- The weighted absolute sine bound with harmonic weights, conditional on the finite
    cosine lower bound. -/
private theorem sum_abs_sin_div_le_of_cos_sum_lower_bound (K : ℕ) (ξ : ℝ)
    (hC : ∀ θ : ℝ, -(Real.log 2 + 1 / ((K : ℝ) + 1)) ≤
      ∑ k ∈ Finset.Icc 1 K, Real.cos (k * θ) / k) :
    (∑ k ∈ Finset.Icc 1 K, |Real.sin (k * ξ)| / k) ≤
      (2 / Real.pi) * ((harmonic K : ℝ) + Real.log 2 + 1 / ((K : ℝ) + 1)) := by
  have hw (x y : ℝ) : 1 / x * y = y / x := by ring
  simpa only [hw, sum_Icc_one_div_eq_harmonic, ← add_assoc] using
    weighted_abs_sin_le_of_cos_sum_lower_bound (Finset.Icc 1 K)
      (fun k : ℕ => (1 : ℝ) / k) (fun k : ℕ => (k : ℝ))
      (Real.log 2 + 1 / ((K : ℝ) + 1)) ξ (by simpa only [hw] using hC)

end

private theorem weighted_absolute_sine_strict (K : ℕ) (hK : 1 ≤ K) (ξ : ℝ)
    (h : ∑ k ∈ Icc 1 K, |Real.sin (k * ξ)| / k ≤
      (2 / Real.pi) * ((harmonic K : ℝ) + Real.log 2 + 1 / ((K : ℝ) + 1))) :
    (∑ k ∈ Icc 1 K, |Real.sin (k * ξ)| / k <
      (2 / Real.pi) * (Real.log (K + 1) + Real.eulerMascheroniConstant + Real.log 2) +
        3 / (Real.pi * (K + 1))) ∧
    (∑ k ∈ Icc 1 K, |Real.sin (k * ξ)| / k <
      (2 / Real.pi) * Real.log K +
        (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) + 5 / (Real.pi * K)) := by
  have hγ := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant K
  unfold Real.eulerMascheroniSeq at hγ
  have hK₀ : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hπ : 0 < 2 / Real.pi := by positivity
  have hnext : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have hlog : Real.log ((K : ℝ) + 1) < Real.log K + 1 / K := by
    have hx : (0 : ℝ) < 1 + 1 / (K : ℝ) := by positivity
    have hx₁ : (1 : ℝ) + 1 / K ≠ 1 := (lt_add_of_pos_right _ (by positivity)).ne'
    have hlog := Real.log_lt_sub_one_of_pos hx hx₁
    have heq : (K : ℝ) + 1 = K * (1 + 1 / (K : ℝ)) := by field_simp
    rw [heq, Real.log_mul hK₀.ne' hx.ne']
    linarith
  have hmain := mul_lt_mul_of_pos_left
    (show (harmonic K : ℝ) + Real.log 2 + 1 / ((K : ℝ) + 1) <
      (Real.log ((K : ℝ) + 1) + Real.eulerMascheroniConstant + Real.log 2) +
        1 / ((K : ℝ) + 1) by linarith) hπ
  have scaled_inv (x : ℝ) (hx : 0 < x) : (2 / Real.pi) * (1 / x) = 2 / (Real.pi * x) := by
    field_simp [Real.pi_pos.ne', hx.ne']
  constructor
  · refine h.trans_lt (hmain.trans_le ?_)
    rw [mul_add, scaled_inv _ hnext]
    apply add_le_add_right
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · have hinv : 1 / ((K : ℝ) + 1) ≤ 1 / (K : ℝ) :=
      one_div_le_one_div_of_le hK₀ (by linarith)
    have herror := mul_le_mul_of_nonneg_left hinv hπ.le
    have hnextlog := mul_lt_mul_of_pos_left hlog hπ
    have hlast : (4 : ℝ) / (Real.pi * K) ≤ 5 / (Real.pi * K) :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    rw [scaled_inv _ hnext, scaled_inv _ hK₀] at herror
    rw [mul_add, scaled_inv _ hK₀] at hnextlog
    refine h.trans_lt (hmain.trans_le ?_)
    calc
      _ = (2 / Real.pi) * Real.log ((K : ℝ) + 1) +
          (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) +
          2 / (Real.pi * ((K : ℝ) + 1)) := by
        rw [mul_add, scaled_inv _ hnext]
        ring
      _ ≤ ((2 / Real.pi) * Real.log K + 2 / (Real.pi * K)) +
          (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) + 2 / (Real.pi * K) :=
        add_le_add (add_le_add_left hnextlog.le _) herror
      _ = (2 / Real.pi) * Real.log K +
          (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) + 4 / (Real.pi * K) := by ring
      _ ≤ _ := add_le_add_right hlast _

/-- **Bound for a weighted sum of absolute sines.** Let $K$ be a positive integer, let $\xi$ be a
real number, and let $\gamma$ be the Euler–Mascheroni constant. Then
$$
\sum_{y=1}^{K} \frac{|\sin(y\xi)|}{y} <
\frac{2}{\pi}\left(\log(K + 1) + \gamma + \log 2\right) + \frac{3}{\pi(K + 1)}
$$
and
$$
\sum_{y=1}^{K} \frac{|\sin(y\xi)|}{y} <
\frac{2}{\pi}\log K + \frac{2}{\pi}(\gamma + \log 2) + \frac{5}{\pi K}.
$$

The second bound is the form (3.1) of the first, obtained from $\log(K + 1) < \log K + 1/K$.

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.4 (quoted from [3, Lemma 2.1]) and inequality (3.1)
(`integers-2025-A48-lem-3-4`). -/
public theorem sum_abs_sin_mul_div_lt (K : ℕ) (hK : 1 ≤ K) (ξ : ℝ) :
    ∑ y ∈ Icc 1 K, |Real.sin (y * ξ)| / y <
        (2 / Real.pi) * (Real.log (K + 1) + Real.eulerMascheroniConstant + Real.log 2) +
          3 / (Real.pi * (K + 1)) ∧
      ∑ y ∈ Icc 1 K, |Real.sin (y * ξ)| / y <
        (2 / Real.pi) * Real.log K +
          (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) + 5 / (Real.pi * K) := by
  exact weighted_absolute_sine_strict K hK ξ
    (sum_abs_sin_div_le_of_cos_sum_lower_bound K ξ (weighted_cosine_lower K hK))

set_option maxHeartbeats 800000 in
-- The ratio bound uses several ring normalizations with cast natural denominators.
/-- **Bound for a sum of sine ratios.** Let $q$, $K$ and $B$ be natural numbers with
$1 \le K < q$ and $B \ge 1$, and let $\gamma$ be the Euler–Mascheroni constant. Then
$$
\sum_{k=1}^{K} \frac{|\sin(\pi B k / q)|}{|\sin(\pi k / q)|} <
\frac{2}{\pi^2} q \log K + \frac{2q}{\pi^2}(\gamma + \log 2) + \frac{q}{\pi} \cdot \frac{K}{q - K} +
\frac{5q}{\pi^2 K}.
$$

Source: Todd Cochrane, *Explicit Estimates for Incomplete Exponential Sums*, INTEGERS 25
(2025), Article A48, Lemma 3.5 (`integers-2025-A48-lem-3-5`). -/
public theorem sum_abs_sin_div_abs_sin_lt (q K B : ℕ) (hK : 1 ≤ K) (hKq : K < q)
    (hB : 1 ≤ B) :
    ∑ k ∈ Icc 1 K, |Real.sin (Real.pi * B * k / q)| / |Real.sin (Real.pi * k / q)| <
      2 / Real.pi ^ 2 * q * Real.log K +
          2 * q / Real.pi ^ 2 * (Real.eulerMascheroniConstant + Real.log 2) +
        q / Real.pi * (K / ((q : ℝ) - K)) + 5 * q / (Real.pi ^ 2 * K) := by
  have _ := hB
  have hKpos : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hKqr : (K : ℝ) < q := by exact_mod_cast hKq
  have hgap : 0 < (q : ℝ) - K := sub_pos.mpr hKqr
  have hq : (0 : ℝ) < q := hKpos.trans hKqr
  have hscale : 0 < (q : ℝ) / Real.pi := div_pos hq Real.pi_pos
  let ξ : ℝ := Real.pi * B / q
  let f (k : ℕ) : ℝ := |Real.sin (k * ξ)|
  have hterm (k : ℕ) (hk : k ∈ Icc 1 K) :
      |Real.sin (Real.pi * B * k / q)| / |Real.sin (Real.pi * k / q)| ≤
        (q / Real.pi) * (f k / k) + (q / Real.pi) / ((q : ℝ) - K) := by
    obtain ⟨hk1, hkK⟩ := mem_Icc.mp hk
    have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hkKr : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have hkqr : (k : ℝ) < q := hkKr.trans_lt hKqr
    have hqk : 0 < (q : ℝ) - k := sub_pos.mpr hkqr
    let x : ℝ := (k : ℝ) / q
    have hx0 : 0 < x := div_pos hkpos hq
    have hx1 : x < 1 := (div_lt_iff₀ hq).2 (by simpa only [one_mul] using hkqr)
    have hxminus : 0 < 1 - x := sub_pos.mpr hx1
    have hxplus : 0 < 1 + x := by linarith
    have hxsq : 0 < 1 - x ^ 2 := by
      calc
        0 < (1 - x) * (1 + x) := mul_pos hxminus hxplus
        _ = 1 - x ^ 2 := by ring
    have hrelax : 2 * x / (1 - x ^ 2) ≤ 1 / (1 - x) := by
      apply (div_le_iff₀ hxsq).2
      calc
        2 * x ≤ 1 + x := by linarith
        _ = (1 / (1 - x)) * (1 - x ^ 2) := by
          field_simp [hxminus.ne']
          ring
    have hsin : 0 < Real.sin (Real.pi * x) :=
      Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hx0) (by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hx1 Real.pi_pos)
    have hrecip : 1 / x = (q : ℝ) / k := by simp only [x, one_div_div]
    have herr : 1 / (1 - x) = (q : ℝ) / ((q : ℝ) - k) := by
      have hxgap : 1 - x = ((q : ℝ) - k) / q := by
        dsimp only [x]
        field_simp [hq.ne']
      rw [hxgap, one_div_div]
    have hcsc : 1 / Real.sin (Real.pi * x) ≤
        (q / Real.pi) / k + (q / Real.pi) / ((q : ℝ) - k) := by
      calc
        _ ≤ (1 / Real.pi) * (1 / x + 2 * x / (1 - x ^ 2)) :=
          (one_div_sin_pi_lt x hx0 hx1).le
        _ ≤ (1 / Real.pi) * (1 / x + 1 / (1 - x)) :=
          mul_le_mul_of_nonneg_left (add_le_add_right hrelax _) (by positivity)
        _ = _ := by rw [hrecip, herr]; ring
    have harg : Real.pi * (B : ℝ) * k / q = (k : ℝ) * ξ := by
      dsimp only [ξ]
      ring
    have hden : Real.pi * (k : ℝ) / q = Real.pi * x := by
      dsimp only [x]
      ring
    have hf0 : 0 ≤ f k := abs_nonneg _
    have hf1 : f k ≤ 1 := Real.abs_sin_le_one _
    have herr_le : (q / Real.pi) / ((q : ℝ) - k) ≤ (q / Real.pi) / ((q : ℝ) - K) :=
      div_le_div_of_nonneg_left hscale.le hgap (sub_le_sub_left hkKr _)
    calc
      _ = f k * (1 / Real.sin (Real.pi * x)) := by
        rw [harg, hden, abs_of_pos hsin]
        simp only [f, div_eq_mul_inv, one_mul]
      _ ≤ f k * ((q / Real.pi) / k + (q / Real.pi) / ((q : ℝ) - k)) :=
        mul_le_mul_of_nonneg_left hcsc hf0
      _ = (q / Real.pi) * (f k / k) + f k * ((q / Real.pi) / ((q : ℝ) - k)) := by ring
      _ ≤ (q / Real.pi) * (f k / k) + (q / Real.pi) / ((q : ℝ) - K) := by
        apply add_le_add_right
        calc
          _ ≤ 1 * ((q / Real.pi) / ((q : ℝ) - k)) :=
            mul_le_mul_of_nonneg_right hf1 (div_nonneg hscale.le hqk.le)
          _ = (q / Real.pi) / ((q : ℝ) - k) := one_mul _
          _ ≤ _ := herr_le
  have hcard : (Icc 1 K).card = K := by rw [Nat.card_Icc]; omega
  calc
    _ ≤ ∑ k ∈ Icc 1 K, ((q / Real.pi) * (f k / k) + (q / Real.pi) / ((q : ℝ) - K)) :=
      sum_le_sum (fun k hk => hterm k hk)
    _ = (q / Real.pi) * (∑ k ∈ Icc 1 K, f k / k) + q / Real.pi * (K / ((q : ℝ) - K)) := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hcard]
      ring
    _ < (q / Real.pi) * ((2 / Real.pi) * Real.log K +
          (2 / Real.pi) * (Real.eulerMascheroniConstant + Real.log 2) + 5 / (Real.pi * K)) +
        q / Real.pi * (K / ((q : ℝ) - K)) :=
      add_lt_add_left (mul_lt_mul_of_pos_left ((sum_abs_sin_mul_div_lt K hK ξ).2) hscale) _
    _ = _ := by ring

end MetaMathlibExt
