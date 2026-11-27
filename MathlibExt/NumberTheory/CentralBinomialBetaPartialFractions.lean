/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.HyperharmonicEulerSums
import all MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries
import MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma
import all MathlibExt.NumberTheory.CatalanOddMultipleHarmonicDivTsum
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Central binomial sums with reciprocal binomial weights

Partial fractions reduce the sum to beta integrals at positive integers and at $1/2$, and to
one derivative of the beta function at $1/2$.

## References

* Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
  INTEGERS 26 (2026), Article A81, pp. 1–22, Corollary 9, first identity. The beta-series
  argument uses the $k=0$, $r=1/2$ case of Theorem 1 and the derivative formula (3.1).
* David Borwein, Jonathan M. Borwein, and David M. Bradley, *Parametric Euler sum identities*,
  Journal of Mathematical Analysis and Applications 316 (2006), pp. 328–338, for the parametric
  Euler sums that motivate Young's extension.
* Ce Xu and Jianqiang Zhao, *Apéry-type series and colored multiple zeta values*, Advances in
  Applied Mathematics 153 (2024), Article 102610, Corollary 9.8, for the unweighted half-integer
  central binomial sums in Young's (1.7).
-/

namespace MetaMathlibExt

open Finset Filter MeasureTheory Set
open MathlibExt.Analysis.SpecialFunctions.ArcsinTaylorSeries
open scoped Real Topology

private noncomputable def betaHalf (a : ℝ) : ℝ :=
  Real.Gamma a * Real.Gamma (1 / 2) / Real.Gamma (a + 1 / 2)

private lemma betaHalf_integrand_cast (a t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    ((t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) =
      (t : ℂ) ^ ((a : ℂ) - 1) * (1 - (t : ℂ)) ^ ((1 / 2 : ℂ) - 1) := by
  rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1.le,
    Complex.ofReal_cpow (sub_nonneg.mpr ht.2.le)]
  push_cast
  ring_nf

private lemma betaHalf_integral {a : ℝ} (ha : 0 < a) :
    ∫ t in Ioo (0 : ℝ) 1, t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ) = betaHalf a := by
  apply Complex.ofReal_injective
  have h := Complex.betaIntegral_eq_Gamma_mul_div (a : ℂ) (1 / 2)
    (by simpa using ha) (by norm_num)
  rw [Complex.betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    ← restrict_Ioo_eq_restrict_Ioc] at h
  have hcast : (∫ t in Ioo (0 : ℝ) 1, (↑(t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ)) : ℂ)) =
      ↑(∫ t in Ioo (0 : ℝ) 1, t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ)) := integral_ofReal
  rw [← hcast, betaHalf, Complex.ofReal_div, Complex.ofReal_mul, ← Complex.Gamma_ofReal,
    ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]
  push_cast
  rw [← h]
  exact setIntegral_congr_fun measurableSet_Ioo fun t ht => by
    rw [← Complex.ofReal_mul]
    exact betaHalf_integrand_cast a t ht

private lemma betaHalf_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ)) (Ioo 0 1) := by
  have h := Complex.betaIntegral_convergent (u := (a : ℂ)) (v := 1 / 2)
    (by simpa using ha) (by norm_num)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one,
    IntegrableOn, ← restrict_Ioo_eq_restrict_Ioc] at h
  have he : (fun t : ℝ => (↑(t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ)) : ℂ)) =ᵐ[
      volume.restrict (Ioo (0 : ℝ) 1)] (fun t : ℝ =>
        (t : ℂ) ^ ((a : ℂ) - 1) * (1 - (t : ℂ)) ^ ((1 / 2 : ℂ) - 1)) :=
    (ae_restrict_mem (μ := volume) measurableSet_Ioo).mono (betaHalf_integrand_cast a)
  simpa only [IntegrableOn, RCLike.re_eq_complex_re, Complex.ofReal_re] using (h.congr he.symm).re

-- Integrate the binomial series against the beta weight, with both endpoints ignored a.e.
private lemma centralBinomial_hasSum_beta {a : ℝ} (ha : 0 < a) :
    HasSum (fun n : ℕ => centralBinomialCoeff n / (n + a)) (betaHalf a) := by
  let F (n : ℕ) (t : ℝ) := centralBinomialCoeff n * t ^ (n + a - 1 : ℝ)
  have hterm (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) (n : ℕ) :
      F n t = t ^ (a - 1) * (centralBinomialCoeff n * t ^ n) := by
    dsimp only [F]
    rw [show (n + a - 1 : ℝ) = (a - 1) + n by ring, Real.rpow_add ht.1,
      Real.rpow_natCast]
    ring
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasSum (fun n => F n t) (t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht
    have hs := centralBinomial_hasSum (s := t) (by
      rw [Real.norm_eq_abs, abs_of_pos ht.1]
      exact ht.2)
    simpa only [hterm t ht, Real.rpow_neg (sub_nonneg.mpr ht.2.le), one_div] using
      hs.mul_left (t ^ (a - 1))
  have hs := hasSum_integral_of_dominated_convergence (μ := volume.restrict (Ioo (0 : ℝ) 1))
    (F := F) (f := fun t => t ^ (a - 1) * (1 - t) ^ (-(1 / 2) : ℝ)) F
    (fun n => (show Measurable (F n) by dsimp [F]; fun_prop).aestronglyMeasurable)
    (fun n => by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioo] with t ht
      rw [Real.norm_of_nonneg (mul_nonneg (centralBinomialCoeff_nonneg n)
        (Real.rpow_nonneg ht.1.le _))])
    (hpoint.mono fun _ h => h.summable)
    ((betaHalf_integrable ha).congr (hpoint.mono fun _ h => h.tsum_eq.symm)) hpoint
  rw [betaHalf_integral ha] at hs
  refine hs.congr_fun fun n => ?_
  have hn : 0 < (n : ℝ) + a := by positivity
  simp only [F, MeasureTheory.integral_const_mul]
  rw [restrict_Ioo_eq_restrict_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith : -1 < (n : ℝ) + a - 1)), sub_add_cancel,
    Real.one_rpow, Real.zero_rpow hn.ne', sub_zero, div_eq_mul_inv, one_div]

private lemma betaHalf_one_half : betaHalf (1 / 2) = π := by
  norm_num [betaHalf, Real.Gamma_one_half_eq, ← pow_two, Real.sq_sqrt Real.pi_pos.le]

private lemma hasDerivAt_betaHalf_one_half :
    HasDerivAt betaHalf (-(2 * π * Real.log 2)) (1 / 2) := by
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  have hd (a : ℝ) (ha : 0 < a) :
      Complex.digamma (a : ℂ) = ((deriv Real.Gamma a / Real.Gamma a : ℝ) : ℂ) := by
    rw [Complex.digamma_def, logDeriv_apply, Complex.deriv_Gamma_ofReal _ ha,
      Complex.Gamma_ofReal, Complex.ofReal_div]
  have hdiff : deriv Real.Gamma (1 / 2) / Real.Gamma (1 / 2) - deriv Real.Gamma 1 =
      -2 * Real.log 2 := by
    apply Complex.ofReal_injective
    have hd1 := hd 1 one_pos
    rw [Real.Gamma_one, div_one] at hd1
    rw [Complex.ofReal_sub, ← hd (1 / 2) hh, ← hd1]
    have hlog : ((Real.log 2 : ℝ) : ℂ) = Complex.log 2 := by
      simpa only [Complex.ofReal_ofNat] using Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      Complex.digamma_one_half, Complex.digamma_one,
      Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat, hlog]
    ring
  have hg0 := (Real.hasDerivAt_Gamma_of_pos hh).differentiableAt.hasDerivAt
  have hshift := (hasDerivAt_id' (1 / 2 : ℝ)).add_const (1 / 2)
  have hright : HasDerivAt Real.Gamma (deriv Real.Gamma 1)
      ((fun a : ℝ => a + 1 / 2) (1 / 2)) := by
    norm_num only [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num]
    exact (Real.hasDerivAt_Gamma_of_pos one_pos).differentiableAt.hasDerivAt
  have hg1 := hright.comp (1 / 2) (h := fun a : ℝ => a + 1 / 2) hshift
  have h := (hg0.mul_const (Real.Gamma (1 / 2))).fun_div hg1
    (Real.Gamma_pos_of_pos (by norm_num)).ne'
  convert h using 1
  · rfl
  · simp only [Function.comp_def, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num,
      Real.Gamma_one, mul_one, one_pow, div_one]
    have hp : Real.Gamma (1 / 2) * Real.Gamma (1 / 2) = π := by
      rw [Real.Gamma_one_half_eq, ← pow_two, Real.sq_sqrt Real.pi_pos.le]
    have he : -(2 * π * Real.log 2) = π * (-2 * Real.log 2) := by ring
    rw [he, ← hp, ← hdiff]
    field_simp [(Real.Gamma_pos_of_pos hh).ne']

private lemma centralBinomial_hasSum_half_sq :
    HasSum (fun n : ℕ => centralBinomialCoeff n / ((n : ℝ) + 1 / 2) ^ 2)
      (2 * π * Real.log 2) := by
  let g (n : ℕ) (a : ℝ) := centralBinomialCoeff n / (n + a)
  let g' (n : ℕ) (a : ℝ) := -(centralBinomialCoeff n / (n + a) ^ 2)
  have hu : Summable (fun n : ℕ => 16 * (1 / ((n : ℝ) + 1) ^ 2)) :=
    Real.summable_one_div_add_nat_succ_sq.mul_left _
  have hs : (1 / 2 : ℝ) ∈ Set.Ioi (1 / 4) := by norm_num
  have hbound (n : ℕ) (a : ℝ) (ha : a ∈ Set.Ioi (1 / 4)) :
      ‖g' n a‖ ≤ 16 * (1 / ((n : ℝ) + 1) ^ 2) := by
    have h0 : (n : ℝ) + 1 ≤ 4 * (n + a) := by
      have := Set.mem_Ioi.mp ha
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    have h1 : 0 < (n : ℝ) + a := by have := Set.mem_Ioi.mp ha; positivity
    dsimp only [g']
    rw [norm_neg, Real.norm_of_nonneg (div_nonneg (centralBinomialCoeff_nonneg n) (sq_nonneg _))]
    calc
      _ ≤ 1 / ((n : ℝ) + a) ^ 2 := by gcongr; exact centralBinomialCoeff_le_one n
      _ = 16 * (1 / (4 * ((n : ℝ) + a)) ^ 2) := by field_simp; ring
      _ ≤ 16 * (1 / ((n : ℝ) + 1) ^ 2) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ (by positivity) h0 2)) (by norm_num)
  have hd : HasDerivAt (fun a => ∑' n, g n a) (∑' n, g' n (1 / 2)) (1 / 2) := by
    refine hasDerivAt_tsum_of_isPreconnected (g := g) (g' := g') hu isOpen_Ioi
      isPreconnected_Ioi ?_ hbound hs
      (centralBinomial_hasSum_beta (show (0 : ℝ) < 1 / 2 by norm_num)).summable hs
    intro n a ha
    have hna : (n : ℝ) + a ≠ 0 := by have := Set.mem_Ioi.mp ha; positivity
    simpa [g, g', neg_div] using (hasDerivAt_const a (centralBinomialCoeff n)).fun_div
      ((hasDerivAt_id' a).const_add (n : ℝ)) hna
  have he : (fun a => ∑' n, g n a) =ᶠ[𝓝 (1 / 2 : ℝ)] betaHalf := by
    filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with a ha
    exact (centralBinomial_hasSum_beta ha).tsum_eq
  have hv := (hd.congr_of_eventuallyEq he.symm).unique hasDerivAt_betaHalf_one_half
  simp only [g', tsum_neg, neg_inj] at hv
  have hsum : Summable (fun n : ℕ => centralBinomialCoeff n / ((n : ℝ) + 1 / 2) ^ 2) := by
    simpa only [g', summable_neg_iff] using
      (hu.of_norm_bounded (fun n => hbound n _ hs) : Summable (fun n : ℕ => g' n (1 / 2)))
  rw [← hv]
  exact hsum.hasSum

private noncomputable def recipChoose (m : ℕ) (x : ℝ) : ℝ :=
  m.factorial * ∏ i ∈ range m, (x + 1 + i)⁻¹

private lemma recipChoose_nat (m n : ℕ) : recipChoose m n = ((n + m).choose m : ℝ)⁻¹ := by
  have hp : (∏ i ∈ range m, ((n : ℝ) + 1 + i)) =
      ((n + 1).ascFactorial m : ℝ) := by
    rw [Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [recipChoose, prod_inv_distrib, hp, Nat.ascFactorial_eq_factorial_mul_choose,
    Nat.cast_mul, mul_inv_rev, mul_left_comm, mul_inv_cancel₀ (by positivity), mul_one]

private lemma recipChoose_neg_half (m : ℕ) :
    recipChoose m (-1 / 2) = 4 ^ m / ((2 * m).choose m : ℝ) := by
  have hp : (∏ i ∈ range m, ((-1 / 2 : ℝ) + 1 + i)) =
      ((2 * m).factorial : ℝ) / ((m.factorial : ℝ) * 4 ^ m) := by
    apply Complex.ofReal_injective
    push_cast
    norm_num only [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]
    exact catalan_oddMultipleHarmonic_div_tsum.prod_half_add m
  have hfac : ((2 * m).choose m : ℝ) * m.factorial * m.factorial = (2 * m).factorial := by
    exact_mod_cast (by simpa only [two_mul] using Nat.add_choose_mul_factorial_mul_factorial m m)
  rw [recipChoose, prod_inv_distrib, hp, ← hfac]
  field_simp

private lemma oddMultipleHarmonic_one_eq (m : ℕ) :
    oddMultipleHarmonic 1 m = ∑ i ∈ range m, ((-1 / 2 : ℝ) + 1 + i)⁻¹ := by
  apply Complex.ofReal_injective
  rw [catalan_oddMultipleHarmonic_div_tsum.oddMultipleHarmonic_eq_sum_range]
  push_cast
  simp [Finset.powersetCard_one]
  norm_num only [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]

private lemma hasDerivAt_recipProd (m : ℕ) {x : ℝ} (hx : -1 < x) :
    HasDerivAt (fun y : ℝ => ∏ i ∈ range m, (y + 1 + i)⁻¹)
      (-(∏ i ∈ range m, (x + 1 + i)⁻¹) * ∑ i ∈ range m, (x + 1 + i)⁻¹) x := by
  induction m with
  | zero => simpa using hasDerivAt_const x (1 : ℝ)
  | succ m ih =>
    have hm : 0 < x + 1 + (m : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) m
      linarith
    have hd := (((hasDerivAt_id' x).add_const 1).add_const (m : ℝ)).inv hm.ne'
    simp_rw [prod_range_succ, sum_range_succ]
    convert ih.mul hd using 1
    let P := ∏ i ∈ range m, (x + 1 + (i : ℝ))⁻¹
    let S := ∑ i ∈ range m, (x + 1 + (i : ℝ))⁻¹
    let d := x + 1 + (m : ℝ)
    change -(P * d⁻¹) * (S + d⁻¹) = (-P * S) * d⁻¹ + P * (-1 / d ^ 2)
    have hd0 : d ≠ 0 := hm.ne'
    field_simp
    ring

private lemma hasDerivAt_recipChoose_neg_half (m : ℕ) :
    HasDerivAt (recipChoose m) (-(recipChoose m (-1 / 2) * oddMultipleHarmonic 1 m)) (-1 / 2) := by
  rw [oddMultipleHarmonic_one_eq]
  convert (hasDerivAt_recipProd m (show (-1 : ℝ) < -1 / 2 by norm_num)).const_mul
    (m.factorial : ℝ) using 1
  · rfl
  · simp only [recipChoose]
    ring

-- The alternating sum is the simple-pole expansion of the reciprocal rising product.
private lemma alternating_choose_div_eq (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ∑ i ∈ range (k + 1), (k.choose i : ℝ) * ((-1) ^ i / (x + i)) =
      (k.factorial : ℝ) * ∏ i ∈ range (k + 1), (x + i)⁻¹ := by
  induction k generalizing x with
  | zero => simp [one_div]
  | succ k ih =>
    rw [Finset.sum_choose_succ_mul (fun i _ => (-1 : ℝ) ^ i / (x + i)) k, ih hx]
    have hshift :
        ∑ i ∈ range (k + 1), (k.choose i : ℝ) * ((-1) ^ (i + 1) / (x + (↑(i + 1 : ℕ)))) =
          -(∑ i ∈ range (k + 1), (k.choose i : ℝ) * ((-1) ^ i / (x + 1 + i))) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro i _
      push_cast
      rw [pow_succ]
      ring_nf
    rw [hshift, ih (show 0 < x + 1 by positivity), Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    let W := ∏ i ∈ range (k + 2), (x + i)⁻¹
    have hleft : (∏ i ∈ range (k + 1), (x + i)⁻¹) = (x + (k : ℝ) + 1) * W := by
      have hn : (x + (k : ℝ) + 1) ≠ 0 := by positivity
      simp only [W, prod_range_succ (fun i : ℕ => (x + (i : ℝ))⁻¹) (k + 1), Nat.cast_add,
        Nat.cast_one, ← add_assoc]
      field_simp
    have hright : (∏ i ∈ range (k + 1), (x + 1 + i)⁻¹) = x * W := by
      simp only [W, prod_range_succ' (fun i : ℕ => (x + (i : ℝ))⁻¹) (k + 1), Nat.cast_add,
        Nat.cast_one, Nat.cast_zero, add_zero]
      rw [show (fun i : ℕ => (x + (i + 1 : ℝ))⁻¹) = (fun i : ℕ => (x + 1 + i)⁻¹) by
        funext i; congr 1; ring]
      field_simp
    rw [hleft, hright]
    change _ = _ * W
    ring

private noncomputable def residue (m q : ℕ) : ℝ := -((-1) ^ q * (m.choose q : ℝ) * q)

private lemma recipChoose_eq_sum (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : -1 < x) :
    recipChoose m x = ∑ q ∈ Finset.Icc 1 m, residue m q / (x + q) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
  rw [← Finset.Ico_succ_right_eq_Icc, Finset.sum_Ico_eq_sum_range,
    show Order.succ k.succ - 1 = k + 1 by rfl,
    recipChoose, Nat.factorial_succ, Nat.cast_mul, mul_assoc,
    ← alternating_choose_div_eq k (show 0 < x + 1 by linarith), mul_sum]
  apply sum_congr rfl
  intro i _
  have hi : ((k : ℝ) + 1) * (k.choose i : ℝ) = ((k + 1).choose (i + 1) : ℝ) * (i + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq k i
  rw [show 1 + i = i + 1 by omega, residue, pow_succ]
  push_cast
  rw [show (x + ((i : ℝ) + 1)) = x + 1 + i by ring]
  linear_combination ((-1 : ℝ) ^ i / (x + 1 + i)) * hi

private lemma recipChoose_coeff (m : ℕ) (hm : 0 < m) :
    ∑ q ∈ Finset.Icc 1 m, residue m q / ((q : ℝ) - 1 / 2) ^ 2 =
      recipChoose m (-1 / 2) * oddMultipleHarmonic 1 m := by
  have ht : HasDerivAt (fun x : ℝ => ∑ q ∈ Finset.Icc 1 m, residue m q / (x + q))
      (∑ q ∈ Finset.Icc 1 m, -(residue m q / ((q : ℝ) - 1 / 2) ^ 2)) (-1 / 2) := by
    apply HasDerivAt.fun_sum
    intro q hq
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
    have hne : (-1 / 2 : ℝ) + q ≠ 0 := by linarith
    have h := (hasDerivAt_const (-1 / 2 : ℝ) (residue m q)).fun_div
      ((hasDerivAt_id' (-1 / 2 : ℝ)).add_const (q : ℝ)) hne
    simpa [sub_eq_add_neg, add_comm, neg_div] using h
  have he : (fun x : ℝ => ∑ q ∈ Finset.Icc 1 m, residue m q / (x + q)) =ᶠ[𝓝 (-1 / 2 : ℝ)]
      recipChoose m := by
    filter_upwards [Ioi_mem_nhds (show (-1 : ℝ) < -1 / 2 by norm_num)] with x hx
    exact (recipChoose_eq_sum m hm hx).symm
  have h := (ht.congr_of_eventuallyEq he.symm).unique (hasDerivAt_recipChoose_neg_half m)
  simpa only [sum_neg_distrib, neg_inj] using h

private lemma betaHalf_nat (q : ℕ) (hq : 0 < q) :
    betaHalf q = 4 ^ q / ((q : ℝ) * ((2 * q).choose q : ℝ)) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  have hk : 0 < (k.succ : ℂ).re := by
    exact_mod_cast k.succ_pos
  have hh : 0 < (1 / 2 : ℂ).re := by norm_num
  have hval := Complex.betaIntegral_eq_Gamma_mul_div (k.succ : ℂ) (1 / 2) hk hh
  rw [← Complex.betaIntegral_symm (k.succ : ℂ) (1 / 2), Nat.cast_succ,
    Complex.betaIntegral_eval_nat_add_one_right hh] at hval
  have heq : betaHalf (k.succ : ℝ) = recipChoose k.succ (-1 / 2) / (k.succ : ℝ) := by
    apply Complex.ofReal_injective
    rw [betaHalf, recipChoose, prod_inv_distrib, Complex.ofReal_div, Complex.ofReal_mul,
      ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]
    push_cast
    rw [← hval, Nat.factorial_succ]
    push_cast
    norm_num only [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]
    field_simp [(by exact_mod_cast k.succ_ne_zero : (k : ℂ) + 1 ≠ 0)]
  rw [heq, recipChoose_neg_half]
  ring

-- Split each simple pole against the double pole at `-1/2` and collect its two coefficients.
private lemma recipChoose_div_half_sq (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : 0 ≤ x) :
    recipChoose m x / (x + 1 / 2) ^ 2 =
      recipChoose m (-1 / 2) / (x + 1 / 2) ^ 2 -
        (recipChoose m (-1 / 2) * oddMultipleHarmonic 1 m) / (x + 1 / 2) +
      ∑ q ∈ Finset.Icc 1 m, residue m q / ((q : ℝ) - 1 / 2) ^ 2 / (x + q) := by
  rw [← recipChoose_coeff m hm, recipChoose_eq_sum m hm (show -1 < x by linarith),
    recipChoose_eq_sum m hm (show (-1 : ℝ) < -1 / 2 by norm_num)]
  simp only [sum_div, ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast (mem_Icc.mp hq).1
  have hqhalf : (q : ℝ) - 1 / 2 ≠ 0 := by linarith
  have hqadd : x + (q : ℝ) ≠ 0 := by linarith
  have hxhalf : x + 1 / 2 ≠ 0 := by linarith
  rw [show (-1 / 2 : ℝ) + q = q - 1 / 2 by ring]
  rw [show x + (q : ℝ) = (x + 1 / 2) + ((q : ℝ) - 1 / 2) by ring] at hqadd ⊢
  generalize x + 1 / 2 = u at hxhalf hqadd ⊢
  generalize (q : ℝ) - 1 / 2 = v at hqhalf hqadd ⊢
  field_simp
  ring

/-- **Central binomial sum over $\binom{n+m}{m} (n + 1/2)^2$.** Let $m \ge 1$ be an integer and
write $O_m = O_m(1) = \sum_{i=1}^{m} 1/(i - 1/2)$ for the depth-one odd harmonic number. Then
$$\sum_{n \ge 0} \frac{\binom{2n}{n}}{4^n \binom{n+m}{m} (n + 1/2)^2} =
\frac{4^m \pi}{\binom{2m}{m}} \bigl(2 \log 2 - O_m\bigr) -
\sum_{q=1}^{m} \frac{(-4)^q \binom{m}{q}}{\binom{2q}{q} (q - 1/2)^2}.$$

Source: Paul Thomas Young, *Parametric Euler Sums of Generalized Hyperharmonic Numbers*,
INTEGERS 26 (2026), Article A81, Corollary 9, first identity (`integers-2026-A81-cor-9`). -/
public theorem centralBinom_div_choose_half_sq_tsum (m : ℕ) (hm : 0 < m) :
    ∑' n : ℕ, ((2 * n).choose n : ℝ) / (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 2) ^ 2) =
      4 ^ m * π / ((2 * m).choose m : ℝ) * (2 * Real.log 2 - oddMultipleHarmonic 1 m) -
        ∑ q ∈ Finset.Icc 1 m,
          (-4 : ℝ) ^ q * (m.choose q : ℝ) / (((2 * q).choose q : ℝ) * ((q : ℝ) - 1 / 2) ^ 2) := by
  let A := recipChoose m (-1 / 2)
  let C (q : ℕ) := residue m q / ((q : ℝ) - 1 / 2) ^ 2
  have hbase := centralBinomial_hasSum_beta (show (0 : ℝ) < 1 / 2 by norm_num)
  rw [betaHalf_one_half] at hbase
  have hfin := hasSum_sum (s := Finset.Icc 1 m) (f := fun q n =>
      C q * (centralBinomialCoeff n / (n + (q : ℝ)))) (a := fun q => C q * betaHalf q) (by
    intro q hq
    have hq' : (0 : ℝ) < q := by exact_mod_cast zero_lt_one.trans_le (mem_Icc.mp hq).1
    exact (centralBinomial_hasSum_beta hq').mul_left _)
  have hs := ((centralBinomial_hasSum_half_sq.mul_left A).sub
    (hbase.mul_left (A * oddMultipleHarmonic 1 m))).add hfin
  have hlhs : HasSum (fun n : ℕ =>
      ((2 * n).choose n : ℝ) / (4 ^ n * ((n + m).choose m : ℝ) * ((n : ℝ) + 1 / 2) ^ 2))
      (A * (2 * π * Real.log 2) - (A * oddMultipleHarmonic 1 m) * π +
        ∑ q ∈ Finset.Icc 1 m, C q * betaHalf q) := by
    refine hs.congr_fun fun n => ?_
    have h := recipChoose_div_half_sq m hm (Nat.cast_nonneg (α := ℝ) n)
    rw [recipChoose_nat] at h
    have hpow : (2 : ℝ) ^ (2 * n) = 4 ^ n := by rw [pow_mul]; norm_num
    calc
      _ = centralBinomialCoeff n * (((n + m).choose m : ℝ)⁻¹ / ((n : ℝ) + 1 / 2) ^ 2) := by
        rw [centralBinomialCoeff, hpow]
        simp only [div_eq_mul_inv, mul_inv_rev]
        ac_rfl
      _ = _ := by
        rw [h, mul_add, mul_sub, mul_sum]
        congr 1
        · dsimp only [A]
          ring
        · apply sum_congr rfl
          intro q _
          dsimp only [C]
          ring
  rw [hlhs.tsum_eq]
  have hC : ∑ q ∈ Finset.Icc 1 m, C q * betaHalf q =
      -(∑ q ∈ Finset.Icc 1 m,
          (-4 : ℝ) ^ q * (m.choose q : ℝ) / (((2 * q).choose q : ℝ) * ((q : ℝ) - 1 / 2) ^ 2)) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro q hq
    have hq0 : 0 < q := zero_lt_one.trans_le (mem_Icc.mp hq).1
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq0.ne'
    rw [betaHalf_nat q hq0]
    dsimp only [C, residue]
    rw [show (-4 : ℝ) ^ q = (-1 : ℝ) ^ q * 4 ^ q by rw [← mul_pow]; norm_num]
    field_simp
  rw [hC, show A = 4 ^ m / ((2 * m).choose m : ℝ) from recipChoose_neg_half m]
  ring

end MetaMathlibExt
