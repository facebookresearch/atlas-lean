/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry1Powersum
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic.LinearCombination

/-!
# Asymptotic expansion of logarithmically weighted power sums

Differentiating the normalized power-sum expansion gives the Bernoulli corrections.
The functional equation of the Riemann zeta function evaluates the constant term.
-/

@[expose] public noncomputable section

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry27Clausen

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum

/-- The derivative $D_m(r)$ of $r(r-1)\cdots(r-m)$, expressed as a sum of products
with one factor omitted. -/
def chapter9FallingDerivative (m : ℕ) (r : ℝ) : ℝ :=
  ∑ j ∈ range (m + 1),
    ∏ q ∈ (range (m + 1)).erase j, (r - q)

/-- For $k \ge 1$, the coefficient $B_{2k}D_{2k-2}(r)/(2k)!$ in the logarithmically
weighted power-sum expansion. -/
def chapter9Entry27Coeff (k : ℕ) (r : ℝ) : ℝ :=
  (bernoulli (2 * k) : ℝ) / ((2 * k).factorial : ℝ) *
    chapter9FallingDerivative (2 * k - 2) r

/-- The sum of the constant $C$, the leading term $-x^{r+1}/(r+1)^2$, and the
first $N$ Bernoulli corrections for logarithmically weighted power sums. -/
def chapter9Entry27Approx (r C : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  C - Real.rpow x (r + 1) / (r + 1) ^ 2 +
    ∑ j ∈ range N,
      let k := j + 1
      chapter9Entry27Coeff k r * Real.rpow x (r - 2 * (k : ℝ) + 1)

/-- The logarithmically weighted Dirichlet series term $\log(j+1)/(j+1)^{r+1}$. -/
def chapter9Entry27LogTerm (r : ℝ) (j : ℕ) : ℝ :=
  Real.log (j + 1 : ℝ) / Real.rpow (j + 1 : ℝ) (r + 1)

/-- The sum of $k^r \log k$ over the positive integers $k \le x$. -/
def chapter9PhiR (r x : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (Nat.floor x),
    Real.rpow (k : ℝ) r * Real.log k

/-- The sum of $k^r$ over the positive integers $k \le x$. -/
def chapter9PowerSumR (r x : ℝ) : ℝ :=
  ∑ k ∈ Icc 1 (Nat.floor x), Real.rpow (k : ℝ) r

private def coeff (j : ℕ) (z : ℂ) : ℂ :=
  ((bernoulli (2 * (j + 1)) : ℂ) / ((2 * (j + 1)).factorial : ℂ)) *
    chapter7FallingGammaRatio z (2 * (j + 1) - 1)

private def weight (j n : ℕ) : ℝ := (n : ℝ) ^ (-2 * (j : ℝ) - 1)

-- Normalizing by the power of n removes the logarithm from every correction term.
private def residual (N n : ℕ) (z : ℂ) : ℂ :=
  (chapter7PowerSum z n - riemannZeta (-z)) * (n : ℂ) ^ (-z) -
    ((n : ℂ) / (z + 1) + 1 / 2 + ∑ j ∈ range N, coeff j z * (weight j n : ℂ))

private theorem residual_eq {M n : ℕ} (hn : 1 < n) (hM : 0 < M)
    {z : ℂ} (hz : z ≠ -1) (hu : z.re < 2 * M) :
    residual M n z = -(powerSumRemainderFactor M z * powerSumTail M z n * (n : ℂ) ^ (-z)) := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hpow (a : ℂ) : chapter7NatCpow n (z + a) * (n : ℂ) ^ (-z) = (n : ℂ) ^ a := by
    change (n : ℂ) ^ (z + a) * (n : ℂ) ^ (-z) = _
    rw [← Complex.cpow_add _ _ hn0]
    congr 1
    ring
  have hterm (j : ℕ) : chapter7Entry1Term z n j * (n : ℂ) ^ (-z) =
      coeff j z * (weight j n : ℂ) := by
    unfold chapter7Entry1Term coeff weight
    rw [mul_assoc, show z - ((2 * (j + 1) : ℕ) : ℂ) + 1 = z + ↑(-2 * (j : ℝ) - 1) by
      push_cast; ring, hpow, Complex.ofReal_cpow (Nat.cast_nonneg n), Complex.ofReal_natCast]
  have hzpow : chapter7NatCpow n z * (n : ℂ) ^ (-z) = 1 := by
    simpa using hpow 0
  have hmain := hpow 1
  rw [Complex.cpow_one] at hmain
  unfold residual
  rw [chapter7PowerSum_exact_expansion z M n hz hM hu hn]
  have hsum := Finset.sum_congr (s₁ := range M) rfl (fun j _ => hterm j)
  rw [← Finset.sum_mul] at hsum
  linear_combination hsum + (1 / (z + 1)) * hmain + (1 / 2) * hzpow

private theorem coeff_continuous (j : ℕ) : Continuous (coeff j) := by
  unfold coeff chapter7FallingGammaRatio
  fun_prop

private theorem residual_diff {n : ℕ} (hn : 1 < n) (N : ℕ) {z : ℂ} (hz : z ≠ -1) :
    DifferentiableAt ℂ (residual N n) z := by
  have hsum : DifferentiableAt ℂ (fun w => chapter7PowerSum w n) z := by
    unfold chapter7PowerSum chapter7NatCpow
    apply DifferentiableAt.fun_sum
    intro i hi
    have hi0 : i ≠ 0 := Nat.ne_of_gt (mem_Icc.mp hi).1
    exact differentiableAt_id.const_cpow (Or.inl (Nat.cast_ne_zero.mpr hi0))
  have hζ : DifferentiableAt ℂ (fun w => riemannZeta (-w)) z :=
    (differentiableAt_riemannZeta (by intro h; apply hz; linear_combination -h)).comp z
      differentiableAt_id.neg
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hz1 : z + 1 ≠ 0 := by intro h; apply hz; linear_combination h
  unfold residual coeff chapter7FallingGammaRatio
  fun_prop (disch := first | assumption | exact Or.inl hn0)

-- The same kernel bound works throughout the half-plane one unit from the convergence boundary.
private theorem uniform_tail (M : ℕ) (hM : 0 < M) :
    ∃ B ≥ (0 : ℝ), ∀ (n : ℕ), 1 < n → ∀ z : ℂ, z.re + 1 ≤ 2 * M →
      ‖powerSumTail M z n‖ ≤ B * (n : ℝ) ^ (z.re - 2 * M) := by
  obtain ⟨B, hB⟩ := MetaMathlibExt.bernoulliKernel_norm_le M hM
  have hB0 := (norm_nonneg _).trans (hB 0)
  refine ⟨B, hB0, fun n hn z hz => ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  let a := z.re - 2 * M - 1
  have ha : a < -1 := by dsimp [a]; linarith
  have hg := (integrableOn_Ioi_rpow_of_lt ha hn0).const_mul B
  calc
    ‖powerSumTail M z n‖ ≤ ∫ x : ℝ in Set.Ioi (n : ℝ), B * x ^ a := by
      apply norm_integral_le_of_norm_le hg
      apply (ae_restrict_mem measurableSet_Ioi).mono
      intro x hx
      have hx0 : 0 < x := hn0.trans hx
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, mul_comm]
      have he : (z - ((2 * M + 1 : ℕ) : ℂ)).re = a := by simp [a]; ring
      rw [he]
      gcongr
      exact hB x
    _ = B * ((n : ℝ) ^ (z.re - 2 * M) / (2 * M - z.re)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt ha hn0]
      dsimp [a]
      rw [sub_add_cancel, neg_div, ← div_neg, neg_sub]
    _ ≤ B * (n : ℝ) ^ (z.re - 2 * M) := by
      gcongr
      apply div_le_self (Real.rpow_nonneg hn0.le _)
      linarith

private theorem residual_bound (N : ℕ) (r : ℝ) (hr : -1 < r) :
    ∃ B : ℝ, ∀ n : ℕ, 1 < n → ‖deriv (residual N n) (r : ℂ)‖ ≤ B * weight N n := by
  let R := (r + 1) / 2
  have hR : 0 < R := by dsimp [R]; linarith
  let K := Metric.closedBall (r : ℂ) R
  have hK : IsCompact K := isCompact_closedBall _ _
  have hre {z : ℂ} (hz : z ∈ K) : |z.re - r| ≤ R := by
    apply (Complex.abs_re_le_norm (z - r)).trans
    simpa [dist_eq_norm] using Metric.mem_closedBall.mp hz
  have hne {z : ℂ} (hz : z ∈ K) : z ≠ -1 := by
    rintro rfl
    have h := (abs_le.mp (hre hz)).1
    simp [R] at h
    linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (r + R + 1)
  let M := max L (N + 1)
  have hNM : N < M := lt_of_lt_of_le (Nat.lt_succ_self N) (le_max_right _ _)
  have hM : 0 < M := by omega
  have hu {z : ℂ} (hz : z ∈ K) : z.re + 1 ≤ 2 * M := by
    have h := (abs_le.mp (hre hz)).2
    have hLM : (L : ℝ) ≤ M := by exact_mod_cast (le_max_left L (N + 1))
    linarith
  let P (i : ℕ) := ∃ B : ℝ, ∀ n : ℕ, 1 < n → ∀ z ∈ K, ‖residual i n z‖ ≤ B * weight N n
  have hbase : P M := by
    obtain ⟨B, hB0, hB⟩ := uniform_tail M hM
    have hc : Continuous (powerSumRemainderFactor M) := by
      unfold powerSumRemainderFactor chapter7FallingGammaRatio
      fun_prop
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
    have hD0 := (norm_nonneg _).trans (hD r (Metric.mem_closedBall_self hR.le))
    refine ⟨D * B, fun n hn z hz => ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
    have hn0 : (0 : ℝ) < n := zero_lt_one.trans_le hn1
    rw [residual_eq hn hM (hne hz) (by linarith [hu hz]), norm_neg, norm_mul, norm_mul,
      Complex.norm_natCast_cpow_of_pos (by omega : 0 < n), Complex.neg_re]
    calc
      _ ≤ D * (B * (n : ℝ) ^ (z.re - 2 * M)) * (n : ℝ) ^ (-z.re) := by
        gcongr
        · exact hD z hz
        · exact hB n hn z (hu hz)
      _ = D * B * (n : ℝ) ^ (-(2 * M : ℝ)) := by
        rw [mul_assoc D, mul_assoc, ← Real.rpow_add hn0]
        ring_nf
      _ ≤ _ := by
        unfold weight
        gcongr
        have : (N : ℝ) + 1 ≤ M := by exact_mod_cast hNM
        linarith
  -- Drop the extra corrections one at a time. Each is bounded by the first omitted power.
  have hbound : P N := by
    refine Nat.decreasingInduction' (motive := P) ?_ hNM.le hbase
    intro j _ hj h
    obtain ⟨B, hB⟩ := h
    obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn (coeff_continuous j).continuousOn
    refine ⟨B + D, fun n hn z hz => ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
    have hw (i : ℕ) : 0 ≤ weight i n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have he : residual j n z = residual (j + 1) n z + coeff j z * (weight j n : ℂ) := by
      simp only [residual, sum_range_succ]
      ring
    rw [he, add_mul]
    apply (norm_add_le _ _).trans
    apply add_le_add (hB n hn z hz)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw j)]
    apply mul_le_mul (hD z hz) _ (hw j) ((norm_nonneg _).trans (hD z hz))
    apply Real.rpow_le_rpow_of_exponent_le hn1
    have : (N : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  obtain ⟨B, hB⟩ := hbound
  refine ⟨B / R, fun n hn => ?_⟩
  have hd : DifferentiableOn ℂ (residual N n) K :=
    fun z hz => (residual_diff hn N (hne hz)).differentiableWithinAt
  have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
    (hd.diffContOnCl_ball subset_rfl) (fun z hz => hB n hn z (Metric.sphere_subset_closedBall hz))
  exact h.trans_eq (by ring)

private def realCoeff (j : ℕ) (t : ℝ) : ℝ :=
  (bernoulli (2 * (j + 1)) : ℝ) / ((2 * (j + 1)).factorial : ℝ) *
    ∏ q ∈ range (2 * (j + 1) - 1), (t - q)

private def negZeta (t : ℝ) : ℝ := (riemannZeta (-t : ℂ)).re

private theorem residual_re (N n : ℕ) (t : ℝ) :
    (residual N n t).re = (chapter9PowerSumR t n - negZeta t) * (n : ℝ) ^ (-t) -
      ((n : ℝ) / (t + 1) + 1 / 2 + ∑ j ∈ range N, realCoeff j t * weight j n) := by
  have hs : chapter7PowerSum t n = (chapter9PowerSumR t n : ℂ) := by
    simp [chapter7PowerSum, chapter9PowerSumR, Real.rpow_eq_pow, chapter7NatCpow,
      Complex.ofReal_cpow (Nat.cast_nonneg _)]
  have hc (j : ℕ) : coeff j t = (realCoeff j t : ℂ) := by
    simp [coeff, realCoeff, chapter7FallingGammaRatio]
  have hpow : (n : ℂ) ^ (-(t : ℂ)) = ((n : ℝ) ^ (-t) : ℝ) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp
  unfold residual
  rw [hs, hpow]
  simp only [hc, ← Complex.ofReal_mul, ← Complex.ofReal_sum, ← Complex.ofReal_one,
    ← Complex.ofReal_ofNat, ← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_div,
    Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rfl

private theorem hasDerivAt_coeff (j : ℕ) (r : ℝ) :
    HasDerivAt (realCoeff j) (chapter9Entry27Coeff (j + 1) r) r := by
  unfold realCoeff chapter9Entry27Coeff chapter9FallingDerivative
  apply HasDerivAt.const_mul
  rw [show 2 * (j + 1) - 2 + 1 = 2 * (j + 1) - 1 by omega]
  simpa only [smul_eq_mul, mul_one] using HasDerivAt.fun_finsetProd
    (u := range (2 * (j + 1) - 1)) (fun (q : ℕ) _ => (hasDerivAt_id' r).sub_const (q : ℝ))

private theorem hasDerivAt_powerSum (n : ℕ) (r : ℝ) :
    HasDerivAt (fun t => chapter9PowerSumR t n) (chapter9PhiR r n) r := by
  simp only [chapter9PowerSumR, chapter9PhiR, Nat.floor_natCast, Real.rpow_eq_pow]
  apply HasDerivAt.fun_sum
  intro q hq
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast (mem_Icc.mp hq).1
  simpa [mul_comm] using (hasDerivAt_id' r).const_rpow hq0

private theorem residual_deriv_re (N n : ℕ) (hn : 1 < n) (r : ℝ) (hr : -1 < r) :
    chapter9PhiR r n - Real.log n * (chapter9PowerSumR r n - negZeta r) -
      chapter9Entry27Approx r (deriv negZeta r) N n =
        (n : ℝ) ^ r * (deriv (residual N n) (r : ℂ)).re := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hz1 : (r : ℂ) ≠ -1 := by exact_mod_cast (by linarith : r ≠ -1)
  have hζ : DifferentiableAt ℂ (fun z => riemannZeta (-z)) (r : ℂ) :=
    (differentiableAt_riemannZeta (by intro h; apply hz1; linear_combination -h)).comp _
      differentiableAt_id.neg
  have hzr : DifferentiableAt ℝ negZeta r := hζ.hasDerivAt.real_of_complex.differentiableAt
  have hnr := (hasDerivAt_id' r).neg.const_rpow hn0
  have hquot := (hasDerivAt_const r (n : ℝ)).div ((hasDerivAt_id' r).add_const 1)
    (by linarith : r + 1 ≠ 0)
  have hsum := HasDerivAt.fun_sum (u := range N)
    (fun j _ => (hasDerivAt_coeff j r).mul_const (weight j n))
  have hd := (((hasDerivAt_powerSum n r).sub hzr.hasDerivAt).mul hnr).sub
    ((hquot.add_const (1 / 2)).add hsum)
  have hcopy := (residual_diff hn N hz1).hasDerivAt.real_of_complex
  have he := hcopy.unique (hd.congr_of_eventuallyEq (Eventually.of_forall (residual_re N n)))
  simp only [Pi.neg_apply, Pi.sub_apply] at he
  rw [he]
  have hcancel : (n : ℝ) ^ r * (n : ℝ) ^ (-r) = 1 := by
    rw [← Real.rpow_add hn0]; simp
  have hmain : (n : ℝ) ^ (r + 1) = (n : ℝ) ^ r * n := by rw [Real.rpow_add_one hn0.ne']
  have hterms : (n : ℝ) ^ r * (∑ j ∈ range N, chapter9Entry27Coeff (j + 1) r * weight j n) =
      ∑ j ∈ range N, chapter9Entry27Coeff (j + 1) r *
        (n : ℝ) ^ (r - 2 * ((j + 1 : ℕ) : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [mul_left_comm, weight, ← Real.rpow_add hn0]
    congr 2
    push_cast
    ring
  simp only [chapter9Entry27Approx, Real.rpow_eq_pow, hmain]
  linear_combination (norm := ring_nf) hterms -
    (chapter9PhiR r n - deriv negZeta r - Real.log n * (chapter9PowerSumR r n - negZeta r)) *
      hcancel

private theorem zeta_log_series (r : ℝ) (hr : 0 < r) :
    Summable (chapter9Entry27LogTerm r) ∧
    HasDerivAt (fun t : ℝ => (riemannZeta (t : ℂ)).re)
      (-(∑' j, chapter9Entry27LogTerm r j)) (r + 1) := by
  let s : ℂ := ↑(r + 1)
  have hs : 1 < s.re := by dsimp [s]; linarith
  have ha : LSeries.abscissaOfAbsConv 1 < s.re := by
    rw [LSeries.abscissaOfAbsConv_one]
    exact_mod_cast hs
  let f := LSeries.term (LSeries.logMul 1) s
  have hf : Summable f := LSeriesSummable_logMul_of_lt_re ha
  have hshift (j : ℕ) : f (j + 1) = (chapter9Entry27LogTerm r j : ℂ) := by
    simp [f, LSeries.logMul, chapter9Entry27LogTerm, Real.rpow_eq_pow, s,
      Complex.ofReal_log (by positivity : 0 ≤ (j : ℝ) + 1),
      Complex.ofReal_cpow (by positivity : 0 ≤ (j : ℝ) + 1)]
  have hfs : Summable (fun j : ℕ => f (j + 1)) := (summable_nat_add_iff 1).mpr hf
  refine ⟨Complex.summable_ofReal.mp (hfs.congr hshift), ?_⟩
  have hsum : LSeries (LSeries.logMul 1) s = ((∑' j, chapter9Entry27LogTerm r j : ℝ) : ℂ) := by
    change ∑' n, f n = _
    rw [hf.tsum_eq_zero_add]
    simp only [f, LSeries.term_zero, zero_add]
    rw [Complex.ofReal_tsum]
    exact tsum_congr hshift
  have heq : riemannZeta =ᶠ[𝓝 s] LSeries 1 := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz
    exact (LSeries_one_eq_riemannZeta hz).symm
  have hd := (LSeries_hasDerivAt ha).congr_of_eventuallyEq heq
  simpa only [hsum, Complex.neg_re, Complex.ofReal_re] using hd.real_of_complex

private theorem negZeta_eq (t : ℝ) (ht : 0 < t) :
    negZeta t = -(2 * Real.Gamma (t + 1) * Real.sin (Real.pi * t / 2) *
      (2 * Real.pi) ^ (-(t + 1)) * (riemannZeta (t + 1 : ℂ)).re) := by
  have h := riemannZeta_one_sub (s := ↑(t + 1))
    (fun n hn => by
      have := congrArg Complex.re hn
      simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α := ℝ) n])
    (by exact_mod_cast (by linarith : t + 1 ≠ 1))
  have harg : 1 - (↑(t + 1) : ℂ) = -(t : ℂ) := by push_cast; ring
  have hcos : (Real.pi : ℂ) * ↑(t + 1) / 2 = ↑(Real.pi * t / 2 + Real.pi / 2) := by
    push_cast
    ring
  rw [harg, hcos, ← Complex.ofReal_cos, Real.cos_add_pi_div_two, Complex.Gamma_ofReal] at h
  have hpow : (2 * (Real.pi : ℂ)) ^ (-(↑(t + 1) : ℂ)) =
      (((2 * Real.pi) ^ (-(t + 1)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [hpow] at h
  unfold negZeta
  rw [h]
  simp only [← Complex.ofReal_ofNat, ← Complex.ofReal_mul, Complex.re_ofReal_mul,
    Complex.ofReal_add, Complex.ofReal_one]
  ring

private theorem constant_formula (r : ℝ) (hr : 0 < r) :
    0 < Real.Gamma (r + 1) ∧ Summable (chapter9Entry27LogTerm r) ∧
    deriv negZeta r =
      2 * Real.Gamma (r + 1) * (riemannZeta (r + 1 : ℂ)).re /
          (2 * Real.pi) ^ (r + 1) *
        (Real.sin (Real.pi * r / 2) * (Real.log (2 * Real.pi) -
          deriv Real.Gamma (r + 1) / Real.Gamma (r + 1)) -
          Real.pi / 2 * Real.cos (Real.pi * r / 2)) +
      2 * Real.Gamma (r + 1) * Real.sin (Real.pi * r / 2) /
          (2 * Real.pi) ^ (r + 1) * ∑' j : ℕ, chapter9Entry27LogTerm r j := by
  have hg := Real.Gamma_pos_of_pos (by linarith : 0 < r + 1)
  obtain ⟨hs, hz⟩ := zeta_log_series r hr
  refine ⟨hg, hs, ?_⟩
  have hshift := (hasDerivAt_id' r).add_const 1
  have hG := (Real.differentiableAt_Gamma (s := r + 1)
    (fun n h => by linarith [Nat.cast_nonneg (α := ℝ) n])).hasDerivAt.comp r hshift
  have hsin := (((hasDerivAt_id' r).const_mul Real.pi).div_const 2).sin
  have hbase : 0 < 2 * Real.pi := by positivity
  have hpow := hshift.neg.const_rpow hbase
  have h := ((((hG.const_mul 2).mul hsin).mul hpow).mul (hz.comp r hshift)).neg
  have heq := h.congr_of_eventuallyEq (f₁ := negZeta) ((eventually_gt_nhds hr).mono fun t ht => by
    simpa only [Pi.neg_apply, Pi.mul_apply, Function.comp_apply, Complex.ofReal_add,
      Complex.ofReal_one] using negZeta_eq t ht)
  rw [heq.deriv]
  simp only [Pi.mul_apply, Function.comp_apply, Pi.neg_apply, Complex.ofReal_add,
    Complex.ofReal_one, mul_one, Real.rpow_neg hbase.le]
  field_simp [hg.ne', (Real.rpow_pos_of_pos hbase (r + 1)).ne']
  ring

/-- **Asymptotic expansion of partial sums of powers times logarithms.** Let $r > -1$ be a real
number. For a natural number $n$ write $\varphi_r(n) = \sum_{k=1}^{n} k^r \log k$ and
$S_r(n) = \sum_{k=1}^{n} k^r$, and for a natural number $m$ let
$D_m(r) = \sum_{j=0}^{m} \prod_{0 \le q \le m,\ q \ne j} (r - q)$, the derivative of
$r(r-1)\cdots(r-m)$ with respect to $r$. Let $B_j$ be the Bernoulli numbers and $\zeta$ the Riemann
zeta function. Then there is a real constant $C$ such that for every natural number $N$, as
$n \to \infty$ through the natural numbers,

$$
\varphi_r(n) - \log n \, \bigl(S_r(n) - \zeta(-r)\bigr) = C - \frac{n^{r+1}}{(r+1)^2} +
\sum_{k=1}^{N} \frac{B_{2k}}{(2k)!} D_{2k-2}(r) \, n^{r-2k+1} + O\bigl(n^{r-2N-1}\bigr).
$$

Moreover, if $r > 0$, then $\Gamma(r+1) > 0$, the series $\sum_{n \ge 1} \log n / n^{r+1}$
converges, and

$$
C = \frac{2\Gamma(r+1)\zeta(r+1)}{(2\pi)^{r+1}} \Bigl(\sin\frac{\pi r}{2} \Bigl(\log(2\pi) -
\frac{\Gamma'(r+1)}{\Gamma(r+1)}\Bigr) - \frac{\pi}{2} \cos\frac{\pi r}{2}\Bigr) +
\frac{2\Gamma(r+1)\sin\frac{\pi r}{2}}{(2\pi)^{r+1}} \sum_{n=1}^{\infty} \frac{\log n}{n^{r+1}}.
$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9. -/
theorem ramanujan_part1_ch9_entry27_clausen (r : ℝ) (hr : -1 < r) :
    ∃ C : ℝ,
      (∀ N : ℕ, Asymptotics.IsBigO
        (Filter.map (fun n : ℕ => (n : ℝ)) atTop)
        (fun x : ℝ =>
          chapter9PhiR r x - Real.log x *
              (chapter9PowerSumR r x - (riemannZeta (-r : ℂ)).re) -
            chapter9Entry27Approx r C N x)
        (fun x : ℝ => Real.rpow x (r - 2 * (N : ℝ) - 1))) ∧
      (0 < r →
        0 < Real.Gamma (r + 1) ∧
        Summable (chapter9Entry27LogTerm r) ∧
        C =
          2 * Real.Gamma (r + 1) * (riemannZeta (r + 1 : ℂ)).re /
              Real.rpow (2 * Real.pi) (r + 1) *
            (Real.sin (Real.pi * r / 2) *
                (Real.log (2 * Real.pi) -
                  deriv Real.Gamma (r + 1) / Real.Gamma (r + 1)) -
              Real.pi / 2 * Real.cos (Real.pi * r / 2)) +
          2 * Real.Gamma (r + 1) * Real.sin (Real.pi * r / 2) /
              Real.rpow (2 * Real.pi) (r + 1) *
            ∑' j : ℕ, chapter9Entry27LogTerm r j) := by
  refine ⟨deriv negZeta r, fun N => ?_, constant_formula r⟩
  obtain ⟨B, hB⟩ := residual_bound N r hr
  rw [isBigO_map, isBigO_iff]
  refine ⟨B, ?_⟩
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  change ‖chapter9PhiR r n - Real.log n * (chapter9PowerSumR r n - negZeta r) -
    chapter9Entry27Approx r (deriv negZeta r) N n‖ ≤ B * ‖(n : ℝ) ^ (r - 2 * N - 1)‖
  rw [residual_deriv_re N n hn r hr, norm_mul, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hn0 _), Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hn0 _)]
  calc
    _ ≤ (n : ℝ) ^ r * (B * weight N n) :=
      mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hB n hn))
        (Real.rpow_nonneg hn0.le _)
    _ = _ := by
      rw [weight, mul_left_comm, ← Real.rpow_add hn0]
      congr 2
      ring

end MathlibExt.Analysis.Ramanujan.Part1Ch9.Entry27Clausen
