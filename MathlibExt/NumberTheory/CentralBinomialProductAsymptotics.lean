/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import MathlibExt.NumberTheory.BinomialProductAsymptotics
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry1Powersum
import Mathlib.Analysis.SpecialFunctions.Log.Sum
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.Harmonic.ZetaAsymp

/-!
# Products of central binomial coefficients and Catalan numbers

The theorem `tendsto_prod_centralBinom_catalan_div` gives the limits of the normalized products
of central binomial coefficients and of Catalan numbers. The theorem `tendsto_prod_choose_row_div`
gives the limit of the normalized product of a row of Pascal’s triangle.

Differentiating the Euler–Maclaurin expansion for the sum of `k ^ r` at `r = 0` and `r = 1`
gives expansions for the sums of `log k` and `k * log k`. Regrouping the factorials expresses
the central binomial product in terms of these sums. Dividing by `(n + 1)!` gives the Catalan
product. The same log sums handle the Pascal-row product via the factorial identity in
Kellner’s proof of Theorem 10, equation (8).

The namespace `LogFactorialExpansion` exposes the error terms of these expansions for
`log n!` and for the sum of `k * log k`, their limits and their recurrences, for reuse by
other product asymptotics.
-/

namespace MetaMathlibExt

open Filter Topology
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry1Powersum
open MeasureTheory

namespace LogFactorialExpansion

private theorem integrand_bound {C x : ℝ} {r : ℂ} {b : ℝ}
    (hC : ‖bernoulliKernel 3 x‖ ≤ C) (hx : 1 ≤ x) (hr : r.re ≤ b) :
    ‖(x : ℂ) ^ (r - 3) * (bernoulliKernel 3 x : ℂ)‖ ≤ C * x ^ (b - 3) := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < x), Complex.norm_real,
    mul_comm C]
  apply mul_le_mul _ hC (norm_nonneg _) (Real.rpow_nonneg (by linarith) _)
  apply Real.rpow_le_rpow_of_exponent_le hx
  simpa using hr

private theorem tail_continuous {n : ℕ} (hn : 1 < n) {a : ℂ} (ha : a.re < 3 / 2) :
    ContinuousAt (fun r => powerSumTail 1 r n) a := by
  obtain ⟨C, hC⟩ := bernoulliKernel_norm_le 1 (by decide)
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn.le
  change Tendsto (fun r : ℂ => ∫ x : ℝ in Set.Ioi (n : ℝ),
    (x : ℂ) ^ (r - 3) * (bernoulliKernel 3 x : ℂ)) _ _
  apply tendsto_integral_filter_of_dominated_convergence (fun x : ℝ => C * x ^ (3 / 2 - 3 : ℝ))
  · apply Eventually.of_forall
    intro r
    have hk := (bernoulliKernel_continuous (by decide : 3 ≠ 1)).measurable
    exact (by fun_prop (disch := norm_num) :
      Measurable (fun x : ℝ => (x : ℂ) ^ (r - 3) * (bernoulliKernel 3 x : ℂ))).aestronglyMeasurable
  · filter_upwards [Complex.continuous_re.continuousAt.eventually_lt_const ha] with r hr
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi)] with x hx
    exact integrand_bound (hC x) (hn'.trans hx.le) hr.le
  · exact (integrableOn_Ioi_rpow_of_lt (by norm_num : (3 / 2 - 3 : ℝ) < -1)
      (by positivity : 0 < (n : ℝ))).const_mul C
  · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi)] with x hx
    have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast (show x ≠ 0 by linarith [hx.out])
    apply ContinuousAt.tendsto
    exact ((continuousAt_const_cpow hx').comp (continuousAt_id.sub_const _)).mul
      continuousAt_const

private theorem tail_bound {n : ℕ} (hn : 1 < n) {a : ℂ} (ha : a.re < 2)
    {C : ℝ} (hC : ∀ x, ‖bernoulliKernel 3 x‖ ≤ C) :
    ‖powerSumTail 1 a n‖ ≤ C * (-(n : ℝ) ^ (a.re - 2) / (a.re - 2)) := by
  have hn' : 1 ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hp : 0 < (n : ℝ) := by positivity
  have he : a.re - 3 < -1 := by linarith
  have h := norm_integral_le_of_norm_le
    ((integrableOn_Ioi_rpow_of_lt he hp).const_mul C)
    ((ae_restrict_mem (μ := volume) measurableSet_Ioi).mono
      (fun x hx => integrand_bound (hC x) (hn'.trans hx.le) (le_refl a.re)))
  simpa only [powerSumTail_eq_integral, Nat.reduceMul, Nat.reduceAdd, Nat.cast_ofNat,
    integral_const_mul, integral_Ioi_rpow_of_lt he hp,
    show a.re - 3 + 1 = a.re - 2 by ring] using h

-- The tail coefficient vanishes at both exponents where we differentiate.
private theorem deriv_mul_at_root {f g : ℂ → ℂ} {a d : ℂ} (hf : HasDerivAt f d a)
    (hz : f a = 0) (hg : ContinuousAt g a) :
    HasDerivAt (fun r => f r * g r) (d * g a) a := by
  apply hasDerivAt_iff_tendsto_slope.mpr
  refine (hf.tendsto_slope.mul (hg.tendsto.mono_left nhdsWithin_le_nhds)).congr ?_
  intro r
  simp [slope_def_field, hz, div_eq_mul_inv, mul_right_comm]

private theorem power_sum_derivative (n : ℕ) (hn : 1 < n) (a : ℂ) (ha : a = 0 ∨ a = 1) :
    ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ a * Complex.log k =
      -deriv riemannZeta (-a) +
      ((n : ℂ) ^ (a + 1) * Complex.log n * (a + 1) - (n : ℂ) ^ (a + 1)) / (a + 1) ^ 2 +
      (n : ℂ) ^ a * Complex.log n / 2 +
      ((n : ℂ) ^ (a - 1) + a * ((n : ℂ) ^ (a - 1) * Complex.log n)) / 12 -
      ((a - 1) * (a - 2) + a * (a - 2) + a * (a - 1)) / 6 * powerSumTail 1 a n := by
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have ha1 : a ≠ -1 := by rcases ha with rfl | rfl <;> norm_num
  have ha2 : a.re < 3 / 2 := by rcases ha with rfl | rfl <;> norm_num
  have heq : (fun r => chapter7PowerSum r n) =ᶠ[𝓝 a] fun r : ℂ =>
      riemannZeta (-r) + (n : ℂ) ^ (r + 1) / (r + 1) + (n : ℂ) ^ r / 2 +
        r * (n : ℂ) ^ (r - 1) / 12 -
        (r * (r - 1) * (r - 2) / 6) * powerSumTail 1 r n := by
    filter_upwards [eventually_ne_nhds ha1,
      Complex.continuous_re.continuousAt.eventually_lt_const ha2] with r hr hr'
    rw [chapter7PowerSum_exact_expansion r 1 n hr (by decide) (by norm_num; linarith) hn]
    norm_num [chapter7Entry1Term, chapter7NatCpow, powerSumRemainderFactor,
      chapter7FallingGammaRatio, Finset.prod_range_succ, bernoulli_two, Nat.factorial]
    ring_nf
  have hsum : HasDerivAt (fun r => chapter7PowerSum r n)
      (∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ a * Complex.log k) a := by
    apply HasDerivAt.fun_sum
    intro k hk
    have hk0 : (k : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hk).1)
    unfold chapter7NatCpow
    simpa using (hasDerivAt_id a).const_cpow (Or.inl hk0)
  have hid := hasDerivAt_id a
  have hz := (differentiableAt_riemannZeta
    (show -a ≠ 1 by simpa [neg_eq_iff_eq_neg] using ha1)).hasDerivAt.comp a hid.neg
  have hu := hid.add_const 1
  have hv := hid.sub_const 1
  have hw := hid.sub_const 2
  have hpoly := ((hid.mul hv).mul hw).div_const 6
  have htail := deriv_mul_at_root hpoly
    (by rcases ha with rfl | rfl <;> norm_num) (tail_continuous hn ha2)
  have hquot := (hu.const_cpow (.inl hn0)).div hu
    (show a + 1 ≠ 0 by rcases ha with rfl | rfl <;> norm_num)
  have h := (((hz.add hquot).add ((hid.const_cpow (.inl hn0)).div_const 2)).add
    ((hid.mul (hv.const_cpow (.inl hn0))).div_const 12)).sub htail
  have he := (hsum.congr_of_eventuallyEq heq.symm).unique h
  dsimp at he
  rw [he]
  ring

/-- The weighted logarithmic sum $\sum_{k=1}^{n} k \log k$. -/
@[expose] public noncomputable def weightedLog (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * Real.log k

/-- The main term $(x + 1/2) \log x - x + \log(2\pi)/2 + 1/(12x)$ of the expansion of
$\log x!$. -/
@[expose] public noncomputable def factorialMain (x : ℝ) : ℝ :=
  (x + 1 / 2) * Real.log x - x + Real.log (2 * Real.pi) / 2 + 1 / (12 * x)

/-- The main term $(x^2/2 + x/2 + 1/12) \log x - x^2/4 + \log A$ of the expansion of
`weightedLog`, where $A$ is the Glaisher–Kinkelin constant. -/
@[expose] public noncomputable def weightedMain (x : ℝ) : ℝ :=
  (x ^ 2 / 2 + x / 2 + 1 / 12) * Real.log x - x ^ 2 / 4 + Real.log glaisherKinkelinConstant

private theorem factorial_expansion {n : ℕ} (hn : 1 < n) :
    Real.log n.factorial = factorialMain n - (powerSumTail 1 0 n).re / 3 := by
  have h := power_sum_derivative n hn 0 (.inl rfl)
  norm_num [deriv_riemannZeta_zero, Complex.cpow_neg_one] at h
  have hd : (Real.log (n.factorial : ℝ) : ℂ) =
      (factorialMain n : ℂ) - powerSumTail 1 0 n / 3 := by
    rw [← Real.sum_log_eq_log_factorial, ← Finset.Icc_add_one_left_eq_Ioc]
    unfold factorialMain
    push_cast
    simp only [Complex.ofReal_log (by positivity : 0 ≤ 2 * Real.pi),
      Complex.ofReal_mul, Complex.ofReal_ofNat]
    convert h using 1
    ring
  simpa only [Complex.sub_re, Complex.ofReal_re, Complex.div_ofNat_re] using congrArg Complex.re hd

private theorem weighted_expansion {n : ℕ} (hn : 1 < n) :
    weightedLog n = weightedMain n + (powerSumTail 1 1 n).re / 6 := by
  have h := power_sum_derivative n hn 1 (.inr rfl)
  norm_num [Complex.cpow_two] at h
  have hd : (weightedLog n : ℂ) =
      (((n : ℝ) ^ 2 / 2 + n / 2 + 1 / 12) * Real.log n - n ^ 2 / 4 + 1 / 12 : ℝ) -
        deriv riemannZeta (-1) + powerSumTail 1 1 n / 6 := by
    unfold weightedLog
    push_cast
    convert h using 1
    ring
  have hre := congrArg Complex.re hd
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.div_ofNat_re] at hre
  unfold weightedMain
  rw [log_glaisherKinkelinConstant]
  linear_combination hre

/-- The error `Real.log n.factorial - factorialMain n` of the expansion of $\log n!$. -/
@[expose] public noncomputable def factorialError (n : ℕ) : ℝ :=
  Real.log n.factorial - factorialMain n

/-- The error `weightedLog n - weightedMain n` of the expansion of `weightedLog`. -/
@[expose] public noncomputable def weightedError (n : ℕ) : ℝ :=
  weightedLog n - weightedMain n

/-- As $n \to \infty$, both `n * factorialError n` and `weightedError n` tend to $0$. -/
public theorem error_limits :
    Tendsto (fun n : ℕ => n * factorialError n) atTop (𝓝 0) ∧
    Tendsto weightedError atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := bernoulliKernel_norm_le 1 (by decide)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hlim : Tendsto (fun n : ℕ => C * (n : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul C
  constructor
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn0 : 0 < (n : ℝ) := by positivity
    have hb := (Complex.abs_re_le_norm _).trans (tail_bound hn (a := 0) (by norm_num) hC)
    norm_num [Real.rpow_neg hn0.le] at hb
    simp [factorialError, factorial_expansion hn]
    field_simp [hn0.ne'] at hb ⊢
    nlinarith [abs_nonneg (powerSumTail 1 0 n).re]
  · apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hn0 : 0 < (n : ℝ) := by positivity
    have hb := (Complex.abs_re_le_norm _).trans (tail_bound hn (a := 1) (by norm_num) hC)
    norm_num [Real.rpow_neg hn0.le] at hb
    simp [weightedError, weighted_expansion hn]
    field_simp [hn0.ne'] at hb ⊢
    linarith

/-- For every natural number $n$, $\log (n + 1)! = \log n! + \log (n + 1)$. -/
public theorem log_factorial_succ (n : ℕ) :
    Real.log ((n + 1).factorial : ℝ) = Real.log n.factorial + Real.log (n + 1 : ℝ) := by
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add_one, Real.log_mul (by positivity)
    (by positivity), add_comm]

/-- For every natural number $n$,
`weightedLog (n + 1) = weightedLog n + (n + 1) * log (n + 1)`. -/
public theorem weightedLog_succ (n : ℕ) :
    weightedLog (n + 1) = weightedLog n + (n + 1 : ℝ) * Real.log (n + 1 : ℝ) := by
  simp [weightedLog, Finset.sum_Icc_succ_top (show 1 ≤ n + 1 by omega)]

/-- As $n \to \infty$, `factorialError n` tends to $0$. -/
public theorem factorialError_limit : Tendsto factorialError atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).mul error_limits.1
  refine (show Tendsto _ _ (𝓝 (0 : ℝ)) by simpa only [zero_mul] using h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  change (n : ℝ)⁻¹ * (n * factorialError n) = _
  field_simp

end LogFactorialExpansion

open LogFactorialExpansion

namespace tendsto_prod_centralBinom_catalan_div

private theorem log_centralBinom (n : ℕ) :
    Real.log n.centralBinom = Real.log (2 * n).factorial - 2 * Real.log n.factorial := by
  have h : (n.centralBinom : ℝ) * n.factorial * n.factorial = (2 * n).factorial := by
    exact_mod_cast (by simpa [Nat.centralBinom_eq_two_mul_choose, two_mul] using
      Nat.add_choose_mul_factorial_mul_factorial n n :
        n.centralBinom * n.factorial * n.factorial = (2 * n).factorial)
  have hb : (0 : ℝ) < n.centralBinom := by exact_mod_cast n.centralBinom_pos
  rw [← h, Real.log_mul (by positivity) (by positivity),
    Real.log_mul hb.ne' (by positivity)]
  ring

private noncomputable def centralProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (k.centralBinom : ℝ)

private theorem centralProduct_pos (n : ℕ) : 0 < centralProduct n :=
  Finset.prod_pos fun k _ => by exact_mod_cast k.centralBinom_pos

-- Regrouping the factorials at even and odd indices expresses the log product in two log sums.
private theorem log_centralProduct (n : ℕ) :
    Real.log (centralProduct n) =
      (n + 1 / 2 : ℝ) * Real.log (2 * n).factorial -
        (2 * n + 3 / 2 : ℝ) * Real.log n.factorial + n / 2 * Real.log 2 -
        weightedLog (2 * n) / 2 + 2 * weightedLog n := by
  induction n with
  | zero => simp [centralProduct, weightedLog]
  | succ n ih =>
    have hprod : centralProduct (n + 1) = centralProduct n * (n + 1).centralBinom := by
      apply Finset.prod_Icc_succ_top (by omega)
    have hb : (0 : ℝ) < (n + 1).centralBinom := by exact_mod_cast (n + 1).centralBinom_pos
    rw [hprod, Real.log_mul (centralProduct_pos n).ne' hb.ne', ih, log_centralBinom,
      show 2 * (n + 1) = 2 * n + 1 + 1 by omega]
    simp only [log_factorial_succ, weightedLog_succ, Nat.cast_add, Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat]
    rw [show (2 : ℝ) * n + 1 + 1 = 2 * (n + 1) by ring,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    ring

private noncomputable def centralScale (x : ℝ) : ℝ :=
  2 ^ (x ^ 2) * (4 * Real.exp 1 / Real.pi) ^ (x / 2) / x ^ (x / 2 + 3 / 8)

private noncomputable def catalanScale (x : ℝ) : ℝ :=
  2 ^ (x ^ 2) * (4 * Real.exp 3 / Real.pi) ^ (x / 2) / x ^ (3 * x / 2 + 15 / 8)

private noncomputable def centralConstant : ℝ :=
  2 ^ ((5 : ℝ) / 24) * glaisherKinkelinConstant ^ ((3 : ℝ) / 2) /
    ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 8))

private theorem centralConstant_pos : 0 < centralConstant := by
  unfold centralConstant glaisherKinkelinConstant
  positivity

private theorem log_four : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
  norm_num

private theorem central_log_error (n : ℕ) (hn : 0 < n) :
    Real.log (centralProduct n) - Real.log (centralScale n) - Real.log centralConstant =
      (2 * n : ℝ) * factorialError (2 * n) / 2 + factorialError (2 * n) / 2 -
        2 * (n * factorialError n) - 3 / 2 * factorialError n -
        weightedError (2 * n) / 2 + 2 * weightedError n - 5 / 48 * (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hA : 0 < glaisherKinkelinConstant := Real.exp_pos _
  rw [log_centralProduct]
  unfold centralScale centralConstant factorialError weightedError factorialMain weightedMain
  push_cast
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow, Real.log_exp,
    log_four]
  field_simp
  ring

private theorem central_log_limit :
    Tendsto (fun n : ℕ => Real.log (centralProduct n) - Real.log (centralScale n) -
      Real.log centralConstant) atTop (𝓝 0) := by
  have hd : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ 2 * n; omega) tendsto_id
  have hf := factorialError_limit
  have ⟨hF, hW⟩ := error_limits
  have hDouble := ((hF.comp hd).div_const 2).add ((hf.comp hd).div_const 2)
  have hFactorials := (hDouble.sub (hF.const_mul 2)).sub (hf.const_mul (3 / 2))
  have hSums := (hFactorials.sub ((hW.comp hd).div_const 2)).add (hW.const_mul 2)
  have h := hSums.sub ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul
    (5 / 48 : ℝ))
  refine (show Tendsto _ _ (𝓝 (0 : ℝ)) by simpa only [zero_div, mul_zero, add_zero, sub_zero]
    using h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [Function.comp_def] using (central_log_error n hn).symm

private noncomputable def catalanProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 n, (catalan k : ℝ)

private theorem catalanProduct_mul (n : ℕ) :
    catalanProduct n * (n + 1).factorial = centralProduct n := by
  induction n with
  | zero => simp [centralProduct, catalanProduct]
  | succ n ih =>
    have hc : ((n + 1 : ℕ) + 1 : ℝ) * catalan (n + 1) = (n + 1).centralBinom := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom (n + 1)
    unfold centralProduct catalanProduct at *
    rw [Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega),
      Nat.factorial_succ (n + 1), Nat.cast_mul, Nat.cast_add_one]
    rw [← ih, ← hc]
    ring

private theorem catalan_log_limit :
    Tendsto (fun n : ℕ => Real.log (catalanProduct n) - Real.log (catalanScale n) -
      Real.log (centralConstant * (2 * Real.pi) ^ (-(1 : ℝ) / 2))) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlog := ((hi.const_add 1).log (by norm_num : (1 : ℝ) + 0 ≠ 0))
  have h := ((central_log_limit.sub factorialError_limit).sub (hi.const_mul (1 / 12))).sub hlog
  refine (show Tendsto _ _ (𝓝 (0 : ℝ)) by simpa using h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : catalanProduct n = centralProduct n / (n + 1).factorial :=
    (eq_div_iff (by positivity)).mpr (catalanProduct_mul n)
  have hshift : 1 + (n : ℝ)⁻¹ = (n + 1) / n := by field_simp
  rw [hc, Real.log_div (centralProduct_pos n).ne' (by positivity), log_factorial_succ, hshift]
  unfold centralScale catalanScale factorialError factorialMain
  have hpos := centralConstant_pos
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow, Real.log_exp]
  ring

private theorem tendsto_ratio_of_log {P Q : ℕ → ℝ} {c : ℝ} (hc : 0 < c)
    (hPQ : ∀ᶠ n in atTop, 0 < P n ∧ 0 < Q n)
    (h : Tendsto (fun n => Real.log (P n) - Real.log (Q n) - Real.log c) atTop (𝓝 0)) :
    Tendsto (fun n => P n / Q n) atTop (𝓝 c) := by
  have hl := Real.continuous_exp.continuousAt.tendsto.comp (h.add_const (Real.log c))
  rw [zero_add, Real.exp_log hc] at hl
  refine hl.congr' ?_
  filter_upwards [hPQ] with n hn
  simp [← Real.log_div hn.1.ne' hn.2.ne', Real.exp_log (div_pos hn.1 hn.2)]

end tendsto_prod_centralBinom_catalan_div

open tendsto_prod_centralBinom_catalan_div

/-- **Asymptotics of products of central binomial coefficients and Catalan numbers.** Let $A$ be
the Glaisher–Kinkelin constant, let $\mathrm{Cat}_n$ denote the $n$-th Catalan number, and put
$C_{2,1} = 2^{5/24} A^{3/2} / \left((2\pi)^{1/2} e^{1/8}\right)$. As $m \to \infty$, the ratio of
$\prod_{n=1}^{m} \binom{2n}{n}$ to $2^{m^2} (4e/\pi)^{m/2} / m^{m/2 + 3/8}$ tends to $C_{2,1}$,
and the ratio of $\prod_{n=1}^{m} \mathrm{Cat}_n$ to
$2^{m^2} (4e^3/\pi)^{m/2} / m^{3m/2 + 15/8}$ tends to $C_{2,1} (2\pi)^{-1/2}$.

The decimal approximations of the constants are not part of this statement.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Corollary 7. -/
public theorem tendsto_prod_centralBinom_catalan_div :
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, (n.centralBinom : ℝ)) /
        (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 1 / Real.pi) ^ ((m : ℝ) / 2) /
          (m : ℝ) ^ ((m : ℝ) / 2 + 3 / 8)))
      atTop (𝓝 (2 ^ ((5 : ℝ) / 24) * glaisherKinkelinConstant ^ ((3 : ℝ) / 2) /
        ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 8)))) ∧
    Tendsto (fun m : ℕ => (∏ n ∈ Finset.Icc 1 m, (catalan n : ℝ)) /
        (2 ^ ((m : ℝ) ^ 2) * (4 * Real.exp 3 / Real.pi) ^ ((m : ℝ) / 2) /
          (m : ℝ) ^ (3 * (m : ℝ) / 2 + 15 / 8)))
      atTop (𝓝 (2 ^ ((5 : ℝ) / 24) * glaisherKinkelinConstant ^ ((3 : ℝ) / 2) /
        ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 8)) * (2 * Real.pi) ^ (-(1 : ℝ) / 2))) := by
  constructor
  · apply tendsto_ratio_of_log centralConstant_pos _ central_log_limit
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact ⟨centralProduct_pos n, by unfold centralScale; positivity⟩
  · apply tendsto_ratio_of_log (mul_pos centralConstant_pos (by positivity)) _ catalan_log_limit
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hp := centralProduct_pos n
    rw [← catalanProduct_mul] at hp
    exact ⟨pos_of_mul_pos_left hp (by positivity), by unfold catalanScale; positivity⟩


namespace tendsto_prod_choose_row_div

private noncomputable def rowProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range (n + 1), (n.choose k : ℝ)

private theorem rowProduct_pos (n : ℕ) : 0 < rowProduct n :=
  Finset.prod_pos fun k hk => by
    exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

-- Summing the factorial logs counts the summand `log k` exactly `n + 1 - k` times.
private theorem sum_log_factorial (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), Real.log (k.factorial : ℝ)) =
      (n + 1 : ℝ) * Real.log n.factorial - weightedLog n := by
  induction n with
  | zero => simp [weightedLog]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, weightedLog_succ, log_factorial_succ]
    push_cast
    ring

private theorem log_rowProduct (n : ℕ) :
    Real.log (rowProduct n) = 2 * weightedLog n - (n + 1 : ℝ) * Real.log n.factorial := by
  have hchoose (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      Real.log (n.choose k : ℝ) =
        Real.log n.factorial - Real.log k.factorial - Real.log (n - k).factorial := by
    have hkn := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h : (n.choose k : ℝ) * k.factorial * (n - k).factorial = n.factorial := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
    have hkpos : (0 : ℝ) < n.choose k := by exact_mod_cast Nat.choose_pos hkn
    rw [← h, Real.log_mul (by positivity) (by positivity), Real.log_mul hkpos.ne' (by positivity)]
    ring
  have hreflect : (∑ k ∈ Finset.range (n + 1), Real.log ((n - k).factorial : ℝ)) =
      ∑ k ∈ Finset.range (n + 1), Real.log (k.factorial : ℝ) := by
    simpa only [Nat.add_sub_cancel] using
      Finset.sum_range_reflect (fun k => Real.log (k.factorial : ℝ)) (n + 1)
  unfold rowProduct
  rw [Real.log_prod (fun k hk => by
    exact_mod_cast (Nat.choose_pos (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).ne'),
    Finset.sum_congr rfl hchoose]
  simp_rw [Finset.sum_sub_distrib]
  rw [hreflect, sum_log_factorial]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  ring

private noncomputable def rowScale (x : ℝ) : ℝ :=
  Real.exp (x ^ 2 / 2 + x) / ((2 * Real.pi) ^ (x / 2) * x ^ (x / 2 + 1 / 3))

private noncomputable def rowConstant : ℝ :=
  (factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹

private theorem rowConstant_pos : 0 < rowConstant := by
  unfold rowConstant
  have hF := factorialProductConstant_pos 1
  positivity

private theorem log_rowConstant :
    Real.log rowConstant =
      2 * Real.log glaisherKinkelinConstant - Real.log (2 * Real.pi) / 2 - 1 / 12 := by
  unfold rowConstant
  rw [Real.log_inv, Real.log_mul (factorialProductConstant_pos 1).ne' (by positivity),
    Real.log_rpow (by positivity), log_factorialProductConstant_one]
  ring

private theorem row_log_error (n : ℕ) (hn : 0 < n) :
    Real.log (rowProduct n) - Real.log (rowScale n) - Real.log rowConstant =
      2 * weightedError n - n * factorialError n - factorialError n - (1 / 12) * (n : ℝ)⁻¹ := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  rw [log_rowProduct, log_rowConstant]
  unfold rowScale weightedError factorialError weightedMain factorialMain
  simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_rpow, Real.log_exp]
  field_simp
  ring

private theorem row_log_limit :
    Tendsto (fun n : ℕ => Real.log (rowProduct n) - Real.log (rowScale n) -
      Real.log rowConstant) atTop (𝓝 0) := by
  have hi : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  obtain ⟨hF, hW⟩ := error_limits
  have h := (((hW.const_mul 2).sub hF).sub factorialError_limit).sub (hi.const_mul (1 / 12))
  refine (show Tendsto _ _ (𝓝 (0 : ℝ)) by simpa only [mul_zero, sub_zero] using h).congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (row_log_error n hn).symm

end tendsto_prod_choose_row_div

open tendsto_prod_choose_row_div

/-- **Asymptotics of the product of a row of Pascal's triangle.** Let $F_1$ be the first factorial
product constant and $A$ the Glaisher–Kinkelin constant, and put
$C_{\mathrm{row}} = \left(F_1 (2\pi)^{1/4}\right)^{-1}$. As $n \to \infty$, the ratio of
$\prod_{\nu=0}^{n} \binom{n}{\nu}$ to $e^{n^2/2 + n} / \left((2\pi)^{n/2} n^{n/2 + 1/3}\right)$
tends to $C_{\mathrm{row}}$, and $C_{\mathrm{row}} = A^2 / \left((2\pi)^{1/2} e^{1/12}\right)$.

Source: Bernd C. Kellner, *Asymptotic Products of Binomial and Multinomial Coefficients
Revisited*, INTEGERS 24 (2024), Article A59, Theorem 10. -/
public theorem tendsto_prod_choose_row_div :
    Tendsto (fun n : ℕ => (∏ ν ∈ Finset.range (n + 1), (n.choose ν : ℝ)) /
        (Real.exp ((n : ℝ) ^ 2 / 2 + n) /
          ((2 * Real.pi) ^ ((n : ℝ) / 2) * (n : ℝ) ^ ((n : ℝ) / 2 + 1 / 3))))
      atTop (𝓝 ((factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹)) ∧
    (factorialProductConstant 1 * (2 * Real.pi) ^ ((1 : ℝ) / 4))⁻¹ =
      glaisherKinkelinConstant ^ 2 / ((2 * Real.pi) ^ ((1 : ℝ) / 2) * Real.exp (1 / 12)) := by
  constructor
  · apply tendsto_ratio_of_log rowConstant_pos _ row_log_limit
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact ⟨rowProduct_pos n, by unfold rowScale; positivity⟩
  · change rowConstant = _
    have hA : 0 < glaisherKinkelinConstant := Real.exp_pos _
    apply Real.log_injOn_pos (show rowConstant ∈ Set.Ioi 0 from rowConstant_pos)
      (show _ ∈ Set.Ioi (0 : ℝ) by apply Set.mem_Ioi.mpr; positivity)
    rw [log_rowConstant]
    simp (disch := positivity) only [Real.log_div, Real.log_mul, Real.log_pow, Real.log_rpow,
      Real.log_exp, Nat.cast_ofNat]
    ring

end MetaMathlibExt
