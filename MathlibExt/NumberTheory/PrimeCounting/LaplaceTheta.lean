/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.SumPrimeReciprocals
public import Mathlib.NumberTheory.Chebyshev
public import MathlibExt.Analysis.LaplaceTransform.ExponentialBound

/-!
# Laplace transform of `theta (exp ·)`

ATLAS NumberTheoryI Lemma 16.10: for `1 < s.re`, the Laplace transform of
`theta (exp t)` equals `primeLogSeries s / s` and is holomorphic on
`{s | 1 < s.re}`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Chebyshev

private lemma prime_log_pos (p : Nat.Primes) :
    0 < Real.log ↑(↑p : ℕ) := by
  rw [Real.log_pos_iff (by exact_mod_cast p.2.pos.le : (0 : ℝ) ≤ ↑(↑p : ℕ))]
  exact_mod_cast p.2.one_lt

private lemma abel_norm_summand_eq (c : ℝ) (hc : 0 ≤ c) (s : ℂ) (t : ℝ) :
    ‖Complex.exp (-s * (t : ℂ)) * ((if c ≤ t then c else 0 : ℝ) : ℂ)‖ =
    if c ≤ t then c * Real.exp (-s.re * t) else 0 := by
  rw [norm_mul, Complex.norm_exp]
  simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.norm_real]
  split_ifs with h
  · simp [Real.norm_of_nonneg hc, mul_comm]
  · simp

private lemma abel_indicator_integral_real (c : ℝ) (hc : 0 < c)
    (σ : ℝ) (hσ : 0 < σ) :
    ∫ t in Set.Ioi (0 : ℝ),
      (if c ≤ t then c * Real.exp (-σ * t) else 0) =
    c * Real.exp (-σ * c) / σ := by
  have h_eq : ∀ t : ℝ, (if c ≤ t then c * Real.exp (-σ * t) else 0) =
      (Set.Ici c).indicator (fun t => c * Real.exp (-σ * t)) t := by
    intro t
    simp [Set.indicator, Set.mem_Ici]
  simp_rw [h_eq]
  rw [integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hIci : Set.Ici c ∩ Set.Ioi (0 : ℝ) = Set.Ici c := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨And.left, fun hx => ⟨hx, lt_of_lt_of_le hc hx⟩⟩
  rw [hIci, integral_Ici_eq_integral_Ioi, integral_const_mul]
  rw [integral_exp_mul_Ioi (by linarith : -σ < 0) c]
  field_simp

private lemma abel_indicator_integral_complex (c : ℝ) (hc : 0 < c)
    (s : ℂ) :
    ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-s * (t : ℂ)) *
      ((if c ≤ t then c else 0 : ℝ) : ℂ) =
    (c : ℂ) * ∫ t in Set.Ioi c, Complex.exp (-s * (t : ℂ)) := by
  have h_eq : ∀ t : ℝ, Complex.exp (-s * (t : ℂ)) *
      ((if c ≤ t then c else 0 : ℝ) : ℂ) =
      (Set.Ici c).indicator
        (fun t : ℝ => (c : ℂ) * Complex.exp (-s * (t : ℂ))) t := by
    intro t
    simp only [Set.indicator, Set.mem_Ici]
    split_ifs with h <;> simp [mul_comm]
  simp_rw [h_eq]
  rw [integral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hIci : Set.Ici c ∩ Set.Ioi (0 : ℝ) = Set.Ici c := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨And.left, fun hx => ⟨hx, lt_of_lt_of_le hc hx⟩⟩
  rw [hIci, ← integral_Ici_eq_integral_Ioi]
  exact integral_const_mul _ _

private lemma exp_neg_mul_log_eq_cpow (p : ℕ) (hp : 0 < p) (s : ℂ) :
    Complex.exp (-s * ((Real.log (p : ℝ) : ℝ) : ℂ)) = (p : ℂ) ^ (-s) := by
  have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [Complex.cpow_def_of_ne_zero hp_ne]
  congr 1
  rw [← Complex.natCast_log (n := p)]
  ring

private lemma integral_indicator_prime (p : ℕ) (hp : Nat.Prime p)
    (s : ℂ) (hs : 0 < s.re) :
    ∫ t in Set.Ioi (Real.log (p : ℝ)), Complex.exp (-s * (t : ℂ)) =
    (p : ℂ) ^ (-s) / s := by
  have hs_ne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hns_re : (-s).re < 0 := by
    simp
    linarith
  rw [integral_exp_mul_complex_Ioi hns_re (Real.log (p : ℝ))]
  rw [exp_neg_mul_log_eq_cpow p (Nat.Prime.pos hp) s]
  field_simp

private lemma abel_summable_primes_log_rpow (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun p : Nat.Primes =>
      Real.log ↑(↑p : ℕ) * (↑(↑p : ℕ) : ℝ) ^ (-σ)) := by
  have hε : (0 : ℝ) < (σ - 1) / 2 := by linarith
  have hexp : (σ - 1) / 2 - σ < -1 := by linarith
  apply Summable.of_nonneg_of_le
  · intro p
    positivity
  · intro p
    have hp_pos : (0 : ℝ) < ↑(↑p : ℕ) := by exact_mod_cast p.2.pos
    calc Real.log ↑(↑p : ℕ) * (↑(↑p : ℕ) : ℝ) ^ (-σ)
        ≤ ((↑(↑p : ℕ) : ℝ) ^ ((σ - 1) / 2) / ((σ - 1) / 2)) *
          (↑(↑p : ℕ) : ℝ) ^ (-σ) :=
          mul_le_mul_of_nonneg_right (Real.log_le_rpow_div hp_pos.le hε)
            (by positivity)
      _ = (1 / ((σ - 1) / 2)) * (↑(↑p : ℕ) : ℝ) ^ ((σ - 1) / 2 - σ) := by
          rw [div_mul_eq_mul_div, ← Real.rpow_add hp_pos]
          ring_nf
  · exact (Nat.Primes.summable_rpow.mpr hexp).const_smul (1 / ((σ - 1) / 2))

private lemma abel_integrableOn_prime_summand (p : Nat.Primes)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-s * (t : ℂ)) *
      ((if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ)
        else 0 : ℝ) : ℂ)) (Set.Ioi 0) := by
  have hlog_pos := prime_log_pos p
  have h_eq : (fun t : ℝ => Complex.exp (-s * (t : ℂ)) *
        ((if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ)
          else 0 : ℝ) : ℂ)) =
      (Set.Ici (Real.log ↑(↑p : ℕ))).indicator
        (fun t : ℝ => ((Real.log ↑(↑p : ℕ) : ℝ) : ℂ) *
          Complex.exp (-s * (t : ℂ))) := by
    ext t
    simp only [Set.indicator, Set.mem_Ici]
    split_ifs with h <;> simp [mul_comm]
  rw [h_eq, integrableOn_indicator_iff measurableSet_Ici.nullMeasurableSet]
  have hIci : Set.Ici (Real.log ↑(↑p : ℕ)) ∩ Set.Ioi (0 : ℝ) =
      Set.Ici (Real.log ↑(↑p : ℕ)) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Ioi]
    exact ⟨And.left, fun hx => ⟨hx, lt_of_lt_of_le hlog_pos hx⟩⟩
  rw [hIci]
  have h_base : IntegrableOn
      (fun t : ℝ => Complex.exp ((-s) * (t : ℂ)))
      (Set.Ici (Real.log ↑(↑p : ℕ))) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_complex_Ioi (by simp; linarith) _
  exact h_base.const_mul (((Real.log ↑(↑p : ℕ) : ℝ)) : ℂ)

private lemma theta_exp_eq_tsum (t : ℝ) :
    theta (Real.exp t) = ∑' p : Nat.Primes,
      (if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ) else 0) := by
  set S := Finset.subtype Nat.Prime (Ioc 0 ⌊Real.exp t⌋₊)
  have h1 : theta (Real.exp t) = ∑ p ∈ S, Real.log ↑(↑p : ℕ) := by
    rw [Chebyshev.theta, ← sum_subtype_eq_sum_filter]
  have h2 : (∑' p : Nat.Primes, if Real.log ↑(↑p : ℕ) ≤ t then
        Real.log ↑(↑p : ℕ) else 0) =
      ∑ p ∈ S, if Real.log ↑(↑p : ℕ) ≤ t then
        Real.log ↑(↑p : ℕ) else 0 := by
    apply tsum_eq_sum
    intro p hp
    have hp' : (⟨(p : ℕ), p.2⟩ : {q : ℕ // Nat.Prime q}) ∉ S := by
      change p ∉ S at hp
      exact hp
    have hmem : ¬((↑p : ℕ) ∈ Ioc 0 ⌊Real.exp t⌋₊) := by
      simpa only [S, Finset.mem_subtype] using hp'
    rw [Finset.mem_Ioc, not_and_or, not_lt, not_le] at hmem
    simp only [ite_eq_right_iff]
    intro hlog
    exfalso
    have hp_pos : (0 : ℕ) < ↑p := p.2.pos
    rcases hmem with h | h
    · omega
    · have hle : (↑↑p : ℝ) ≤ Real.exp t := by
        rw [← Real.log_le_iff_le_exp
          (by exact_mod_cast hp_pos : (0 : ℝ) < ↑↑p)]
        exact hlog
      exact absurd (Nat.le_floor hle) (not_le.mpr h)
  rw [h1, h2]
  apply Finset.sum_congr rfl
  intro p hp
  have hmem : (↑p : ℕ) ∈ Ioc 0 ⌊Real.exp t⌋₊ :=
    Finset.mem_subtype.mp hp
  rw [Finset.mem_Ioc] at hmem
  have hp_pos : (0 : ℝ) < (↑↑p : ℝ) := by exact_mod_cast hmem.1
  have hlog : Real.log ↑(↑p : ℕ) ≤ t := by
    rw [Real.log_le_iff_le_exp hp_pos]
    exact le_trans (by exact_mod_cast hmem.2)
      (Nat.floor_le (le_of_lt (Real.exp_pos t)))
  rw [ite_eq_left hlog]

private theorem abel_summation_laplace (s : ℂ) (hs : 1 < s.re) :
    (∫ t in Set.Ioi (0 : ℝ), Complex.exp (-s * (t : ℂ)) *
      ((theta (Real.exp t) : ℝ) : ℂ)) =
    ∑' p : Nat.Primes, ((Real.log ↑(↑p : ℕ) : ℂ) *
      (↑(↑p : ℕ) : ℂ) ^ (-s) / s) := by
  have hs0 : 0 < s.re := by linarith
  simp_rw [theta_exp_eq_tsum]
  conv_lhs =>
    arg 2
    ext t
    rw [show Complex.exp (-s * (t : ℂ)) *
        (((∑' p : Nat.Primes, (if Real.log ↑(↑p : ℕ) ≤ t then
          Real.log ↑(↑p : ℕ) else 0) : ℝ)) : ℂ) =
        ∑' p : Nat.Primes, Complex.exp (-s * (t : ℂ)) *
        (((if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ)
          else 0 : ℝ)) : ℂ) from by
      push_cast
      rw [tsum_mul_left]]
  have h_int : ∀ p : Nat.Primes, Integrable
      (fun t : ℝ => Complex.exp (-s * (t : ℂ)) *
        (((if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ)
          else 0 : ℝ)) : ℂ)) (volume.restrict (Set.Ioi 0)) :=
    fun p => abel_integrableOn_prime_summand p s hs0
  have h_norm_eq : ∀ p : Nat.Primes, ∫ t in Set.Ioi (0 : ℝ),
      ‖Complex.exp (-s * (t : ℂ)) *
        (((if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ)
          else 0 : ℝ)) : ℂ)‖ =
      Real.log ↑(↑p : ℕ) * (↑(↑p : ℕ) : ℝ) ^ (-s.re) / s.re := by
    intro p
    simp_rw [abel_norm_summand_eq _ (prime_log_pos p).le s]
    rw [abel_indicator_integral_real _ (prime_log_pos p) _ hs0]
    congr 1
    congr 1
    rw [Real.rpow_def_of_pos
      (by exact_mod_cast p.2.pos : (0 : ℝ) < ↑(↑p : ℕ))]
    ring_nf
  have h_summ : Summable (fun p : Nat.Primes => ∫ t in Set.Ioi (0 : ℝ),
      ‖Complex.exp (-s * (t : ℂ)) *
        (((if Real.log ↑(↑p : ℕ) ≤ t then Real.log ↑(↑p : ℕ)
          else 0 : ℝ)) : ℂ)‖) := by
    simp_rw [h_norm_eq]
    exact (abel_summable_primes_log_rpow s.re hs).div_const s.re
  rw [(integral_tsum_of_summable_integral_norm h_int h_summ).symm]
  congr 1
  ext p
  rw [abel_indicator_integral_complex _ (prime_log_pos p) s]
  rw [integral_indicator_prime _ p.2 s hs0]
  ring

private lemma theta_exp_meas :
    AEStronglyMeasurable (fun t : ℝ => ((theta (Real.exp t) : ℝ) : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
  have hcomp : Measurable (fun t : ℝ => theta (Real.exp t)) :=
    Chebyshev.theta_mono.measurable.comp Real.measurable_exp
  exact (Complex.continuous_ofReal.measurable.comp hcomp).aestronglyMeasurable

private lemma theta_exp_bound_C : (0 : ℝ) ≤ Real.log 4 :=
  Real.log_nonneg (by norm_num)

private lemma theta_exp_bound : ∀ t : ℝ, 0 ≤ t →
    ‖((theta (Real.exp t) : ℝ) : ℂ)‖ ≤
    Real.log 4 * Real.exp (1 * t) := by
  intro t _
  have hpos : 0 ≤ Real.exp t := le_of_lt (Real.exp_pos t)
  have hle := @Chebyshev.theta_le_log4_mul_x (Real.exp t) hpos
  have hnn := @Chebyshev.theta_nonneg (Real.exp t)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  calc theta (Real.exp t) ≤ Real.log 4 * Real.exp t := hle
    _ = Real.log 4 * Real.exp (1 * t) := by rw [one_mul]

/-- **The prime logarithm series.** For $s \in \mathbb{C}$, the prime logarithm series at $s$
is the complex number $\sum_p \log p \cdot p^{-s}$, where the sum runs over all primes $p$ and
$p^{-s}$ is the complex power. The sum is unconditional and is taken to be $0$ by convention
when the family $(\log p \cdot p^{-s})_p$ is not summable.

Source: ATLAS NumberTheoryI Lemma 16.10. -/
noncomputable def primeLogSeries (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes,
    (Real.log ↑(↑p : ℕ) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s)

/-- **Laplace transform of $\theta(e^t)$.** Let $\theta(x) = \sum_{p \le x} \log p$ be
Chebyshev's function, the sum running over the primes $p \le x$. For every $s \in \mathbb{C}$
with $\operatorname{Re} s > 1$, the Laplace transform
$\int_{(0, \infty)} e^{-st}\,\theta(e^t)\,dt$ of $t \mapsto \theta(e^t)$ at $s$ equals
$\frac{1}{s} \sum_p \log p \cdot p^{-s}$, the prime logarithm series at $s$ divided by $s$,
where the sum runs over all primes $p$.

Source: ATLAS NumberTheoryI Lemma 16.10. -/
theorem laplace_theta_exp_eq_primeLogSeries_div (s : ℂ) (hs : 1 < s.re) :
    laplace (fun t : ℝ => (theta (Real.exp t) : ℂ)) s =
      primeLogSeries s / s := by
  have hsum := abel_summation_laplace s hs
  unfold laplace primeLogSeries
  change (∫ t in Set.Ioi (0 : ℝ),
      Complex.exp (-s * (t : ℂ)) * (theta (Real.exp t) : ℂ)) =
    (∑' p : Nat.Primes,
      (Real.log ↑(↑p : ℕ) : ℂ) * (↑(↑p : ℕ) : ℂ) ^ (-s)) / s
  rw [hsum, tsum_div_const]

/-- **Convergence of the Laplace transform of $\theta(e^t)$.** Let
$\theta(x) = \sum_{p \le x} \log p$ be Chebyshev's function, the sum running over the primes
$p \le x$. For every $s \in \mathbb{C}$ with $\operatorname{Re} s > 1$, the function
$t \mapsto \theta(e^t)$ has Laplace transform $\frac{1}{s} \sum_p \log p \cdot p^{-s}$ at $s$,
where the sum runs over all primes $p$ (this is the prime logarithm series at $s$ divided by
$s$): the function $t \mapsto e^{-st}\,\theta(e^t)$ is integrable on $(0, \infty)$ and its
integral over $(0, \infty)$ equals $\frac{1}{s} \sum_p \log p \cdot p^{-s}$.

Source: ATLAS NumberTheoryI Lemma 16.10. -/
theorem hasLaplace_theta_exp (s : ℂ) (hs : 1 < s.re) :
    HasLaplace (fun t : ℝ => (theta (Real.exp t) : ℂ)) s
      (primeLogSeries s / s) := by
  refine ⟨?_, ?_⟩
  · exact laplaceConvergent_of_norm_le_exp _ 1 _ theta_exp_meas
      theta_exp_bound_C theta_exp_bound hs
  · exact laplace_theta_exp_eq_primeLogSeries_div s hs

/-- **Holomorphy of the Laplace transform of $\theta(e^t)$.** Let
$\theta(x) = \sum_{p \le x} \log p$ be Chebyshev's function, the sum running over the primes
$p \le x$. Then the Laplace transform $F(s) = \int_{(0, \infty)} e^{-st}\,\theta(e^t)\,dt$ of
$t \mapsto \theta(e^t)$ is complex differentiable at every point of the open half-plane
$\{s \in \mathbb{C} : \operatorname{Re} s > 1\}$, so it is holomorphic there.

Source: ATLAS NumberTheoryI Lemma 16.10. -/
theorem differentiableOn_laplace_theta_exp :
    DifferentiableOn ℂ (laplace (fun t : ℝ => (theta (Real.exp t) : ℂ)))
      {s | 1 < s.re} :=
  differentiableOn_laplace_of_norm_le_exp _ 1 _ theta_exp_meas
    theta_exp_bound_C theta_exp_bound

end Chebyshev
