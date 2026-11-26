/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic

/-!
# A zeta-twisted cyclotomic product identity

Partitioning the roots of unity by order gives a divisor sum identity for principal
logarithms on the unit disk. Möbius inversion and the multiplication rule for absolutely
convergent Dirichlet series then give the common limit of Bal's two partial products.
-/

open Complex Filter Polynomial Topology
open scoped ArithmeticFunction.Moebius

namespace MetaMathlibExt

private lemma one_sub_mem_slitPlane {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ∈ slitPlane := by
  rw [sub_eq_add_neg]
  exact mem_slitPlane_of_norm_lt_one (by simpa only [norm_neg] using hw)

private lemma norm_pow_lt_one {w : ℂ} (hw : ‖w‖ < 1) {n : ℕ} (hn : n ≠ 0) : ‖w ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hw hn

/-- Summing principal logarithms over all roots introduces no branch jump on the unit disk. -/
private lemma sum_log_nthRoots {z : ℂ} (hz : ‖z‖ < 1) {n : ℕ} (hn : 0 < n) :
    ∑ ζ ∈ nthRootsFinset n (1 : ℂ), log (1 - z * ζ) = log (1 - z ^ n) := by
  let D := Metric.ball (0 : ℂ) 1
  let S := nthRootsFinset n (1 : ℂ)
  let f (w : ℂ) := (∑ ζ ∈ S, log (1 - w * ζ)) - log (1 - w ^ n)
  have hnorm (w : ℂ) (hw : w ∈ D) : ‖w‖ < 1 := by
    simpa [D, Metric.mem_ball, dist_zero_right] using hw
  have hroot (w : ℂ) (hw : w ∈ D) (ζ : ℂ) (hζ : ζ ∈ S) : 1 - w * ζ ∈ slitPlane := by
    have hζ' : ‖ζ‖ = 1 := norm_eq_one_of_pow_eq_one ((mem_nthRootsFinset hn 1).mp hζ) hn.ne'
    exact one_sub_mem_slitPlane (by simpa only [norm_mul, hζ', mul_one] using hnorm w hw)
  have hpow (w : ℂ) (hw : w ∈ D) : 1 - w ^ n ∈ slitPlane :=
    one_sub_mem_slitPlane (norm_pow_lt_one (hnorm w hw) hn.ne')
  have hexp (w : ℂ) (hw : w ∈ D) : exp (f w) = 1 := by
    have hprod : ∏ ζ ∈ S, (1 - w * ζ) = 1 - w ^ n := by
      simpa only [S, one_pow, mul_comm w] using
        ((isPrimitiveRoot_exp n hn.ne').pow_sub_pow_eq_prod_sub_mul 1 w hn).symm
    change exp ((∑ ζ ∈ S, log (1 - w * ζ)) - log (1 - w ^ n)) = 1
    rw [exp_sub, exp_sum, exp_log (slitPlane_ne_zero (hpow w hw))]
    rw [Finset.prod_congr rfl (fun ζ hζ ↦ exp_log (slitPlane_ne_zero (hroot w hw ζ hζ))), hprod,
      div_self (slitPlane_ne_zero (hpow w hw))]
  have hdiff (w : ℂ) (hw : w ∈ D) : DifferentiableAt ℂ f w := by
    apply DifferentiableAt.sub
    · refine DifferentiableAt.fun_sum fun ζ hζ ↦ ?_
      exact DifferentiableAt.clog (f := fun v ↦ 1 - v * ζ) (by fun_prop) (hroot w hw ζ hζ)
    · exact DifferentiableAt.clog (f := fun v ↦ 1 - v ^ n) (by fun_prop) (hpow w hw)
  -- The exponential of the difference is constant, so the difference has zero derivative.
  have hderiv : Set.EqOn (deriv f) 0 D := by
    intro w hw
    have hmem : ∀ᶠ v in 𝓝 w, v ∈ D := Metric.isOpen_ball.mem_nhds hw
    have hconst : (fun v ↦ exp (f v)) =ᶠ[𝓝 w] fun _ ↦ (1 : ℂ) :=
      hmem.mono fun v hv ↦ hexp v hv
    have h := (hdiff w hw).hasDerivAt.cexp
    rw [hexp w hw, one_mul] at h
    exact (h.congr_of_eventuallyEq hconst.symm).unique (hasDerivAt_const w (1 : ℂ))
  have hf : f z = f 0 := Metric.isOpen_ball.is_const_of_deriv_eq_zero
    (convex_ball (0 : ℂ) 1).isPreconnected (fun w hw ↦ (hdiff w hw).differentiableWithinAt)
    hderiv (by simpa [D, Metric.mem_ball, dist_zero_right] using hz)
    (Metric.mem_ball_self zero_lt_one)
  exact sub_eq_zero.mp (hf.trans (by simp [f, hn.ne']))

private noncomputable def primitiveLogSum (z : ℂ) (n : ℕ) : ℂ :=
  ∑ ζ ∈ primitiveRoots n ℂ, log (1 - z * ζ)

private lemma sum_primitiveLogSum_divisors {z : ℂ} (hz : ‖z‖ < 1) {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, primitiveLogSum z d = log (1 - z ^ n) := by
  rw [← sum_log_nthRoots hz hn, IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots,
    Finset.sum_biUnion (fun _ _ _ _ hij ↦ IsPrimitiveRoot.disjoint hij)]
  rfl

private lemma tendsto_prod_exp_Icc {f : ℕ → ℂ} {a : ℂ} (hf : HasSum f a) (h0 : f 0 = 0) :
    Tendsto (fun N : ℕ ↦ ∏ i ∈ Finset.Icc 1 N, exp (f i)) atTop (𝓝 (exp a)) := by
  have hsum (N : ℕ) : ∑ i ∈ Finset.Icc 1 N, f i = ∑ i ∈ Finset.Iic N, f i := by
    refine Finset.sum_subset Finset.Icc_subset_Iic_self fun i hi hnot ↦ ?_
    have hi0 : i = 0 := by
      rw [Finset.mem_Iic] at hi
      rw [Finset.mem_Icc] at hnot
      omega
    simpa only [hi0] using h0
  simpa only [Function.comp_def, ← exp_sum, hsum] using
    continuous_exp.continuousAt.tendsto.comp (hf.comp tendsto_finset_Iic_atTop_atTop)

private lemma lSeriesSummable_log_one_sub_pow {z : ℂ} (hz : ‖z‖ < 1) {s : ℝ} (hs : 1 < s) :
    LSeriesSummable (fun n : ℕ ↦ log (1 - z ^ n)) (s : ℂ) := by
  have hpow : Tendsto (fun n : ℕ ↦ z ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz
  have hlog : Tendsto (fun n : ℕ ↦ log (1 - z ^ n)) atTop (𝓝 0) := by
    simpa only [sub_zero, log_one] using
      ((tendsto_const_nhds (x := (1 : ℂ))).sub hpow).clog (by simp)
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ hlog).exists_norm_le
  exact LSeriesSummable_of_bounded_of_one_lt_real (fun n _ ↦ hC _ ⟨n, rfl⟩) hs

/-- **A zeta-twisted cyclotomic product identity.** For $n \ge 1$ and complex $z$, let
$\hat\Phi_n(z) = \prod_\omega (1 - z\omega)$, the product over the primitive $n$-th roots of
unity $\omega$. Let $z$ be a complex number with $|z| < 1$, let $s > 1$ be real, and let
$\zeta$ be the Riemann zeta function. Then
$$
\prod_{i \ge 1} (1 - z^i)^{-1/i^s} = \prod_{i \ge 1} \hat\Phi_i(z)^{-\zeta(s)/i^s}
$$
in the sense that, as $N \to \infty$, the partial products over $1 \le i \le N$ of both sides
converge to a common limit. Here $(1 - z^i)^{-1/i^s} = \exp(-i^{-s} \log(1 - z^i))$ and
$\hat\Phi_i(z)^{-\zeta(s)/i^s} = \exp(-\zeta(s) \, i^{-s} \sum_\omega \log(1 - z\omega))$, where
$\log$ is the principal branch of the logarithm.

The published Theorem 2 and arXiv:2511.16975, Theorem 2.2, both use the exponent
$-\zeta(s)/i^s$.

Source: Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*,
INTEGERS 25 (2025), Article A96, Theorem 2 (`integers-2025-A96-thm-2`). -/
public theorem exists_tendsto_prod_one_sub_pow_and_cyclotomicHat_zeta {z : ℂ}
    (hz : ‖z‖ < 1) {s : ℝ} (hs : 1 < s) :
    ∃ L : ℂ,
      Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N,
          Complex.exp (-(((i : ℝ) ^ s : ℝ) : ℂ)⁻¹ * Complex.log (1 - z ^ i))) atTop (𝓝 L) ∧
      Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N,
          Complex.exp (-(riemannZeta (s : ℂ) / (((i : ℝ) ^ s : ℝ) : ℂ)) *
            ∑ ζ ∈ primitiveRoots i ℂ, Complex.log (1 - z * ζ))) atTop (𝓝 L) := by
  let A := primitiveLogSum z
  let B (n : ℕ) := log (1 - z ^ n)
  let M (n : ℕ) : ℂ := μ n
  let J (_ : ℕ) : ℂ := 1
  have hB : LSeries.convolution J A = B := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [B]
    rw [LSeries.convolution_def]
    change (∑ p ∈ n.divisorsAntidiagonal, 1 * A p.2) = B n
    simp only [one_mul, Nat.sum_divisorsAntidiagonal' (fun _ d ↦ A d)]
    exact sum_primitiveLogSum_divisors hz (Nat.pos_of_ne_zero hn)
  have hA : LSeries.convolution M B = A := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp [A, primitiveLogSum, primitiveRoots_zero]
    rw [LSeries.convolution_def]
    exact ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
      (fun _ hn' ↦ sum_primitiveLogSum_divisors hz hn') n (Nat.pos_of_ne_zero hn)
  -- Möbius inversion proves absolute convergence without bounding each root separately.
  have hm : LSeriesSummable M (s : ℂ) := by
    apply LSeriesSummable_of_bounded_of_one_lt_real (m := 1) _ hs
    intro n _
    change ‖(μ n : ℂ)‖ ≤ 1
    rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;> simp [h]
  have ha : LSeriesSummable A (s : ℂ) := hA ▸ hm.convolution (lSeriesSummable_log_one_sub_pow hz hs)
  have hj : LSeriesHasSum J (s : ℂ) (riemannZeta (s : ℂ)) := by
    have hs' : 1 < (s : ℂ).re := by simpa only [ofReal_re] using hs
    simpa [J, HurwitzZeta.cosZeta_zero] using HurwitzZeta.LSeriesHasSum_cos 0 hs'
  have hb : LSeriesHasSum B (s : ℂ) (riemannZeta (s : ℂ) * LSeries A (s : ℂ)) :=
    hB ▸ hj.convolution ha.LSeriesHasSum
  have hterm (f : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
      LSeries.term f (s : ℂ) n = f n / (((n : ℝ) ^ s : ℝ) : ℂ) := by
    rw [LSeries.term_of_ne_zero hn, ofReal_cpow n.cast_nonneg, ofReal_natCast]
  refine ⟨exp (-(riemannZeta (s : ℂ) * LSeries A (s : ℂ))), ?_, ?_⟩
  · have h : HasSum (LSeries.term B (s : ℂ)) (riemannZeta (s : ℂ) * LSeries A (s : ℂ)) := hb
    refine (tendsto_prod_exp_Icc h.neg (by simp)).congr fun N ↦ ?_
    refine Finset.prod_congr rfl fun i hi ↦ ?_
    rw [hterm B (Nat.ne_of_gt (Finset.mem_Icc.mp hi).1), div_eq_inv_mul, neg_mul]
  · have h : HasSum (LSeries.term A (s : ℂ)) (LSeries A (s : ℂ)) := ha.LSeriesHasSum
    refine (tendsto_prod_exp_Icc (h.mul_left (riemannZeta (s : ℂ))).neg (by simp)).congr
      fun N ↦ Finset.prod_congr rfl fun i hi ↦ ?_
    rw [hterm A (Nat.ne_of_gt (Finset.mem_Icc.mp hi).1), ← mul_div_assoc,
      ← div_mul_eq_mul_div, neg_mul]
    rfl

end MetaMathlibExt
