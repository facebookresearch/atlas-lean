/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.PSeriesComplex

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.ZMod
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Phi
public import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry10Zetaviabernoulli
public import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry8Bernoullibound
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry9Zetaeven

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
open Entry10Zetaviabernoulli (chapter7Admissible chapter7PowerDifferenceTerm)
open Entry8Bernoullibound (chapter7BernoulliPolynomial chapter7IntegerPhi)

noncomputable section

private lemma chap7_base_ne_zero (j : ℕ) : ((j : ℂ) + 1) ≠ 0 := by
  have h : (((j + 1 : ℕ)) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero j
  simpa [Nat.cast_add, Nat.cast_one] using h

private lemma chap7_base_norm (j : ℕ) : ‖((j : ℂ) + 1)‖ = (((j + 1 : ℕ)) : ℝ) := by
  have heq : ((j : ℂ) + 1) = (((j + 1 : ℕ)) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_natCast]

private def chap7W (x : ℂ) (j : ℕ) : ℂ := x / ((j : ℂ) + 1)

private lemma chap7W_exists (x : ℂ) :
    ∃ J : ℕ, ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2 := by
  obtain ⟨J, hJ⟩ := exists_nat_ge (2 * ‖x‖)
  refine ⟨J, fun j hj => ?_⟩
  unfold chap7W
  rw [norm_div, chap7_base_norm]
  have hpos : (0 : ℝ) < (((j + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.succ_pos j
  have hle : 2 * ‖x‖ ≤ (((j + 1 : ℕ)) : ℝ) := by
    have hJ' : 2 * ‖x‖ ≤ (J : ℝ) := hJ
    have hJj : (J : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hj1 : (j : ℝ) ≤ (((j + 1 : ℕ)) : ℝ) := by
      have h2 : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
      rw [h2]
      exact le_add_of_nonneg_right zero_le_one
    linarith
  rw [div_le_iff₀ hpos]
  linarith

private lemma chap7_one_add_w_ne_zero {x : ℂ} {j : ℕ}
    (hw : ‖chap7W x j‖ ≤ 1 / 2) : (1 : ℂ) + chap7W x j ≠ 0 := by
  intro hcon
  have h1 : chap7W x j = (-1 : ℂ) := by linear_combination hcon
  have hnorm : ‖chap7W x j‖ = 1 := by
    rw [h1, norm_neg, norm_one]
  linarith

private lemma chap7_base_eq (j : ℕ) :
    ((j : ℂ) + 1) = ((((j + 1 : ℕ)) : ℝ) : ℂ) := by
  push_cast
  ring

private lemma chap7_mul_cpow_of_pos {a : ℝ} (ha : 0 < a) {b : ℂ} (hb : b ≠ 0)
    (r : ℂ) : (((a : ℂ) * b) ^ r) = (a : ℂ) ^ r * b ^ r := by
  have ha0 : (a : ℂ) ≠ 0 := by
    exact_mod_cast ha.ne'
  have hab0 : (a : ℂ) * b ≠ 0 := mul_ne_zero ha0 hb
  rw [Complex.cpow_def_of_ne_zero hab0, Complex.cpow_def_of_ne_zero ha0,
    Complex.cpow_def_of_ne_zero hb, Complex.log_ofReal_mul ha hb,
    Complex.ofReal_log ha.le, add_mul, Complex.exp_add]

private lemma chap7_factor {x : ℂ} {j : ℕ} (r : ℂ)
    (hw : ‖chap7W x j‖ ≤ 1 / 2) :
    (((j : ℂ) + 1 + x) ^ r) =
      (((j : ℂ) + 1) ^ r) * ((1 + chap7W x j) ^ r) := by
  have hbase : ((j : ℂ) + 1) ≠ 0 := chap7_base_ne_zero j
  have h1w : (1 : ℂ) + chap7W x j ≠ 0 := chap7_one_add_w_ne_zero hw
  have hEq : ((j : ℂ) + 1 + x) = ((j : ℂ) + 1) * (1 + chap7W x j) := by
    unfold chap7W
    field_simp
  rw [hEq]
  have ha : (0 : ℝ) < (((j + 1 : ℕ)) : ℝ) := by
    exact_mod_cast Nat.succ_pos j
  have hbaseR : ((j : ℂ) + 1) = ((((j + 1 : ℕ)) : ℝ) : ℂ) := chap7_base_eq j
  rw [hbaseR]
  exact chap7_mul_cpow_of_pos ha h1w r

private lemma chap7_binom_hasSum (r w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => Ring.choose r k * w ^ k) ((1 + w) ^ r) := by
  have hPS := Complex.one_add_cpow_hasFPowerSeriesOnBall_zero (a := r)
  have hmem : w ∈ Metric.eball (0 : ℂ) 1 := by
    have h1 : (1 : ENNReal) = ((1 : NNReal) : ENNReal) := by simp
    rw [h1, Metric.eball_coe, Metric.mem_ball, dist_eq_norm]
    simpa using hw
  have hsum := hPS.hasSum hmem
  have hterm : ∀ n : ℕ,
      binomialSeries ℂ r n (fun _ : Fin n => w) =
        Ring.choose r n * w ^ n := by
    intro n
    have h1 : binomialSeries ℂ r n (fun _ : Fin n => w) =
        Ring.choose r n • w ^ n := by
      unfold binomialSeries
      rw [FormalMultilinearSeries.ofScalars_apply_eq]
    rw [h1, smul_eq_mul]
  have hcongr : (fun n : ℕ => binomialSeries ℂ r n (fun _ : Fin n => w)) =
      (fun k : ℕ => Ring.choose r k * w ^ k) := funext hterm
  rw [hcongr] at hsum
  simpa using hsum

private lemma chap7_descPochhammer_smeval_eq_prod (r : ℂ) (k : ℕ) :
    (descPochhammer ℤ k).smeval r =
      ∏ i ∈ Finset.range k, (r - (i : ℂ)) := by
  induction k with
  | zero =>
    simp [descPochhammer_zero]
  | succ k ih =>
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, ih,
      Finset.prod_range_succ]
    congr 1
    have hX : (Polynomial.X : ℤ[X]).smeval r = r ^ 1 := by simp
    have hN : ((k : ℤ[X])).smeval r = (k : ℂ) := by
      rw [Polynomial.smeval_natCast]
      simp [pow_zero, nsmul_eq_mul]
    have hsub : ((Polynomial.X - (k : ℤ[X]) : ℤ[X])).smeval r =
        (Polynomial.X : ℤ[X]).smeval r - ((k : ℤ[X])).smeval r := by
      rw [Polynomial.smeval_sub]
    rw [hsub, hX, hN, pow_one]

private lemma chap7_choose_eq_prod (r : ℂ) (k : ℕ) :
    Ring.choose r k =
      ∏ i ∈ Finset.range k, ((r - (i : ℂ)) / ((i : ℂ) + 1)) := by
  have hchoose : Ring.choose r k =
      ((k.factorial : ℂ))⁻¹ * (descPochhammer ℤ k).smeval r := by
    rw [Ring.choose_eq_smul, smul_eq_mul]
  rw [hchoose, chap7_descPochhammer_smeval_eq_prod]
  have hfact : ((k.factorial : ℕ) : ℂ) =
      ∏ i ∈ Finset.range k, (((i + 1 : ℕ)) : ℂ) := by
    rw [Nat.factorial_eq_prod_range_add_one]
    rw [Nat.cast_prod]
  have hfact2 : ((k.factorial : ℕ) : ℂ) =
      ∏ i ∈ Finset.range k, ((i : ℂ) + 1) := by
    rw [hfact]
    apply Finset.prod_congr rfl
    intro i _
    push_cast
    ring
  rw [hfact2, Finset.prod_div_distrib]
  ring

private lemma chap7_factorial_mul_prod (N k : ℕ) :
    (N + k)! = N ! * ∏ i ∈ Finset.range k, (N + 1 + i) := by
  induction k with
  | zero =>
    simp
  | succ k ih =>
    have h1 : N + (k + 1) = (N + k) + 1 := by omega
    rw [h1, Nat.factorial_succ, ih, Finset.prod_range_succ]
    have h2 : N + 1 + k = N + k + 1 := by omega
    rw [h2]
    ring

private lemma chap7_prod_eq_choose (N k : ℕ) :
    ∏ i ∈ Finset.range k, ((((N + 1 + i : ℕ)) : ℝ) / (((i + 1 : ℕ)) : ℝ)) =
      ((((N + k).choose k : ℕ)) : ℝ) := by
  have hfact : ((N + k)! : ℕ) = ((N + k).choose k) * (k !) * (N !) := by
    have hle : k ≤ N + k := Nat.le_add_left k N
    have h := Nat.choose_mul_factorial_mul_factorial hle
    have hsub : N + k - k = N := by omega
    rw [hsub] at h
    exact h.symm
  have hfactR : (((N + k)! : ℕ) : ℝ) =
      ((((N + k).choose k : ℕ)) : ℝ) * ((k ! : ℕ) : ℝ) * ((N ! : ℕ) : ℝ) := by
    exact_mod_cast hfact
  have hkpos : ((k ! : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero k
  have hNpos : ((N ! : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero N
  have hchoose : ((((N + k).choose k : ℕ)) : ℝ) =
      (((N + k)! : ℕ) : ℝ) / (((k ! : ℕ) : ℝ) * ((N ! : ℕ) : ℝ)) := by
    rw [hfactR]
    field_simp
  rw [hchoose]
  have hNk : (((N + k)! : ℕ) : ℝ) =
      ((N ! : ℕ) : ℝ) * ∏ i ∈ Finset.range k, (((N + 1 + i : ℕ)) : ℝ) := by
    have h := chap7_factorial_mul_prod N k
    have hR : (((N + k)! : ℕ) : ℝ) =
        (((N ! * ∏ i ∈ Finset.range k, (N + 1 + i) : ℕ)) : ℝ) := by
      rw [h]
    rw [hR, Nat.cast_mul, Nat.cast_prod]
  have hk : ((k ! : ℕ) : ℝ) = ∏ i ∈ Finset.range k, (((i + 1 : ℕ)) : ℝ) := by
    have h : (k ! : ℕ) = ∏ i ∈ Finset.range k, (i + 1) :=
      Nat.factorial_eq_prod_range_add_one k
    have hR : ((k ! : ℕ) : ℝ) = ((∏ i ∈ Finset.range k, (i + 1) : ℕ) : ℝ) := by
      rw [h]
    rw [hR, Nat.cast_prod]
  rw [hNk, hk, Finset.prod_div_distrib]
  field_simp

private lemma chap7_choose_bound (r : ℂ) (N k : ℕ) (hr : ‖r‖ ≤ (N : ℝ)) :
    ‖Ring.choose r k‖ ≤ ((((N + k).choose k : ℕ)) : ℝ) := by
  rw [chap7_choose_eq_prod, norm_prod, ← chap7_prod_eq_choose]
  apply Finset.prod_le_prod₀
  · intro i _
    exact norm_nonneg _
  · intro i _
    rw [norm_div, chap7_base_norm]
    have hpos : (0 : ℝ) < (((i + 1 : ℕ)) : ℝ) := by
      exact_mod_cast Nat.succ_pos i
    have hnum : ‖r - (i : ℂ)‖ ≤ ((((N + 1 + i : ℕ))) : ℝ) := by
      have h1 : ‖r - (i : ℂ)‖ ≤ ‖r‖ + ‖(i : ℂ)‖ := norm_sub_le r (i : ℂ)
      rw [Complex.norm_natCast] at h1
      have h2 : (N : ℝ) + (i : ℝ) ≤ ((((N + 1 + i : ℕ))) : ℝ) := by
        have heq : ((((N + 1 + i : ℕ))) : ℝ) = (N : ℝ) + 1 + (i : ℝ) := by
          push_cast
          ring
        rw [heq]
        linarith
      linarith [h1, hr]
    have hle : ‖r - (i : ℂ)‖ / ((((i + 1 : ℕ))) : ℝ) ≤
        ((((N + 1 + i : ℕ))) : ℝ) / ((((i + 1 : ℕ))) : ℝ) := by
      apply div_le_div_of_nonneg_right hnum hpos.le
    exact hle

private def chap7R (K : ℕ) (r w : ℂ) : ℂ :=
  (1 + w) ^ r - ∑ k ∈ Finset.range (K + 1), Ring.choose r k * w ^ k

private lemma chap7R_hasSum (r w : ℂ) (K : ℕ) (hw : ‖w‖ < 1) :
    HasSum (fun n : ℕ => Ring.choose r (n + K + 1) * w ^ (n + K + 1))
      (chap7R K r w) := by
  have hfull := chap7_binom_hasSum r w hw
  have htail := (hasSum_nat_add_iff' (K + 1)).mpr hfull
  simpa [chap7R, add_assoc] using htail

private lemma chap7_choose_geometric (N : ℕ) :
    HasSum (fun k : ℕ => ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k)
      ((2 : ℝ) ^ (N + 1)) := by
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) N hr
  have hval : (1 : ℝ) / (1 - (1 / 2 : ℝ)) ^ (N + 1) = (2 : ℝ) ^ (N + 1) := by
    have h12 : (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) := by norm_num
    rw [h12, div_eq_mul_inv, one_mul, ← inv_pow]
    norm_num
  rw [hval] at h
  have hcongr : (fun n : ℕ => ((n + N).choose N : ℝ) * (1 / 2 : ℝ) ^ n) =
      (fun k : ℕ => ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k) := by
    funext n
    congr 1
    have h1 : n + N = N + n := Nat.add_comm n N
    rw [h1]
    have h2 : (N + n).choose N = (N + n).choose n := by
      have hle : N ≤ N + n := Nat.le_add_right N n
      have hsym := Nat.choose_symm hle
      have hsub : N + n - N = n := by omega
      rw [hsub] at hsym
      exact hsym.symm
    rw [h2]
  rw [hcongr] at h
  simpa using h

private lemma chap7R_bound (r w : ℂ) (N K : ℕ) (hr : ‖r‖ ≤ (N : ℝ))
    (hw : ‖w‖ ≤ 1 / 2) :
    ‖chap7R K r w‖ ≤ (2 : ℝ) ^ (N + 1) * (2 * ‖w‖) ^ (K + 1) := by
  have hwlt : ‖w‖ < 1 := lt_of_le_of_lt hw (by norm_num)
  have hTail := chap7R_hasSum r w K hwlt
  have hFull := chap7_choose_geometric N
  have hFullTail : HasSum
      (fun n : ℕ => ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
        (1 / 2 : ℝ) ^ (n + K + 1))
      ((2 : ℝ) ^ (N + 1) -
        ∑ k ∈ Finset.range (K + 1),
          ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k) := by
    have h := (hasSum_nat_add_iff' (K + 1)).mpr hFull
    simpa [add_assoc] using h
  have hhead_nonneg : 0 ≤ ∑ k ∈ Finset.range (K + 1),
      ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k := by
    apply Finset.sum_nonneg
    intro k _
    apply mul_nonneg (Nat.cast_nonneg _)
    apply pow_nonneg (by norm_num) _
  have htail_le : ((2 : ℝ) ^ (N + 1) -
        ∑ k ∈ Finset.range (K + 1),
          ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k) ≤
      (2 : ℝ) ^ (N + 1) := by
    linarith [hhead_nonneg]
  have hc_nonneg : (0 : ℝ) ≤ (2 * ‖w‖) ^ (K + 1) := by
    apply pow_nonneg
    apply mul_nonneg (by norm_num) (norm_nonneg _)
  have hg : HasSum
      (fun n : ℕ => ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
        (1 / 2 : ℝ) ^ (n + K + 1) * (2 * ‖w‖) ^ (K + 1))
      (((2 : ℝ) ^ (N + 1) -
        ∑ k ∈ Finset.range (K + 1),
          ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k) *
        (2 * ‖w‖) ^ (K + 1)) :=
    hFullTail.mul_right _
  have hle : ‖chap7R K r w‖ ≤
      (((2 : ℝ) ^ (N + 1) -
        ∑ k ∈ Finset.range (K + 1),
          ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k) *
        (2 * ‖w‖) ^ (K + 1)) := by
    apply hTail.norm_le_of_bounded hg
    intro n
    have hk : n + K + 1 = (K + 1) + n := by omega
    have hchoose : ‖Ring.choose r (n + K + 1)‖ ≤
        ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) :=
      chap7_choose_bound r N (n + K + 1) hr
    have hnorm : ‖Ring.choose r (n + K + 1) * w ^ (n + K + 1)‖ =
        ‖Ring.choose r (n + K + 1)‖ * ‖w‖ ^ (n + K + 1) := by
      rw [norm_mul, norm_pow]
    rw [hnorm]
    have ha0 : (0 : ℝ) ≤ 2 * ‖w‖ := mul_nonneg (by norm_num) (norm_nonneg _)
    have ha1 : 2 * ‖w‖ ≤ 1 := by linarith [hw]
    have hpow_le : (2 * ‖w‖) ^ (n + K + 1) ≤ (2 * ‖w‖) ^ (K + 1) := by
      rw [hk, pow_add]
      have hn1 : (2 * ‖w‖) ^ n ≤ 1 := pow_le_one₀ ha0 ha1
      have hpos : (0 : ℝ) ≤ (2 * ‖w‖) ^ (K + 1) := pow_nonneg ha0 _
      calc (2 * ‖w‖) ^ (K + 1) * (2 * ‖w‖) ^ n
          ≤ (2 * ‖w‖) ^ (K + 1) * 1 :=
            mul_le_mul_of_nonneg_left hn1 hpos
        _ = (2 * ‖w‖) ^ (K + 1) := mul_one _
    have hpow_eq : ‖w‖ ^ (n + K + 1) =
        (2 * ‖w‖) ^ (n + K + 1) * (1 / 2 : ℝ) ^ (n + K + 1) := by
      have hw_eq : ‖w‖ = (2 * ‖w‖) * (1 / 2 : ℝ) := by ring
      conv_lhs => rw [hw_eq, mul_pow]
    have hpow_bound : ‖w‖ ^ (n + K + 1) ≤
        (2 * ‖w‖) ^ (K + 1) * (1 / 2 : ℝ) ^ (n + K + 1) := by
      rw [hpow_eq]
      have h12 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (n + K + 1) :=
        pow_nonneg (by norm_num) _
      calc (2 * ‖w‖) ^ (n + K + 1) * (1 / 2 : ℝ) ^ (n + K + 1)
          ≤ (2 * ‖w‖) ^ (K + 1) * (1 / 2 : ℝ) ^ (n + K + 1) :=
            mul_le_mul_of_nonneg_right hpow_le h12
        _ = (2 * ‖w‖) ^ (K + 1) * (1 / 2 : ℝ) ^ (n + K + 1) := rfl
    have hch_nonneg : (0 : ℝ) ≤ ‖Ring.choose r (n + K + 1)‖ := norm_nonneg _
    have hch_le : ‖Ring.choose r (n + K + 1)‖ ≤
        ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) := hchoose
    have hpow_nonneg : (0 : ℝ) ≤ ‖w‖ ^ (n + K + 1) := pow_nonneg (norm_nonneg _) _
    have hmul1 : ‖Ring.choose r (n + K + 1)‖ * ‖w‖ ^ (n + K + 1) ≤
        ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
          ‖w‖ ^ (n + K + 1) :=
      mul_le_mul_of_nonneg_right hch_le hpow_nonneg
    have hchR_nonneg : (0 : ℝ) ≤
        ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) :=
      Nat.cast_nonneg _
    have hmul2 : ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
          ‖w‖ ^ (n + K + 1) ≤
        ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
          ((2 * ‖w‖) ^ (K + 1) * (1 / 2 : ℝ) ^ (n + K + 1)) :=
      mul_le_mul_of_nonneg_left hpow_bound hchR_nonneg
    calc ‖Ring.choose r (n + K + 1)‖ * ‖w‖ ^ (n + K + 1)
        ≤ ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
            ‖w‖ ^ (n + K + 1) := hmul1
      _ ≤ ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
            ((2 * ‖w‖) ^ (K + 1) * (1 / 2 : ℝ) ^ (n + K + 1)) := hmul2
      _ = ((((N + (n + K + 1)).choose (n + K + 1) : ℕ)) : ℝ) *
            (1 / 2 : ℝ) ^ (n + K + 1) * (2 * ‖w‖) ^ (K + 1) := by ring
  calc ‖chap7R K r w‖
      ≤ (((2 : ℝ) ^ (N + 1) -
          ∑ k ∈ Finset.range (K + 1),
            ((((N + k).choose k : ℕ)) : ℝ) * (1 / 2 : ℝ) ^ k) *
          (2 * ‖w‖) ^ (K + 1)) := hle
    _ ≤ (2 : ℝ) ^ (N + 1) * (2 * ‖w‖) ^ (K + 1) :=
        mul_le_mul_of_nonneg_right htail_le hc_nonneg

private lemma chap7_choose_differentiable (k : ℕ) :
    Differentiable ℂ (fun r : ℂ => Ring.choose r k) := by
  have heq : (fun r : ℂ => Ring.choose r k) =
      (fun r : ℂ => ∏ i ∈ Finset.range k, ((r - (i : ℂ)) / ((i : ℂ) + 1))) := by
    funext r
    exact chap7_choose_eq_prod r k
  rw [heq]
  apply Differentiable.fun_finsetProd
  intro i _
  apply Differentiable.div_const
  apply Differentiable.sub differentiable_id (differentiable_const _)

private lemma chap7R_differentiable (K : ℕ) (w : ℂ) (hw0 : (1 : ℂ) + w ≠ 0) :
    Differentiable ℂ (fun r : ℂ => chap7R K r w) := by
  unfold chap7R
  apply Differentiable.sub
  · exact differentiable_id.const_cpow (Or.inl hw0)
  · apply Differentiable.fun_sum
    intro k _
    apply Differentiable.mul
    · exact chap7_choose_differentiable k
    · exact differentiable_const _

private def chap7g (K J : ℕ) (x : ℂ) (n : ℕ) (r : ℂ) : ℂ :=
  -((((n + J : ℕ) : ℂ) + 1) ^ r * chap7R K r (chap7W x (n + J)))

private lemma chap7g_differentiable (K J : ℕ) (x : ℂ)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2) (n : ℕ) :
    Differentiable ℂ (fun r : ℂ => chap7g K J x n r) := by
  unfold chap7g
  have hbase : (((n + J : ℕ) : ℂ) + 1) ≠ 0 := chap7_base_ne_zero (n + J)
  have hw : ‖chap7W x (n + J)‖ ≤ 1 / 2 := hJ (n + J) (Nat.le_add_left J n)
  have h1w : (1 : ℂ) + chap7W x (n + J) ≠ 0 := chap7_one_add_w_ne_zero hw
  apply Differentiable.neg
  apply Differentiable.mul
  · exact differentiable_id.const_cpow (Or.inl hbase)
  · exact chap7R_differentiable K _ h1w

private lemma chap7g_norm (K J : ℕ) (x : ℂ) (n : ℕ) (r : ℂ) :
    ‖chap7g K J x n r‖ =
      ‖(((n + J : ℕ) : ℂ) + 1) ^ r‖ * ‖chap7R K r (chap7W x (n + J))‖ := by
  unfold chap7g
  rw [norm_neg, norm_mul]

private lemma chap7_base_cpow_norm (j : ℕ) (r : ℂ) :
    ‖(((j : ℕ) : ℂ) + 1) ^ r‖ = ((((j + 1 : ℕ)) : ℝ)) ^ (r.re) := by
  have heq : (((j : ℕ) : ℂ) + 1) = (((j + 1 : ℕ)) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_natCast_cpow_of_pos (Nat.succ_pos j) r]

private lemma chap7W_norm (x : ℂ) (j : ℕ) :
    ‖chap7W x j‖ = ‖x‖ / ((((j + 1 : ℕ)) : ℝ)) := by
  unfold chap7W
  rw [norm_div, chap7_base_norm]

private lemma chap7g_bound (m N K J : ℕ) (x : ℂ) (hK : K = m + 2)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2) (n : ℕ) (r : ℂ)
    (hrU : r.re < ((((m + 1 : ℕ))) : ℝ)) (hrN : ‖r‖ < (N : ℝ)) :
    ‖chap7g K J x n r‖ ≤
      (2 : ℝ) ^ (N + 1) * (2 * ‖x‖) ^ (K + 1) *
        (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2) := by
  have hj : J ≤ n + J := Nat.le_add_left J n
  have hw : ‖chap7W x (n + J)‖ ≤ 1 / 2 := hJ (n + J) hj
  have hrN' : ‖r‖ ≤ (N : ℝ) := le_of_lt hrN
  have hR : ‖chap7R K r (chap7W x (n + J))‖ ≤
      (2 : ℝ) ^ (N + 1) * (2 * ‖chap7W x (n + J)‖) ^ (K + 1) :=
    chap7R_bound r (chap7W x (n + J)) N K hrN' hw
  have hbase : ‖(((n + J : ℕ) : ℂ) + 1) ^ r‖ =
      ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) := chap7_base_cpow_norm (n + J) r
  have hW : ‖chap7W x (n + J)‖ = ‖x‖ / ((((n + J + 1 : ℕ))) : ℝ) :=
    chap7W_norm x (n + J)
  have hpos : (0 : ℝ) < ((((n + J + 1 : ℕ))) : ℝ) := by
    exact_mod_cast Nat.succ_pos (n + J)
  have hge1 : (1 : ℝ) ≤ ((((n + J + 1 : ℕ))) : ℝ) := by
    have h1 : 1 ≤ n + J + 1 := Nat.succ_le_succ (Nat.zero_le _)
    exact_mod_cast h1
  have h2w : 2 * ‖chap7W x (n + J)‖ =
      (2 * ‖x‖) / ((((n + J + 1 : ℕ))) : ℝ) := by
    rw [hW]
    ring
  have h2w_pow : (2 * ‖chap7W x (n + J)‖) ^ (K + 1) =
      (2 * ‖x‖) ^ (K + 1) / ((((n + J + 1 : ℕ))) : ℝ) ^ (K + 1) := by
    rw [h2w, div_pow]
  have hrpow : ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) *
        (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ (K + 1)) =
      ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re - ((K + 1 : ℕ) : ℝ)) := by
    have h1 : ((((n + J + 1 : ℕ))) : ℝ) ^ (K + 1) =
        ((((n + J + 1 : ℕ))) : ℝ) ^ (((K + 1 : ℕ) : ℝ)) := by
      rw [Real.rpow_natCast]
    rw [h1, one_div, ← div_eq_mul_inv, ← Real.rpow_sub hpos]
  have hexp : r.re - ((K + 1 : ℕ) : ℝ) ≤ (-2 : ℝ) := by
    have hK1 : ((K + 1 : ℕ) : ℝ) = (m : ℝ) + 3 := by
      rw [hK]
      push_cast
      ring
    have hm1 : ((((m + 1 : ℕ))) : ℝ) = (m : ℝ) + 1 := by
      push_cast
      ring
    rw [hK1]
    rw [hm1] at hrU
    linarith
  have hrpow_le : ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re - ((K + 1 : ℕ) : ℝ)) ≤
      ((((n + J + 1 : ℕ))) : ℝ) ^ ((-2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hge1 hexp
  have hrpow_neg : ((((n + J + 1 : ℕ))) : ℝ) ^ ((-2 : ℝ)) =
      1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2 := by
    have h2 : ((-2 : ℝ)) = -(2 : ℝ) := by ring
    rw [h2, Real.rpow_neg hpos.le]
    have hr2 : ((((n + J + 1 : ℕ))) : ℝ) ^ (2 : ℝ) =
        ((((n + J + 1 : ℕ))) : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hr2, inv_eq_one_div]
  have hmain : ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) *
        ((2 * ‖chap7W x (n + J)‖) ^ (K + 1)) ≤
      (2 * ‖x‖) ^ (K + 1) * (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2) := by
    rw [h2w_pow]
    have hpos2 : (0 : ℝ) ≤ (2 * ‖x‖) ^ (K + 1) := pow_nonneg
      (mul_nonneg (by norm_num) (norm_nonneg _)) _
    calc ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) *
            ((2 * ‖x‖) ^ (K + 1) / ((((n + J + 1 : ℕ))) : ℝ) ^ (K + 1))
          = (2 * ‖x‖) ^ (K + 1) *
              (((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) *
                (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ (K + 1))) := by
            rw [div_eq_mul_inv, one_div]
            ring
        _ = (2 * ‖x‖) ^ (K + 1) *
              (((((n + J + 1 : ℕ))) : ℝ) ^ (r.re - ((K + 1 : ℕ) : ℝ))) := by
            rw [hrpow]
        _ ≤ (2 * ‖x‖) ^ (K + 1) *
              (((((n + J + 1 : ℕ))) : ℝ) ^ ((-2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hrpow_le hpos2
        _ = (2 * ‖x‖) ^ (K + 1) * (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2) := by
            rw [hrpow_neg]
  rw [chap7g_norm, hbase]
  calc ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) *
          ‖chap7R K r (chap7W x (n + J))‖
        ≤ ((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) *
            ((2 : ℝ) ^ (N + 1) * (2 * ‖chap7W x (n + J)‖) ^ (K + 1)) := by
          apply mul_le_mul_of_nonneg_left hR
          apply Real.rpow_pos_of_pos hpos _ |>.le
      _ = (2 : ℝ) ^ (N + 1) *
            (((((n + J + 1 : ℕ))) : ℝ) ^ (r.re) *
              (2 * ‖chap7W x (n + J)‖) ^ (K + 1)) := by ring
      _ ≤ (2 : ℝ) ^ (N + 1) *
            ((2 * ‖x‖) ^ (K + 1) * (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left hmain
          apply pow_nonneg (by norm_num) _
      _ = (2 : ℝ) ^ (N + 1) * (2 * ‖x‖) ^ (K + 1) *
            (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2) := by ring

private def chap7U (m : ℕ) : Set ℂ := {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ)}

private def chap7S (m N : ℕ) : Set ℂ :=
  {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ) ∧ ‖r‖ < (N : ℝ)}

private lemma chap7U_open (m : ℕ) : IsOpen (chap7U m) := by
  unfold chap7U
  exact Complex.continuous_re.isOpen_preimage _ isOpen_Iio

private lemma chap7S_open (m N : ℕ) : IsOpen (chap7S m N) := by
  unfold chap7S
  have h1 : IsOpen {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ)} :=
    Complex.continuous_re.isOpen_preimage _ isOpen_Iio
  have h2 : IsOpen {r : ℂ | ‖r‖ < (N : ℝ)} := isOpen_lt continuous_norm continuous_const
  have heq : {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ) ∧ ‖r‖ < (N : ℝ)} =
      {r : ℂ | r.re < ((((m + 1 : ℕ))) : ℝ)} ∩ {r : ℂ | ‖r‖ < (N : ℝ)} := rfl
  rw [heq]
  exact h1.inter h2

private lemma chap7S_subset_U (m N : ℕ) : chap7S m N ⊆ chap7U m := by
  intro r hr
  exact hr.1

private def chap7G (K J : ℕ) (x : ℂ) (r : ℂ) : ℂ :=
  ∑' n : ℕ, chap7g K J x n r

private lemma chap7_bound_summable (J : ℕ) (C : ℝ) :
    Summable (fun n : ℕ => C * (1 / (((n + J + 1 : ℕ) : ℝ) ^ 2))) := by
  have h2' : Summable (fun n : ℕ => (1 / ((n : ℝ) ^ 2) : ℝ)) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 / (((n + (J + 1) : ℕ) : ℝ) ^ 2) : ℝ)) :=
    (summable_nat_add_iff
      (f := fun m : ℕ => (1 / ((m : ℝ) ^ 2) : ℝ)) (J + 1)).mpr h2'
  have hcongr : (fun n : ℕ => (1 / (((n + (J + 1) : ℕ) : ℝ) ^ 2) : ℝ)) =
      (fun n : ℕ => (1 / (((n + J + 1 : ℕ) : ℝ) ^ 2) : ℝ)) := rfl
  rw [hcongr] at hshift
  exact hshift.mul_left C

private lemma chap7G_differentiableOn_S (m N K J : ℕ) (x : ℂ) (hK : K = m + 2)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2) :
    DifferentiableOn ℂ (fun r : ℂ => ∑' n : ℕ, chap7g K J x n r)
      (chap7S m N) := by
  have hu : Summable
      (fun n : ℕ => (2 : ℝ) ^ (N + 1) * (2 * ‖x‖) ^ (K + 1) *
        (1 / (((n + J + 1 : ℕ) : ℝ) ^ 2))) :=
    chap7_bound_summable J _
  have hf : ∀ n : ℕ, DifferentiableOn ℂ (fun r : ℂ => chap7g K J x n r)
      (chap7S m N) := fun n =>
    (chap7g_differentiable K J x hJ n).differentiableOn
  have hU : IsOpen (chap7S m N) := chap7S_open m N
  have hF_le : ∀ n : ℕ, ∀ r : ℂ, r ∈ chap7S m N →
      ‖chap7g K J x n r‖ ≤
        (2 : ℝ) ^ (N + 1) * (2 * ‖x‖) ^ (K + 1) *
          (1 / (((n + J + 1 : ℕ) : ℝ) ^ 2)) := by
    intro n r hr
    have hrU : r.re < ((((m + 1 : ℕ))) : ℝ) := hr.1
    have hrN : ‖r‖ < (N : ℝ) := hr.2
    have hle := chap7g_bound m N K J x hK hJ n r hrU hrN
    simpa [mul_assoc] using hle
  exact Complex.differentiableOn_tsum_of_summable_norm hu hf hU hF_le

private lemma chap7G_differentiableOn_U (m K J : ℕ) (x : ℂ) (hK : K = m + 2)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2) :
    DifferentiableOn ℂ (fun r : ℂ => ∑' n : ℕ, chap7g K J x n r)
      (chap7U m) := by
  intro r hr
  obtain ⟨N, hN⟩ := exists_nat_gt ‖r‖
  have hrS : r ∈ chap7S m N := ⟨hr, hN⟩
  have hdiffS := chap7G_differentiableOn_S m N K J x hK hJ
  have hopen := chap7S_open m N
  have hmem : chap7S m N ∈ nhds r := hopen.mem_nhds hrS
  have hAt : DifferentiableAt ℂ (fun r : ℂ => ∑' n : ℕ, chap7g K J x n r) r :=
    hdiffS.differentiableAt hmem
  exact hAt.differentiableWithinAt

private def chap7E : ℂ → ℂ :=
  Function.update (fun s : ℂ => (s - 1) * riemannZeta s) 1 1

private lemma chap7E_differentiableAt_of_ne {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ chap7E s := by
  apply DifferentiableAt.congr_of_eventuallyEq
  · have h1 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s :=
      differentiableAt_id.sub (differentiableAt_const 1)
    have h2 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
    exact h1.mul h2
  · filter_upwards [eventually_ne_nhds hs] with t ht using
      Function.update_of_ne ht _ _

private lemma chap7E_continuousAt_one : ContinuousAt chap7E 1 := by
  have h : Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ)
      (nhds 1) := riemannZeta_residue_one
  simpa [chap7E, continuousAt_update_same] using h

private lemma chap7E_differentiable : Differentiable ℂ chap7E := by
  intro s
  rcases ne_or_eq s 1 with hs | rfl
  · exact chap7E_differentiableAt_of_ne hs
  · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      ?_ chap7E_continuousAt_one).differentiableAt
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact chap7E_differentiableAt_of_ne ht

private lemma chap7E_one : chap7E 1 = 1 := by
  simp [chap7E]

private lemma chap7E_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    chap7E s = (s - 1) * riemannZeta s := by
  simp [chap7E, Function.update_of_ne hs]

private def chap7P (k : ℕ) (r : ℂ) : ℂ :=
  ∏ i ∈ Finset.range (k - 1), (r - (i : ℂ))

private lemma chap7P_differentiable (k : ℕ) :
    Differentiable ℂ (fun r : ℂ => chap7P k r) := by
  unfold chap7P
  apply Differentiable.fun_finsetProd
  intro i _
  exact Differentiable.sub differentiable_id (differentiable_const _)

private lemma chap7_choose_eq_P (r : ℂ) (k : ℕ) (hk : 1 ≤ k) :
    Ring.choose r k = (r - ((k - 1 : ℕ) : ℂ)) * chap7P k r / ((k ! : ℕ) : ℂ) := by
  have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  have hdesc : (descPochhammer ℤ k).smeval r =
      (descPochhammer ℤ (k - 1)).smeval r * (r - ((k - 1 : ℕ) : ℂ)) := by
    conv_lhs => rw [← hk1, descPochhammer_succ_right]
    rw [Polynomial.smeval_mul]
    congr 1
    have hX : (Polynomial.X : ℤ[X]).smeval r = r ^ 1 := by simp
    have hN : (((k - 1 : ℕ) : ℤ[X])).smeval r = (((k - 1 : ℕ)) : ℂ) := by
      rw [Polynomial.smeval_natCast]
      simp [pow_zero, nsmul_eq_mul]
    have hsub : ((Polynomial.X - ((k - 1 : ℕ) : ℤ[X]) : ℤ[X])).smeval r =
        (Polynomial.X : ℤ[X]).smeval r - ((((k - 1 : ℕ)) : ℤ[X])).smeval r := by
      rw [Polynomial.smeval_sub]
    rw [hsub, hX, hN, pow_one]
  have hchoose : Ring.choose r k =
      ((k ! : ℂ))⁻¹ * (descPochhammer ℤ k).smeval r := by
    rw [Ring.choose_eq_smul, smul_eq_mul]
  have hP : (descPochhammer ℤ (k - 1)).smeval r = chap7P k r := by
    rw [chap7_descPochhammer_smeval_eq_prod]
    rfl
  rw [hchoose, hdesc, hP]
  ring

private def chap7H (J : ℕ) (s : ℂ) : ℂ :=
  ∑ j ∈ Finset.range J, ((((j : ℕ) : ℂ) + 1) ^ (-s))

private lemma chap7HKR_differentiable (J k : ℕ) :
    Differentiable ℂ (fun r : ℂ => chap7H J (((k : ℕ) : ℂ) - r)) := by
  unfold chap7H
  apply Differentiable.fun_sum
  intro j _
  have hbase : (((j : ℕ) : ℂ) + 1) ≠ 0 := chap7_base_ne_zero j
  have hf : Differentiable ℂ (fun r : ℂ => -(((k : ℕ) : ℂ) - r)) :=
    Differentiable.neg (Differentiable.sub (differentiable_const _) differentiable_id)
  have h := hf.const_cpow (c := (((j : ℕ) : ℂ) + 1)) (Or.inl hbase)
  simpa using h

private def chap7T (x : ℂ) (j : ℕ) (r : ℂ) : ℂ :=
  ((((j : ℕ) : ℂ) + 1) ^ r - ((((j : ℕ) : ℂ) + 1 + x) ^ r))

private lemma chap7T_differentiable (x : ℂ) (hx : chapter7Admissible x) (j : ℕ) :
    Differentiable ℂ (fun r : ℂ => chap7T x j r) := by
  unfold chap7T
  have h1 : (((j : ℕ) : ℂ) + 1) ≠ 0 := chap7_base_ne_zero j
  have h2 : (((j : ℕ) : ℂ) + 1 + x) ≠ 0 := hx j
  apply Differentiable.sub
  · exact differentiable_id.const_cpow (Or.inl h1)
  · exact differentiable_id.const_cpow (Or.inl h2)

private lemma chap7PE_differentiable (k : ℕ) :
    Differentiable ℂ (fun r : ℂ =>
      chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ)) := by
  have hP := chap7P_differentiable k
  have hE : Differentiable ℂ (fun r : ℂ => chap7E (((k : ℕ) : ℂ) - r)) :=
    chap7E_differentiable.comp
      (Differentiable.sub (differentiable_const _) differentiable_id)
  have hmul := hP.mul hE
  exact hmul.div_const _

private lemma chap7CH_differentiable (J k : ℕ) :
    Differentiable ℂ (fun r : ℂ =>
      Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r)) := by
  apply Differentiable.mul
  · exact chap7_choose_differentiable k
  · exact chap7HKR_differentiable J k

private def chap7PhiCont (K J : ℕ) (x : ℂ) (r : ℂ) : ℂ :=
  (∑ j ∈ Finset.range J, chap7T x j r) +
    (∑' n : ℕ, chap7g K J x n r) +
    ∑ k ∈ Finset.Icc 1 K,
      x ^ k * (chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
        Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r))

private lemma chap7PhiCont_differentiableOn (m K J : ℕ) (x : ℂ)
    (hx : chapter7Admissible x) (hK : K = m + 2)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2) :
    DifferentiableOn ℂ (fun r : ℂ => chap7PhiCont K J x r) (chap7U m) := by
  have hS1 : DifferentiableOn ℂ
      (fun r : ℂ => ∑ j ∈ Finset.range J, chap7T x j r) (chap7U m) := by
    have hent : Differentiable ℂ (fun r : ℂ => ∑ j ∈ Finset.range J, chap7T x j r) := by
      apply Differentiable.fun_sum
      intro j _
      exact chap7T_differentiable x hx j
    exact hent.differentiableOn
  have hG : DifferentiableOn ℂ (fun r : ℂ => ∑' n : ℕ, chap7g K J x n r)
      (chap7U m) :=
    chap7G_differentiableOn_U m K J x hK hJ
  have hS3 : DifferentiableOn ℂ
      (fun r : ℂ => ∑ k ∈ Finset.Icc 1 K,
        x ^ k * (chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
          Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r)))
      (chap7U m) := by
    have hent : Differentiable ℂ
        (fun r : ℂ => ∑ k ∈ Finset.Icc 1 K,
          x ^ k * (chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
            Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r))) := by
      apply Differentiable.fun_sum
      intro k _
      have hPE := chap7PE_differentiable k
      have hCH := chap7CH_differentiable J k
      have hadd := hPE.add hCH
      exact (differentiable_const (x ^ k)).mul hadd
    exact hent.differentiableOn
  have h12 := hS1.add hG
  have h123 := h12.add hS3
  refine h123.congr (fun x _ => ?_)
  simp [chap7PhiCont]

private lemma chap7_cpow_base_w_pow (j : ℕ) (x r : ℂ) (k : ℕ) :
    ((((j : ℕ) : ℂ) + 1) ^ r) * (chap7W x j) ^ k =
      x ^ k * (((((j : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
  have hbase : (((j : ℕ) : ℂ) + 1) ≠ 0 := chap7_base_ne_zero j
  unfold chap7W
  have hdiv : (x / ((((j : ℕ) : ℂ) + 1))) ^ k =
      x ^ k / ((((j : ℕ) : ℂ) + 1) ^ k) := div_pow x _ k
  rw [hdiv]
  have hcpow_nat : ((((j : ℕ) : ℂ) + 1) ^ (k : ℂ)) =
      ((((j : ℕ) : ℂ) + 1) ^ k) := Complex.cpow_natCast _ k
  have hr_eq : r = (k : ℂ) + (r - (k : ℂ)) := by ring
  have hcpow_add : ((((j : ℕ) : ℂ) + 1) ^ r) =
      ((((j : ℕ) : ℂ) + 1) ^ (k : ℂ)) *
        ((((j : ℕ) : ℂ) + 1) ^ (r - (k : ℂ))) := by
    conv_lhs => rw [hr_eq]
    rw [Complex.cpow_add _ _ hbase]
  rw [hcpow_add, hcpow_nat]
  have hpow_ne : ((((j : ℕ) : ℂ) + 1) ^ k) ≠ 0 := pow_ne_zero k hbase
  field_simp

private lemma chap7_range_split (K : ℕ) :
    Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
  ext a
  simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
  omega

private lemma chap7_zero_not_mem_Icc (K : ℕ) : 0 ∉ Finset.Icc 1 K := by
  simp

private lemma chap7_sum_range_eq (K : ℕ) (r w : ℂ) :
    (∑ k ∈ Finset.range (K + 1), Ring.choose r k * w ^ k) =
      1 + ∑ k ∈ Finset.Icc 1 K, Ring.choose r k * w ^ k := by
  rw [chap7_range_split K, Finset.sum_insert (chap7_zero_not_mem_Icc K)]
  have h0 : Ring.choose r 0 * w ^ (0 : ℕ) = 1 := by
    rw [Ring.choose_zero_right, pow_zero, mul_one]
  rw [h0]

private lemma chap7T_eq (K J : ℕ) (x : ℂ) (n : ℕ) (r : ℂ)
    (hw : ‖chap7W x (n + J)‖ ≤ 1 / 2) :
    chap7T x (n + J) r = chap7g K J x n r -
      ∑ k ∈ Finset.Icc 1 K,
        Ring.choose r k * x ^ k *
          (((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
  have hfact := chap7_factor (x := x) (j := n + J) r hw
  have hR_eq : ((1 : ℂ) + chap7W x (n + J)) ^ r =
      (∑ k ∈ Finset.range (K + 1), Ring.choose r k * (chap7W x (n + J)) ^ k) +
        chap7R K r (chap7W x (n + J)) := by
    unfold chap7R
    ring
  have hsum := chap7_sum_range_eq K r (chap7W x (n + J))
  have hT : chap7T x (n + J) r =
      ((((n + J : ℕ) : ℂ) + 1) ^ r) -
        ((((n + J : ℕ) : ℂ) + 1) ^ r) *
          ((1 : ℂ) + chap7W x (n + J)) ^ r := by
    unfold chap7T
    rw [hfact]
  have hg : chap7g K J x n r =
      -((((n + J : ℕ) : ℂ) + 1) ^ r * chap7R K r (chap7W x (n + J))) := rfl
  have hdist : ∀ k ∈ Finset.Icc 1 K,
      ((((n + J : ℕ) : ℂ) + 1) ^ r) * (Ring.choose r k * (chap7W x (n + J)) ^ k) =
        Ring.choose r k * x ^ k *
          (((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
    intro k _
    have h1 := chap7_cpow_base_w_pow (n + J) x r k
    calc ((((n + J : ℕ) : ℂ) + 1) ^ r) * (Ring.choose r k * (chap7W x (n + J)) ^ k)
        = Ring.choose r k * (((((n + J : ℕ) : ℂ) + 1) ^ r) * (chap7W x (n + J)) ^ k) := by
          ring
      _ = Ring.choose r k * (x ^ k * (((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ))))) := by
          rw [h1]
      _ = Ring.choose r k * x ^ k * (((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
          ring
  have hsum_dist : ((((n + J : ℕ) : ℂ) + 1) ^ r) *
        (∑ k ∈ Finset.Icc 1 K, Ring.choose r k * (chap7W x (n + J)) ^ k) =
      ∑ k ∈ Finset.Icc 1 K,
        Ring.choose r k * x ^ k *
          (((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    exact hdist k hk
  have hbase_mul : ((((n + J : ℕ) : ℂ) + 1) ^ r) *
        (1 + ∑ k ∈ Finset.Icc 1 K, Ring.choose r k * (chap7W x (n + J)) ^ k +
          chap7R K r (chap7W x (n + J))) =
      ((((n + J : ℕ) : ℂ) + 1) ^ r) +
        ((((n + J : ℕ) : ℂ) + 1) ^ r) *
          (∑ k ∈ Finset.Icc 1 K, Ring.choose r k * (chap7W x (n + J)) ^ k) +
        ((((n + J : ℕ) : ℂ) + 1) ^ r) * chap7R K r (chap7W x (n + J)) := by
    ring
  calc chap7T x (n + J) r
      = ((((n + J : ℕ) : ℂ) + 1) ^ r) -
          ((((n + J : ℕ) : ℂ) + 1) ^ r) *
            (1 + ∑ k ∈ Finset.Icc 1 K, Ring.choose r k * (chap7W x (n + J)) ^ k +
              chap7R K r (chap7W x (n + J))) := by
        rw [hT]
        congr 1
        congr 1
        rw [hR_eq, hsum]
    _ = -((((n + J : ℕ) : ℂ) + 1) ^ r * chap7R K r (chap7W x (n + J))) -
          ∑ k ∈ Finset.Icc 1 K,
            Ring.choose r k * x ^ k *
              (((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
        rw [hbase_mul, hsum_dist]
        ring
    _ = chap7g K J x n r -
          ∑ k ∈ Finset.Icc 1 K,
            Ring.choose r k * x ^ k *
              (((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
        rw [hg]

private lemma chap7_neg_zeta_eq (r : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (hr : r ≠ (((k - 1 : ℕ)) : ℂ)) :
    -(Ring.choose r k) * riemannZeta (((k : ℕ) : ℂ) - r) =
      chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) := by
  have hs : (((k : ℕ) : ℂ) - r) ≠ 1 := by
    intro hcon
    apply hr
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have heq : (((k : ℕ) : ℂ)) = ((((k - 1 : ℕ)) : ℂ)) + 1 := by
      conv_lhs => rw [← hk1]
      push_cast
      ring
    have h1 : (((k : ℕ) : ℂ) - r) = 1 := hcon
    rw [heq] at h1
    have h2 : ((((k - 1 : ℕ)) : ℂ)) - r = 0 := by
      have h3 : ((((k - 1 : ℕ)) : ℂ)) - r =
          ((((k - 1 : ℕ)) : ℂ) + 1 - r) - 1 := by ring
      rw [h3, h1, sub_self]
    have : r = ((((k - 1 : ℕ)) : ℂ)) := (sub_eq_zero.mp h2).symm
    exact this
  have hE := chap7E_eq_of_ne hs
  have hC := chap7_choose_eq_P r k hk
  have hsub : ((((k : ℕ) : ℂ) - r - 1)) = -((r - (((k - 1 : ℕ)) : ℂ))) := by
    have hk1 : k - 1 + 1 = k := Nat.sub_add_cancel hk
    have heq : (((k : ℕ) : ℂ)) = ((((k - 1 : ℕ)) : ℂ)) + 1 := by
      conv_lhs => rw [← hk1]
      push_cast
      ring
    rw [heq]
    ring
  rw [hE, hC]
  rw [hsub]
  ring

private lemma chap7T_eq_term (x r : ℂ) (j : ℕ) :
    chap7T x j r = chapter7PowerDifferenceTerm r x j := rfl

private lemma chap7_cpow_neg_one_div (b s : ℂ) :
    b ^ (-s) = 1 / b ^ s := by
  rw [Complex.cpow_neg, one_div]

private lemma chap7_zeta_summable {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / ((((n : ℕ) : ℂ) + 1) ^ s)) := by
  have h0 : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ s)) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have h1 : Summable (fun n : ℕ => 1 / ((((n + 1 : ℕ)) : ℂ) ^ s)) :=
    (summable_nat_add_iff 1).mpr h0
  have hcongr : (fun n : ℕ => 1 / ((((n + 1 : ℕ)) : ℂ) ^ s)) =
      (fun n : ℕ => 1 / ((((n : ℕ) : ℂ) + 1) ^ s)) := by
    funext n
    congr 1
    congr 1
    push_cast
    ring
  rwa [hcongr] at h1

private lemma chap7_zeta_tsum {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, 1 / ((((n : ℕ) : ℂ) + 1) ^ s)) = riemannZeta s := by
  have hz := zeta_eq_tsum_one_div_nat_add_one_cpow hs
  have hcongr : (fun n : ℕ => 1 / (((n + 1 : ℂ)) ^ s)) =
      (fun n : ℕ => 1 / ((((n : ℕ) : ℂ) + 1) ^ s)) := rfl
  rw [hcongr] at hz
  exact hz.symm

private lemma chap7_H_eq_one_div (J : ℕ) (s : ℂ) :
    chap7H J s = ∑ j ∈ Finset.range J, 1 / ((((j : ℕ) : ℂ) + 1) ^ s) := by
  unfold chap7H
  apply Finset.sum_congr rfl
  intro j _
  exact chap7_cpow_neg_one_div _ _

private lemma chap7_tail_summable (J : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun n : ℕ => 1 / (((((n + J : ℕ) : ℂ) + 1) ^ s))) := by
  have h := chap7_zeta_summable hs
  have h2 := (summable_nat_add_iff J).mpr h
  simpa only [Function.comp_def] using h2

private lemma chap7_tail_tsum (J : ℕ) {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, 1 / (((((n + J : ℕ) : ℂ) + 1) ^ s))) =
      riemannZeta s - ∑ j ∈ Finset.range J, 1 / ((((j : ℕ) : ℂ) + 1) ^ s) := by
  have hsum := chap7_zeta_summable hs
  have htsum := chap7_zeta_tsum hs
  have hsplit := Summable.sum_add_tsum_nat_add J hsum
  rw [htsum] at hsplit
  have htail_eq : (∑' n : ℕ, 1 / (((((n + J : ℕ) : ℂ) + 1) ^ s))) =
      ∑' n : ℕ, (fun m : ℕ => 1 / ((((m : ℕ) : ℂ) + 1) ^ s)) (n + J) := rfl
  rw [htail_eq]
  linear_combination hsplit

private lemma chap7_base_pow_eq_one_div (j J : ℕ) (r : ℂ) (k : ℕ) :
    ((((j + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ))) =
      1 / (((((j + J : ℕ) : ℂ) + 1) ^ (((k : ℕ) : ℂ) - r))) := by
  have hneg : r - (k : ℂ) = -(((k : ℕ) : ℂ) - r) := by ring
  rw [hneg, chap7_cpow_neg_one_div]

private lemma chap7_g_summable (m N K J : ℕ) (x r : ℂ) (hK : K = m + 2)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2)
    (hrU : r.re < ((((m + 1 : ℕ))) : ℝ)) (hrN : ‖r‖ < (N : ℝ)) :
    Summable (fun n : ℕ => chap7g K J x n r) := by
  have hbound : ∀ n : ℕ, ‖chap7g K J x n r‖ ≤
      (2 : ℝ) ^ (N + 1) * (2 * ‖x‖) ^ (K + 1) *
        (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2) :=
    fun n => chap7g_bound m N K J x hK hJ n r hrU hrN
  have hsum : Summable (fun n : ℕ =>
      (2 : ℝ) ^ (N + 1) * (2 * ‖x‖) ^ (K + 1) *
        (1 / ((((n + J + 1 : ℕ))) : ℝ) ^ 2)) :=
    chap7_bound_summable J _
  exact Summable.of_norm_bounded hsum hbound

private lemma chap7_inner_summable (J : ℕ) (r : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : r.re < 0) :
    Summable (fun n : ℕ => ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
  have hs : 1 < ((((k : ℕ) : ℂ) - r).re) := by
    have hre : ((((k : ℕ) : ℂ) - r).re) = ((k : ℝ)) - r.re := by
      simp [Complex.sub_re]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [hr0]
  have hsum := chap7_tail_summable J hs
  have hcongr : (fun n : ℕ => 1 / (((((n + J : ℕ) : ℂ) + 1) ^ (((k : ℕ) : ℂ) - r)))) =
      (fun n : ℕ => ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
    funext n
    exact (chap7_base_pow_eq_one_div n J r k).symm
  rwa [hcongr] at hsum

private lemma chap7_inner_mul_summable (J : ℕ) (r x : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : r.re < 0) :
    Summable (fun n : ℕ => Ring.choose r k * x ^ k *
      ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
  have h := chap7_inner_summable J r k hk hr0
  exact h.mul_left (Ring.choose r k * x ^ k)

private lemma chap7_finite_inner_summable (J K : ℕ) (r x : ℂ) (hr0 : r.re < 0) :
    Summable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 K,
      Ring.choose r k * x ^ k *
        ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
  apply summable_sum
  intro k hk
  simp only [Finset.mem_Icc] at hk
  exact chap7_inner_mul_summable J r x k hk.1 hr0

private lemma chap7_inner_tsum (J : ℕ) (r : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : r.re < 0) :
    (∑' n : ℕ, ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) =
      riemannZeta (((k : ℕ) : ℂ) - r) - chap7H J (((k : ℕ) : ℂ) - r) := by
  have hs : 1 < ((((k : ℕ) : ℂ) - r).re) := by
    have hre : ((((k : ℕ) : ℂ) - r).re) = ((k : ℝ)) - r.re := by
      simp [Complex.sub_re]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith [hr0]
  have h1 : (∑' n : ℕ, ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) =
      ∑' n : ℕ, 1 / (((((n + J : ℕ) : ℂ) + 1) ^ (((k : ℕ) : ℂ) - r))) := by
    apply tsum_congr
    intro n
    exact chap7_base_pow_eq_one_div n J r k
  rw [h1, chap7_tail_tsum J hs, chap7_H_eq_one_div]

private lemma chap7_inner_mul_tsum (J : ℕ) (r x : ℂ) (k : ℕ) (hk : 1 ≤ k)
    (hr0 : r.re < 0) :
    (∑' n : ℕ, Ring.choose r k * x ^ k *
        ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) =
      Ring.choose r k * x ^ k *
        (riemannZeta (((k : ℕ) : ℂ) - r) - chap7H J (((k : ℕ) : ℂ) - r)) := by
  have hsum := chap7_inner_summable J r k hk hr0
  have htsum := chap7_inner_tsum J r k hk hr0
  have hmul := hsum.tsum_mul_left (Ring.choose r k * x ^ k)
  have heq : (fun n : ℕ => Ring.choose r k * x ^ k *
      ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) =
      (fun n : ℕ => (Ring.choose r k * x ^ k) *
        ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := rfl
  rw [heq, hmul, htsum]

private lemma chap7_finite_inner_tsum (J K : ℕ) (r x : ℂ) (hr0 : r.re < 0) :
    (∑' n : ℕ, ∑ k ∈ Finset.Icc 1 K, Ring.choose r k * x ^ k *
        ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) =
      ∑ k ∈ Finset.Icc 1 K, Ring.choose r k * x ^ k *
        (riemannZeta (((k : ℕ) : ℂ) - r) - chap7H J (((k : ℕ) : ℂ) - r)) := by
  have hf : ∀ k ∈ Finset.Icc 1 K, Summable (fun n : ℕ =>
      Ring.choose r k * x ^ k *
        ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    exact chap7_inner_mul_summable J r x k hk.1 hr0
  have hswap := Summable.tsum_finsetSum hf
  rw [hswap]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  exact chap7_inner_mul_tsum J r x k hk.1 hr0

private lemma chap7_ne_of_re_neg (r : ℂ) (k : ℕ) (hr0 : r.re < 0) :
    r ≠ ((((k - 1 : ℕ))) : ℂ) := by
  intro hcon
  have h1 : r.re = ((((k - 1 : ℕ))) : ℝ) := by
    rw [hcon]
    simp
  have h2 : (0 : ℝ) ≤ ((((k - 1 : ℕ))) : ℝ) := Nat.cast_nonneg _
  linarith [hr0]

private lemma chap7_agree (m K J : ℕ) (x r : ℂ) (hK : K = m + 2)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2)
    (hr0 : r.re < 0) (phi : ℂ)
    (hphi : HasSum (chapter7PowerDifferenceTerm r x) phi) :
    phi = chap7PhiCont K J x r := by
  have hfun : (fun j : ℕ => chap7T x j r) = chapter7PowerDifferenceTerm r x :=
    funext (fun j => chap7T_eq_term x r j)
  have hT : HasSum (fun j : ℕ => chap7T x j r) phi := by
    rw [hfun]
    exact hphi
  have hsumT : Summable (fun j : ℕ => chap7T x j r) := hT.summable
  have htsumT : (∑' j : ℕ, chap7T x j r) = phi := hT.tsum_eq
  have hsplit := Summable.sum_add_tsum_nat_add J hsumT
  rw [htsumT] at hsplit
  have hrU : r.re < ((((m + 1 : ℕ))) : ℝ) := by
    have hpos : (0 : ℝ) < ((((m + 1 : ℕ))) : ℝ) := by
      exact_mod_cast Nat.succ_pos m
    linarith [hr0]
  obtain ⟨N, hN⟩ := exists_nat_gt ‖r‖
  have hg_sum : Summable (fun n : ℕ => chap7g K J x n r) :=
    chap7_g_summable m N K J x r hK hJ hrU hN
  have hfin_sum : Summable (fun n : ℕ => ∑ k ∈ Finset.Icc 1 K,
      Ring.choose r k * x ^ k *
        ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) :=
    chap7_finite_inner_summable J K r x hr0
  have htail_sum : Summable (fun n : ℕ => chap7T x (n + J) r) :=
    (summable_nat_add_iff J).mpr hsumT
  have htail_eq_fun : (fun n : ℕ => chap7T x (n + J) r) =
      (fun n : ℕ => chap7g K J x n r - ∑ k ∈ Finset.Icc 1 K,
        Ring.choose r k * x ^ k *
          ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ)))) := by
    funext n
    have hw : ‖chap7W x (n + J)‖ ≤ 1 / 2 := hJ (n + J) (Nat.le_add_left J n)
    exact chap7T_eq K J x n r hw
  have htail_tsum : (∑' n : ℕ, chap7T x (n + J) r) =
      (∑' n : ℕ, chap7g K J x n r) -
        ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 K, Ring.choose r k * x ^ k *
          ((((n + J : ℕ) : ℂ) + 1) ^ (r - (k : ℂ))) := by
    rw [htail_eq_fun]
    exact Summable.tsum_sub hg_sum hfin_sum
  have hfin_tsum := chap7_finite_inner_tsum J K r x hr0
  have hper : ∀ k ∈ Finset.Icc 1 K, Ring.choose r k * x ^ k *
        (riemannZeta (((k : ℕ) : ℂ) - r) - chap7H J (((k : ℕ) : ℂ) - r)) =
        -(x ^ k * (chap7P k r * chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
          Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r))) := by
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hr_ne : r ≠ ((((k - 1 : ℕ))) : ℂ) := chap7_ne_of_re_neg r k hr0
    have hzeta := chap7_neg_zeta_eq r k hk.1 hr_ne
    linear_combination -(x ^ k) * hzeta
  have hsum_per : (∑ k ∈ Finset.Icc 1 K, Ring.choose r k * x ^ k *
        (riemannZeta (((k : ℕ) : ℂ) - r) - chap7H J (((k : ℕ) : ℂ) - r))) =
      -∑ k ∈ Finset.Icc 1 K, x ^ k * (chap7P k r *
        chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
        Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    exact hper k hk
  have hphi_eq : phi = (∑ j ∈ Finset.range J, chap7T x j r) +
      (∑' n : ℕ, chap7g K J x n r) +
      ∑ k ∈ Finset.Icc 1 K, x ^ k * (chap7P k r *
        chap7E (((k : ℕ) : ℂ) - r) / (((k ! : ℕ)) : ℂ) +
        Ring.choose r k * chap7H J (((k : ℕ) : ℂ) - r)) := by
    have h1 : phi = (∑ j ∈ Finset.range J, chap7T x j r) +
        ∑' n : ℕ, chap7T x (n + J) r := hsplit.symm
    rw [h1, htail_tsum, hfin_tsum, hsum_per]
    ring
  rw [hphi_eq]
  rfl

private lemma chap7_phi_eq_PhiCont_at_nat (m K J : ℕ) (x : ℂ)
    (hx : chapter7Admissible x) (hK : K = m + 2)
    (hJ : ∀ j : ℕ, J ≤ j → ‖chap7W x j‖ ≤ 1 / 2)
    (phi : ℂ → ℂ → ℂ)
    (hphi_entire : Differentiable ℂ (fun r : ℂ => phi r x))
    (hphi_series : ∀ r, r.re < 0 → HasSum (chapter7PowerDifferenceTerm r x) (phi r x)) :
    phi (m : ℂ) x = chap7PhiCont K J x (m : ℂ) := by
  have hU_open : IsOpen (chap7U m) := chap7U_open m
  have hU_pre : IsPreconnected (chap7U m) :=
    (convex_halfSpace_re_lt _).isPreconnected
  have hz0_mem : (-1 : ℂ) ∈ chap7U m := by
    change (-1 : ℂ).re < ((((m + 1 : ℕ))) : ℝ)
    have h1 : ((-1 : ℂ).re) = (-1 : ℝ) := by simp
    rw [h1]
    have hpos : (0 : ℝ) ≤ ((((m + 1 : ℕ))) : ℝ) := Nat.cast_nonneg _
    linarith
  have hm_mem : (m : ℂ) ∈ chap7U m := by
    change ((m : ℂ).re) < ((((m + 1 : ℕ))) : ℝ)
    have h1 : ((m : ℂ).re) = (m : ℝ) := by simp
    rw [h1]
    have h2 : ((m : ℝ)) < ((((m + 1 : ℕ))) : ℝ) := by
      have heq : ((((m + 1 : ℕ))) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [heq]
      linarith
    exact h2
  have hmem : {r : ℂ | r.re < 0} ∈ nhds (-1 : ℂ) := by
    have hre : ((-1 : ℂ).re) = (-1 : ℝ) := by simp
    have hIio : Set.Iio (0 : ℝ) ∈ nhds ((-1 : ℂ).re) := by
      rw [hre]
      exact Iio_mem_nhds (by norm_num)
    have hpre := Complex.continuous_re.continuousAt.preimage_mem_nhds hIio
    have hset : Complex.re ⁻¹' Set.Iio (0 : ℝ) = {r : ℂ | r.re < 0} := rfl
    rwa [hset] at hpre
  have hev : (fun r : ℂ => phi r x) =ᶠ[nhds (-1 : ℂ)]
      fun r : ℂ => chap7PhiCont K J x r := by
    filter_upwards [hmem] with r hr
    exact chap7_agree m K J x r hK hJ hr (phi r x) (hphi_series r hr)
  have hphi_an : AnalyticOnNhd ℂ (fun r : ℂ => phi r x) (chap7U m) :=
    hphi_entire.differentiableOn.analyticOnNhd hU_open
  have hPhi_an : AnalyticOnNhd ℂ (fun r : ℂ => chap7PhiCont K J x r) (chap7U m) :=
    (chap7PhiCont_differentiableOn m K J x hx hK hJ).analyticOnNhd hU_open
  have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
    hphi_an hPhi_an hU_pre hz0_mem hev
  exact hEqOn hm_mem

private lemma chap7_choose_nat_eq_zero (m k : ℕ) (h : m < k) :
    Ring.choose ((m : ℕ) : ℂ) k = 0 := by
  rw [Ring.choose_natCast, Nat.choose_eq_zero_of_lt h, Nat.cast_zero]

private lemma chap7_binom_sum_nat (m : ℕ) (w : ℂ) :
    (∑ k ∈ Finset.range (m + 1), Ring.choose ((m : ℕ) : ℂ) k * w ^ k) =
      (1 + w) ^ m := by
  have hadd := add_pow (R := ℂ) w 1 m
  have hcomm : w + 1 = 1 + w := add_comm _ _
  rw [hcomm] at hadd
  rw [hadd]
  apply Finset.sum_congr rfl
  intro k _
  rw [Ring.choose_natCast]
  simp only [one_pow, mul_one]
  ring

private lemma chap7R_nat_eq_zero (m K : ℕ) (w : ℂ) (hle : m ≤ K) :
    chap7R K ((m : ℕ) : ℂ) w = 0 := by
  unfold chap7R
  have hcpow : ((1 + w) ^ (((m : ℕ)) : ℂ)) = (1 + w) ^ m :=
    Complex.cpow_natCast _ m
  rw [hcpow]
  have hsub : Finset.range (m + 1) ⊆ Finset.range (K + 1) :=
    Finset.range_subset_range.mpr (Nat.succ_le_succ hle)
  have hzero : ∀ k ∈ Finset.range (K + 1), k ∉ Finset.range (m + 1) →
      Ring.choose ((m : ℕ) : ℂ) k * w ^ k = 0 := by
    intro k _ hk_not
    simp only [Finset.mem_range, not_lt] at hk_not
    have hlt : m < k := by omega
    have hchoose := chap7_choose_nat_eq_zero m k hlt
    rw [hchoose, zero_mul]
  have hsubset := Finset.sum_subset hsub hzero
  have hbinom := chap7_binom_sum_nat m w
  rw [hsubset] at hbinom
  rw [← hbinom, sub_self]

private lemma chap7G_nat_eq_zero (m K J : ℕ) (x : ℂ) (hK : K = m + 2) :
    (∑' n : ℕ, chap7g K J x n ((m : ℕ) : ℂ)) = 0 := by
  have hle : m ≤ K := by omega
  have hzero : ∀ n : ℕ, chap7g K J x n ((m : ℕ) : ℂ) = 0 := by
    intro n
    unfold chap7g
    have hR : chap7R K ((m : ℕ) : ℂ) (chap7W x (n + J)) = 0 :=
      chap7R_nat_eq_zero m K _ hle
    rw [hR, mul_zero, neg_zero]
  simp [hzero]

private lemma chap7T_nat (x : ℂ) (j m : ℕ) :
    chap7T x j ((m : ℕ) : ℂ) =
      ((((j : ℕ) : ℂ) + 1) ^ m - ((((j : ℕ) : ℂ) + 1 + x) ^ m)) := by
  unfold chap7T
  rw [Complex.cpow_natCast, Complex.cpow_natCast]

private lemma chap7_add_pow_swap (a x : ℂ) (m : ℕ) :
    (a + x) ^ m =
      ∑ k ∈ Finset.range (m + 1), x ^ k * a ^ (m - k) * ((m.choose k : ℕ) : ℂ) := by
  have hadd := add_pow (R := ℂ) x a m
  have hcomm : x + a = a + x := add_comm _ _
  have heq : (a + x) ^ m = (x + a) ^ m := by rw [hcomm]
  rw [heq]
  exact hadd

private lemma chap7T_nat_eq (x : ℂ) (j m : ℕ) :
    chap7T x j ((m : ℕ) : ℂ) = -∑ k ∈ Finset.Icc 1 m,
      x ^ k * ((((j : ℕ) : ℂ) + 1) ^ (m - k)) * ((m.choose k : ℕ) : ℂ) := by
  rw [chap7T_nat]
  have hexp := chap7_add_pow_swap ((((j : ℕ) : ℂ) + 1)) x m
  have hsplit := chap7_range_split m
  have hsum : (∑ k ∈ Finset.range (m + 1),
      x ^ k * ((((j : ℕ) : ℂ) + 1) ^ (m - k)) * ((m.choose k : ℕ) : ℂ)) =
      ((((j : ℕ) : ℂ) + 1) ^ m) + ∑ k ∈ Finset.Icc 1 m,
        x ^ k * ((((j : ℕ) : ℂ) + 1) ^ (m - k)) * ((m.choose k : ℕ) : ℂ) := by
    rw [hsplit, Finset.sum_insert (chap7_zero_not_mem_Icc m)]
    congr 1
    simp [Nat.choose_zero_right]
  rw [hexp, hsum]
  ring

private lemma chap7H_nat (J m k : ℕ) (hk_le : k ≤ m) :
    chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) =
      ∑ j ∈ Finset.range J, ((((j : ℕ) : ℂ) + 1) ^ (m - k)) := by
  have hneg : -(((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) = ((((m - k : ℕ))) : ℂ) := by
    rw [Nat.cast_sub hk_le]
    ring
  unfold chap7H
  apply Finset.sum_congr rfl
  intro j _
  rw [hneg, Complex.cpow_natCast]

private lemma chap7_head_eq (J m : ℕ) (x : ℂ) :
    (∑ j ∈ Finset.range J, chap7T x j ((m : ℕ) : ℂ)) =
      -∑ k ∈ Finset.Icc 1 m, x ^ k *
        (∑ j ∈ Finset.range J, ((((j : ℕ) : ℂ) + 1) ^ (m - k))) *
        ((m.choose k : ℕ) : ℂ) := by
  have hT : ∀ j ∈ Finset.range J, chap7T x j ((m : ℕ) : ℂ) =
      -∑ k ∈ Finset.Icc 1 m, x ^ k * ((((j : ℕ) : ℂ) + 1) ^ (m - k)) *
        ((m.choose k : ℕ) : ℂ) := fun j _ => chap7T_nat_eq x j m
  rw [Finset.sum_congr rfl hT, Finset.sum_neg_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  have h1 : (∑ j ∈ Finset.range J, x ^ k * ((((j : ℕ) : ℂ) + 1) ^ (m - k)) *
      ((m.choose k : ℕ) : ℂ)) =
      ∑ j ∈ Finset.range J, (x ^ k * ((m.choose k : ℕ) : ℂ)) *
        ((((j : ℕ) : ℂ) + 1) ^ (m - k)) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, ← Finset.mul_sum]
  ring

private lemma chap7P_succ (m : ℕ) :
    chap7P (m + 1) ((m : ℕ) : ℂ) = (((m ! : ℕ)) : ℂ) := by
  unfold chap7P
  have hsub : m + 1 - 1 = m := by omega
  rw [hsub]
  have hterm : ∀ i ∈ Finset.range m,
      (((m : ℕ) : ℂ) - ((i : ℕ) : ℂ)) = ((((m - i : ℕ))) : ℂ) := by
    intro i hi
    simp only [Finset.mem_range] at hi
    have hle : i ≤ m := Nat.le_of_lt hi
    exact (Nat.cast_sub hle).symm
  rw [Finset.prod_congr rfl hterm, ← Nat.cast_prod]
  congr 1
  have hfact : (m ! : ℕ) = ∏ i ∈ Finset.range m, (i + 1) :=
    Nat.factorial_eq_prod_range_add_one m
  rw [hfact]
  have hreflect := Finset.prod_range_reflect (fun j => j + 1) m
  rw [← hreflect]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  omega

private lemma chap7P_m2_zero (m : ℕ) :
    chap7P (m + 2) ((m : ℕ) : ℂ) = 0 := by
  unfold chap7P
  have hsub : m + 2 - 1 = m + 1 := by omega
  rw [hsub]
  have hmem : m ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_self m)
  have hzero : (((m : ℕ) : ℂ) - ((m : ℕ) : ℂ)) = 0 := sub_self _
  exact Finset.prod_eq_zero hmem hzero

private lemma chap7PE_le (m k : ℕ) (hk1 : 1 ≤ k) (hk_le : k ≤ m) :
    chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
        ((((k ! : ℕ))) : ℂ) =
      -(Ring.choose ((m : ℕ) : ℂ) k) *
        riemannZeta (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) := by
  have hne : m ≠ k - 1 := by omega
  have hr_ne : ((m : ℕ) : ℂ) ≠ ((((k - 1 : ℕ))) : ℂ) := by exact_mod_cast hne
  exact (chap7_neg_zeta_eq ((m : ℕ) : ℂ) k hk1 hr_ne).symm

private lemma chap7PE_m1 (m J : ℕ) (x : ℂ) :
    x ^ (m + 1) * (chap7P (m + 1) ((m : ℕ) : ℂ) *
        chap7E ((((m + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ)) / ((((m + 1)! : ℕ)) : ℂ) +
        Ring.choose ((m : ℕ) : ℂ) (m + 1) *
          chap7H J ((((m + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ))) =
      x ^ (m + 1) / ((((m + 1 : ℕ))) : ℂ) := by
  have hC : Ring.choose ((m : ℕ) : ℂ) (m + 1) = 0 :=
    chap7_choose_nat_eq_zero m (m + 1) (Nat.lt_succ_self m)
  have harg : ((((m + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ)) = 1 := by
    push_cast
    ring
  have hE : chap7E ((((m + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ)) = 1 := by
    rw [harg, chap7E_one]
  have hP := chap7P_succ m
  have hfact : ((((m + 1)! : ℕ)) : ℂ) =
      ((((m + 1 : ℕ))) : ℂ) * ((((m ! : ℕ))) : ℂ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
  have hfact_ne : ((((m ! : ℕ))) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero m
  have hm1_ne : ((((m + 1 : ℕ))) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  rw [hC, hE, hP, hfact]
  field_simp
  ring

private lemma chap7PE_m2 (m J : ℕ) (x : ℂ) :
    x ^ (m + 2) * (chap7P (m + 2) ((m : ℕ) : ℂ) *
        chap7E ((((m + 2 : ℕ)) : ℂ) - ((m : ℕ) : ℂ)) / ((((m + 2)! : ℕ)) : ℂ) +
        Ring.choose ((m : ℕ) : ℂ) (m + 2) *
          chap7H J ((((m + 2 : ℕ)) : ℂ) - ((m : ℕ) : ℂ))) = 0 := by
  have hC : Ring.choose ((m : ℕ) : ℂ) (m + 2) = 0 :=
    chap7_choose_nat_eq_zero m (m + 2) (by omega)
  have hP := chap7P_m2_zero m
  rw [hC, hP]
  simp

private lemma chap7_PhiCont_nat (m J : ℕ) (x : ℂ) :
    chap7PhiCont (m + 2) J x ((m : ℕ) : ℂ) =
      (∑ k ∈ Finset.Icc 1 m, x ^ k * (-(Ring.choose ((m : ℕ) : ℂ) k) *
        riemannZeta (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)))) +
        x ^ (m + 1) / ((((m + 1 : ℕ))) : ℂ) := by
  have hG0 := chap7G_nat_eq_zero m (m + 2) J x rfl
  have hhead := chap7_head_eq J m x
  have hthird_split : (∑ k ∈ Finset.Icc 1 (m + 2), x ^ k *
      (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
        ((((k ! : ℕ))) : ℂ) +
        Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)))) =
      (∑ k ∈ Finset.Icc 1 m, x ^ k *
        (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
          ((((k ! : ℕ))) : ℂ) +
          Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)))) +
        x ^ (m + 1) / ((((m + 1 : ℕ))) : ℂ) := by
    have h1 := Finset.sum_Icc_succ_top (a := 1) (b := m + 1)
      (by omega : 1 ≤ m + 1 + 1) (fun k => x ^ k *
        (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
          ((((k ! : ℕ))) : ℂ) +
          Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ))))
    have h2 := Finset.sum_Icc_succ_top (a := 1) (b := m)
      (by omega : 1 ≤ m + 1) (fun k => x ^ k *
        (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
          ((((k ! : ℕ))) : ℂ) +
          Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ))))
    have hm2 : m + 1 + 1 = m + 2 := by omega
    rw [hm2] at h1
    have hm1 : x ^ (m + 1) * (chap7P (m + 1) ((m : ℕ) : ℂ) *
        chap7E ((((m + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ)) / ((((m + 1)! : ℕ)) : ℂ) +
        Ring.choose ((m : ℕ) : ℂ) (m + 1) *
          chap7H J ((((m + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ))) =
        x ^ (m + 1) / ((((m + 1 : ℕ))) : ℂ) := chap7PE_m1 m J x
    have hm2z : x ^ (m + 1 + 1) * (chap7P (m + 1 + 1) ((m : ℕ) : ℂ) *
        chap7E ((((m + 1 + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ)) / ((((m + 1 + 1)! : ℕ)) : ℂ) +
        Ring.choose ((m : ℕ) : ℂ) (m + 1 + 1) *
          chap7H J ((((m + 1 + 1 : ℕ)) : ℂ) - ((m : ℕ) : ℂ))) = 0 := by
      have hz := chap7PE_m2 m J x
      simpa [hm2] using hz
    rw [h1, h2, hm2z, add_zero, hm1]
  have hthird_m_split : (∑ k ∈ Finset.Icc 1 m, x ^ k *
        (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
          ((((k ! : ℕ))) : ℂ) +
          Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)))) =
      (∑ k ∈ Finset.Icc 1 m, x ^ k *
        (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
          ((((k ! : ℕ))) : ℂ))) +
        ∑ k ∈ Finset.Icc 1 m, x ^ k *
          (Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ))) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hHm_eq : (∑ k ∈ Finset.Icc 1 m, x ^ k *
        (Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)))) =
      ∑ k ∈ Finset.Icc 1 m, x ^ k *
        (∑ j ∈ Finset.range J, ((((j : ℕ) : ℂ) + 1) ^ (m - k))) *
        ((m.choose k : ℕ) : ℂ) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hC : Ring.choose ((m : ℕ) : ℂ) k = ((m.choose k : ℕ) : ℂ) :=
      Ring.choose_natCast m k
    have hH := chap7H_nat J m k hk.2
    rw [hC, hH]
    ring
  have hPEm_eq : (∑ k ∈ Finset.Icc 1 m, x ^ k *
        (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
          ((((k ! : ℕ))) : ℂ))) =
      ∑ k ∈ Finset.Icc 1 m, x ^ k * (-(Ring.choose ((m : ℕ) : ℂ) k) *
        riemannZeta (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ))) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hPE := chap7PE_le m k hk.1 hk.2
    rw [hPE]
  have hPhi : chap7PhiCont (m + 2) J x ((m : ℕ) : ℂ) =
      (∑ j ∈ Finset.range J, chap7T x j ((m : ℕ) : ℂ)) +
        (∑' n : ℕ, chap7g (m + 2) J x n ((m : ℕ) : ℂ)) +
        ∑ k ∈ Finset.Icc 1 (m + 2), x ^ k *
          (chap7P k ((m : ℕ) : ℂ) * chap7E (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) /
            ((((k ! : ℕ))) : ℂ) +
            Ring.choose ((m : ℕ) : ℂ) k * chap7H J (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ))) := rfl
  rw [hPhi, hG0, hthird_split, hthird_m_split, hHm_eq, hPEm_eq, hhead]
  ring

private lemma chap7B_eq_aeval (n : ℕ) (x : ℂ) :
    chapter7BernoulliPolynomial n x = Polynomial.aeval x (Polynomial.bernoulli n) := by
  unfold chapter7BernoulliPolynomial
  rw [Polynomial.eval_map_algebraMap]

private lemma chap7B_one (n : ℕ) :
    chapter7BernoulliPolynomial n 1 = (((bernoulli' n : ℚ)) : ℂ) := by
  rw [chap7B_eq_aeval]
  have h1 : (1 : ℂ) = algebraMap ℚ ℂ (1 : ℚ) := (map_one _).symm
  rw [h1, Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval,
    Polynomial.bernoulli_eval_one, Algebra.algebraMap_eq_smul_one,
    Rat.smul_one_eq_cast]

private lemma chap7B_one_add (n : ℕ) (x : ℂ) :
    chapter7BernoulliPolynomial n (1 + x) =
      chapter7BernoulliPolynomial n x + (n : ℂ) * x ^ (n - 1) := by
  have hcomp := Polynomial.bernoulli_comp_one_add_X n
  have haeval := congrArg (Polynomial.aeval x) hcomp
  simp only [Polynomial.aeval_add, Polynomial.aeval_comp, map_nsmul,
    Polynomial.aeval_X_pow, Polynomial.aeval_X, Polynomial.aeval_one] at haeval
  rw [chap7B_eq_aeval, chap7B_eq_aeval, haeval]
  congr 1
  rw [nsmul_eq_mul]

private lemma chap7B_expand (n : ℕ) (x : ℂ) :
    chapter7BernoulliPolynomial n x =
      ∑ i ∈ Finset.range (n + 1),
        (((_root_.bernoulli (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i := by
  rw [chap7B_eq_aeval, Polynomial.bernoulli_def, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
    Rat.smul_one_eq_cast]

private lemma chap7B_one_add_eq_bernoulli' (n : ℕ) (x : ℂ) (hn : 1 ≤ n) :
    chapter7BernoulliPolynomial n (1 + x) =
      ∑ i ∈ Finset.range (n + 1),
        (((_root_.bernoulli' (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i := by
  have hB := chap7B_expand n x
  have h1x := chap7B_one_add n x
  rw [hB] at h1x
  rw [h1x]
  have ha_mem : n - 1 ∈ Finset.range (n + 1) := by
    simp only [Finset.mem_range]
    omega
  have hB_erase : (∑ i ∈ Finset.range (n + 1),
        (((_root_.bernoulli (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i) =
      (((_root_.bernoulli (n - (n - 1)) * ((Nat.choose n (n - 1) : ℕ) : ℚ)) : ℚ) : ℂ) *
        x ^ (n - 1) +
        ∑ i ∈ (Finset.range (n + 1)).erase (n - 1),
          (((_root_.bernoulli (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
            x ^ i := by
    rw [← Finset.add_sum_erase _ _ ha_mem, add_comm]
  have hBp_erase : (∑ i ∈ Finset.range (n + 1),
        (((_root_.bernoulli' (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i) =
      (((_root_.bernoulli' (n - (n - 1)) * ((Nat.choose n (n - 1) : ℕ) : ℚ)) : ℚ) : ℂ) *
        x ^ (n - 1) +
        ∑ i ∈ (Finset.range (n + 1)).erase (n - 1),
          (((_root_.bernoulli' (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
            x ^ i := by
    rw [← Finset.add_sum_erase _ _ ha_mem, add_comm]
  have herase_eq : (∑ i ∈ (Finset.range (n + 1)).erase (n - 1),
        (((_root_.bernoulli (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i) =
      ∑ i ∈ (Finset.range (n + 1)).erase (n - 1),
        (((_root_.bernoulli' (n - i) * ((Nat.choose n i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_erase, Finset.mem_range] at hi
    have hne : n - i ≠ 1 := by omega
    have hB : _root_.bernoulli (n - i) = _root_.bernoulli' (n - i) :=
      _root_.bernoulli_eq_bernoulli'_of_ne_one hne
    rw [hB]
  have hnsub : n - (n - 1) = 1 := by omega
  have hchoose : Nat.choose n (n - 1) = n := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    simp [Nat.choose_succ_self_right]
  have hdiff : (_root_.bernoulli' 1 : ℚ) - _root_.bernoulli 1 = 1 := by
    rw [_root_.bernoulli'_one, _root_.bernoulli_one]
    norm_num
  have hterm : (((_root_.bernoulli (n - (n - 1)) *
        ((Nat.choose n (n - 1) : ℕ) : ℚ)) : ℚ) : ℂ) * x ^ (n - 1) +
        (n : ℂ) * x ^ (n - 1) =
      (((_root_.bernoulli' (n - (n - 1)) *
        ((Nat.choose n (n - 1) : ℕ) : ℚ)) : ℚ) : ℂ) * x ^ (n - 1) := by
    have hB1 : ((_root_.bernoulli 1 : ℚ) : ℂ) =
        ((_root_.bernoulli' 1 : ℚ) : ℂ) - 1 := by
      have hq : (_root_.bernoulli 1 : ℚ) = _root_.bernoulli' 1 - 1 := by
        linear_combination -hdiff
      rw [hq]
      push_cast
      ring
    rw [hnsub, hchoose]
    push_cast
    rw [hB1]
    ring
  rw [hB_erase, hBp_erase, herase_eq]
  linear_combination hterm

private lemma chap7_zeta_bernoulli (m k : ℕ) (hk_le : k ≤ m) :
    -(Ring.choose ((m : ℕ) : ℂ) k) * riemannZeta (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) =
      ((((m.choose k : ℕ))) : ℂ) * (((_root_.bernoulli' (m - k + 1) : ℚ)) : ℂ) /
        ((((m - k + 1 : ℕ))) : ℂ) := by
  have hs : (((k : ℕ) : ℂ) - ((m : ℕ) : ℂ)) = -(((((m - k : ℕ)))) : ℂ) := by
    have h : ((((m - k : ℕ))) : ℂ) = ((m : ℕ) : ℂ) - ((k : ℕ) : ℂ) :=
      Nat.cast_sub hk_le
    rw [h]
    ring
  have hz := riemannZeta_neg_nat_eq_bernoulli' (m - k)
  have hC : Ring.choose ((m : ℕ) : ℂ) k = ((((m.choose k : ℕ))) : ℂ) :=
    Ring.choose_natCast m k
  have hcast : ((((m - k + 1 : ℕ))) : ℂ) = ((((m - k : ℕ))) : ℂ) + 1 := by
    push_cast
    ring
  rw [hs, hz, hC, hcast]
  ring

private lemma chap7_PhiCont_bernoulli (m J : ℕ) (x : ℂ) :
    chap7PhiCont (m + 2) J x ((m : ℕ) : ℂ) =
      (∑ k ∈ Finset.Icc 1 m, x ^ k *
        (((((m.choose k : ℕ))) : ℂ) * (((_root_.bernoulli' (m - k + 1) : ℚ)) : ℂ) /
          ((((m - k + 1 : ℕ))) : ℂ))) +
        x ^ (m + 1) / ((((m + 1 : ℕ))) : ℂ) := by
  have hPhi := chap7_PhiCont_nat m J x
  rw [hPhi]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_Icc] at hk
  have hz := chap7_zeta_bernoulli m k hk.2
  rw [hz]

private lemma chap7_IntegerPhi_expand (m : ℕ) (x : ℂ) :
    chapter7IntegerPhi m x =
      ∑ i ∈ Finset.Icc 1 (m + 1),
        ((((_root_.bernoulli' ((m + 1) - i) * ((Nat.choose (m + 1) i : ℕ) : ℚ)) : ℚ)) : ℂ) *
          x ^ i / ((((m + 1 : ℕ))) : ℂ) := by
  have hB1x := chap7B_one_add_eq_bernoulli' (m + 1) x (by omega : 1 ≤ m + 1)
  have hB1 := chap7B_one (m + 1)
  have hx1 : x + 1 = 1 + x := add_comm _ _
  unfold chapter7IntegerPhi
  rw [hx1, hB1x, hB1]
  have hsplit := chap7_range_split (m + 1)
  have hsum0 : (∑ i ∈ Finset.range (m + 1 + 1),
        (((_root_.bernoulli' ((m + 1) - i) * ((Nat.choose (m + 1) i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i) =
      (((_root_.bernoulli' (m + 1) : ℚ)) : ℂ) +
        ∑ i ∈ Finset.Icc 1 (m + 1),
          (((_root_.bernoulli' ((m + 1) - i) * ((Nat.choose (m + 1) i : ℕ) : ℚ)) : ℚ) : ℂ) *
            x ^ i := by
    rw [hsplit, Finset.sum_insert (chap7_zero_not_mem_Icc (m + 1))]
    congr 1
    simp [Nat.choose_zero_right]
  rw [hsum0]
  have hcancel : (((_root_.bernoulli' (m + 1) : ℚ)) : ℂ) +
        ∑ i ∈ Finset.Icc 1 (m + 1),
          (((_root_.bernoulli' ((m + 1) - i) * ((Nat.choose (m + 1) i : ℕ) : ℚ)) : ℚ) : ℂ) *
            x ^ i - (((_root_.bernoulli' (m + 1) : ℚ)) : ℂ) =
      ∑ i ∈ Finset.Icc 1 (m + 1),
        (((_root_.bernoulli' ((m + 1) - i) * ((Nat.choose (m + 1) i : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ i := by ring
  rw [hcancel, Finset.sum_div]
  have hcast : ((((m + 1 : ℕ))) : ℂ) = ((m : ℕ) : ℂ) + 1 := by
    push_cast
    ring
  rw [hcast]

private lemma chap7_PhiCont_eq_IntegerPhi (m J : ℕ) (x : ℂ) :
    chap7PhiCont (m + 2) J x ((m : ℕ) : ℂ) = chapter7IntegerPhi m x := by
  have hPhi := chap7_PhiCont_bernoulli m J x
  have hInt := chap7_IntegerPhi_expand m x
  have hsplit := Finset.sum_Icc_succ_top (a := 1) (b := m)
    (by omega : 1 ≤ m + 1) (fun i =>
      (((_root_.bernoulli' ((m + 1) - i) * ((Nat.choose (m + 1) i : ℕ) : ℚ)) : ℚ) : ℂ) *
        x ^ i / ((((m + 1 : ℕ))) : ℂ))
  have htop : (((_root_.bernoulli' ((m + 1) - (m + 1)) *
        ((Nat.choose (m + 1) (m + 1) : ℕ) : ℚ)) : ℚ) : ℂ) * x ^ (m + 1) /
      ((((m + 1 : ℕ))) : ℂ) = x ^ (m + 1) / ((((m + 1 : ℕ))) : ℂ) := by
    have hsub : m + 1 - (m + 1) = 0 := by omega
    have hchoose : Nat.choose (m + 1) (m + 1) = 1 := Nat.choose_self _
    rw [hsub, hchoose]
    simp [_root_.bernoulli'_zero]
  have hsum : (∑ k ∈ Finset.Icc 1 m, x ^ k *
        (((((m.choose k : ℕ))) : ℂ) * (((_root_.bernoulli' (m - k + 1) : ℚ)) : ℂ) /
          ((((m - k + 1 : ℕ))) : ℂ))) =
      ∑ k ∈ Finset.Icc 1 m,
        (((_root_.bernoulli' ((m + 1) - k) * ((Nat.choose (m + 1) k : ℕ) : ℚ)) : ℚ) : ℂ) *
          x ^ k / ((((m + 1 : ℕ))) : ℂ) := by
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Finset.mem_Icc] at hk
    have hsub_eq : m - k + 1 = (m + 1) - k := by omega
    have hchoose := Nat.choose_mul_succ_eq m k
    have hchooseC : ((((m.choose k : ℕ))) : ℂ) * ((((m + 1 : ℕ))) : ℂ) =
        ((((Nat.choose (m + 1) k : ℕ))) : ℂ) * ((((m + 1 - k : ℕ))) : ℂ) := by
      exact_mod_cast hchoose
    have hm1_ne : ((((m + 1 : ℕ))) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero m
    have hmk2_ne : ((((m + 1 - k : ℕ))) : ℂ) ≠ 0 := by
      have h0 : m + 1 - k ≠ 0 := by omega
      exact_mod_cast h0
    have hsub_rw : ((((m - k + 1 : ℕ))) : ℂ) = ((((m + 1 - k : ℕ))) : ℂ) := by
      rw [hsub_eq]
    have hB_rw : ((_root_.bernoulli' (m - k + 1) : ℚ) : ℂ) =
        ((_root_.bernoulli' ((m + 1) - k) : ℚ) : ℂ) := by
      rw [hsub_eq]
    rw [hB_rw, hsub_rw]
    have hpush : (((_root_.bernoulli' ((m + 1) - k) *
          ((Nat.choose (m + 1) k : ℕ) : ℚ)) : ℚ) : ℂ) =
        (((_root_.bernoulli' ((m + 1) - k) : ℚ)) : ℂ) *
          ((((Nat.choose (m + 1) k : ℕ))) : ℂ) := by
      push_cast
      ring
    rw [hpush]
    field_simp [hm1_ne, hmk2_ne]
    linear_combination (x ^ k * (((_root_.bernoulli' ((m + 1) - k) : ℚ)) : ℂ)) * hchooseC
  rw [hPhi, hInt, hsplit, htop, hsum]

/-- **Entire continuations of the power-difference series agree and take Bernoulli values.**
Let $f$ and $g$ be complex-valued functions of two complex variables $(r, x)$ such that, for every
admissible $x$, both $r \mapsto f(r, x)$ and $r \mapsto g(r, x)$ are entire, and for every
admissible $x$ and every complex $r$ with $\operatorname{Re} r < 0$ the series
$\sum_{j \ge 0} \bigl((j + 1)^r - (j + 1 + x)^r\bigr)$ (principal powers) has sum $f(r, x)$ and
also has sum $g(r, x)$. Then $f(r, x) = g(r, x)$ for every admissible $x$ and every complex $r$,
and for every natural number $m$ and every admissible $x$,
$f(m, x) = g(m, x) = \bigl(B_{m+1}(x + 1) - B_{m+1}(1)\bigr)/(m + 1)$, where $B_n$ is the $n$-th
Bernoulli polynomial.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
-/
theorem ramanujan_part1_ch7_entry9_zetaeven
    (phi psi : ℂ → ℂ → ℂ)
    (hphi_entire : ∀ x, chapter7Admissible x →
      Differentiable ℂ (fun r : ℂ => phi r x))
    (hpsi_entire : ∀ x, chapter7Admissible x →
      Differentiable ℂ (fun r : ℂ => psi r x))
    (hphi_series : ∀ r x, r.re < 0 → chapter7Admissible x →
      HasSum (chapter7PowerDifferenceTerm r x) (phi r x))
    (hpsi_series : ∀ r x, r.re < 0 → chapter7Admissible x →
      HasSum (chapter7PowerDifferenceTerm r x) (psi r x)) :
    (∀ x, chapter7Admissible x → ∀ r, phi r x = psi r x) ∧
      (∀ m : ℕ, ∀ x, chapter7Admissible x →
        phi m x = chapter7IntegerPhi m x ∧
          psi m x = chapter7IntegerPhi m x) := by
  have hfirst : ∀ x, chapter7Admissible x → ∀ r, phi r x = psi r x := by
    intro x hx r
    have hphi : AnalyticOnNhd ℂ (fun r : ℂ => phi r x) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (hphi_entire x hx)
    have hpsi : AnalyticOnNhd ℂ (fun r : ℂ => psi r x) Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr (hpsi_entire x hx)
    have heq : (fun r : ℂ => phi r x) = fun r : ℂ => psi r x := by
      have hmem : {r : ℂ | r.re < 0} ∈ nhds (-1 : ℂ) := by
        have hre : ((-1 : ℂ).re) = (-1 : ℝ) := by simp
        have hIio : Set.Iio (0 : ℝ) ∈ nhds ((-1 : ℂ).re) := by
          rw [hre]
          exact Iio_mem_nhds (by norm_num)
        have hpre := Complex.continuous_re.continuousAt.preimage_mem_nhds hIio
        have hset : Complex.re ⁻¹' Set.Iio (0 : ℝ) = {r : ℂ | r.re < 0} := rfl
        rwa [hset] at hpre
      have hev : (fun r : ℂ => phi r x) =ᶠ[nhds (-1 : ℂ)] fun r : ℂ => psi r x := by
        filter_upwards [hmem] with r hr
        exact HasSum.unique (hphi_series r x hr hx) (hpsi_series r x hr hx)
      exact AnalyticOnNhd.eq_of_eventuallyEq hphi hpsi hev
    exact congrFun heq r
  refine ⟨hfirst, fun m x hx => ?_⟩
  have hphi_eq : phi (m : ℂ) x = chapter7IntegerPhi m x := by
    obtain ⟨J, hJ⟩ := chap7W_exists x
    have hphi_at := chap7_phi_eq_PhiCont_at_nat m (m + 2) J x hx rfl hJ phi
      (hphi_entire x hx) (fun r hr => hphi_series r x hr hx)
    have hPhiInt := chap7_PhiCont_eq_IntegerPhi m J x
    exact hphi_at.trans hPhiInt
  exact ⟨hphi_eq, (hfirst x hx _).symm.trans hphi_eq⟩

end
end Entry9Zetaeven
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
