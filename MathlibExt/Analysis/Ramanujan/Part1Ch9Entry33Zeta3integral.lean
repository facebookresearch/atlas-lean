/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Harmonic.Bounds

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9, Entry 33

∫ x cosⁿx sin(nx) over [0,π/2] evaluates via harmonic numbers.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry33Zeta3integral

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry33Integrand (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos x ^ n * Real.sin ((n : ℝ) * x)

def chapter9Entry33WeightedIntegrand (n : ℕ) (x : ℝ) : ℝ :=
  x * Real.cos x ^ n * Real.sin ((n : ℝ) * x)

-- H1: pointwise trig identity via complex exponentials
private lemma cos_pow_mul_sin_eq (x : ℝ) (n : ℕ) :
    Real.cos x ^ n * Real.sin ((n : ℝ) * x)
      = (2 : ℝ)⁻¹ ^ n * ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * Real.sin (2 * j * x) := by
  have ofReal_mul_im' : ∀ (a : ℝ) (b : ℂ), (↑a * b).im = a * b.im := by
    intro a b
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have ofReal_mul_im'' : ∀ (b : ℂ) (a : ℝ), (b * ↑a).im = b.im * a := by
    intro b a
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  set E : ℂ := Complex.exp ((x : ℂ) * Complex.I) with hE
  have hEpow : ∀ k : ℕ, E ^ k = Complex.exp (((((k : ℝ) * x : ℝ)) : ℝ) * Complex.I) := by
    intro k
    rw [hE, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcos : ((Real.cos x : ℝ) : ℂ) = (E + E⁻¹) / 2 := by
    have h := Complex.two_cos ((x : ℂ))
    rw [← Complex.ofReal_cos] at h
    have hexp : Complex.exp (-(x : ℂ) * Complex.I) = E⁻¹ := by
      rw [hE, ← Complex.exp_neg]
      congr 1
      ring
    rw [hexp] at h
    linear_combination h / 2
  have hmain : ((Real.cos x : ℝ) : ℂ) ^ n * E ^ n
      = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * E ^ (2 * j)) / (2 : ℂ) ^ n := by
    rw [hcos]
    have hmul : ((E + E⁻¹) / 2) * E = (E ^ 2 + 1) / 2 := by
      rw [div_mul_eq_mul_div, add_mul, inv_mul_cancel₀ (Complex.exp_ne_zero _)]
      ring
    have step1 : ((E + E⁻¹) / 2) ^ n * E ^ n = ((E ^ 2 + 1) / 2) ^ n := by
      rw [← mul_pow, hmul]
    rw [step1, div_pow, add_pow (E ^ 2) 1 n]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_mul E 2 j, one_pow, mul_one, mul_comm]
  have him := congrArg Complex.im hmain
  have hL : (((Real.cos x : ℝ) : ℂ) ^ n * E ^ n).im
      = Real.cos x ^ n * Real.sin ((n : ℝ) * x) := by
    rw [← Complex.ofReal_pow, hEpow n, ofReal_mul_im', Complex.exp_ofReal_mul_I_im]
  have hterm : ∀ j : ℕ, (((n.choose j : ℂ)) * E ^ (2 * j)).im
      = (n.choose j : ℝ) * Real.sin (2 * j * x) := by
    intro j
    have hc : ((n.choose j : ℂ)) = (((n.choose j : ℝ)) : ℂ) := by norm_cast
    rw [hc, ofReal_mul_im', hEpow (2 * j), Complex.exp_ofReal_mul_I_im]
    congr 1
    congr 1
    push_cast
    ring
  have hR : (((∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * E ^ (2 * j)) / (2 : ℂ) ^ n)).im
      = (∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * Real.sin (2 * j * x)) / (2 : ℝ) ^ n := by
    have h2 : (2 : ℂ) ^ n = ((((2 : ℝ) ^ n : ℝ)) : ℂ) := by norm_cast
    rw [div_eq_mul_inv, h2, ← Complex.ofReal_inv, ofReal_mul_im'', Complex.im_sum]
    have hsum : (∑ j ∈ Finset.range (n + 1), ((((n.choose j : ℂ)) * E ^ (2 * j))).im)
        = ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * Real.sin (2 * j * x) :=
      Finset.sum_congr rfl (fun j _ => hterm j)
    rw [hsum, div_eq_mul_inv]
  rw [hL, hR] at him
  rw [him, div_eq_inv_mul, inv_pow]

-- H2: elementary sine integral
private lemma integral_sin_two_mul (j : ℕ) :
    ∫ x in (0:ℝ)..Real.pi/2, Real.sin (2 * j * x) = (1 - (-1 : ℝ)^j) / (2 * j) := by
  by_cases hj : j = 0
  · subst hj
    simp
  · have hc : (2:ℝ) * j ≠ 0 :=
      mul_ne_zero two_ne_zero (by exact_mod_cast hj)
    rw [intervalIntegral.integral_comp_mul_left Real.sin hc, smul_eq_mul, integral_sin,
      mul_zero]
    have harg : (2:ℝ) * j * (Real.pi/2) = j * Real.pi := by ring
    rw [harg, Real.cos_zero, Real.cos_nat_mul_pi]
    ring

-- FTC lemma: ∫ u sin u
private lemma integral_u_mul_sin (m : ℕ) :
    ∫ u in (0:ℝ)..((m : ℝ) * Real.pi), u * Real.sin u
      = Real.sin ((m : ℝ) * Real.pi) - ((m : ℝ) * Real.pi) * Real.cos ((m : ℝ) * Real.pi) := by
  have hF : ∀ u : ℝ, HasDerivAt (fun u => Real.sin u - u * Real.cos u) (u * Real.sin u) u := by
    intro u
    have h := (Real.hasDerivAt_sin u).sub ((hasDerivAt_id' u).mul (Real.hasDerivAt_cos u))
    have heq : Real.cos u - (1 * Real.cos u + u * -Real.sin u) = u * Real.sin u := by ring
    rwa [heq] at h
  have hdiff : ∀ u ∈ [[(0:ℝ), (m:ℝ)*Real.pi]],
      DifferentiableAt ℝ (fun u => Real.sin u - u * Real.cos u) u :=
    fun u _ => (hF u).differentiableAt
  have hdeq : deriv (fun u => Real.sin u - u * Real.cos u) = (fun u => u * Real.sin u) :=
    funext fun u => (hF u).deriv
  have hint : IntervalIntegrable (deriv (fun u => Real.sin u - u * Real.cos u)) volume
      (0:ℝ) ((m:ℝ)*Real.pi) := by
    rw [hdeq]
    exact (continuous_id.mul Real.continuous_sin).intervalIntegrable _ _
  rw [← hdeq, intervalIntegral.integral_deriv_eq_sub hdiff hint]
  simp [Real.sin_zero]

-- H3: weighted elementary integral
private lemma integral_x_mul_sin_two_mul (j : ℕ) :
    ∫ x in (0:ℝ)..Real.pi/2, x * Real.sin (2 * j * x)
      = -(Real.pi * (-1 : ℝ)^j) / (4 * j) := by
  by_cases hj : j = 0
  · subst hj
    simp
  · have hj' : (j:ℝ) ≠ 0 := by exact_mod_cast hj
    have hc : (2:ℝ) * j ≠ 0 := mul_ne_zero two_ne_zero hj'
    have hfun : (fun x : ℝ => x * Real.sin (2 * j * x))
        = (fun x => ((2:ℝ)*j)⁻¹ * ((fun u => u * Real.sin u) (((2:ℝ)*j) * x))) := by
      funext x
      field_simp
    rw [hfun, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_mul_left (fun u => u * Real.sin u) hc, smul_eq_mul,
      mul_zero]
    have harg : (2:ℝ) * j * (Real.pi/2) = j * Real.pi := by ring
    rw [harg, integral_u_mul_sin, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi]
    have h4j : (4:ℝ) * j ≠ 0 := mul_ne_zero (by norm_num) hj'
    field_simp
    ring

-- absorption (nat)
private lemma nat_absorb (n j : ℕ) (hjn : j ≤ n) :
    (n+1) * n.choose j = (j+1) * (n+1).choose (j+1) := by
  have h1 := Nat.choose_succ_succ n j
  have h2 := Nat.choose_succ_right_eq n j
  have h3 : (j+1) + (n-j) = n+1 := by omega
  have h4 : (n-j) * n.choose j = (j+1) * n.choose (j+1) := by
    rw [mul_comm (n-j) (n.choose j), ← h2]
    exact mul_comm _ _
  calc (n+1) * n.choose j = ((j+1) + (n-j)) * n.choose j := by rw [h3]
    _ = (j+1) * n.choose j + (n-j) * n.choose j := by ring
    _ = (j+1) * n.choose j + (j+1) * n.choose (j+1) := by rw [h4]
    _ = (j+1) * (n.choose j + n.choose (j+1)) := by ring
    _ = (j+1) * (n+1).choose (j+1) := by rw [h1]

-- absorption (real)
private lemma real_absorb (n j : ℕ) (hjn : j ≤ n) :
    (n.choose j : ℝ) * (((j:ℝ)+1)⁻¹) = ((n+1).choose (j+1) : ℝ) * (((n:ℝ)+1)⁻¹) := by
  have h := nat_absorb n j hjn
  have hR : ((n:ℝ)+1) * (n.choose j : ℝ) = ((j:ℝ)+1) * ((n+1).choose (j+1) : ℝ) := by
    exact_mod_cast h
  have hj1 : (j:ℝ)+1 ≠ 0 := by positivity
  have hn1 : (n:ℝ)+1 ≠ 0 := by positivity
  field_simp
  linear_combination hR

-- alternating partial row sum = 1
private lemma alt_row_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (-1:ℝ)^j * ((n+1).choose (j+1) : ℝ) = 1 := by
  have h := add_pow (-1 : ℝ) 1 (n+1)
  simp only [one_pow, mul_one] at h
  rw [show (-1:ℝ)+1 = 0 from by ring, zero_pow (Nat.succ_ne_zero n)] at h
  rw [Finset.sum_range_succ'] at h
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at h
  have hneg : (∑ m ∈ Finset.range (n+1), (-1:ℝ)^(m+1) * ((n+1).choose (m+1) : ℝ))
      = -(∑ j ∈ Finset.range (n+1), (-1:ℝ)^j * ((n+1).choose (j+1) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [pow_succ]
    ring
  rw [hneg] at h
  linarith

-- row sum = 2^(n+1) - 1
private lemma row_sum_pred (n : ℕ) :
    ∑ i ∈ Finset.range (n+1), ((n+1).choose (i+1) : ℝ) = (2:ℝ)^(n+1) - 1 := by
  have h := add_pow (1:ℝ) 1 (n+1)
  simp only [one_pow, mul_one, one_mul] at h
  rw [show (1:ℝ)+1 = 2 from by ring] at h
  rw [Finset.sum_range_succ'] at h
  simp only [Nat.choose_zero_right, Nat.cast_one] at h
  linarith

-- (W): alternating binomial reciprocal sum
private lemma alt_choose_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * (-1)^j * (j:ℝ)⁻¹
      = -∑ k ∈ Finset.Icc 1 n, (k:ℝ)⁻¹ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpeel : (∑ j ∈ Finset.range (n+1+1), ((n+1).choose j : ℝ) * (-1:ℝ)^j * (j:ℝ)⁻¹)
        = ∑ i ∈ Finset.range (n+1),
          ((n+1).choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, inv_zero, mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      rw [show ((((i+1 : ℕ)):ℝ)) = (i:ℝ)+1 from by norm_cast]
    have hsplit :
        (∑ i ∈ Finset.range (n+1),
          ((n+1).choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
        = (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
          + (∑ i ∈ Finset.range (n+1), (n.choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)) := by
      have hterm : ∀ i ∈ Finset.range (n+1),
          ((n+1).choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)
          = ((n.choose i : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)
            + (n.choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)) := by
        intro i _
        rw [Nat.choose_succ_succ]
        push_cast
        ring
      calc (∑ i ∈ Finset.range (n+1),
            ((n+1).choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
          = ∑ i ∈ Finset.range (n+1),
            ((n.choose i : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)
              + (n.choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)) :=
            Finset.sum_congr rfl hterm
        _ = _ := Finset.sum_add_distrib
    have hA : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
        = -(((n:ℝ)+1)⁻¹) := by
      have hP := alt_row_sum n
      have htermA : ∀ i ∈ Finset.range (n+1),
          (n.choose i : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)
          = (-(((n:ℝ)+1)⁻¹)) * ((-1:ℝ)^i * ((n+1).choose (i+1) : ℝ)) := by
        intro i hi
        have hi_le : i ≤ n := by
          have hmem := Finset.mem_range.mp hi
          omega
        have hr := real_absorb n i hi_le
        have hp : (-1:ℝ)^(i+1) = -(-1)^i := by rw [pow_succ]; ring
        rw [hp]
        linear_combination -(-1:ℝ)^i * hr
      calc (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
          = (-(((n:ℝ)+1)⁻¹)) * ∑ i ∈ Finset.range (n+1), ((-1:ℝ)^i * ((n+1).choose (i+1) : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl htermA
        _ = -(((n:ℝ)+1)⁻¹) := by rw [hP, mul_one]
    have hB : (∑ i ∈ Finset.range (n+1), (n.choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
        = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * (-1:ℝ)^k * ((k:ℝ)⁻¹) := by
      have e1 : (∑ i ∈ Finset.range (n+1), (n.choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
          = (∑ i ∈ Finset.range n, (n.choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹))
            + (n.choose (n+1) : ℝ) * (-1:ℝ)^(n+1) * ((((n:ℝ))+1)⁻¹) :=
        Finset.sum_range_succ _ n
      have hlast : (n.choose (n+1) : ℝ) * (-1:ℝ)^(n+1) * ((((n:ℝ))+1)⁻¹) = 0 := by
        have hz : n.choose (n+1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
        rw [hz, Nat.cast_zero, zero_mul, zero_mul]
      have e2 : (∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * (-1:ℝ)^k * ((k:ℝ)⁻¹))
          = (∑ i ∈ Finset.range n, (n.choose (i+1) : ℝ) * (-1:ℝ)^(i+1) * (((i:ℝ)+1)⁻¹)) + 0 := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, Nat.cast_zero,
          inv_zero, mul_zero]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [show ((((i+1 : ℕ)):ℝ)) = (i:ℝ)+1 from by norm_cast]
      rw [e1, hlast, add_zero, e2, add_zero]
    have hcastn : ((((n+1 : ℕ)):ℝ)) = (n:ℝ)+1 := by norm_cast
    have htarget : -∑ k ∈ Finset.Icc 1 (n+1), (k:ℝ)⁻¹
        = -∑ k ∈ Finset.Icc 1 n, (k:ℝ)⁻¹ - (((n:ℝ)+1)⁻¹) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), hcastn, neg_add, sub_eq_add_neg]
    rw [hpeel, hsplit, hA, hB, ih, htarget]
    ring

-- (U): plain binomial reciprocal sum
private lemma choose_sum (n : ℕ) :
    ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * (j:ℝ)⁻¹
      = ∑ k ∈ Finset.Icc 1 n, ((2:ℝ)^k - 1) / (k:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpeel : (∑ j ∈ Finset.range (n+1+1), ((n+1).choose j : ℝ) * (j:ℝ)⁻¹)
        = ∑ i ∈ Finset.range (n+1), ((n+1).choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹) := by
      rw [Finset.sum_range_succ']
      simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, inv_zero,
        mul_zero, add_zero]
      apply Finset.sum_congr rfl
      intro i _
      rw [show ((((i+1 : ℕ)):ℝ)) = (i:ℝ)+1 from by norm_cast]
    have hsplit :
        (∑ i ∈ Finset.range (n+1), ((n+1).choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹))
        = (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (((i:ℝ)+1)⁻¹))
          + (∑ i ∈ Finset.range (n+1), (n.choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹)) := by
      have hterm : ∀ i ∈ Finset.range (n+1),
          ((n+1).choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹)
          = ((n.choose i : ℝ) * (((i:ℝ)+1)⁻¹)
            + (n.choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹)) := by
        intro i _
        rw [Nat.choose_succ_succ]
        push_cast
        ring
      calc (∑ i ∈ Finset.range (n+1), ((n+1).choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹))
          = ∑ i ∈ Finset.range (n+1),
            ((n.choose i : ℝ) * (((i:ℝ)+1)⁻¹)
              + (n.choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹)) :=
            Finset.sum_congr rfl hterm
        _ = _ := Finset.sum_add_distrib
    have hA : (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (((i:ℝ)+1)⁻¹))
        = ((2:ℝ)^(n+1) - 1) * (((n:ℝ)+1)⁻¹) := by
      have hQ := row_sum_pred n
      have htermA : ∀ i ∈ Finset.range (n+1),
          (n.choose i : ℝ) * (((i:ℝ)+1)⁻¹)
          = ((((n:ℝ)+1)⁻¹)) * (((n+1).choose (i+1) : ℝ)) := by
        intro i hi
        have hi_le : i ≤ n := by
          have hmem := Finset.mem_range.mp hi
          omega
        rw [real_absorb n i hi_le]
        ring
      calc (∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * (((i:ℝ)+1)⁻¹))
          = ((((n:ℝ)+1)⁻¹)) * ∑ i ∈ Finset.range (n+1), (((n+1).choose (i+1) : ℝ)) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl htermA
        _ = ((2:ℝ)^(n+1) - 1) * (((n:ℝ)+1)⁻¹) := by rw [hQ]; ring
    have hB : (∑ i ∈ Finset.range (n+1), (n.choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹))
        = ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * ((k:ℝ)⁻¹) := by
      have e1 : (∑ i ∈ Finset.range (n+1), (n.choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹))
          = (∑ i ∈ Finset.range n, (n.choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹))
            + (n.choose (n+1) : ℝ) * ((((n:ℝ))+1)⁻¹) :=
        Finset.sum_range_succ _ n
      have hlast : (n.choose (n+1) : ℝ) * ((((n:ℝ))+1)⁻¹) = 0 := by
        have hz : n.choose (n+1) = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
        rw [hz, Nat.cast_zero, zero_mul]
      have e2 : (∑ k ∈ Finset.range (n+1), (n.choose k : ℝ) * ((k:ℝ)⁻¹))
          = (∑ i ∈ Finset.range n, (n.choose (i+1) : ℝ) * (((i:ℝ)+1)⁻¹)) + 0 := by
        rw [Finset.sum_range_succ']
        simp only [Nat.choose_zero_right, Nat.cast_one, Nat.cast_zero, inv_zero,
          mul_zero]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [show ((((i+1 : ℕ)):ℝ)) = (i:ℝ)+1 from by norm_cast]
      rw [e1, hlast, add_zero, e2, add_zero]
    have hcastn : ((((n+1 : ℕ)):ℝ)) = (n:ℝ)+1 := by norm_cast
    have htarget : ∑ k ∈ Finset.Icc 1 (n+1), ((2:ℝ)^k - 1) / (k:ℝ)
        = ∑ k ∈ Finset.Icc 1 n, ((2:ℝ)^k - 1) / (k:ℝ)
          + ((2:ℝ)^(n+1) - 1) / (((n:ℝ)+1)) := by
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1), hcastn]
    rw [hpeel, hsplit, hA, hB, ih, htarget]
    ring

-- integrability auxiliaries
private lemma hint_each (n : ℕ) : ∀ j ∈ Finset.range (n+1),
    IntervalIntegrable (fun x : ℝ => (n.choose j:ℝ) * Real.sin (2*j*x)) volume
      0 (Real.pi/2) := by
  intro j _
  exact ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul
    (n.choose j : ℝ)).intervalIntegrable _ _

private lemma hwint_each (n : ℕ) : ∀ j ∈ Finset.range (n+1),
    IntervalIntegrable (fun x : ℝ => (n.choose j:ℝ) * (x * Real.sin (2*j*x))) volume
      0 (Real.pi/2) := by
  intro j _
  exact ((continuous_id.mul (Real.continuous_sin.comp
    (continuous_const.mul continuous_id))).const_mul
    (n.choose j : ℝ)).intervalIntegrable _ _

-- harmonic cast
private lemma harmonic_cast (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Finset.Icc 1 n, (k:ℝ)⁻¹ := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Rat.cast_inv, Rat.cast_natCast]

/-- **Ramanujan's integrals of $\cos^n x \sin nx$ for every $n \ge 0$.** Let $n$ be a natural
number and let $H_n = \sum_{k=1}^{n} 1/k$ be the $n$-th harmonic number. Then
$x \cos^n x \sin(nx)$ and $\cos^n x \sin(nx)$ are integrable on $[0, \pi/2]$,
$\int_0^{\pi/2} x \cos^n x \sin(nx)\,dx = \frac{\pi}{2^{n+2}} H_n$ and
$\int_0^{\pi/2} \cos^n x \sin(nx)\,dx = \frac{1}{2^{n+1}} \sum_{k=1}^{n} \frac{2^k}{k}$.

This is Entry 33 without the hypothesis $n > 0$: at $n = 0$ both sides of each identity are $0$.
-/
theorem ramanujan_part1_ch9_entry33_zeta3integral_general (n : ℕ) :
    IntervalIntegrable (chapter9Entry33WeightedIntegrand n) volume 0
        (Real.pi / 2) ∧
      IntervalIntegrable (chapter9Entry33Integrand n) volume 0
        (Real.pi / 2) ∧
      (∫ x in (0 : ℝ)..Real.pi / 2,
          chapter9Entry33WeightedIntegrand n x) =
        Real.pi / (2 : ℝ) ^ (n + 2) * ((harmonic n : ℚ) : ℝ) ∧
      (∫ x in (0 : ℝ)..Real.pi / 2, chapter9Entry33Integrand n x) =
        1 / (2 : ℝ) ^ (n + 1) *
          ∑ k ∈ Icc 1 n, (2 : ℝ) ^ k / (k : ℝ) := by
  have hcos : Continuous (fun x : ℝ => Real.cos x ^ n) := Real.continuous_cos.pow n
  have hsin : Continuous (fun x : ℝ => Real.sin ((n:ℝ) * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hcontI : Continuous (chapter9Entry33Integrand n) := hcos.mul hsin
  have hcontW : Continuous (chapter9Entry33WeightedIntegrand n) :=
    (continuous_id.mul hcos).mul hsin
  refine ⟨hcontW.intervalIntegrable _ _, hcontI.intervalIntegrable _ _, ?_, ?_⟩
  · -- weighted integral
    have hssW : (∫ x in (0:ℝ)..Real.pi/2, ∑ j ∈ Finset.range (n+1),
          (n.choose j:ℝ) * (x * Real.sin (2*j*x)))
        = ∑ j ∈ Finset.range (n+1), ∫ x in (0:ℝ)..Real.pi/2,
          (n.choose j:ℝ) * (x * Real.sin (2*j*x)) :=
      intervalIntegral.integral_finsetSum (hwint_each n)
    have hIntW : (∫ x in (0:ℝ)..Real.pi/2, chapter9Entry33WeightedIntegrand n x)
        = (2:ℝ)⁻¹^n * ∑ j ∈ Finset.range (n+1),
          (n.choose j:ℝ) * (-(Real.pi*(-1:ℝ)^j)/(4*j)) := by
      have hw : ∀ x : ℝ, (x * Real.cos x ^ n) * Real.sin (↑n * x)
          = (2:ℝ)⁻¹^n * ∑ j ∈ Finset.range (n+1),
            (n.choose j:ℝ) * (x * Real.sin (2*j*x)) := by
        intro x
        rw [mul_assoc, cos_pow_mul_sin_eq]
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      simp only [chapter9Entry33WeightedIntegrand, hw, intervalIntegral.integral_const_mul]
      rw [hssW]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul, integral_x_mul_sin_two_mul]
    have hWcomb : (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ) * (-(Real.pi*(-1:ℝ)^j)/(4*j)))
        = (Real.pi/4) * (∑ k ∈ Finset.Icc 1 n, (k:ℝ)⁻¹) := by
      have hstep : (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ) * (-(Real.pi*(-1:ℝ)^j)/(4*j)))
          = (-(Real.pi/4)) * (∑ j ∈ Finset.range (n+1),
            (n.choose j:ℝ)*(-1:ℝ)^j*(j:ℝ)⁻¹) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hstep, alt_choose_sum]
      ring
    rw [hIntW, hWcomb, ← harmonic_cast n]
    have h2 : (2:ℝ)^(n+2) = 2^n * 4 := by rw [pow_add]; norm_num
    rw [h2]
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring
  · -- unweighted integral
    have hss : (∫ x in (0:ℝ)..Real.pi/2, ∑ j ∈ Finset.range (n+1),
          (n.choose j:ℝ) * Real.sin (2*j*x))
        = ∑ j ∈ Finset.range (n+1), ∫ x in (0:ℝ)..Real.pi/2,
          (n.choose j:ℝ) * Real.sin (2*j*x) :=
      intervalIntegral.integral_finsetSum (hint_each n)
    have hInt : (∫ x in (0:ℝ)..Real.pi/2, chapter9Entry33Integrand n x)
        = (2:ℝ)⁻¹^n * ∑ j ∈ Finset.range (n+1),
          (n.choose j:ℝ) * ((1 - (-1:ℝ)^j)/(2*j)) := by
      have hu : ∀ x : ℝ, Real.cos x ^ n * Real.sin (↑n * x)
          = (2:ℝ)⁻¹^n * ∑ j ∈ Finset.range (n+1),
            (n.choose j:ℝ) * Real.sin (2*j*x) :=
        fun x => cos_pow_mul_sin_eq x n
      simp only [chapter9Entry33Integrand, hu, intervalIntegral.integral_const_mul]
      rw [hss]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul, integral_sin_two_mul]
    have hcomb : (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ) * ((1 - (-1:ℝ)^j)/(2*j)))
        = (1/2) * ((∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*(j:ℝ)⁻¹)
          - (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*(-1:ℝ)^j*(j:ℝ)⁻¹)) := by
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hUW : (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*(j:ℝ)⁻¹)
        - (∑ j ∈ Finset.range (n+1), (n.choose j:ℝ)*(-1:ℝ)^j*(j:ℝ)⁻¹)
        = ∑ k ∈ Finset.Icc 1 n, (2:ℝ)^k/(k:ℝ) := by
      rw [choose_sum, alt_choose_sum, sub_neg_eq_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      rw [← one_div, ← add_div, sub_add_cancel]
    rw [hInt, hcomb, hUW]
    have h2 : (2:ℝ)^(n+1) = 2^n * 2 := by rw [pow_add, pow_one]
    rw [h2]
    simp only [div_eq_mul_inv, mul_inv, inv_pow]
    ring

set_option linter.unusedVariables false in
/-- **Ramanujan's integrals of $\cos^n x \sin nx$ (Entry 33).** Let $n$ be a positive integer and
let $H_n = \sum_{k=1}^{n} 1/k$ be the $n$-th harmonic number. Then $x \cos^n x \sin(nx)$ and
$\cos^n x \sin(nx)$ are integrable on $[0, \pi/2]$,
$\int_0^{\pi/2} x \cos^n x \sin(nx)\,dx = \frac{\pi}{2^{n+2}} H_n$ and
$\int_0^{\pi/2} \cos^n x \sin(nx)\,dx = \frac{1}{2^{n+1}} \sum_{k=1}^{n} \frac{2^k}{k}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
Proves `Wanted` entry `ramanujan_part1_ch9_entry33_zeta3integral`.
-/
theorem ramanujan_part1_ch9_entry33_zeta3integral (n : ℕ) (hn : 0 < n) :
    IntervalIntegrable (chapter9Entry33WeightedIntegrand n) volume 0
        (Real.pi / 2) ∧
      IntervalIntegrable (chapter9Entry33Integrand n) volume 0
        (Real.pi / 2) ∧
      (∫ x in (0 : ℝ)..Real.pi / 2,
          chapter9Entry33WeightedIntegrand n x) =
        Real.pi / (2 : ℝ) ^ (n + 2) * ((harmonic n : ℚ) : ℝ) ∧
      (∫ x in (0 : ℝ)..Real.pi / 2, chapter9Entry33Integrand n x) =
        1 / (2 : ℝ) ^ (n + 1) *
          ∑ k ∈ Icc 1 n, (2 : ℝ) ^ k / (k : ℝ) :=
  ramanujan_part1_ch9_entry33_zeta3integral_general ..

end

end Entry33Zeta3integral

end MathlibExt.Analysis.Ramanujan.Part1Ch9
