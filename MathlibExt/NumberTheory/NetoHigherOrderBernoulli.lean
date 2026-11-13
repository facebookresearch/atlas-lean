/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/Algebra/Polynomial/Derivative.lean` (Mathlib):
Copyright (c) 2018 Chris Hughes. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.Binomial
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Algebra.Polynomial.Roots

/-! # Neto's symmetry identity for higher-order Bernoulli numbers

This file defines higher-order Bernoulli numbers through their formal exponential generating
series and proves Neto's symmetry identity for them.
-/

@[expose] public section

namespace MetaMathlibExt

open Finset

private theorem neto_hasSubst_bernoulli_sub_one :
    PowerSeries.HasSubst (bernoulliPowerSeries ℂ - 1 : PowerSeries ℂ) := by
  apply PowerSeries.HasSubst.of_constantCoeff_zero'
  simp [bernoulliPowerSeries]

private noncomputable def neto_choosePolynomial (j : ℕ) : Polynomial ℂ :=
  Polynomial.C (j.factorial : ℂ)⁻¹ * descPochhammer ℂ j

private theorem neto_choose_eq_eval (x : ℂ) (j : ℕ) :
    Ring.choose x j = Polynomial.eval x (neto_choosePolynomial j) := by
  rw [Ring.choose_eq_smul]
  simp only [neto_choosePolynomial, smul_eq_mul, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval,
    ← descPochhammer_eval_eq_ascPochhammer]

private theorem neto_coeff_pow_bernoulli_sub_one_eq_zero {m j : ℕ} (h : m < j) :
    PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) = 0 := by
  apply PowerSeries.coeff_of_lt_order
  refine lt_of_lt_of_le ?_
    (PowerSeries.le_order_pow_of_constantCoeff_eq_zero j ?_)
  · exact_mod_cast h
  · simp [bernoulliPowerSeries]

private theorem neto_coeff_subst_binomial (x : ℂ) (m : ℕ) :
    PowerSeries.coeff m
        (PowerSeries.subst (bernoulliPowerSeries ℂ - 1)
          (PowerSeries.binomialSeries ℂ x)) =
      ∑ j ∈ Finset.range (m + 1), Ring.choose x j *
        PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) := by
  rw [PowerSeries.coeff_subst' neto_hasSubst_bernoulli_sub_one]
  have hs : Function.support (fun j : ℕ =>
      PowerSeries.coeff j (PowerSeries.binomialSeries ℂ x) •
        PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j)) ⊆
      (Finset.range (m + 1) : Set ℕ) := by
    intro j hj
    simp only [Finset.mem_coe, Finset.mem_range]
    by_contra h
    apply hj
    have hmj : m < j := by omega
    change PowerSeries.coeff j (PowerSeries.binomialSeries ℂ x) •
      PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j) = 0
    rw [neto_coeff_pow_bernoulli_sub_one_eq_zero hmj, smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp only [PowerSeries.binomialSeries_coeff, smul_eq_mul, mul_one]

/-- **Higher-order Bernoulli numbers.** For a complex number $\alpha$ and a natural number $n$, the
higher-order Bernoulli number $B_n^{(\alpha)}$ is $n!$ times the coefficient of $t^n$ in the
formal power series $\left(t / (e^t - 1)\right)^{\alpha}$. Here $t / (e^t - 1)$ is the Bernoulli
generating series $\sum_{k \ge 0} B_k t^k / k!$ (with $B_1 = -1/2$), and its $\alpha$-th power is
the binomial series $(1 + u)^{\alpha} = \sum_{j \ge 0} \binom{\alpha}{j} u^j$ with
$u = t / (e^t - 1) - 1$ substituted.

Equivalently, $B_n^{(\alpha)} = B_n^{(\alpha)}(0)$, where the generalized Bernoulli polynomials
$B_n^{(\alpha)}(x)$ are given by the exponential generating function
$\sum_{n \ge 0} B_n^{(\alpha)}(x) t^n / n! = \left(t / (e^t - 1)\right)^{\alpha} e^{tx}$.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex
Definition span: lines 99-112,
text_sha256 `0acb659f24f1fa6140d178c11f64ab833f8d8a20336d0828a32665f37f2b7951`.
File sha256 `ce83119262833b8219cb7670521e7602617dae3f645a76e913bff79b7ba7dc9c`. -/
public noncomputable def higherOrderBernoulliNumber (α : ℂ) (n : ℕ) : ℂ :=
  (n.factorial : ℂ) * PowerSeries.coeff n
    (PowerSeries.subst (bernoulliPowerSeries ℂ - 1) (PowerSeries.binomialSeries ℂ α))

/-- **Higher-order Bernoulli numbers of natural order.** Let $B_k$ denote the Bernoulli numbers,
with $B_1 = -1/2$. For natural numbers $d$ and $n$, the higher-order Bernoulli number
$B_n^{(d)}$ equals $n!$ times the coefficient of $t^n$ in the $d$-th power of the Bernoulli
generating series $\sum_{k \ge 0} B_k t^k / k!$. -/
public theorem higherOrderBernoulliNumber_nat (d n : ℕ) :
    higherOrderBernoulliNumber (d : ℂ) n =
      (n.factorial : ℂ) * PowerSeries.coeff n (bernoulliPowerSeries ℂ ^ d) := by
  rw [higherOrderBernoulliNumber, PowerSeries.binomialSeries_nat]
  rw [PowerSeries.subst_pow neto_hasSubst_bernoulli_sub_one]
  congr 2
  have hone : PowerSeries.subst (bernoulliPowerSeries ℂ - 1) (1 : PowerSeries ℂ) = 1 := by
    rw [← PowerSeries.coe_substAlgHom neto_hasSubst_bernoulli_sub_one, map_one]
  rw [PowerSeries.subst_add neto_hasSubst_bernoulli_sub_one,
    PowerSeries.subst_X neto_hasSubst_bernoulli_sub_one, hone]
  ring

/-- **Higher-order Bernoulli numbers of order one.** For every natural number $n$, the
higher-order Bernoulli number $B_n^{(1)}$ equals the Bernoulli number $B_n$, with the
convention $B_1 = -1/2$. -/
public theorem higherOrderBernoulliNumber_one (n : ℕ) :
    higherOrderBernoulliNumber 1 n = (bernoulli n : ℂ) := by
  have h1 : (1 : ℂ) = ((1 : ℕ) : ℂ) := by norm_num
  rw [h1, higherOrderBernoulliNumber_nat]
  simp only [pow_one]
  rw [bernoulliPowerSeries, PowerSeries.coeff_mk]
  rw [← map_natCast (algebraMap ℚ ℂ) n.factorial, ← map_mul]
  apply congr_arg (algebraMap ℚ ℂ)
  apply mul_div_cancel₀
  exact_mod_cast Nat.factorial_ne_zero n

private theorem neto_higherOrderBernoulliNumber_polynomial (m : ℕ) :
    ∃ P : Polynomial ℂ, ∀ x : ℂ,
      higherOrderBernoulliNumber x m = Polynomial.eval x P := by
  let P : Polynomial ℂ :=
    Polynomial.C (m.factorial : ℂ) *
      ∑ j ∈ Finset.range (m + 1), neto_choosePolynomial j *
        Polynomial.C (PowerSeries.coeff m ((bernoulliPowerSeries ℂ - 1) ^ j))
  refine ⟨P, ?_⟩
  intro x
  rw [higherOrderBernoulliNumber, neto_coeff_subst_binomial]
  simp_rw [neto_choose_eq_eval]
  simp only [P, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum]

private noncomputable def neto_higherOrderBernoulliPolynomial (m : ℕ) : Polynomial ℂ :=
  Classical.choose (neto_higherOrderBernoulliNumber_polynomial m)

private theorem neto_higherOrderBernoulliPolynomial_eval (x : ℂ) (m : ℕ) :
    Polynomial.eval x (neto_higherOrderBernoulliPolynomial m) =
      higherOrderBernoulliNumber x m := by
  symm
  exact Classical.choose_spec (neto_higherOrderBernoulliNumber_polynomial m) x

private theorem neto_bernoulli_reflection :
    PowerSeries.evalNegHom (bernoulliPowerSeries ℂ) =
      bernoulliPowerSeries ℂ * PowerSeries.exp ℂ := by
  have hB := bernoulliPowerSeries_mul_exp_sub_one ℂ
  have hfactor :
      PowerSeries.evalNegHom (PowerSeries.exp ℂ) - 1 ≠ 0 := by
    intro h
    have hc := congrArg (PowerSeries.coeff 1) (sub_eq_zero.mp h)
    norm_num [PowerSeries.evalNegHom, PowerSeries.coeff_rescale,
      PowerSeries.coeff_exp] at hc
  apply mul_right_cancel₀ hfactor
  calc
    PowerSeries.evalNegHom (bernoulliPowerSeries ℂ) *
        (PowerSeries.evalNegHom (PowerSeries.exp ℂ) - 1) =
      PowerSeries.evalNegHom
        (bernoulliPowerSeries ℂ * (PowerSeries.exp ℂ - 1)) := by
          rw [map_mul, map_sub, map_one]
    _ = -PowerSeries.X := by rw [hB, PowerSeries.evalNegHom_X]
    _ = (bernoulliPowerSeries ℂ * PowerSeries.exp ℂ) *
        (PowerSeries.evalNegHom (PowerSeries.exp ℂ) - 1) := by
      rw [mul_sub, mul_one, mul_assoc,
        PowerSeries.exp_mul_exp_neg_eq_one, mul_one]
      linear_combination hB

private theorem neto_bernoulli_power_reflection (d : ℕ) :
    PowerSeries.evalNegHom (bernoulliPowerSeries ℂ ^ d) =
      bernoulliPowerSeries ℂ ^ d *
        PowerSeries.rescale (d : ℂ) (PowerSeries.exp ℂ) := by
  rw [map_pow, neto_bernoulli_reflection, mul_pow,
    PowerSeries.exp_pow_eq_rescale_exp]

private theorem neto_iterate_derivative_evalNeg (f : PowerSeries ℂ) (l : ℕ) :
    PowerSeries.derivative^[l] (PowerSeries.evalNegHom f) =
      (-1 : ℂ) ^ l • PowerSeries.evalNegHom (PowerSeries.derivative^[l] f) := by
  ext n
  simp only [PowerSeries.coeff_iterate_derivative, PowerSeries.evalNegHom,
    PowerSeries.coeff_rescale, map_smul, smul_eq_mul]
  rw [pow_add]
  ring

private theorem neto_derivative_rescale (a : ℂ) (f : PowerSeries ℂ) :
    PowerSeries.derivative (PowerSeries.rescale a f) =
      a • PowerSeries.rescale a (PowerSeries.derivative f) := by
  ext n
  simp only [PowerSeries.coeff_derivative, PowerSeries.coeff_rescale,
    map_smul, smul_eq_mul]
  rw [pow_succ]
  ring

private theorem neto_iterate_derivative_rescale_exp (a : ℂ) (r : ℕ) :
    PowerSeries.derivative^[r] (PowerSeries.rescale a (PowerSeries.exp ℂ)) =
      a ^ r • PowerSeries.rescale a (PowerSeries.exp ℂ) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.map_smul,
      neto_derivative_rescale, PowerSeries.derivative_exp, smul_smul, pow_succ]

private theorem neto_iterate_derivative_mul (p q : PowerSeries ℂ) (n : ℕ) :
    PowerSeries.derivative^[n] (p * q) =
      ∑ k ∈ range n.succ, n.choose k •
        (PowerSeries.derivative^[n - k] p * PowerSeries.derivative^[k] q) := by
  induction n with
  | zero => simp [Finset.range]
  | succ n ih =>
    calc
      PowerSeries.derivative^[n + 1] (p * q) =
          PowerSeries.derivative (∑ k ∈ range n.succ,
            n.choose k • (PowerSeries.derivative^[n - k] p *
              PowerSeries.derivative^[k] q)) := by
        rw [Function.iterate_succ_apply', ih]
      _ = (∑ k ∈ range n.succ, n.choose k •
            (PowerSeries.derivative^[n - k + 1] p *
              PowerSeries.derivative^[k] q)) +
          ∑ k ∈ range n.succ, n.choose k •
            (PowerSeries.derivative^[n - k] p *
              PowerSeries.derivative^[k + 1] q) := by
        simp only [Nat.succ_eq_add_one, map_sum, map_nsmul,
          PowerSeries.derivative.leibniz, Function.iterate_succ', Function.comp_apply]
        simp_rw [smul_add, sum_add_distrib]
        simp only [smul_eq_mul]
        rw [add_comm]
        congr 1
        apply sum_congr rfl
        intro x hx
        ring
      _ = (∑ k ∈ range n.succ, n.choose k.succ •
              (PowerSeries.derivative^[n - k] p *
                PowerSeries.derivative^[k + 1] q)) +
            1 • (PowerSeries.derivative^[n + 1] p * PowerSeries.derivative^[0] q) +
          ∑ k ∈ range n.succ, n.choose k •
            (PowerSeries.derivative^[n - k] p *
              PowerSeries.derivative^[k + 1] q) := ?_
      _ = ((∑ k ∈ range n.succ, n.choose k •
              (PowerSeries.derivative^[n - k] p *
                PowerSeries.derivative^[k + 1] q)) +
            ∑ k ∈ range n.succ, n.choose k.succ •
              (PowerSeries.derivative^[n - k] p *
                PowerSeries.derivative^[k + 1] q)) +
          1 • (PowerSeries.derivative^[n + 1] p * PowerSeries.derivative^[0] q) := by
        rw [add_comm, add_assoc]
      _ = (∑ i ∈ range n.succ, (n + 1).choose (i + 1) •
              (PowerSeries.derivative^[n + 1 - (i + 1)] p *
                PowerSeries.derivative^[i + 1] q)) +
          1 • (PowerSeries.derivative^[n + 1] p * PowerSeries.derivative^[0] q) := by
        simp_rw [Nat.choose_succ_succ, Nat.succ_sub_succ, add_smul, sum_add_distrib]
      _ = ∑ k ∈ range n.succ.succ, n.succ.choose k •
            (PowerSeries.derivative^[n.succ - k] p *
              PowerSeries.derivative^[k] q) := by
        rw [sum_range_succ' _ n.succ, Nat.choose_zero_right, tsub_zero]
    congr
    refine (sum_range_succ' _ _).trans (congr_arg₂ (fun x y => x + y) ?_ ?_)
    · rw [sum_range_succ, Nat.choose_succ_self, zero_smul, add_zero]
      refine sum_congr rfl fun k hk => ?_
      rw [mem_range] at hk
      congr
      omega
    · rw [Nat.choose_zero_right, tsub_zero]

private theorem neto_iterate_derivative_rescale_exp_mul
    (a : ℂ) (f : PowerSeries ℂ) (l : ℕ) :
    PowerSeries.derivative^[l]
        (PowerSeries.rescale a (PowerSeries.exp ℂ) * f) =
      PowerSeries.rescale a (PowerSeries.exp ℂ) *
        ∑ k ∈ range (l + 1),
          (a ^ (l - k) * (l.choose k : ℂ)) • PowerSeries.derivative^[k] f := by
  rw [neto_iterate_derivative_mul]
  simp_rw [neto_iterate_derivative_rescale_exp]
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  simp only [Algebra.smul_def, map_mul, map_natCast]
  ring

private theorem neto_normalized_coeff_exp_mul_derivative
    (a : ℂ) (f : PowerSeries ℂ) (n l : ℕ) :
    (n.factorial : ℂ) * PowerSeries.coeff n
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[l] f) =
      ∑ k ∈ range (n + 1),
        a ^ (n - k) * (n.choose k : ℂ) *
          ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f := by
  have hiter (k : ℕ) :
      PowerSeries.constantCoeff
          (PowerSeries.derivative^[k] (PowerSeries.derivative^[l] f)) =
        ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f := by
    rw [← Function.iterate_add_apply PowerSeries.derivative k l f,
      PowerSeries.constantCoeff_iterate_derivative]
    rw [add_comm]
  have hE : PowerSeries.constantCoeff
      (PowerSeries.rescale a (PowerSeries.exp ℂ)) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_rescale,
      PowerSeries.coeff_exp]
    norm_num
  calc
    (n.factorial : ℂ) * PowerSeries.coeff n
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[l] f) =
      PowerSeries.constantCoeff (PowerSeries.derivative^[n]
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[l] f)) := by
            rw [PowerSeries.constantCoeff_iterate_derivative]
    _ = PowerSeries.constantCoeff
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          ∑ k ∈ range (n + 1),
            (a ^ (n - k) * (n.choose k : ℂ)) •
              PowerSeries.derivative^[k] (PowerSeries.derivative^[l] f)) := by
          rw [neto_iterate_derivative_rescale_exp_mul]
    _ = ∑ k ∈ range (n + 1),
        a ^ (n - k) * (n.choose k : ℂ) *
          ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f := by
      rw [map_mul, hE, one_mul, map_sum]
      simp_rw [PowerSeries.constantCoeff_smul, hiter]
      simp only [smul_eq_mul, mul_assoc]

private theorem neto_evalNeg_rescale_exp (a : ℂ) :
    PowerSeries.evalNegHom (PowerSeries.rescale a (PowerSeries.exp ℂ)) =
      PowerSeries.rescale (-a) (PowerSeries.exp ℂ) := by
  ext n
  simp only [PowerSeries.evalNegHom, PowerSeries.coeff_rescale]
  rw [neg_pow]
  ring

private theorem neto_rescale_exp_evalNeg_mul (a : ℂ) :
    PowerSeries.evalNegHom (PowerSeries.rescale a (PowerSeries.exp ℂ)) *
      PowerSeries.rescale a (PowerSeries.exp ℂ) = 1 := by
  rw [neto_evalNeg_rescale_exp, mul_comm,
    PowerSeries.exp_mul_exp_eq_exp_add]
  simp

private theorem neto_reflected_exp_mul_derivative
    (a : ℂ) (f : PowerSeries ℂ) (l : ℕ)
    (href : PowerSeries.evalNegHom f =
      PowerSeries.rescale a (PowerSeries.exp ℂ) * f) :
    PowerSeries.evalNegHom
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[l] f) =
      (-1 : ℂ) ^ l •
        ∑ k ∈ range (l + 1),
          (a ^ (l - k) * (l.choose k : ℂ)) •
            PowerSeries.derivative^[k] f := by
  have hd := congrArg (fun g : PowerSeries ℂ => PowerSeries.derivative^[l] g) href
  rw [neto_iterate_derivative_evalNeg,
    neto_iterate_derivative_rescale_exp_mul] at hd
  have hrd : PowerSeries.evalNegHom (PowerSeries.derivative^[l] f) =
      (-1 : ℂ) ^ l •
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          ∑ k ∈ range (l + 1),
            (a ^ (l - k) * (l.choose k : ℂ)) •
              PowerSeries.derivative^[k] f) := by
    have h := congrArg (fun g : PowerSeries ℂ => (-1 : ℂ) ^ l • g) hd
    simpa only [smul_smul, ← pow_add, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_smul] using h
  rw [map_mul, hrd, mul_smul_comm, ← mul_assoc,
    neto_rescale_exp_evalNeg_mul, one_mul]

private theorem neto_normalized_symmetry
    (a : ℂ) (f : PowerSeries ℂ) (n l : ℕ)
    (href : PowerSeries.evalNegHom f =
      PowerSeries.rescale a (PowerSeries.exp ℂ) * f) :
    (n.factorial : ℂ) * PowerSeries.coeff n
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[l] f) =
      (-1 : ℂ) ^ (n + l) *
        ((l.factorial : ℂ) * PowerSeries.coeff l
          (PowerSeries.rescale a (PowerSeries.exp ℂ) *
            PowerSeries.derivative^[n] f)) := by
  have hc := congrArg (PowerSeries.coeff n)
    (neto_reflected_exp_mul_derivative a f l href)
  simp only [PowerSeries.evalNegHom, PowerSeries.coeff_rescale,
    PowerSeries.coeff_smul, map_sum, PowerSeries.coeff_iterate_derivative,
    smul_eq_mul] at hc
  have hcoeff :
      (-1 : ℂ) ^ n * ((n.factorial : ℂ) * PowerSeries.coeff n
        (PowerSeries.rescale a (PowerSeries.exp ℂ) *
          PowerSeries.derivative^[l] f)) =
      (-1 : ℂ) ^ l *
        ∑ k ∈ range (l + 1),
          a ^ (l - k) * (l.choose k : ℂ) *
            ((n + k).factorial : ℂ) * PowerSeries.coeff (n + k) f := by
    calc
      _ = (n.factorial : ℂ) *
          ((-1 : ℂ) ^ n * PowerSeries.coeff n
            (PowerSeries.rescale a (PowerSeries.exp ℂ) *
              PowerSeries.derivative^[l] f)) := by ring
      _ = (n.factorial : ℂ) *
          ((-1 : ℂ) ^ l *
            ∑ k ∈ range (l + 1),
              a ^ (l - k) * (l.choose k : ℂ) *
                (((n + 1).ascFactorial k : ℂ) *
                  PowerSeries.coeff (n + k) f)) := by rw [hc]
      _ = (-1 : ℂ) ^ l * ((n.factorial : ℂ) *
          ∑ k ∈ range (l + 1),
            a ^ (l - k) * (l.choose k : ℂ) *
              (((n + 1).ascFactorial k : ℂ) *
                PowerSeries.coeff (n + k) f)) := by ring
      _ = (-1 : ℂ) ^ l *
          ∑ k ∈ range (l + 1), (n.factorial : ℂ) *
            (a ^ (l - k) * (l.choose k : ℂ) *
              (((n + 1).ascFactorial k : ℂ) *
                PowerSeries.coeff (n + k) f)) := by rw [mul_sum]
      _ = _ := by
        apply congr_arg ((-1 : ℂ) ^ l * ·)
        apply sum_congr rfl
        intro k hk
        have hfac : (n.factorial : ℂ) * ((n + 1).ascFactorial k : ℂ) =
            ((n + k).factorial : ℂ) := by
          norm_cast
          exact Nat.factorial_mul_ascFactorial n k
        calc
          _ = a ^ (l - k) * (l.choose k : ℂ) *
              (((n.factorial : ℂ) * ((n + 1).ascFactorial k : ℂ)) *
                PowerSeries.coeff (n + k) f) := by ring
          _ = _ := by
            rw [hfac]
            simp only [mul_assoc]
  have hsum := hcoeff
  rw [neto_normalized_coeff_exp_mul_derivative] at hsum
  rw [neto_normalized_coeff_exp_mul_derivative,
    neto_normalized_coeff_exp_mul_derivative]
  calc
    _ = (-1 : ℂ) ^ n *
        ((-1 : ℂ) ^ n *
          ∑ k ∈ range (n + 1),
            a ^ (n - k) * (n.choose k : ℂ) *
              ((l + k).factorial : ℂ) * PowerSeries.coeff (l + k) f) := by
      rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul]
      norm_num
    _ = (-1 : ℂ) ^ n *
        ((-1 : ℂ) ^ l *
          ∑ k ∈ range (l + 1),
            a ^ (l - k) * (l.choose k : ℂ) *
              ((n + k).factorial : ℂ) * PowerSeries.coeff (n + k) f) := by
      rw [hsum]
    _ = _ := by rw [pow_add, mul_assoc]

private theorem neto_identity_nat (d n l : ℕ) :
    (∑ k ∈ range (n + 1),
      (d : ℂ) ^ (n - k) * (n.choose k : ℂ) *
        higherOrderBernoulliNumber (d : ℂ) (l + k)) =
    (-1 : ℂ) ^ (n + l) *
      ∑ k ∈ range (l + 1),
        (d : ℂ) ^ (l - k) * (l.choose k : ℂ) *
          higherOrderBernoulliNumber (d : ℂ) (n + k) := by
  simp_rw [higherOrderBernoulliNumber_nat]
  have href : PowerSeries.evalNegHom (bernoulliPowerSeries ℂ ^ d) =
      PowerSeries.rescale (d : ℂ) (PowerSeries.exp ℂ) *
        bernoulliPowerSeries ℂ ^ d := by
    rw [neto_bernoulli_power_reflection, mul_comm]
  have hs := neto_normalized_symmetry (d : ℂ)
    (bernoulliPowerSeries ℂ ^ d) n l href
  rw [neto_normalized_coeff_exp_mul_derivative,
    neto_normalized_coeff_exp_mul_derivative] at hs
  simpa only [mul_assoc] using hs

/-- **Neto's identity for higher-order Bernoulli numbers.** For every complex number $x$ and all
natural numbers $n$ and $\ell$,
$$\sum_{k=0}^{n} \binom{n}{k} x^{n-k} B_{\ell+k}^{(x)} =
(-1)^{n+\ell} \sum_{k=0}^{\ell} \binom{\ell}{k} x^{\ell-k} B_{n+k}^{(x)},$$
where $B_m^{(x)}$ is the higher-order Bernoulli number of order $x$.

Proof: The substitution coefficient formula makes both sides polynomial in the order. For natural
orders, the cited Bernoulli EGF gives the reflection identity, formal differentiation proves Neto's
formula, and equality on all natural complex points finishes the polynomial argument.

Proves `Wanted` entry `neto_higher_order_bernoulli_identity`.

Source: https://cs.uwaterloo.ca/journals/JIS/VOL23/Chellal/chellal7.tex
Identity span: lines 662-670,
text_sha256 `06790ccab662e77ae848bda8ff92dac6a404d8b43042d433d80c6dd7b127c56f`.
File sha256 `ce83119262833b8219cb7670521e7602617dae3f645a76e913bff79b7ba7dc9c`.
-/
public theorem neto_higher_order_bernoulli_identity (x : ℂ) (n ℓ : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      x ^ (n - k) * (Nat.choose n k : ℂ) * higherOrderBernoulliNumber x (ℓ + k)) =
    (-1 : ℂ) ^ (n + ℓ) *
      ∑ k ∈ Finset.range (ℓ + 1),
        x ^ (ℓ - k) * (Nat.choose ℓ k : ℂ) * higherOrderBernoulliNumber x (n + k) := by
  let P : Polynomial ℂ :=
    ∑ k ∈ range (n + 1), Polynomial.X ^ (n - k) * Polynomial.C (n.choose k : ℂ) *
      neto_higherOrderBernoulliPolynomial (ℓ + k)
  let Q : Polynomial ℂ :=
    Polynomial.C ((-1 : ℂ) ^ (n + ℓ)) *
      ∑ k ∈ range (ℓ + 1), Polynomial.X ^ (ℓ - k) *
        Polynomial.C (ℓ.choose k : ℂ) * neto_higherOrderBernoulliPolynomial (n + k)
  have hP (y : ℂ) : Polynomial.eval y P =
      ∑ k ∈ range (n + 1), y ^ (n - k) * (n.choose k : ℂ) *
        higherOrderBernoulliNumber y (ℓ + k) := by
    simp only [P, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, neto_higherOrderBernoulliPolynomial_eval]
  have hQ (y : ℂ) : Polynomial.eval y Q =
      (-1 : ℂ) ^ (n + ℓ) *
        ∑ k ∈ range (ℓ + 1), y ^ (ℓ - k) * (ℓ.choose k : ℂ) *
          higherOrderBernoulliNumber y (n + k) := by
    simp only [Q, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, neto_higherOrderBernoulliPolynomial_eval]
  have heval_nat (d : ℕ) : Polynomial.eval (d : ℂ) P = Polynomial.eval (d : ℂ) Q := by
    rw [hP, hQ]
    exact neto_identity_nat d n ℓ
  have hrange : (Set.range (fun d : ℕ => (d : ℂ))).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  have hinf : {y : ℂ | Polynomial.eval y P = Polynomial.eval y Q}.Infinite := by
    apply hrange.mono
    rintro y ⟨d, rfl⟩
    exact heval_nat d
  have hPQ : P = Q := Polynomial.eq_of_infinite_eval_eq P Q hinf
  calc
    _ = Polynomial.eval x P := (hP x).symm
    _ = Polynomial.eval x Q := congrArg (Polynomial.eval x) hPQ
    _ = _ := hQ x

end MetaMathlibExt
