/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch5Entry10bEuleriansymmetry
public import MathlibExt.Analysis.Ramanujan.Part1Ch7DirichletBeta

import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry17Bernoullipolysymmetry
import Mathlib.Analysis.Real.Pi.Leibniz
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Dirichlet beta at odd positive integers

The value of the Dirichlet beta function at each odd positive integer is expressed using
an even-index Euler number, a power of pi, and a factorial.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 3, Equation (12)
(`integers-2025-A50-prop-3`), citing its references [3], [6].
-/

namespace MetaMathlibExt

@[expose] public section

open MathlibExt.Analysis.Ramanujan.Part1Ch5.Entry10bEuleriansymmetry
open MathlibExt.Analysis.Ramanujan.Part1Ch7.DirichletBeta
open MathlibExt.Analysis.Ramanujan.Part1Ch7.Entry17Bernoullipolysymmetry
open Finset

private theorem eulerEven_recurrenceQ (m : ℕ) :
    ∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℚ) * ((chapter5EulerEven k : ℤ) : ℚ) =
      if m = 0 then 1 else 0 := by
  have h := chapter5EulerEven_recurrence m
  have h2 : ((∑ k ∈ Finset.range (m + 1),
      ((Nat.choose (2 * m) (2 * k) : ℕ) : ℤ) * chapter5EulerEven k : ℤ) : ℚ) =
      ((if m = 0 then (1 : ℤ) else 0 : ℤ) : ℚ) := by rw [h]
  rw [Int.cast_sum] at h2
  simp only [Int.cast_mul, Int.cast_natCast] at h2
  rw [h2]
  split <;> simp

private theorem sum_range_two_mul_succ (g : ℕ → ℚ) (m : ℕ)
    (hg : ∀ k, Odd k → g k = 0) :
    ∑ k ∈ Finset.range (2 * m + 1), g k = ∑ j ∈ Finset.range (m + 1), g (2 * j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by ring
    have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
    conv_lhs => rw [h1, Finset.sum_range_succ, Finset.sum_range_succ, hg _ hodd, add_zero]
    conv_rhs => rw [Finset.sum_range_succ]
    rw [ih]
    congr 1

private noncomputable def eulerEGF : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    if n % 2 = 1 then 0
    else (((chapter5EulerEven (n / 2) : ℤ) : ℚ) / (n.factorial : ℚ))

private noncomputable def coshPS : PowerSeries ℚ :=
  (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) *
    PowerSeries.C (2⁻¹ : ℚ)

private theorem coeff_eulerEGF (n : ℕ) :
    PowerSeries.coeff n eulerEGF =
      if n % 2 = 1 then 0
      else (((chapter5EulerEven (n / 2) : ℤ) : ℚ) / (n.factorial : ℚ)) := by
  simp [eulerEGF, PowerSeries.coeff_mk]

private theorem coeff_coshPS (n : ℕ) :
    PowerSeries.coeff n coshPS =
      (if n % 2 = 0 then (1 : ℚ) / (n.factorial : ℚ) else 0) := by
  unfold coshPS
  rw [PowerSeries.coeff_mul_C]
  have h1 : PowerSeries.coeff n
      (PowerSeries.exp ℚ + (PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
      (1 : ℚ) / (n.factorial : ℚ) + (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
    have e1 : PowerSeries.coeff n (PowerSeries.exp ℚ) = (1 : ℚ) / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_exp]; simp
    have e2 : PowerSeries.coeff n ((PowerSeries.rescale (-1)) (PowerSeries.exp ℚ)) =
        (-1 : ℚ) ^ n / (n.factorial : ℚ) := by
      rw [PowerSeries.coeff_rescale, PowerSeries.coeff_exp]
      simp [div_eq_mul_inv]
    rw [map_add, e1, e2]
  rw [h1]
  by_cases hn : n % 2 = 0
  · have hpow : (-1 : ℚ) ^ n = 1 := Even.neg_one_pow (Nat.even_iff.mpr hn)
    simp [hn, hpow]
    field_simp
    ring
  · have hodd : (-1 : ℚ) ^ n = -1 := Odd.neg_one_pow (Nat.odd_iff.mpr (by omega))
    simp only [hn, hodd, ↓reduceIte]
    have hfact : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    field_simp
    ring

private theorem euler_cosh : eulerEGF * coshPS = 1 := by
  ext n
  have hant : (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n,
        PowerSeries.coeff p.1 eulerEGF * PowerSeries.coeff p.2 coshPS) =
      ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k eulerEGF * PowerSeries.coeff (n - k) coshPS := by
    have h := Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => PowerSeries.coeff i eulerEGF * PowerSeries.coeff j coshPS) n
    simpa using h
  rw [PowerSeries.coeff_mul, hant, PowerSeries.coeff_one]
  by_cases hn : n % 2 = 1
  · have hn0 : n ≠ 0 := by omega
    simp only [hn0, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_range] at hk
    have hkle : k ≤ n := by omega
    by_cases hk2 : k % 2 = 1
    · rw [coeff_eulerEGF, ite_eq_left hk2, zero_mul]
    · have hnk : (n - k) % 2 = 1 := by omega
      have hne : ¬ ((n - k) % 2 = 0) := by omega
      rw [coeff_coshPS, ite_eq_right hne, mul_zero]
  · have hn0 : n % 2 = 0 := by omega
    have hn2 : n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even (Nat.even_iff.mpr hn0)).symm
    have hfact_n : ((n.factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hsum : ∑ k ∈ Finset.range (n + 1),
          PowerSeries.coeff k eulerEGF * PowerSeries.coeff (n - k) coshPS =
        ∑ j ∈ Finset.range (n / 2 + 1),
          PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (n - 2 * j) coshPS := by
      have hnr : n + 1 = 2 * (n / 2) + 1 := by omega
      rw [hnr]
      apply sum_range_two_mul_succ
      intro k hkodd
      rw [coeff_eulerEGF, ite_eq_left (Nat.odd_iff.mp hkodd), zero_mul]
    rw [hsum]
    have hterm : ∀ j ∈ Finset.range (n / 2 + 1),
        PowerSeries.coeff (2 * j) eulerEGF * PowerSeries.coeff (n - 2 * j) coshPS =
        (((Nat.choose n (2 * j) : ℕ) : ℚ) * ((chapter5EulerEven j : ℤ) : ℚ)) /
          (n.factorial : ℚ) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hjn : 2 * j ≤ n := by omega
      have hj2 : (2 * j) / 2 = j := by omega
      have hmod1 : ¬ ((2 * j) % 2 = 1) := by omega
      have hmod2 : (n - 2 * j) % 2 = 0 := by omega
      rw [coeff_eulerEGF, ite_eq_right hmod1, coeff_coshPS, ite_eq_left hmod2, hj2]
      have hchoose := Nat.choose_mul_factorial_mul_factorial hjn
      have hcast : ((Nat.choose n (2 * j) : ℕ) : ℚ) * (((2 * j).factorial : ℕ) : ℚ) *
          (((n - 2 * j).factorial : ℕ) : ℚ) = ((n.factorial : ℕ) : ℚ) := by
        exact_mod_cast hchoose
      have hd1 : (((2 * j).factorial : ℕ) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (2 * j)
      have hd2 : ((((n - 2 * j).factorial : ℕ)) : ℚ) ≠ 0 := by
        exact_mod_cast Nat.factorial_ne_zero (n - 2 * j)
      have hAB : ((((2 * j).factorial : ℕ) : ℚ) * ((((n - 2 * j).factorial : ℕ)) : ℚ)) ≠ 0 :=
        mul_ne_zero hd1 hd2
      rw [div_mul_div_comm, mul_one, div_eq_div_iff hAB hfact_n]
      linear_combination -((chapter5EulerEven j : ℤ) : ℚ) * hcast
    rw [Finset.sum_congr rfl hterm]
    rw [← Finset.sum_div]
    have hrec := eulerEven_recurrenceQ (n / 2)
    rw [← hn2] at hrec
    by_cases hm : n / 2 = 0
    · have hn00 : n = 0 := by omega
      subst hn00
      simp only [Nat.zero_div, zero_add, range_one, sum_singleton, mul_zero,
        Nat.choose_self, Nat.cast_one, one_mul, Nat.factorial_zero, div_one,
        ↓reduceIte, Rat.intCast_eq_one_iff] at hrec ⊢
      rw [hrec]
    · have hn00 : n ≠ 0 := by omega
      simp only [hm, hn00, ↓reduceIte] at hrec ⊢
      rw [hrec]
      simp

private noncomputable def bq (t : ℚ) : PowerSeries ℚ :=
  PowerSeries.rescale 4 (PowerSeries.mk fun n =>
    Polynomial.aeval t ((1 / (n.factorial : ℚ)) • Polynomial.bernoulli n))
private lemma bq_coeff (t : ℚ) (n : ℕ) :
    PowerSeries.coeff n (bq t) = 4 ^ n * (Polynomial.bernoulli n).eval t / n.factorial := by
  simp [bq, Polynomial.aeval_def]
  ring
private lemma bq_rel (t : ℚ) :
    bq t * (PowerSeries.exp ℚ ^ 4 - 1) =
      4 * PowerSeries.X * PowerSeries.rescale (t * 4) (PowerSeries.exp ℚ) := by
  have h := congrArg (PowerSeries.rescale (4 : ℚ))
    (Polynomial.bernoulli_generating_function t)
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_rescale,
    PowerSeries.rescale_X] at h
  simpa only [bq, PowerSeries.exp_pow_eq_rescale_exp, Nat.cast_ofNat,
    map_ofNat] using h
private lemma bq_odd (n : ℕ) :
    PowerSeries.coeff n (bq (3 / 4)) = (-1 : ℚ) ^ n * PowerSeries.coeff n (bq (1 / 4)) := by
  rw [bq_coeff, bq_coeff]
  have h := Polynomial.bernoulli_eval_one_sub n (1 / 4)
  norm_num only at h
  rw [h]
  ring
private noncomputable def bEuler : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    -(PowerSeries.coeff (n + 1) (bq (1 / 4)) - PowerSeries.coeff (n + 1) (bq (3 / 4))) / 2
private lemma X_bEuler :
    PowerSeries.X * bEuler = -(bq (1 / 4) - bq (3 / 4)) * PowerSeries.C (1 / 2) := by
  ext n
  cases n with
  | zero =>
    rw [PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_mul_C, map_neg, map_sub,
      bq_coeff, bq_coeff]
    simp
  | succ n => simp [PowerSeries.coeff_succ_X_mul, bEuler, PowerSeries.coeff_mul_C]; ring
private lemma exp_ne : PowerSeries.exp ℚ ^ 4 - 1 ≠ 0 := by
  intro h
  have hc := congrArg (PowerSeries.coeff 1) h
  simp [PowerSeries.exp_pow_eq_rescale_exp, PowerSeries.coeff_rescale,
    PowerSeries.coeff_exp] at hc
private lemma bEuler_cosh : bEuler * coshPS = 1 := by
  have h1 := bq_rel (1 / 4)
  have h3 := bq_rel (3 / 4)
  norm_num only at h1 h3
  simp only [PowerSeries.rescale_one, RingHom.id_apply] at h1
  have hp3 : PowerSeries.exp ℚ ^ 3 = PowerSeries.rescale (3 : ℚ) (PowerSeries.exp ℚ) := by
    simpa using PowerSeries.exp_pow_eq_rescale_exp (A := ℚ) 3
  rw [← hp3] at h3
  have hprod : PowerSeries.exp ℚ * PowerSeries.rescale (-1) (PowerSeries.exp ℚ) = 1 := by
    have h := PowerSeries.exp_mul_exp_eq_exp_add (A := ℚ) 1 (-1)
    simpa using h
  have hE : (bq (1 / 4) - bq (3 / 4)) *
      (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) =
      -4 * PowerSeries.X := by
    apply mul_right_cancel₀ exp_ne
    calc
      _ = (4 * PowerSeries.X * (PowerSeries.exp ℚ - PowerSeries.exp ℚ ^ 3)) *
          (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) := by
        linear_combination (PowerSeries.exp ℚ +
          PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) * (h1 - h3)
      _ = _ := by
        linear_combination 4 * PowerSeries.X * (1 - PowerSeries.exp ℚ ^ 2) * hprod
  apply mul_left_cancel₀ (PowerSeries.X_ne_zero (R := ℚ))
  rw [← mul_assoc, X_bEuler]
  unfold coshPS
  have hc : PowerSeries.C (1 / 2 : ℚ) * PowerSeries.C (2⁻¹ : ℚ) =
      PowerSeries.C (1 / 4 : ℚ) := by rw [← map_mul]; norm_num
  calc
    _ = -(bq (1 / 4) - bq (3 / 4)) *
        (PowerSeries.exp ℚ + PowerSeries.rescale (-1) (PowerSeries.exp ℚ)) *
        PowerSeries.C (1 / 4) := by rw [← hc]; ring
    _ = _ := by
      rw [neg_mul, hE]
      simp only [neg_mul, neg_neg]
      have hfour : (4 : PowerSeries ℚ) * PowerSeries.C (1 / 4 : ℚ) = 1 := by
        rw [← map_ofNat PowerSeries.C 4, ← map_mul]
        norm_num
      rw [mul_right_comm (4 : PowerSeries ℚ), hfour, one_mul, mul_one]
private lemma euler_bernoulli (m : ℕ) :
    (chapter5EulerEven m : ℚ) =
      -(4 : ℚ) ^ (2 * m + 1) * (Polynomial.bernoulli (2 * m + 1)).eval (1 / 4) /
        (2 * m + 1) := by
  have hc : coshPS ≠ 0 := by
    intro h
    have hh := euler_cosh
    rw [h, mul_zero] at hh
    exact zero_ne_one hh
  have he : eulerEGF = bEuler := mul_right_cancel₀ hc (euler_cosh.trans bEuler_cosh.symm)
  have h := congrArg (PowerSeries.coeff (2 * m)) he
  rw [coeff_eulerEGF] at h
  have hmod : ¬ (2 * m % 2 = 1) := by omega
  have hdiv : 2 * m / 2 = m := by omega
  rw [ite_eq_right hmod, hdiv] at h
  simp only [bEuler, PowerSeries.coeff_mk, bq_odd] at h
  have hodd : Odd (2 * m + 1) := ⟨m, by ring⟩
  rw [hodd.neg_one_pow] at h
  rw [bq_coeff] at h
  have hf : ((2 * m).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * m)
  have hn : (2 * m + 1 : ℚ) ≠ 0 := by positivity
  have hfac : ((2 * m + 1).factorial : ℚ) =
      (2 * m + 1 : ℚ) * ((2 * m).factorial : ℚ) := by
    rw [Nat.factorial_succ]; push_cast; rfl
  rw [hfac] at h
  field_simp at h ⊢
  linear_combination (1 / 2 : ℚ) * h

private lemma addChar_one : ZMod.stdAddChar (1 : ZMod 4) = Complex.I := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rw [show (1 : ZMod 4).val = 1 by decide]
  norm_num
  convert Complex.exp_pi_div_two_mul_I using 1
  congr 1
  ring
private lemma addChar_three : ZMod.stdAddChar (3 : ZMod 4) = -Complex.I := by
  rw [show (3 : ZMod 4) = -1 by decide, AddChar.map_neg_eq_inv, addChar_one, Complex.inv_I]
private lemma betaChar_exp (a : ZMod 4) :
    chapter7BetaCharacter a = (ZMod.stdAddChar a - ZMod.stdAddChar (-a)) / (2 * Complex.I) := by
  have h : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 :=
    (by decide : ∀ a : ZMod 4, a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3) a
  rcases h with rfl | rfl | rfl | rfl
  · simp
  · rw [betaChar1, show (-1 : ZMod 4) = 3 by decide, addChar_one, addChar_three]
    field_simp
    ring
  · rw [betaChar2, show (-2 : ZMod 4) = 2 by decide, sub_self, zero_div]
  · rw [betaChar3, show (-3 : ZMod 4) = 1 by decide, addChar_one, addChar_three]
    field_simp
    ring
private lemma beta_eq_sin (s : ℂ) :
    chapter7DirichletBeta s = HurwitzZeta.sinZeta ((1 / 4 : ℝ) : UnitAddCircle) s := by
  have h1 := ZMod.LFunction_stdAddChar_eq_expZeta (1 : ZMod 4) s (Or.inl (by decide))
  have h3 := ZMod.LFunction_stdAddChar_eq_expZeta (3 : ZMod 4) s (Or.inl (by decide))
  have hc1 : ZMod.toAddCircle (1 : ZMod 4) = ((1 / 4 : ℝ) : UnitAddCircle) := by
    rw [ZMod.toAddCircle_apply, show (1 : ZMod 4).val = 1 by decide]; norm_num
  have hc3 : ZMod.toAddCircle (3 : ZMod 4) = -((1 / 4 : ℝ) : UnitAddCircle) := by
    rw [show (3 : ZMod 4) = -1 by decide, map_neg, hc1]
  rw [hc1] at h1
  rw [hc3] at h3
  rw [HurwitzZeta.sinZeta_eq, ← h1, ← h3]
  unfold chapter7DirichletBeta ZMod.LFunction
  have hthree (a : ZMod 4) : 3 * a = -a := by
    rw [show (3 : ZMod 4) = -1 by decide]
    ring
  simp only [one_mul, hthree]
  simp_rw [betaChar_exp, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  ring
private lemma beta_signed (m : ℕ) (hm : m ≠ 0) :
    chapter7DirichletBeta (2 * m + 1) =
      (Real.pi : ℂ) ^ (2 * m + 1) * ((-1 : ℂ) ^ m * (chapter5EulerEven m : ℂ)) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ)) := by
  have hB : ((Polynomial.bernoulli (2 * m + 1)).map (algebraMap ℚ ℂ)).eval
      ((1 / 4 : ℝ) : ℂ) = (((Polynomial.bernoulli (2 * m + 1)).eval (1 / 4 : ℚ) : ℚ) : ℂ) := by
    rw [Polynomial.eval_map]
    have hq : ((1 / 4 : ℝ) : ℂ) = algebraMap ℚ ℂ (1 / 4 : ℚ) := by norm_num
    rw [hq, Polynomial.eval₂_at_apply]
    simp
  have he := congrArg ((↑) : ℚ → ℂ) (euler_bernoulli m)
  push_cast at he
  have hf4 : (4 : ℂ) ^ (2 * m + 1) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hfact : (((2 * m).factorial : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * m)
  have hn : (2 * (m : ℂ) + 1) ≠ 0 := by
    exact_mod_cast (show (2 * m + 1 : ℕ) ≠ 0 by omega)
  have hb : (((Polynomial.bernoulli (2 * m + 1)).eval (1 / 4 : ℚ) : ℚ) : ℂ) =
      -((2 * (m : ℂ) + 1) * (chapter5EulerEven m : ℂ)) / (4 : ℂ) ^ (2 * m + 1) := by
    apply (eq_div_iff hf4).mpr
    have he' := (eq_div_iff hn).mp he
    linear_combination he'
  rw [beta_eq_sin, HurwitzZeta.sinZeta_two_mul_nat_add_one hm
    (by constructor <;> norm_num), hB, hb]
  have hfac : (((2 * m + 1).factorial : ℕ) : ℂ) =
      (2 * (m : ℂ) + 1) * ((2 * m).factorial : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; rfl
  have hp4 : (4 : ℂ) ^ (2 * m + 1) =
      (2 : ℂ) ^ (2 * m + 1) * (2 : ℂ) ^ (2 * m + 1) := by
    rw [show (4 : ℂ) = 2 * 2 by norm_num, mul_pow]
  have hexp : 2 * m + 2 = (2 * m + 1) + 1 := by omega
  rw [hfac, mul_pow, hp4, pow_succ (-1 : ℂ), hexp, pow_succ (2 : ℂ)]
  field_simp
  ring

private lemma beta_hurwitz (s : ℂ) :
    chapter7DirichletBeta s = 2 * (4 : ℂ) ^ (-s) *
      HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle) s := by
  rw [chapter7DirichletBeta, ZMod.LFunction_def_odd betaCharOdd, betaCharUnivFour]
  rw [Finset.sum_insert (by decide : (0 : ZMod 4) ∉
      ({(1 : ZMod 4), 2, 3} : Finset (ZMod 4))),
    Finset.sum_insert (by decide : (1 : ZMod 4) ∉ ({(2 : ZMod 4), 3} : Finset (ZMod 4))),
    Finset.sum_insert (by decide : (2 : ZMod 4) ∉ ({(3 : ZMod 4)} : Finset (ZMod 4))),
    Finset.sum_singleton]
  simp only [
    betaChar0, betaChar1, betaChar2, betaChar3, zero_mul, one_mul, neg_one_mul, zero_add,
    Nat.cast_ofNat]
  have hc1 : ZMod.toAddCircle (1 : ZMod 4) = ((1 / 4 : ℝ) : UnitAddCircle) := by
    rw [ZMod.toAddCircle_apply, show (1 : ZMod 4).val = 1 by decide]; norm_num
  have hc3 : ZMod.toAddCircle (3 : ZMod 4) = -((1 / 4 : ℝ) : UnitAddCircle) := by
    rw [show (3 : ZMod 4) = -1 by decide, map_neg, hc1]
  rw [hc1, hc3, HurwitzZeta.hurwitzZetaOdd_neg]
  ring
private lemma beta_nonneg (m : ℕ) (hm : m ≠ 0) :
    0 ≤ (chapter7DirichletBeta (2 * m + 1)).re := by
  have hs : 1 < (((2 * m + 1 : ℕ) : ℂ)).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast (show 1 < 2 * m + 1 by omega)
  have hh := HurwitzZeta.hasSum_nat_hurwitzZetaOdd_of_mem_Icc
    (a := (1 / 4 : ℝ)) (by constructor <;> norm_num) hs
  have hn : 0 ≤ (HurwitzZeta.hurwitzZetaOdd ((1 / 4 : ℝ) : UnitAddCircle)
      ((2 * m + 1 : ℕ) : ℂ)).re := by
    apply HasSum.nonneg _ (Complex.hasSum_re hh)
    intro n
    have he :
        ((1 / ((n : ℂ) + ((1 / 4 : ℝ) : ℂ)) ^ ((2 * m + 1 : ℕ) : ℂ) -
          1 / ((n : ℂ) + 1 - ((1 / 4 : ℝ) : ℂ)) ^ ((2 * m + 1 : ℕ) : ℂ)) / 2).re =
        (1 / ((n : ℝ) + 1 / 4) ^ (2 * m + 1) -
          1 / ((n : ℝ) + 3 / 4) ^ (2 * m + 1)) / 2 := by
      rw [Complex.cpow_natCast, Complex.cpow_natCast]
      have hthree : (n : ℂ) + 1 - ((1 / 4 : ℝ) : ℂ) =
          (((n : ℝ) + 3 / 4 : ℝ) : ℂ) := by push_cast; ring
      rw [hthree]
      norm_cast
    rw [he]
    apply div_nonneg _ (by norm_num)
    apply sub_nonneg.mpr
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpow : (4 : ℂ) ^ (-((2 * m + 1 : ℕ) : ℂ)) =
      ((1 / (4 : ℝ) ^ (2 * m + 1) : ℝ) : ℂ) := by
    rw [Complex.cpow_neg, Complex.cpow_natCast]
    norm_num [Complex.ofReal_inv, Complex.ofReal_pow]
  have hcast : (2 * (m : ℂ) + 1) = ((2 * m + 1 : ℕ) : ℂ) := by simp
  rw [hcast, beta_hurwitz, hpow]
  have hreal : (2 : ℂ) * ((1 / (4 : ℝ) ^ (2 * m + 1) : ℝ) : ℂ) =
      ((2 * (1 / (4 : ℝ) ^ (2 * m + 1)) : ℝ) : ℂ) := by push_cast; rfl
  rw [hreal, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg (by positivity) hn

private lemma beta_one : chapter7DirichletBeta 1 = (Real.pi : ℂ) / 4 := by
  have hb := ramanujan_part1_ch7_entry17_bernoullipolysymmetry.2.1 1 (by simp)
  have hp := Complex.continuous_ofReal.tendsto (Real.pi / 4) |>.comp Real.tendsto_sum_pi_div_four
  have hsum : chapter7DirichletBetaPartialSum 1 =
      fun N => ((∑ i ∈ Finset.range N, (-1 : ℝ) ^ i / (2 * (i : ℝ) + 1) : ℝ) : ℂ) := by
    funext N
    simp [chapter7DirichletBetaPartialSum, chapter7DirichletBetaTerm, Complex.cpow_one,
      Complex.ofReal_sum, Complex.ofReal_div, Complex.ofReal_pow]
  rw [hsum] at hb
  simpa using tendsto_nhds_unique hb hp
private lemma euler_abs (m : ℕ) (hm : m ≠ 0) :
    (-1 : ℂ) ^ m * (chapter5EulerEven m : ℂ) = ((|chapter5EulerEven m| : ℤ) : ℂ) := by
  have heq : (chapter7DirichletBeta (2 * m + 1)).re =
      Real.pi ^ (2 * m + 1) * ((-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ)) := by
    rw [beta_signed m hm]
    have hc : (Real.pi : ℂ) ^ (2 * m + 1) * ((-1 : ℂ) ^ m * (chapter5EulerEven m : ℂ)) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ)) =
        ((Real.pi ^ (2 * m + 1) * ((-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)) /
          (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ)) : ℝ) : ℂ) := by
      push_cast
      rfl
    rw [hc]
    rfl
  have hcoeff : 0 < Real.pi ^ (2 * m + 1) /
      (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ)) := by positivity
  have hnonneg : 0 ≤ (Real.pi ^ (2 * m + 1) /
      (2 ^ (2 * m + 2) * ((2 * m).factorial : ℝ))) *
      ((-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)) := by
    have h := beta_nonneg m hm
    rw [heq] at h
    convert h using 1
    ring
  have hs := (mul_nonneg_iff_of_pos_left hcoeff).mp hnonneg
  have habs : |(-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ)| = |(chapter5EulerEven m : ℝ)| := by
    rw [abs_mul, abs_pow]
    simp
  have hr : (-1 : ℝ) ^ m * (chapter5EulerEven m : ℝ) = ((|chapter5EulerEven m| : ℤ) : ℝ) := by
    rw [Int.cast_abs, ← habs, abs_of_nonneg hs]
  have h := congrArg Complex.ofReal hr
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_one, Complex.ofReal_intCast] using h

/-- **Dirichlet beta at odd positive integers.** Let $\beta$ be the Dirichlet $L$-function of the
nontrivial character modulo $4$, which for $\operatorname{Re} s > 1$ is the series
$\beta(s) = \sum_{n \ge 1} (-1)^{n-1}/(2n-1)^s$, and let $E_0 = 1, E_2 = -1, E_4 = 5,
E_6 = -61, \dots$ be the even-index Euler numbers. Then for every natural number $m$,
$$\beta(2m+1) = \frac{\pi^{2m+1} \, |E_{2m}|}{2^{2m+2} \, (2m)!}.$$

For example $\beta(1) = \pi/4$, $\beta(3) = \pi^3/32$, $\beta(5) = 5\pi^5/1536$ and
$\beta(7) = 61\pi^7/184320$. With $k = 2m+2$ this is the source's Equation (12),
$\beta(k-1) = (\pi/2)^{k-1} |E_{k-2}| / (2 (k-2)!)$ for even $k \ge 2$. At $s = 1$ the series
converges only conditionally, and its sum is the value of the $L$-function there.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 3, Equation (12)
(`integers-2025-A50-prop-3`), citing its references [3], [6]. -/
public theorem dirichletBeta_two_mul_add_one (m : ℕ) :
    chapter7DirichletBeta (2 * m + 1) =
      (Real.pi : ℂ) ^ (2 * m + 1) * ((|chapter5EulerEven m| : ℤ) : ℂ) /
        (2 ^ (2 * m + 2) * ((2 * m).factorial : ℂ)) := by
  rcases eq_or_ne m 0 with rfl | hm
  · norm_num [chapter5EulerEven_zero]
    exact beta_one
  · rw [beta_signed m hm, euler_abs m hm]

end

end MetaMathlibExt
