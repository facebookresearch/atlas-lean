/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry16Tanseries
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Polynomial.Smeval
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.RingTheory.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry16Tan

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry16LogTerm (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log |2 * Real.sin x|

def chapter9SineFourierTwoTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  Real.sin (2 * (k : ℝ) * x) / ((k : ℝ) ^ 2)

private lemma aux_sin_ne_zero (x : ℝ) (hx : |x| ≤ Real.pi / 2) (hx0 : x ≠ 0) :
    Real.sin x ≠ 0 := by
  intro hs
  rw [Real.sin_eq_zero_iff] at hs
  obtain ⟨n, hn⟩ := hs
  have hpi : (0:ℝ) < Real.pi := Real.pi_pos
  have hle2 : |(n : ℝ)| * Real.pi ≤ Real.pi / 2 := by
    have h := hx
    rw [← hn, abs_mul, abs_of_pos hpi] at h
    exact h
  have hn_abs : |(n : ℝ)| ≤ 1 / 2 := by nlinarith [hpi, hle2]
  have hlt : |(n : ℝ)| < 1 := lt_of_le_of_lt hn_abs (by norm_num)
  have h2 : |n| < (1:ℤ) := by exact_mod_cast hlt
  have hn0 : n = 0 := Int.abs_lt_one_iff.mp h2
  subst hn0
  rw [Int.cast_zero, zero_mul] at hn
  exact hx0 hn.symm

private lemma aux_pos (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    (x ≠ 0 → 0 < |2 * Real.sin x|) := by
  intro hx0
  have hs := aux_sin_ne_zero x hx hx0
  have h1 : (0:ℝ) < |Real.sin x| := abs_pos.mpr hs
  have h2 : |2 * Real.sin x| = 2 * |Real.sin x| := by
    rw [abs_mul, abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  rw [h2]
  linarith

private lemma aux_summable_inv_sq_succ :
    Summable (fun n : ℕ => (1:ℝ) / (((n : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1:ℝ) / ((n : ℝ) ^ 2)) :=
    Real.summable_one_div_nat_pow (p := 2) |>.mpr (by norm_num)
  have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1:ℝ) / ((n : ℝ) ^ 2)) 1).mpr h
  simpa [Nat.cast_add, Nat.cast_one] using h2

private lemma aux_central_abs (x : ℝ) (k : ℕ) :
    |Entry16Tanseries.chapter9CentralSineTerm x k| ≤ (1:ℝ) / ((((k : ℝ) + 1)) ^ 2) := by
  have hC : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2:ℝ) ^ (2 * k) := by
    have h := Nat.choose_le_two_pow (2 * k) k
    exact_mod_cast h
  have hs1 : |Real.sin x| ^ (2 * k + 1) ≤ (1:ℝ) :=
    pow_le_one₀ (abs_nonneg _) (Real.abs_sin_le_one x)
  have h2k1 : (0:ℝ) < (((2 * k + 1 : ℕ)) : ℝ) := by
    have hkk : 0 < 2 * k + 1 := Nat.succ_pos _
    exact_mod_cast hkk
  have hE : (0:ℝ) < (2:ℝ) ^ (2 * k) := by positivity
  have hD : (0:ℝ) < (2:ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ)) : ℝ) ^ 2 :=
    mul_pos hE (pow_pos h2k1 2)
  have hnum : ((Nat.choose (2 * k) k : ℕ) : ℝ) * |Real.sin x| ^ (2 * k + 1) ≤
      (2:ℝ) ^ (2 * k) := by
    calc ((Nat.choose (2 * k) k : ℕ) : ℝ) * |Real.sin x| ^ (2 * k + 1)
        ≤ (2:ℝ) ^ (2 * k) * 1 :=
          mul_le_mul hC hs1 (pow_nonneg (abs_nonneg _) _) (by positivity)
      _ = (2:ℝ) ^ (2 * k) := mul_one _
  have hterm : |Entry16Tanseries.chapter9CentralSineTerm x k| =
      (((Nat.choose (2 * k) k : ℕ) : ℝ) * |Real.sin x| ^ (2 * k + 1)) /
        ((2:ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    unfold Entry16Tanseries.chapter9CentralSineTerm
    rw [abs_div, abs_mul, abs_pow, abs_of_nonneg (Nat.cast_nonneg _),
      abs_of_pos hD]
  have hM : (0:ℝ) < ((((2 * k + 1 : ℕ))) : ℝ) ^ 2 := pow_pos h2k1 2
  have hcast : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k:ℝ) + 1 := by push_cast; ring
  rw [hterm]
  calc (((Nat.choose (2 * k) k : ℕ) : ℝ) * |Real.sin x| ^ (2 * k + 1)) /
        ((2:ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ))) : ℝ) ^ 2)
      = (((Nat.choose (2 * k) k : ℕ) : ℝ) * |Real.sin x| ^ (2 * k + 1) /
        (2:ℝ) ^ (2 * k)) / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2 := by
        rw [div_div]
    _ ≤ 1 / ((((2 * k + 1 : ℕ))) : ℝ) ^ 2 := by
        rw [div_le_iff₀ hM, div_mul_cancel₀ _ (ne_of_gt hM)]
        exact (div_le_one hE).mpr hnum
    _ ≤ 1 / (((k : ℝ) + 1) ^ 2) := by
        apply one_div_le_one_div_of_le (by positivity)
        apply pow_le_pow_left₀ (by positivity)
        rw [hcast]
        have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith

private lemma aux_fourier_abs (x : ℝ) (j : ℕ) :
    |chapter9SineFourierTwoTerm x j| ≤ (1:ℝ) / ((((j : ℝ) + 1)) ^ 2) := by
  have hK : (0:ℝ) < ((((j + 1 : ℕ))) : ℝ) := by
    have hjj : 0 < j + 1 := Nat.succ_pos j
    exact_mod_cast hjj
  have hK2 : (0:ℝ) < ((((j + 1 : ℕ))) : ℝ) ^ 2 := pow_pos hK 2
  have hterm : chapter9SineFourierTwoTerm x j =
      Real.sin (2 * ((((j + 1 : ℕ))) : ℝ) * x) / ((((j + 1 : ℕ))) : ℝ) ^ 2 := rfl
  have hcast : ((((j + 1 : ℕ))) : ℝ) = ((j : ℝ) + 1) := by push_cast; ring
  rw [hterm, abs_div, abs_of_pos hK2]
  calc |Real.sin (2 * ((((j + 1 : ℕ))) : ℝ) * x)| / ((((j + 1 : ℕ))) : ℝ) ^ 2
      ≤ 1 / ((((j + 1 : ℕ))) : ℝ) ^ 2 := by
        rw [div_le_iff₀ hK2, div_mul_cancel₀ _ (ne_of_gt hK2)]
        exact Real.abs_sin_le_one _
    _ = 1 / (((j : ℝ) + 1) ^ 2) := by rw [hcast]

private lemma aux_summable_central (x : ℝ) : Summable (Entry16Tanseries.chapter9CentralSineTerm x) :=
  Summable.of_abs (aux_summable_inv_sq_succ.of_nonneg_of_le
    (fun _ => abs_nonneg _) (fun k => aux_central_abs x k))

private lemma aux_summable_fourier (x : ℝ) : Summable (chapter9SineFourierTwoTerm x) :=
  Summable.of_abs (aux_summable_inv_sq_succ.of_nonneg_of_le
    (fun _ => abs_nonneg _) (fun j => aux_fourier_abs x j))

private lemma chap9_choose_div_pow_le_one (n : ℕ) :
    (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n) ≤ 1 := by
  have hpos : (0 : ℝ) < 2 ^ (2 * n) := by positivity
  rw [div_le_one hpos]
  have h := Nat.choose_le_two_pow (2 * n) n
  have hcast : (Nat.choose (2 * n) n : ℝ) ≤ ((2 ^ (2 * n) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hcast
  linarith

private lemma chap9_aux_summable :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr h
  have hcongr : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
      (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext k
    rw [Nat.cast_add, Nat.cast_one]
  rwa [hcongr]

private lemma chap9_cast_two_mul_add_one (k : ℕ) :
    (((2 * k + 1 : ℕ)) : ℝ) = 2 * (k : ℝ) + 1 := by
  push_cast
  ring

private lemma chap9_norm_term_le (t : ℝ) (ht : ‖t‖ ≤ 1) (k : ℕ) :
    ‖(Nat.choose (2 * k) k : ℝ) * t ^ (2 * k + 1) /
        ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖ ≤
      (1 : ℝ) / (((k : ℝ) + 1) ^ 2) := by
  have hMpos : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    positivity
  have hDpos : (0 : ℝ) < (2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    positivity
  rw [norm_div, norm_mul, norm_mul]
  have hchoose : ‖(Nat.choose (2 * k) k : ℝ)‖ = (Nat.choose (2 * k) k : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg _)
  have hpow2 : ‖((2 : ℝ) ^ (2 * k))‖ = (2 : ℝ) ^ (2 * k) :=
    abs_of_nonneg (by positivity)
  have hsq : ‖(((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖ = ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
    abs_of_nonneg (by positivity)
  rw [hchoose, norm_pow, hpow2, hsq]
  have hc : (Nat.choose (2 * k) k : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    have h2pos : (0 : ℝ) < 2 ^ (2 * k) := by positivity
    have h := chap9_choose_div_pow_le_one k
    rwa [div_le_one h2pos] at h
  have ht2 : ‖t‖ ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (norm_nonneg _) ht
  have hnum : (Nat.choose (2 * k) k : ℝ) * ‖t‖ ^ (2 * k + 1) ≤
      (2 : ℝ) ^ (2 * k) * 1 :=
    mul_le_mul hc ht2 (by positivity) (by positivity)
  have hbase : (((k : ℝ) + 1) ^ 2) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    rw [chap9_cast_two_mul_add_one]
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hqpos : (0 : ℝ) < (((k : ℝ) + 1) ^ 2) := by positivity
  calc (Nat.choose (2 * k) k : ℝ) * ‖t‖ ^ (2 * k + 1) /
          ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
        ≤ ((2 : ℝ) ^ (2 * k) * 1) / ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) :=
          (div_le_div_iff_of_pos_right hDpos).mpr hnum
      _ = 1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
          field_simp
      _ ≤ 1 / (((k : ℝ) + 1) ^ 2) :=
          one_div_le_one_div_of_le hqpos hbase

private lemma chap9_cosSeries_summable (x : ℝ) :
    Summable (fun k : ℕ => (Nat.choose (2 * k) k : ℝ) * Real.cos x ^ (2 * k + 1) /
      ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))) := by
  have hcos : ‖Real.cos x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one x
  have h : Summable (fun k : ℕ => ‖(Nat.choose (2 * k) k : ℝ) * Real.cos x ^ (2 * k + 1) /
      ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => chap9_norm_term_le _ hcos k) chap9_aux_summable
  exact Summable.of_norm h

private lemma chap9_sinSeries_summable (x : ℝ) :
    Summable (fun k : ℕ => (Nat.choose (2 * k) k : ℝ) * Real.sin x ^ (2 * k + 1) /
      ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))) := by
  have hsin : ‖Real.sin x‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_sin_le_one x
  have h : Summable (fun k : ℕ => ‖(Nat.choose (2 * k) k : ℝ) * Real.sin x ^ (2 * k + 1) /
      ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => chap9_norm_term_le _ hsin k) chap9_aux_summable
  exact Summable.of_norm h

private def chap9Fcoeff (n : ℕ) : ℝ := (Nat.choose (2 * n) n : ℝ) / (2 : ℝ) ^ (2 * n)

private lemma chap9Fcoeff_nonneg (n : ℕ) : 0 ≤ chap9Fcoeff n := by
  unfold chap9Fcoeff
  positivity

private lemma chap9Fcoeff_le_one (n : ℕ) : chap9Fcoeff n ≤ 1 :=
  chap9_choose_div_pow_le_one n

private def chap9G (t : ℝ) : ℝ :=
  ∑' n : ℕ, chap9Fcoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)

private def chap9F (t : ℝ) : ℝ :=
  ∑' n : ℕ, chap9Fcoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2

private lemma chap9_cast_centralBinom (n : ℕ) :
    ((n : ℝ) + 1) * ((Nat.choose (2 * (n + 1)) (n + 1) : ℕ) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * ((Nat.choose (2 * n) n : ℕ) : ℝ) := by
  have h := Nat.succ_mul_centralBinom_succ n
  have hcast : ((n + 1 : ℕ) : ℝ) * ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
      = 2 * ((2 * n + 1 : ℕ) : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [show Nat.centralBinom (n + 1) = Nat.choose (2 * (n + 1)) (n + 1) from rfl,
    show Nat.centralBinom n = Nat.choose (2 * n) n from rfl] at hcast
  push_cast at hcast
  linear_combination hcast

private lemma chap9Fcoeff_succ (n : ℕ) :
    chap9Fcoeff (n + 1)
      = chap9Fcoeff n * ((2 * (n : ℝ) + 1) / (2 * ((n : ℝ) + 1))) := by
  have h2 := chap9_cast_centralBinom n
  have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hPne : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ (2 * (n + 1)) = 4 * (2 : ℝ) ^ (2 * n) := by
    rw [show 2 * (n + 1) = 2 * n + 2 by ring, pow_add]
    ring
  unfold chap9Fcoeff
  rw [hpow]
  field_simp
  linarith [h2]

private lemma chap9_smeval_rec (n : ℕ) :
    (ascPochhammer ℕ (n + 1)).smeval (1 / 2 : ℝ)
      = (ascPochhammer ℕ n).smeval (1 / 2 : ℝ) * ((1 / 2 : ℝ) + (n : ℝ)) := by
  rw [ascPochhammer_succ_right, Polynomial.smeval_mul]
  congr 1
  rw [Polynomial.smeval_add, Polynomial.smeval_X, Polynomial.smeval_natCast]
  simp only [pow_one, pow_zero, nsmul_eq_mul, mul_one]

private lemma chap9_multichoose_succ (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = Ring.multichoose (1 / 2 : ℝ) n * (((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) := by
  have hP := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  have hP1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) (n + 1)
  rw [nsmul_eq_mul] at hP hP1
  have hfact : ((n + 1).factorial : ℝ)
      = ((n : ℝ) + 1) * ((n.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hrec := chap9_smeval_rec n
  have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
  have hPne : ((n.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  rw [hfact, hrec, ← hP] at hP1
  have key : ((n : ℝ) + 1) * Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = ((n : ℝ) + 1 / 2) * Ring.multichoose (1 / 2 : ℝ) n := by
    apply mul_left_cancel₀ hPne
    linear_combination hP1
  rw [← mul_div_assoc, eq_div_iff hne1]
  linear_combination key

private lemma chap9_multichoose_eq (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) n = chap9Fcoeff n := by
  induction n with
  | zero =>
    simp [chap9Fcoeff]
  | succ n ih =>
    have hne1 : ((n : ℝ) + 1) ≠ 0 := ne_of_gt (by positivity)
    have hne2 : 2 * ((n : ℝ) + 1) ≠ 0 := mul_ne_zero (by norm_num) hne1
    rw [chap9_multichoose_succ, chap9Fcoeff_succ, ih]
    congr 1
    field_simp

private lemma chap9_binomial_hasSum {s : ℝ} (hs : ‖s‖ < 1) :
    HasSum (fun n : ℕ => chap9Fcoeff n * s ^ n) (1 / (1 - s) ^ (1 / 2 : ℝ)) := by
  have h0 := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hmem : s ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    exact ENNReal.ofReal_lt_one.mpr hs
  have hsum := h0.hasSum hmem
  rw [zero_add] at hsum
  refine hsum.congr_fun (fun n => ?_)
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul,
    ← Ring.multichoose_eq, chap9_multichoose_eq]

private lemma chap9_sqrt_hasSum {y : ℝ} (hy : ‖y‖ < 1) :
    HasSum (fun n : ℕ => chap9Fcoeff n * y ^ (2 * n)) (1 / √(1 - y ^ 2)) := by
  have hs : ‖y ^ 2‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) hy (by norm_num)
  have h := chap9_binomial_hasSum hs
  have hfun : (fun n : ℕ => chap9Fcoeff n * y ^ (2 * n)) =
      (fun n : ℕ => chap9Fcoeff n * (y ^ 2) ^ n) := by
    funext n
    rw [← pow_mul]
  rw [hfun]
  have hval : (1 : ℝ) / (1 - y ^ 2) ^ (1 / 2 : ℝ) = 1 / √(1 - y ^ 2) := by
    rw [Real.sqrt_eq_rpow]
  rwa [hval] at h

private lemma chap9G_term_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => chap9Fcoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
      (chap9Fcoeff n * t ^ (2 * n)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) t := by
    have h := hasDerivAt_pow (2 * n + 1) t
    have heq : (2 * n + 1) - 1 = 2 * n := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (chap9Fcoeff n)
  have hdiv := hmul.div_const ((2 * n + 1 : ℕ) : ℝ)
  have hsimp : chap9Fcoeff n * (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) /
        ((2 * n + 1 : ℕ) : ℝ) = chap9Fcoeff n * t ^ (2 * n) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma chap9G_majorant (r : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ioo (-r) r) :
    ‖chap9Fcoeff n * y ^ (2 * n)‖ ≤ (r ^ 2) ^ n := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    rw [Set.mem_Ioo] at hy
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hc : ‖chap9Fcoeff n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (chap9Fcoeff_nonneg n)]
    exact chap9Fcoeff_le_one n
  calc ‖chap9Fcoeff n * y ^ (2 * n)‖
        = ‖chap9Fcoeff n‖ * ‖y‖ ^ (2 * n) := by rw [norm_mul, norm_pow]
      _ ≤ 1 * r ^ (2 * n) := by
          apply mul_le_mul hc _ (by positivity) (by norm_num)
          exact pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
      _ = (r ^ 2) ^ n := by ring

private lemma chap9G_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt chap9G (∑' n : ℕ, chap9Fcoeff n * y ^ (2 * n)) y := by
  have hu : Summable (fun n : ℕ => (r ^ 2) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun s : ℝ => chap9Fcoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
        (chap9Fcoeff n * z ^ (2 * n)) z :=
    fun n z _ => chap9G_term_hasDerivAt n z
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖chap9Fcoeff n * z ^ (2 * n)‖ ≤ (r ^ 2) ^ n :=
    fun n z hz => chap9G_majorant r hr0 hr1 n z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun n : ℕ =>
      chap9Fcoeff n * (0 : ℝ) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
    apply Summable.of_norm
    have hle : ∀ n : ℕ,
        ‖chap9Fcoeff n * (0 : ℝ) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤
          (1 : ℝ) / (((n : ℝ) + 1) ^ 2) := by
      intro n
      by_cases hn : n = 0
      · subst hn
        simp [chap9Fcoeff]
      · have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
        rw [hz]
        simp only [mul_zero, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
          zero_div, norm_zero, one_div, inv_nonneg, ge_iff_le]
        positivity
    have haux : Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
      have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
        (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
      have hshift : Summable (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) :=
        (summable_nat_add_iff 1).mpr h
      have hcongr : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
          (fun n : ℕ => (1 : ℝ) / ((((n + 1 : ℕ)) : ℝ) ^ 2)) := by
        funext k
        rw [Nat.cast_add, Nat.cast_one]
      rwa [hcongr]
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle haux
  exact hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound hy0 hsum0 hy

private lemma chap9_mem_Ioo_norm_lt_one (y : ℝ) (hy : y ∈ Set.Ioo (-1 : ℝ) 1) :
    ‖y‖ < 1 := by
  rw [Set.mem_Ioo] at hy
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hy.1, hy.2]

private lemma chap9G_zero : chap9G 0 = 0 := by
  unfold chap9G
  have hzero : (fun n : ℕ => chap9Fcoeff n * (0 : ℝ) ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ)) = fun _ => 0 := by
    funext n
    have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

private lemma chap9G_hasDerivAt_sqrt {y : ℝ} (hy : ‖y‖ < 1) :
    HasDerivAt chap9G (1 / √(1 - y ^ 2)) y := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have habs : |y| < (‖y‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    linarith [hy]
  rw [abs_lt] at habs
  have hymem : y ∈ Set.Ioo (-((‖y‖ + 1) / 2)) ((‖y‖ + 1) / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hder := chap9G_hasDerivAt_of_mem hr0 hr1 hymem
  have hsum := chap9_sqrt_hasSum hy
  rw [hsum.tsum_eq] at hder
  exact hder

private lemma chap9G_eq_arcsin : Set.EqOn chap9G Real.arcsin (Set.Ioo (-1 : ℝ) 1) := by
  have hopen : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-1 : ℝ) 1) := isPreconnected_Ioo
  have hGdiff : DifferentiableOn ℝ chap9G (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hnorm := chap9_mem_Ioo_norm_lt_one x hx
    have h := chap9G_hasDerivAt_sqrt hnorm
    exact (h.differentiableAt).differentiableWithinAt
  have harcsin_diff : DifferentiableOn ℝ Real.arcsin (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    have h1 : x ≠ -1 := by linarith [hx.1]
    have h2 : x ≠ 1 := by linarith [hx.2]
    exact ((Real.hasDerivAt_arcsin h1 h2).differentiableAt).differentiableWithinAt
  have hderiv_eq : Set.EqOn (deriv chap9G) (deriv Real.arcsin) (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have hnorm := chap9_mem_Ioo_norm_lt_one x hx
    have hG := chap9G_hasDerivAt_sqrt hnorm
    rw [Set.mem_Ioo] at hx
    have h1 : x ≠ -1 := by linarith [hx.1]
    have h2 : x ≠ 1 := by linarith [hx.2]
    have hA := Real.hasDerivAt_arcsin h1 h2
    rw [hG.deriv, hA.deriv]
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have h0eq : chap9G 0 = Real.arcsin 0 := by rw [chap9G_zero, Real.arcsin_zero]
  exact IsOpen.eqOn_of_deriv_eq hopen hpre hGdiff harcsin_diff hderiv_eq h0mem h0eq

private lemma chap9F_term_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => chap9Fcoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2)
      (chap9Fcoeff n * t ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) t := by
    have h := hasDerivAt_pow (2 * n + 1) t
    have heq : (2 * n + 1) - 1 = 2 * n := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (chap9Fcoeff n)
  have hdiv := hmul.div_const (((2 * n + 1 : ℕ) : ℝ) ^ 2)
  have hsimp : chap9Fcoeff n * (((2 * n + 1 : ℕ) : ℝ) * t ^ (2 * n)) /
        ((2 * n + 1 : ℕ) : ℝ) ^ 2
      = chap9Fcoeff n * t ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma chap9F_term_eq (n : ℕ) (t : ℝ) :
    chap9Fcoeff n * t ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2
      = (Nat.choose (2 * n) n : ℝ) * t ^ (2 * n + 1) /
        ((2 : ℝ) ^ (2 * n) * ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold chap9Fcoeff
  field_simp

private lemma chap9F_bound (t : ℝ) (ht : ‖t‖ ≤ 1) (k : ℕ) :
    ‖chap9Fcoeff k * t ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℝ) ^ 2‖ ≤
      (1 : ℝ) / (((k : ℝ) + 1) ^ 2) := by
  rw [chap9F_term_eq]
  exact chap9_norm_term_le t ht k

private lemma chap9F_zero : chap9F 0 = 0 := by
  unfold chap9F
  have hzero : (fun n : ℕ => chap9Fcoeff n * (0 : ℝ) ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ) ^ 2) = fun _ => 0 := by
    funext n
    have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

private lemma chap9F_continuousOn : ContinuousOn chap9F (Set.Icc (-1 : ℝ) 1) := by
  apply continuousOn_tsum (fun n => ?_) chap9_aux_summable (fun n x hx => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * n + 1)).continuousOn
  · have ht : ‖x‖ ≤ 1 := by
      rw [Set.mem_Icc] at hx
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    exact chap9F_bound x ht n

private lemma chap9_one_div_le (n : ℕ) : (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ≤ 1 := by
  have h1 : (1 : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) := by
    have hle : 1 ≤ 2 * n + 1 := by omega
    exact_mod_cast hle
  calc (1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ) ≤ 1 / 1 := by
        apply one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by simp

private lemma chap9F_majorant (r : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (n : ℕ) (y : ℝ)
    (hy : y ∈ Set.Ioo (-r) r) :
    ‖chap9Fcoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ (r ^ 2) ^ n := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    rw [Set.mem_Ioo] at hy
    rw [abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  have hc : ‖chap9Fcoeff n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (chap9Fcoeff_nonneg n)]
    exact chap9Fcoeff_le_one n
  have hd : ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact chap9_one_div_le n
  have hpow_le : ‖y‖ ^ (2 * n) ≤ r ^ (2 * n) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have h1 : ‖chap9Fcoeff n‖ * ‖y‖ ^ (2 * n) ≤ 1 * r ^ (2 * n) :=
    mul_le_mul hc hpow_le (by positivity) (by norm_num)
  have h2 : (‖chap9Fcoeff n‖ * ‖y‖ ^ (2 * n)) * ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤
      (1 * r ^ (2 * n)) * 1 :=
    mul_le_mul h1 hd (by positivity) (by positivity)
  have heq : ‖chap9Fcoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)‖
      = (‖chap9Fcoeff n‖ * ‖y‖ ^ (2 * n)) * ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ := by
    rw [div_eq_mul_one_div]
    simp [norm_mul, norm_pow, mul_assoc]
  rw [heq]
  calc (‖chap9Fcoeff n‖ * ‖y‖ ^ (2 * n)) * ‖1 / ((2 * n + 1 : ℕ) : ℝ)‖
        ≤ (1 * r ^ (2 * n)) * 1 := h2
      _ = (r ^ 2) ^ n := by ring

private lemma chap9F_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt chap9F (∑' n : ℕ, chap9Fcoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) y := by
  have hu : Summable (fun n : ℕ => (r ^ 2) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun s : ℝ => chap9Fcoeff n * s ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2)
        (chap9Fcoeff n * z ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)) z :=
    fun n z _ => chap9F_term_hasDerivAt n z
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖chap9Fcoeff n * z ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ (r ^ 2) ^ n :=
    fun n z hz => chap9F_majorant r hr0 hr1 n z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun n : ℕ => chap9Fcoeff n * (0 : ℝ) ^ (2 * n + 1) /
      ((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
    apply Summable.of_norm
    have hle : ∀ n : ℕ,
        ‖chap9Fcoeff n * (0 : ℝ) ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ) ^ 2‖ ≤
          (1 : ℝ) / (((n : ℝ) + 1) ^ 2) := by
      intro n
      have h0 : ‖(0 : ℝ)‖ ≤ 1 := by simp
      exact chap9F_bound 0 h0 n
    exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle chap9_aux_summable
  exact hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound hy0 hsum0 hy

private lemma chap9_norm_mem_Ioo (y : ℝ) (hy : ‖y‖ < 1) : y ∈ Set.Ioo (-1 : ℝ) 1 := by
  rw [Real.norm_eq_abs, abs_lt] at hy
  rw [Set.mem_Ioo]
  constructor <;> linarith [hy.1, hy.2]

private lemma chap9G_summable_at {y : ℝ} (hy : ‖y‖ < 1) :
    Summable (fun n : ℕ => chap9Fcoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have hr : ‖y‖ < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hu : Summable (fun n : ℕ => ((((‖y‖ + 1) / 2) ^ 2) ^ n)) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_) hu
  have hyr : ‖y‖ < (‖y‖ + 1) / 2 := hr
  have hc : ‖chap9Fcoeff n‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (chap9Fcoeff_nonneg n)]
    exact chap9Fcoeff_le_one n
  have hd : ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact chap9_one_div_le n
  have hpow : ‖y‖ ^ (2 * n + 1) ≤ ((‖y‖ + 1) / 2) ^ (2 * n + 1) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have hpow2 : ((‖y‖ + 1) / 2) ^ (2 * n + 1) ≤ ((‖y‖ + 1) / 2) ^ (2 * n) := by
    have hrr : ((‖y‖ + 1) / 2) ^ (2 * n) * ((‖y‖ + 1) / 2) ≤
        ((‖y‖ + 1) / 2) ^ (2 * n) * 1 :=
      mul_le_mul_of_nonneg_left (le_of_lt hr1) (by positivity)
    rwa [← pow_succ, mul_one] at hrr
  calc ‖chap9Fcoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)‖
        = (‖chap9Fcoeff n‖ * ‖y‖ ^ (2 * n + 1)) * ‖(1 : ℝ) / ((2 * n + 1 : ℕ) : ℝ)‖ := by
          rw [div_eq_mul_one_div]
          simp [norm_mul, norm_pow, mul_assoc]
      _ ≤ (1 * ((‖y‖ + 1) / 2) ^ (2 * n + 1)) * 1 := by
          have h1 : ‖chap9Fcoeff n‖ * ‖y‖ ^ (2 * n + 1) ≤
              1 * ((‖y‖ + 1) / 2) ^ (2 * n + 1) :=
            mul_le_mul hc hpow (by positivity) (by norm_num)
          exact mul_le_mul h1 hd (by positivity) (by positivity)
      _ ≤ ((((‖y‖ + 1) / 2) ^ 2) ^ n) := by
          calc (1 * ((‖y‖ + 1) / 2) ^ (2 * n + 1)) * 1
                = ((‖y‖ + 1) / 2) ^ (2 * n + 1) := by ring
            _ ≤ ((‖y‖ + 1) / 2) ^ (2 * n) := hpow2
            _ = ((((‖y‖ + 1) / 2) ^ 2) ^ n) := by
              exact pow_mul _ 2 n

private lemma chap9F_hasDerivAt_arcsin_div {y : ℝ} (hy : ‖y‖ < 1) (hy0 : y ≠ 0) :
    HasDerivAt chap9F (Real.arcsin y / y) y := by
  have hr1 : (‖y‖ + 1) / 2 < 1 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  have hr0 : (0 : ℝ) < (‖y‖ + 1) / 2 := by
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith
  have habs : |y| < (‖y‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    have hnn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg _
    linarith [hy]
  rw [abs_lt] at habs
  have hymem : y ∈ Set.Ioo (-((‖y‖ + 1) / 2)) ((‖y‖ + 1) / 2) := by
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hF := chap9F_hasDerivAt_of_mem hr0 hr1 hymem
  have hGsum := chap9G_summable_at hy
  have hterm : (fun n : ℕ => chap9Fcoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ))
      = (fun n : ℕ => (chap9Fcoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) * y⁻¹) := by
    funext n
    have hne : ((2 * n + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt (by positivity)
    have hpow : y ^ (2 * n + 1) = y ^ (2 * n) * y := by
      rw [show 2 * n + 1 = (2 * n) + 1 by ring, pow_succ]
    rw [hpow]
    field_simp
  have hsum_eq : (∑' n : ℕ, chap9Fcoeff n * y ^ (2 * n) / ((2 * n + 1 : ℕ) : ℝ))
      = (∑' n : ℕ, chap9Fcoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ)) / y := by
    rw [hterm, hGsum.tsum_mul_right, div_eq_mul_inv]
  have hGval : (∑' n : ℕ, chap9Fcoeff n * y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℝ))
      = Real.arcsin y := by
    have heq : chap9G y = Real.arcsin y :=
      chap9G_eq_arcsin (chap9_norm_mem_Ioo y hy)
    unfold chap9G at heq
    exact heq
  rw [hsum_eq, hGval] at hF
  exact hF

private lemma chap9_sin_cos_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.sin θ ∈ Set.Ioo 0 1 ∧ Real.cos θ ∈ Set.Ioo 0 1 := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hθ
  have hsin_pos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith)
  have hcos_pos : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin_ne : Real.sin θ ≠ 1 := by
    intro h
    have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h] at hsq
    nlinarith [hsq, hcos_pos, sq_nonneg (Real.cos θ)]
  have hcos_ne : Real.cos θ ≠ 1 := by
    intro h
    have hsq : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    rw [h] at hsq
    nlinarith [hsq, hsin_pos, sq_nonneg (Real.sin θ)]
  refine ⟨⟨hsin_pos, lt_of_le_of_ne (Real.sin_le_one θ) hsin_ne⟩,
    ⟨hcos_pos, lt_of_le_of_ne (Real.cos_le_one θ) hcos_ne⟩⟩

private lemma chap9_norm_ne_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ‖Real.sin θ‖ < 1 ∧ ‖Real.cos θ‖ < 1 ∧ Real.sin θ ≠ 0 ∧ Real.cos θ ≠ 0 := by
  have hmem := chap9_sin_cos_mem_Ioo hθ
  simp only [Set.mem_Ioo] at hmem
  have hsin_norm : ‖Real.sin θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hmem.1.1, hmem.1.2]
  have hcos_norm : ‖Real.cos θ‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [hmem.2.1, hmem.2.2]
  exact ⟨hsin_norm, hcos_norm, ne_of_gt hmem.1.1, ne_of_gt hmem.2.1⟩

private lemma chap9_arcsin_sin_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Real.arcsin (Real.sin θ) = θ := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hθ
  exact Real.arcsin_sin (by linarith) (by linarith)

private lemma chap9F_sin_eq_tsum (x : ℝ) :
    chap9F (Real.sin x) =
      ∑' k : ℕ, (Nat.choose (2 * k) k : ℝ) * Real.sin x ^ (2 * k + 1) /
        ((2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold chap9F
  congr 1
  funext k
  exact chap9F_term_eq k (Real.sin x)

private lemma chap9_sin_cos_mem_Icc (t : ℝ) : Real.sin t ∈ Set.Icc (-1 : ℝ) 1 ∧
    Real.cos t ∈ Set.Icc (-1 : ℝ) 1 := by
  refine ⟨⟨Real.neg_one_le_sin t, Real.sin_le_one t⟩,
    ⟨Real.neg_one_le_cos t, Real.cos_le_one t⟩⟩

private lemma chap9_sinc_pos_of_mem_Icc {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 2)) : 0 < Real.sinc θ := by
  by_cases h0 : θ = 0
  · subst h0
    rw [Real.sinc_zero]
    norm_num
  · rw [Real.sinc_of_ne_zero h0]
    have hpi := Real.pi_pos
    rw [Set.mem_Icc] at hθ
    have hpos : 0 < θ := lt_of_le_of_ne hθ.1 (Ne.symm h0)
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
    exact div_pos hsin hpos

private def chap9D (θ : ℝ) : ℝ := Real.cos θ / Real.sinc θ

private lemma chap9D_continuousOn :
    ContinuousOn chap9D (Set.Icc 0 (Real.pi / 2)) := by
  unfold chap9D
  exact Real.continuous_cos.continuousOn.div Real.continuous_sinc.continuousOn
    (fun θ hθ => ne_of_gt (chap9_sinc_pos_of_mem_Icc hθ))

private lemma chap9D_eq_mul_div {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    chap9D θ = θ * Real.cos θ / Real.sin θ := by
  unfold chap9D
  have hne : θ ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hθ).1
  rw [Real.sinc_of_ne_zero hne]
  have hsin_ne : Real.sin θ ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (Set.mem_Ioo.mp hθ).1 (by
      have hpi := Real.pi_pos
      have h2 := (Set.mem_Ioo.mp hθ).2
      linarith))
  field_simp

private def chap9Phi (θ : ℝ) : ℝ := chap9F (Real.sin θ)

private lemma chap9Phi_continuousOn :
    ContinuousOn chap9Phi (Set.Icc 0 (Real.pi / 2)) := by
  unfold chap9Phi
  exact chap9F_continuousOn.comp Real.continuous_sin.continuousOn
    (fun θ _ => (chap9_sin_cos_mem_Icc θ).1)

private lemma chap9Phi_hasDerivAt {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt chap9Phi (chap9D θ) θ := by
  have hnorm := chap9_norm_ne_of_mem_Ioo hθ
  have houter := chap9F_hasDerivAt_arcsin_div hnorm.1 hnorm.2.2.1
  have hcomp : HasDerivAt (fun θ : ℝ => chap9F (Real.sin θ))
      ((Real.arcsin (Real.sin θ) / Real.sin θ) * Real.cos θ) θ :=
    houter.comp θ (Real.hasDerivAt_sin θ)
  have harcsin := chap9_arcsin_sin_of_mem hθ
  rw [harcsin] at hcomp
  have hDeq : (θ / Real.sin θ) * Real.cos θ = chap9D θ := by
    rw [chap9D_eq_mul_div hθ]
    ring
  rw [hDeq] at hcomp
  exact hcomp

private lemma chap9_sin_eq_mul_sinc (θ : ℝ) :
    Real.sin θ = θ * Real.sinc θ := by
  by_cases h0 : θ = 0
  · subst h0
    simp only [Real.sin_zero, Real.sinc_zero, zero_mul]
  · rw [Real.sinc_of_ne_zero h0]
    field_simp

private def chap9A (θ : ℝ) : ℝ := θ * Real.log (Real.sin θ)

private lemma chap9A_hasDerivAt {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt chap9A (Real.log (Real.sin θ) + chap9D θ) θ := by
  have hsin_ne : Real.sin θ ≠ 0 :=
    (chap9_norm_ne_of_mem_Ioo hθ).2.2.1
  have hlogsin : HasDerivAt (fun θ : ℝ => Real.log (Real.sin θ))
      ((Real.sin θ)⁻¹ * Real.cos θ) θ :=
    (Real.hasDerivAt_log hsin_ne).comp θ (Real.hasDerivAt_sin θ)
  have hid : HasDerivAt (fun θ : ℝ => θ) 1 θ := hasDerivAt_id' θ
  have hprod : HasDerivAt (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (1 * Real.log (Real.sin θ) + θ * ((Real.sin θ)⁻¹ * Real.cos θ)) θ :=
    hid.mul hlogsin
  have hDeq : 1 * Real.log (Real.sin θ) + θ * ((Real.sin θ)⁻¹ * Real.cos θ)
      = Real.log (Real.sin θ) + chap9D θ := by
    rw [chap9D_eq_mul_div hθ]
    ring
  rw [hDeq] at hprod
  exact hprod

private lemma chap9A_continuousOn :
    ContinuousOn chap9A (Set.Icc 0 (Real.pi / 2)) := by
  have hB : ContinuousOn (fun θ : ℝ => θ * Real.log θ)
      (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_mul_log.continuousOn
  have hsinc_on : ContinuousOn Real.sinc (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuous_sinc.continuousOn
  have hlog_sinc_on : ContinuousOn (fun θ : ℝ => Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    Real.continuousOn_log.comp hsinc_on (fun θ hθ => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (chap9_sinc_pos_of_mem_Icc hθ))
  have hC : ContinuousOn (fun θ : ℝ => θ * Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_id.mul hlog_sinc_on
  have hBC : ContinuousOn
      (fun θ : ℝ => θ * Real.log θ + θ * Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) :=
    hB.add hC
  have hEq : Set.EqOn chap9A
      (fun θ : ℝ => θ * Real.log θ + θ * Real.log (Real.sinc θ))
      (Set.Icc 0 (Real.pi / 2)) := by
    intro θ hθ
    unfold chap9A
    by_cases h0 : θ = 0
    · subst h0
      simp only [Real.sin_zero, Real.log_zero, Real.sinc_zero, Real.log_one,
        zero_mul, add_zero]
    · have hsinc_ne : Real.sinc θ ≠ 0 :=
        ne_of_gt (chap9_sinc_pos_of_mem_Icc hθ)
      have hsin_eq := chap9_sin_eq_mul_sinc θ
      have hlog : Real.log (Real.sin θ)
          = Real.log θ + Real.log (Real.sinc θ) := by
        rw [hsin_eq, Real.log_mul h0 hsinc_ne]
      rw [hlog, mul_add]
  exact hBC.congr hEq

private lemma chap9Phi_zero : chap9Phi 0 = 0 := by
  unfold chap9Phi
  rw [Real.sin_zero, chap9F_zero]

private lemma chap9A_zero : chap9A 0 = 0 := by
  unfold chap9A
  rw [zero_mul]

private lemma chap9Phi_eq_central_tsum (x : ℝ) :
    chap9Phi x = ∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm x k :=
  chap9F_sin_eq_tsum x

private lemma chap9Phi_integral_general {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ Real.pi / 2) :
    (∫ θ in (0 : ℝ)..x, chap9D θ) = chap9Phi x := by
  have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro y hy
    rw [Set.mem_Icc] at hy ⊢
    constructor <;> linarith [hy.1, hy.2, hx]
  have hcont : ContinuousOn chap9Phi (Set.Icc 0 x) :=
    chap9Phi_continuousOn.mono hsub
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) x, HasDerivAt chap9Phi (chap9D θ) θ := by
    intro θ hθ
    rw [Set.mem_Ioo] at hθ
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.mem_Ioo]
      constructor <;> linarith [hθ.1, hθ.2, hx]
    exact chap9Phi_hasDerivAt hmem
  have hDcont : ContinuousOn chap9D (Set.Icc 0 x) :=
    chap9D_continuousOn.mono hsub
  have hint : IntervalIntegrable chap9D MeasureTheory.volume 0 x :=
    hDcont.intervalIntegrable_of_Icc hx0
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hcont
    hderiv hint
  rw [chap9Phi_zero, sub_zero] at hFTC
  exact hFTC

private lemma chap9A_integral_general {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ Real.pi / 2) :
    (∫ θ in (0 : ℝ)..x, (Real.log (Real.sin θ) + chap9D θ)) = chap9A x := by
  have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
    intro y hy
    rw [Set.mem_Icc] at hy ⊢
    constructor <;> linarith [hy.1, hy.2, hx]
  have hcont : ContinuousOn chap9A (Set.Icc 0 x) :=
    chap9A_continuousOn.mono hsub
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) x,
      HasDerivAt chap9A (Real.log (Real.sin θ) + chap9D θ) θ := by
    intro θ hθ
    rw [Set.mem_Ioo] at hθ
    have hmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      rw [Set.mem_Ioo]
      constructor <;> linarith [hθ.1, hθ.2, hx]
    exact chap9A_hasDerivAt hmem
  have hlog_int : IntervalIntegrable (fun θ : ℝ => Real.log (Real.sin θ))
      MeasureTheory.volume 0 x :=
    intervalIntegrable_log_sin
  have hDcont : ContinuousOn chap9D (Set.Icc 0 x) :=
    chap9D_continuousOn.mono hsub
  have hD_int : IntervalIntegrable chap9D MeasureTheory.volume 0 x :=
    hDcont.intervalIntegrable_of_Icc hx0
  have hint : IntervalIntegrable
      (fun θ : ℝ => Real.log (Real.sin θ) + chap9D θ)
      MeasureTheory.volume 0 x :=
    hlog_int.add hD_int
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hcont
    hderiv hint
  rw [chap9A_zero, sub_zero] at hFTC
  exact hFTC

private def chap9r (n : ℕ) : ℝ := 1 - 1 / (2 * ((n : ℝ) + 1))

private lemma chap9r_mem_Ico (n : ℕ) : (1 / 2 : ℝ) ≤ chap9r n ∧ chap9r n < 1 := by
  have hpos : (0 : ℝ) < 2 * ((n : ℝ) + 1) := by positivity
  have h2le : (2 : ℝ) ≤ 2 * ((n : ℝ) + 1) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hle : (1 : ℝ) / (2 * ((n : ℝ) + 1)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) h2le
  have hpos2 : (0 : ℝ) < 1 / (2 * ((n : ℝ) + 1)) := by positivity
  unfold chap9r
  constructor <;> linarith

private lemma chap9r_nonneg (n : ℕ) : 0 ≤ chap9r n := by
  have h := (chap9r_mem_Ico n).1
  linarith

private lemma chap9r_lt_one (n : ℕ) : chap9r n < 1 :=
  (chap9r_mem_Ico n).2

private lemma chap9r_norm_lt_one (n : ℕ) : ‖chap9r n‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (chap9r_nonneg n)]
  exact chap9r_lt_one n

private lemma chap9r_tendsto : Filter.Tendsto chap9r Filter.atTop (nhds 1) := by
  have h0 : Filter.Tendsto (fun n : ℕ => (1 : ℝ) / (((n : ℝ) + 1))) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hmul : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) * ((1 : ℝ) / (((n : ℝ) + 1))))
      Filter.atTop (nhds 0) := by
    have h := Filter.Tendsto.const_mul (1 / 2 : ℝ) h0
    simpa using h
  have hsub : Filter.Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) * ((1 : ℝ) / (((n : ℝ) + 1))))
      Filter.atTop (nhds 1) := by
    have h := Filter.Tendsto.const_sub 1 hmul
    simpa using h
  have heq : chap9r = (fun n : ℕ => 1 - (1 / 2 : ℝ) * ((1 : ℝ) / (((n : ℝ) + 1)))) := by
    funext n
    unfold chap9r
    congr 1
    field_simp
  rw [heq]
  exact hsub

private def chap9S (r x : ℝ) : ℝ :=
  ∑' j : ℕ, r ^ (j + 1) * chapter9SineFourierTwoTerm x j

private lemma chap9S_summable {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Summable (fun j : ℕ => r ^ (j + 1) * chapter9SineFourierTwoTerm x j) := by
  have hle : ∀ j : ℕ,
      ‖r ^ (j + 1) * chapter9SineFourierTwoTerm x j‖ ≤
        (1 : ℝ) / ((((j : ℝ) + 1)) ^ 2) := by
    intro j
    have hrpow_nonneg : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
    have hrpow_le : r ^ (j + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hfour := aux_fourier_abs x j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nonneg]
    calc r ^ (j + 1) * |chapter9SineFourierTwoTerm x j|
        ≤ 1 * (1 / ((((j : ℝ) + 1)) ^ 2)) := by
          apply mul_le_mul hrpow_le hfour (abs_nonneg _) (by positivity)
      _ = 1 / ((((j : ℝ) + 1)) ^ 2) := one_mul _
  exact Summable.of_norm
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hle chap9_aux_summable)

private lemma chap9S_zero (r : ℝ) : chap9S r 0 = 0 := by
  unfold chap9S
  have hzero : (fun j : ℕ => r ^ (j + 1) * chapter9SineFourierTwoTerm 0 j) =
      fun _ => 0 := by
    funext j
    unfold chapter9SineFourierTwoTerm
    simp only [mul_zero, Real.sin_zero, zero_div, mul_zero]
  rw [hzero, tsum_zero]

private lemma chap9S_one_eq_fourier (x : ℝ) :
    chap9S 1 x = ∑' j : ℕ, chapter9SineFourierTwoTerm x j := by
  unfold chap9S
  congr 1
  funext j
  rw [one_pow, one_mul]

private lemma chap9S_term_hasDerivAt (r : ℝ) (j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => r ^ (j + 1) * chapter9SineFourierTwoTerm y j)
      (2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) x := by
  have hkpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) := by
    have h : 0 < j + 1 := Nat.succ_pos j
    exact_mod_cast h
  have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hkpos
  set k : ℝ := ((((j + 1 : ℕ)) : ℝ)) with hkdef
  set C : ℝ := r ^ (j + 1) / (k ^ 2) with hCdef
  set L : ℝ := 2 * k with hLdef
  have hfun : (fun y : ℝ => r ^ (j + 1) * chapter9SineFourierTwoTerm y j) =
      (fun y : ℝ => C * Real.sin (L * y)) := by
    funext y
    unfold chapter9SineFourierTwoTerm
    simp only
    unfold C L k
    field_simp
  have hlin : HasDerivAt (fun y : ℝ => L * y) L x := by
    simpa using (hasDerivAt_id' x).const_mul L
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (L * y))
      (Real.cos (L * x) * L) x :=
    (Real.hasDerivAt_sin (L * x)).comp x hlin
  have hCsin : HasDerivAt (fun y : ℝ => C * Real.sin (L * y))
      (C * (Real.cos (L * x) * L)) x :=
    hsin.const_mul C
  rw [hfun]
  have hsimp : C * (Real.cos (L * x) * L) =
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ)) := by
    unfold C L k
    field_simp
  rwa [hsimp] at hCsin

private lemma chap9S_deriv_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun j : ℕ => (2 : ℝ) * r ^ (j + 1)) := by
  have hgeo : Summable (fun n : ℕ => r ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hr1
  have hshift : Summable (fun j : ℕ => r ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  exact Summable.mul_left 2 hshift

private lemma chap9S_deriv_bound {r : ℝ} (hr0 : 0 ≤ r) (j : ℕ) (y : ℝ) :
    ‖2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ))‖ ≤
      (2 : ℝ) * r ^ (j + 1) := by
  have hkpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) := by
    have h : 0 < j + 1 := Nat.succ_pos j
    exact_mod_cast h
  have h1k : (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ)) ≤ 1 := by
    have h1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
      have hle : 1 ≤ j + 1 := Nat.le_add_left 1 j
      exact_mod_cast hle
    calc (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ)) ≤ 1 / 1 := by
          apply one_div_le_one_div_of_le (by norm_num) h1
      _ = 1 := by simp
  have hcos : ‖Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y)‖ ≤ 1 := by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _
  have hrpow_nonneg : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
  rw [norm_div, norm_mul, norm_mul]
  have h2norm : ‖(2 : ℝ)‖ = 2 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by norm_num)]
  have hrpow_norm : ‖r ^ (j + 1)‖ = r ^ (j + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hrpow_nonneg]
  have hknorm : ‖((((j + 1 : ℕ)) : ℝ))‖ = ((((j + 1 : ℕ)) : ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hkpos)]
  rw [h2norm, hrpow_norm, hknorm]
  have h2r_nonneg : (0 : ℝ) ≤ (2 : ℝ) * r ^ (j + 1) := by positivity
  calc 2 * r ^ (j + 1) * ‖Real.cos (2 * ↑(j + 1) * y)‖ / ↑(j + 1)
        = ((2 : ℝ) * r ^ (j + 1)) * (‖Real.cos (2 * ↑(j + 1) * y)‖ * (1 / ↑(j + 1))) := by
          rw [div_eq_mul_one_div]
          ring
      _ ≤ ((2 : ℝ) * r ^ (j + 1)) * (1 * 1) := by
          apply mul_le_mul_of_nonneg_left _ h2r_nonneg
          have hd : (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ)) ≤ 1 := h1k
          exact mul_le_mul hcos hd (by positivity) (by norm_num)
      _ = (2 : ℝ) * r ^ (j + 1) := by ring

private lemma chap9S_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (chap9S r)
      (∑' j : ℕ, 2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) /
        ((((j + 1 : ℕ)) : ℝ))) x := by
  have hu : Summable (fun j : ℕ => (2 : ℝ) * r ^ (j + 1)) :=
    chap9S_deriv_summable hr0 hr1
  have hderiv : ∀ j : ℕ, ∀ y : ℝ,
      HasDerivAt (fun y : ℝ => r ^ (j + 1) * chapter9SineFourierTwoTerm y j)
        (2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) /
          ((((j + 1 : ℕ)) : ℝ))) y :=
    fun j y => chap9S_term_hasDerivAt r j y
  have hbound : ∀ j : ℕ, ∀ y : ℝ,
      ‖2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) /
        ((((j + 1 : ℕ)) : ℝ))‖ ≤ (2 : ℝ) * r ^ (j + 1) :=
    fun j y => chap9S_deriv_bound hr0 j y
  have hsum0 : Summable (fun j : ℕ => r ^ (j + 1) * chapter9SineFourierTwoTerm 0 j) := by
    have hzero : (fun j : ℕ => r ^ (j + 1) * chapter9SineFourierTwoTerm 0 j) = fun _ => 0 := by
      funext j
      unfold chapter9SineFourierTwoTerm
      simp only [mul_zero, Real.sin_zero, zero_div, mul_zero]
    rw [hzero]
    exact summable_zero
  have h := hasDerivAt_tsum hu hderiv hbound hsum0 x
  exact h

private lemma chap9S_term_continuous (r : ℝ) (j : ℕ) :
    Continuous (fun x : ℝ => r ^ (j + 1) * chapter9SineFourierTwoTerm x j) := by
  have hsin : Continuous (fun x : ℝ => Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)) :=
    Real.continuous_sin.comp (continuous_const.mul continuous_id)
  have hdiv : Continuous (fun x : ℝ =>
      Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) :=
    hsin.div_const _
  have hfun : (fun x : ℝ => r ^ (j + 1) * chapter9SineFourierTwoTerm x j) =
      (fun x : ℝ => r ^ (j + 1) *
        (Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2))) := by
    funext x
    unfold chapter9SineFourierTwoTerm
    simp only
  rw [hfun]
  exact continuous_const.mul hdiv

private lemma chap9S_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Continuous (chap9S r) := by
  have hbound : ∀ j : ℕ, ∀ x : ℝ,
      ‖r ^ (j + 1) * chapter9SineFourierTwoTerm x j‖ ≤
        (1 : ℝ) / ((((j : ℝ) + 1)) ^ 2) := by
    intro j x
    have hrpow_nonneg : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
    have hrpow_le : r ^ (j + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hfour := aux_fourier_abs x j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nonneg]
    calc r ^ (j + 1) * |chapter9SineFourierTwoTerm x j|
          ≤ 1 * (1 / ((((j : ℝ) + 1)) ^ 2)) := by
            apply mul_le_mul hrpow_le hfour (abs_nonneg _) (by positivity)
        _ = 1 / ((((j : ℝ) + 1)) ^ 2) := one_mul _
  have h := continuous_tsum (fun j => chap9S_term_continuous r j)
    chap9_aux_summable hbound
  exact h

private lemma chap9S_deriv_term_continuous (r : ℝ) (j : ℕ) :
    Continuous (fun x : ℝ =>
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) /
        ((((j + 1 : ℕ)) : ℝ))) := by
  have hcos : Continuous (fun x : ℝ => Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hmul : Continuous (fun x : ℝ =>
      (2 * r ^ (j + 1)) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x)) :=
    continuous_const.mul hcos
  have hfun : (fun x : ℝ =>
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) /
        ((((j + 1 : ℕ)) : ℝ))) =
      (fun x : ℝ => ((2 * r ^ (j + 1)) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x)) /
        ((((j + 1 : ℕ)) : ℝ))) := by
    funext x
    ring_nf
  rw [hfun]
  exact hmul.div_const _

private lemma chap9S_deriv_continuous {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun x : ℝ => ∑' j : ℕ,
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) /
        ((((j + 1 : ℕ)) : ℝ))) := by
  apply continuous_tsum (fun j => chap9S_deriv_term_continuous r j)
    (chap9S_deriv_summable hr0 hr1)
  intro j x
  exact chap9S_deriv_bound hr0 j x

private lemma chap9S_integral {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hx0 : 0 ≤ x) :
    (∫ u in (0 : ℝ)..x, (∑' j : ℕ,
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * u) /
        ((((j + 1 : ℕ)) : ℝ)))) = chap9S r x := by
  have hcont : ContinuousOn (chap9S r) (Set.Icc 0 x) :=
    (chap9S_continuous hr0 (le_of_lt hr1)).continuousOn
  have hderiv : ∀ u ∈ Set.Ioo (0 : ℝ) x,
      HasDerivAt (chap9S r)
        (∑' j : ℕ, 2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * u) /
          ((((j + 1 : ℕ)) : ℝ))) u := by
    intro u _
    exact chap9S_hasDerivAt hr0 hr1 u
  have hDcont : ContinuousOn (fun u : ℝ => ∑' j : ℕ,
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * u) /
        ((((j + 1 : ℕ)) : ℝ))) (Set.Icc 0 x) :=
    (chap9S_deriv_continuous hr0 hr1).continuousOn
  have hint : IntervalIntegrable (fun u : ℝ => ∑' j : ℕ,
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * u) /
        ((((j + 1 : ℕ)) : ℝ))) MeasureTheory.volume 0 x :=
    hDcont.intervalIntegrable_of_Icc hx0
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hcont
    hderiv hint
  rw [chap9S_zero, sub_zero] at hFTC
  exact hFTC

private def chap9z (r x : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)

private lemma chap9z_norm {r x : ℝ} (hr0 : 0 ≤ r) : ‖chap9z r x‖ = r := by
  unfold chap9z
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr0, mul_one]

private lemma chap9z_norm_lt_one {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖chap9z r x‖ < 1 := by
  rw [chap9z_norm hr0]
  exact hr1

private lemma chap9z_pow_re {r x : ℝ} (k : ℕ) :
    ((chap9z r x ^ (k + 1) / (((k + 1 : ℕ) : ℂ))) : ℂ).re =
      r ^ (k + 1) * Real.cos (2 * ((((k + 1 : ℕ)) : ℝ)) * x) / ((((k + 1 : ℕ)) : ℝ)) := by
  have hkpos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ)) := by
    have h : 0 < k + 1 := Nat.succ_pos k
    exact_mod_cast h
  have hkne : ((((k + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hkpos
  have hkc : (((k + 1 : ℕ) : ℂ)) = ((((((k + 1 : ℕ)) : ℝ)) : ℂ)) := by
    push_cast
    ring
  have hzpow : chap9z r x ^ (k + 1) = (((r ^ (k + 1) : ℝ) : ℂ)) *
      Complex.exp (((2 * ((((k + 1 : ℕ)) : ℝ)) * x : ℝ) : ℂ) * Complex.I) := by
    unfold chap9z
    rw [mul_pow]
    congr 1
    · push_cast
      ring
    · have hexp : (Complex.exp (((2 * x : ℝ) : ℂ) * Complex.I)) ^ (k + 1) =
          Complex.exp (((k + 1 : ℕ) : ℂ) * ((((2 * x : ℝ) : ℂ) * Complex.I))) := by
        rw [Complex.exp_nat_mul]
      rw [hexp]
      congr 1
      push_cast
      ring
  rw [hzpow, hkc]
  have hexp_re : (Complex.exp (((2 * ((((k + 1 : ℕ)) : ℝ)) * x : ℝ) : ℂ) * Complex.I)).re =
      Real.cos (2 * ((((k + 1 : ℕ)) : ℝ)) * x) := by
    have h := Complex.exp_ofReal_mul_I_re (2 * ((((k + 1 : ℕ)) : ℝ)) * x)
    simpa using h
  have hexp_im : (Complex.exp (((2 * ((((k + 1 : ℕ)) : ℝ)) * x : ℝ) : ℂ) * Complex.I)).im =
      Real.sin (2 * ((((k + 1 : ℕ)) : ℝ)) * x) := by
    have h := Complex.exp_ofReal_mul_I_im (2 * ((((k + 1 : ℕ)) : ℝ)) * x)
    simpa using h
  have hdiv : ((((r ^ (k + 1) : ℝ) : ℂ)) *
      Complex.exp (((2 * ((((k + 1 : ℕ)) : ℝ)) * x : ℝ) : ℂ) * Complex.I) /
        ((((((k + 1 : ℕ)) : ℝ)) : ℂ))).re =
      ((r ^ (k + 1) : ℝ) * Real.cos (2 * ((((k + 1 : ℕ)) : ℝ)) * x) / ((((k + 1 : ℕ)) : ℝ))) := by
    rw [Complex.div_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im]
    rw [hexp_re, hexp_im]
    have hnorm : Complex.normSq ((((((k + 1 : ℕ)) : ℝ)) : ℂ)) = ((((k + 1 : ℕ)) : ℝ)) ^ 2 := by
      rw [Complex.normSq_ofReal]
      ring
    rw [hnorm]
    field_simp
    ring
  exact hdiv

private lemma chap9_cos_hasSum {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasSum (fun j : ℕ =>
      r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ)))
      (-Real.log ‖1 - chap9z r x‖) := by
  have hz : ‖chap9z r x‖ < 1 := chap9z_norm_lt_one hr0 hr1
  have hsum := Complex.hasSum_taylorSeries_neg_log' hz
  have hre := Complex.reCLM.hasSum hsum
  have hfun : (fun j : ℕ => Complex.reCLM
      (chap9z r x ^ (j + 1) / (((j : ℂ) + 1)))) =
      (fun j : ℕ => r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) := by
    funext j
    have hcast : (((j : ℂ) + 1)) = (((j + 1 : ℕ) : ℂ)) := by
      push_cast
      ring
    rw [hcast]
    have h1 : Complex.reCLM (chap9z r x ^ (j + 1) / (((j + 1 : ℕ) : ℂ))) =
        ((chap9z r x ^ (j + 1) / (((j + 1 : ℕ) : ℂ))) : ℂ).re := by
      rw [Complex.reCLM_apply]
    rw [h1, chap9z_pow_re]
  have hval : Complex.reCLM (-Complex.log (1 - chap9z r x)) =
      -Real.log ‖1 - chap9z r x‖ := by
    have h1 : Complex.reCLM (-Complex.log (1 - chap9z r x)) =
        ((-Complex.log (1 - chap9z r x)) : ℂ).re := by
      rw [Complex.reCLM_apply]
    rw [h1, Complex.neg_re, Complex.log_re]
  rw [hfun, hval] at hre
  exact hre

private lemma chap9S_deriv_eq_log {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' j : ℕ, 2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) /
      ((((j + 1 : ℕ)) : ℝ))) = -2 * Real.log ‖1 - chap9z r x‖ := by
  have hcos := chap9_cos_hasSum hr0 hr1 (x := x)
  have hsumm : Summable (fun j : ℕ => r ^ (j + 1) *
      Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) :=
    ⟨_, hcos⟩
  have htsum : (∑' j : ℕ, r ^ (j + 1) *
      Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) =
      -Real.log ‖1 - chap9z r x‖ :=
    hcos.tsum_eq
  have hfun : (fun j : ℕ => 2 * r ^ (j + 1) *
      Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) =
      (fun j : ℕ => (2 : ℝ) * (r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ)))) := by
    funext j
    ring
  rw [hfun, Summable.tsum_mul_left 2 hsumm, htsum]
  ring

private lemma chap9S_eq_log_integral {r x : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx0 : 0 ≤ x) :
    chap9S r x = ∫ u in (0 : ℝ)..x, (-2 * Real.log ‖1 - chap9z r u‖) := by
  have hSint := chap9S_integral hr0 hr1 hx0
  have hfun : (fun u : ℝ => ∑' j : ℕ,
      2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * u) /
        ((((j + 1 : ℕ)) : ℝ))) =
      (fun u : ℝ => -2 * Real.log ‖1 - chap9z r u‖) := by
    funext u
    exact chap9S_deriv_eq_log hr0 hr1
  rw [hfun] at hSint
  exact hSint.symm

private lemma chap9S_tendsto (x : ℝ) :
    Filter.Tendsto (fun n : ℕ => chap9S (chap9r n) x) Filter.atTop
      (nhds (chap9S 1 x)) := by
  have hbound_summ : Summable (fun j : ℕ => (1 : ℝ) / ((((j : ℝ) + 1)) ^ 2)) :=
    chap9_aux_summable
  have hterm_tendsto : ∀ j : ℕ, Filter.Tendsto
      (fun n : ℕ => (chap9r n) ^ (j + 1) * chapter9SineFourierTwoTerm x j)
      Filter.atTop (nhds (chapter9SineFourierTwoTerm x j)) := by
    intro j
    have hpow : Filter.Tendsto (fun n : ℕ => (chap9r n) ^ (j + 1))
        Filter.atTop (nhds 1) := by
      have h := chap9r_tendsto.pow (j + 1)
      simpa using h
    have hmul := hpow.mul_const (chapter9SineFourierTwoTerm x j)
    simpa using hmul
  have hbound : ∀ᶠ n : ℕ in Filter.atTop, ∀ j : ℕ,
      ‖(chap9r n) ^ (j + 1) * chapter9SineFourierTwoTerm x j‖ ≤
        (1 : ℝ) / ((((j : ℝ) + 1)) ^ 2) := by
    apply Filter.Eventually.of_forall
    intro n j
    have hr0 := chap9r_nonneg n
    have hr1 : chap9r n ≤ 1 := le_of_lt (chap9r_lt_one n)
    have hrpow_nonneg : (0 : ℝ) ≤ (chap9r n) ^ (j + 1) := pow_nonneg hr0 _
    have hrpow_le : (chap9r n) ^ (j + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hfour := aux_fourier_abs x j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hrpow_nonneg]
    calc (chap9r n) ^ (j + 1) * |chapter9SineFourierTwoTerm x j|
          ≤ 1 * (1 / ((((j : ℝ) + 1)) ^ 2)) := by
            apply mul_le_mul hrpow_le hfour (abs_nonneg _) (by positivity)
        _ = 1 / ((((j : ℝ) + 1)) ^ 2) := one_mul _
  have htannery := tendsto_tsum_of_dominated_convergence hbound_summ
    hterm_tendsto hbound
  have hfun_eq : (fun n : ℕ => ∑' j : ℕ,
      (chap9r n) ^ (j + 1) * chapter9SineFourierTwoTerm x j) =
      (fun n : ℕ => chap9S (chap9r n) x) := by
    funext n
    rfl
  have hlim_eq : (∑' j : ℕ, chapter9SineFourierTwoTerm x j) = chap9S 1 x := by
    rw [chap9S_one_eq_fourier]
  rw [hfun_eq, hlim_eq] at htannery
  exact htannery

private lemma chap9z_one_sub_ne_zero {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (1 : ℂ) - chap9z r u ≠ 0 := by
  intro h
  have hnorm : ‖chap9z r u‖ = 1 := by
    have h1 : chap9z r u = 1 := sub_eq_zero.mp h |>.symm
    rw [h1, norm_one]
  rw [chap9z_norm hr0] at hnorm
  linarith

private lemma chap9z_re_im (r u : ℝ) :
    (chap9z r u).re = r * Real.cos (2 * u) ∧
      (chap9z r u).im = r * Real.sin (2 * u) := by
  unfold chap9z
  have hexp_re : (Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I)).re =
      Real.cos (2 * u) := by
    have h := Complex.exp_ofReal_mul_I_re (2 * u)
    simpa using h
  have hexp_im : (Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I)).im =
      Real.sin (2 * u) := by
    have h := Complex.exp_ofReal_mul_I_im (2 * u)
    simpa using h
  constructor
  · rw [Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    rw [hexp_re, hexp_im]
    ring
  · rw [Complex.mul_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    rw [hexp_re, hexp_im]
    ring

private lemma chap9z_normSq {r u : ℝ} :
    Complex.normSq (1 - chap9z r u) =
      1 - 2 * r * Real.cos (2 * u) + r ^ 2 := by
  have hre := (chap9z_re_im r u).1
  have him := (chap9z_re_im r u).2
  have hwre : ((1 : ℂ) - chap9z r u).re = 1 - r * Real.cos (2 * u) := by
    rw [Complex.sub_re]
    simp only [Complex.one_re]
    rw [hre]
  have hwim : ((1 : ℂ) - chap9z r u).im = -(r * Real.sin (2 * u)) := by
    rw [Complex.sub_im]
    simp only [Complex.one_im]
    rw [him]
    ring
  rw [Complex.normSq_apply, hwre, hwim]
  have hcos2 : Real.cos (2 * u) ^ 2 + Real.sin (2 * u) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq (2 * u)
  nlinarith [hcos2]

private lemma chap9z_normSq_eq {r u : ℝ} :
    Complex.normSq (1 - chap9z r u) =
      (1 - r) ^ 2 + 4 * r * Real.sin u ^ 2 := by
  rw [chap9z_normSq]
  have hcos : Real.cos (2 * u) = 1 - 2 * Real.sin u ^ 2 :=
    Real.cos_two_mul_eq_one_sub u
  rw [hcos]
  ring

private lemma chap9z_norm_ne_zero {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ‖1 - chap9z r u‖ ≠ 0 := by
  have hne := chap9z_one_sub_ne_zero hr0 hr1 (u := u)
  exact norm_ne_zero_iff.mpr hne

private lemma chap9z_norm_pos {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 < ‖1 - chap9z r u‖ :=
  lt_of_le_of_ne (norm_nonneg _) (Ne.symm (chap9z_norm_ne_zero hr0 hr1))

private lemma chap9z_norm_le_two {r u : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    ‖1 - chap9z r u‖ ≤ 2 := by
  calc ‖1 - chap9z r u‖ ≤ ‖(1 : ℂ)‖ + ‖chap9z r u‖ := norm_sub_le _ _
    _ = 1 + r := by rw [norm_one, chap9z_norm hr0]
    _ ≤ 2 := by linarith

private lemma chap9z_norm_lower {r u : ℝ} (hr_half : (1 / 2 : ℝ) ≤ r)
    (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    Real.sqrt 2 * Real.sin u ≤ ‖1 - chap9z r u‖ := by
  have hsin_pos : 0 < Real.sin u := by
    have hpi := Real.pi_pos
    exact Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith)
  have hsin_nonneg : (0 : ℝ) ≤ Real.sin u := le_of_lt hsin_pos
  have hsqrt_nonneg : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have ha_nonneg : (0 : ℝ) ≤ Real.sqrt 2 * Real.sin u :=
    mul_nonneg hsqrt_nonneg hsin_nonneg
  have hb_nonneg : (0 : ℝ) ≤ ‖1 - chap9z r u‖ := norm_nonneg _
  have hsq2 : (Real.sqrt 2 * Real.sin u) ^ 2 = 2 * Real.sin u ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
  have hnormsq : Complex.normSq (1 - chap9z r u) =
      (1 - r) ^ 2 + 4 * r * Real.sin u ^ 2 :=
    chap9z_normSq_eq
  have hge : 2 * Real.sin u ^ 2 ≤ Complex.normSq (1 - chap9z r u) := by
    rw [hnormsq]
    have h1 : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (4 * r - 2) * Real.sin u ^ 2 := by
      apply mul_nonneg _ (sq_nonneg _)
      linarith
    nlinarith [h1, h2]
  have hnorm_eq : ‖1 - chap9z r u‖ ^ 2 = Complex.normSq (1 - chap9z r u) :=
    Complex.sq_norm _
  have hle : (Real.sqrt 2 * Real.sin u) ^ 2 ≤ ‖1 - chap9z r u‖ ^ 2 := by
    rw [hsq2, hnorm_eq]
    exact hge
  exact (sq_le_sq₀ ha_nonneg hb_nonneg).mp hle

private lemma chap9z_log_bound {r u : ℝ} (hr_half : (1 / 2 : ℝ) ≤ r) (hr1 : r < 1)
    (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    |Real.log ‖1 - chap9z r u‖| ≤ |Real.log (Real.sin u)| +
      (|Real.log (Real.sqrt 2)| + |Real.log 2|) := by
  have hsin_pos : 0 < Real.sin u := by
    have hpi := Real.pi_pos
    exact Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith)
  have hsin_ne : Real.sin u ≠ 0 := ne_of_gt hsin_pos
  have hsqrt_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := ne_of_gt hsqrt_pos
  have hr0 : (0 : ℝ) ≤ r := by linarith
  have hnorm_pos : (0 : ℝ) < ‖1 - chap9z r u‖ := chap9z_norm_pos hr0 hr1
  have hnorm_le : ‖1 - chap9z r u‖ ≤ 2 := chap9z_norm_le_two hr0 (le_of_lt hr1)
  have hlow_pos : (0 : ℝ) < Real.sqrt 2 * Real.sin u :=
    mul_pos hsqrt_pos hsin_pos
  have hlow_le : Real.sqrt 2 * Real.sin u ≤ ‖1 - chap9z r u‖ :=
    chap9z_norm_lower hr_half hu0 hu
  have hlog_low : Real.log (Real.sqrt 2 * Real.sin u) ≤ Real.log ‖1 - chap9z r u‖ :=
    Real.log_le_log hlow_pos hlow_le
  have hlog_high : Real.log ‖1 - chap9z r u‖ ≤ Real.log 2 :=
    Real.log_le_log hnorm_pos hnorm_le
  have habs_le : |Real.log ‖1 - chap9z r u‖| ≤
      |Real.log (Real.sqrt 2 * Real.sin u)| + |Real.log 2| := by
    have hL : Real.log (Real.sqrt 2 * Real.sin u) ≤ Real.log ‖1 - chap9z r u‖ := hlog_low
    have hU : Real.log ‖1 - chap9z r u‖ ≤ Real.log 2 := hlog_high
    have h1 : -(|Real.log (Real.sqrt 2 * Real.sin u)| + |Real.log 2|) ≤
        Real.log ‖1 - chap9z r u‖ := by
      have hneg1 : -|Real.log (Real.sqrt 2 * Real.sin u)| ≤
          Real.log (Real.sqrt 2 * Real.sin u) := neg_abs_le _
      have hneg2 : -(|Real.log (Real.sqrt 2 * Real.sin u)| + |Real.log 2|) ≤
          -|Real.log (Real.sqrt 2 * Real.sin u)| := by
        have hnn : (0 : ℝ) ≤ |Real.log 2| := abs_nonneg _
        linarith
      linarith
    have h2 : Real.log ‖1 - chap9z r u‖ ≤
        |Real.log (Real.sqrt 2 * Real.sin u)| + |Real.log 2| := by
      have hpos1 : Real.log ‖1 - chap9z r u‖ ≤ Real.log 2 := hU
      have hpos2 : Real.log 2 ≤ |Real.log 2| := le_abs_self _
      have hpos3 : |Real.log 2| ≤
          |Real.log (Real.sqrt 2 * Real.sin u)| + |Real.log 2| := by
        have hnn : (0 : ℝ) ≤ |Real.log (Real.sqrt 2 * Real.sin u)| := abs_nonneg _
        linarith
      linarith
    exact abs_le.mpr ⟨h1, h2⟩
  have hlog_mul : Real.log (Real.sqrt 2 * Real.sin u) =
      Real.log (Real.sqrt 2) + Real.log (Real.sin u) :=
    Real.log_mul hsqrt_ne hsin_ne
  rw [hlog_mul] at habs_le
  have habs_add : |Real.log (Real.sqrt 2) + Real.log (Real.sin u)| ≤
      |Real.log (Real.sqrt 2)| + |Real.log (Real.sin u)| :=
    abs_add_le _ _
  calc |Real.log ‖1 - chap9z r u‖|
        ≤ |Real.log (Real.sqrt 2) + Real.log (Real.sin u)| + |Real.log 2| := habs_le
      _ ≤ (|Real.log (Real.sqrt 2)| + |Real.log (Real.sin u)|) + |Real.log 2| := by
          linarith [habs_add]
      _ = |Real.log (Real.sin u)| + (|Real.log (Real.sqrt 2)| + |Real.log 2|) := by ring

private lemma chap9z_continuous_u (r : ℝ) :
    Continuous (fun u : ℝ => chap9z r u) := by
  unfold chap9z
  have h2u : Continuous (fun u : ℝ => 2 * u) :=
    continuous_const.mul continuous_id
  have hcoe : Continuous (fun u : ℝ => ((2 * u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp h2u
  have hI : Continuous (fun u : ℝ => (((2 * u : ℝ) : ℂ) * Complex.I)) :=
    hcoe.mul continuous_const
  have hexp : Continuous (fun u : ℝ =>
      Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I)) :=
    Complex.continuous_exp.comp hI
  exact continuous_const.mul hexp

private lemma chap9z_one_sub_continuous_u (r : ℝ) :
    Continuous (fun u : ℝ => (1 : ℂ) - chap9z r u) :=
  continuous_const.sub (chap9z_continuous_u r)

private lemma chap9z_norm_continuous_u (r : ℝ) :
    Continuous (fun u : ℝ => ‖1 - chap9z r u‖) :=
  continuous_norm.comp (chap9z_one_sub_continuous_u r)

private lemma chap9z_log_continuous_u {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun u : ℝ => Real.log ‖1 - chap9z r u‖) := by
  have hne : ∀ u : ℝ, ‖1 - chap9z r u‖ ≠ 0 := fun u =>
    chap9z_norm_ne_zero hr0 hr1
  exact (chap9z_norm_continuous_u r).log hne

private lemma chap9z_F_continuous_u {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun u : ℝ => -2 * Real.log ‖1 - chap9z r u‖) :=
  continuous_const.mul (chap9z_log_continuous_u hr0 hr1)

private lemma chap9z_bound_integrable {x : ℝ} :
    MeasureTheory.Integrable
      (fun u : ℝ => 2 * |Real.log (Real.sin u)| +
        (2 * (|Real.log (Real.sqrt 2)| + |Real.log 2|)))
      (MeasureTheory.volume.restrict (Set.Ioc 0 x)) := by
  have hlog_int : IntervalIntegrable (fun u : ℝ => Real.log (Real.sin u))
      MeasureTheory.volume 0 x :=
    intervalIntegrable_log_sin
  have h1 : MeasureTheory.IntegrableOn (fun u : ℝ => Real.log (Real.sin u))
      (Set.Ioc 0 x) MeasureTheory.volume :=
    hlog_int.1
  have h2 : MeasureTheory.Integrable (fun u : ℝ => Real.log (Real.sin u))
      (MeasureTheory.volume.restrict (Set.Ioc 0 x)) :=
    h1.integrable
  have h3 : MeasureTheory.Integrable (fun u : ℝ => ‖Real.log (Real.sin u)‖)
      (MeasureTheory.volume.restrict (Set.Ioc 0 x)) :=
    h2.norm
  have h4 : MeasureTheory.Integrable (fun u : ℝ => |Real.log (Real.sin u)|)
      (MeasureTheory.volume.restrict (Set.Ioc 0 x)) := by
    simpa [Real.norm_eq_abs] using h3
  have h5 : MeasureTheory.Integrable (fun u : ℝ => 2 * |Real.log (Real.sin u)|)
      (MeasureTheory.volume.restrict (Set.Ioc 0 x)) :=
    h4.const_mul 2
  have hconst_int : IntervalIntegrable
      (fun _ : ℝ => (2 * (|Real.log (Real.sqrt 2)| + |Real.log 2|)))
      MeasureTheory.volume 0 x :=
    intervalIntegrable_const
  have h6 : MeasureTheory.Integrable
      (fun _ : ℝ => (2 * (|Real.log (Real.sqrt 2)| + |Real.log 2|)))
      (MeasureTheory.volume.restrict (Set.Ioc 0 x)) :=
    hconst_int.1.integrable
  exact h5.fun_add h6

private lemma chap9z_one_eq_exp (u : ℝ) : chap9z 1 u =
    Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I) := by
  unfold chap9z
  simp

private lemma chap9z_one_norm_eq (u : ℝ) :
    ‖1 - chap9z 1 u‖ = |2 * Real.sin u| := by
  rw [chap9z_one_eq_exp]
  have hcomm : (((2 * u : ℝ) : ℂ) * Complex.I) =
      Complex.I * (((2 * u : ℝ) : ℂ)) := by ring
  rw [hcomm]
  have hlem := Complex.norm_exp_I_mul_ofReal_sub_one (2 * u)
  have hrev : ‖(1 : ℂ) - Complex.exp (Complex.I * (((2 * u : ℝ) : ℂ)))‖ =
      ‖Complex.exp (Complex.I * (((2 * u : ℝ) : ℂ))) - 1‖ :=
    norm_sub_rev _ _
  rw [hrev, hlem]
  have hhalf : (2 * u) / 2 = u := by ring
  rw [hhalf]
  rw [Real.norm_eq_abs]

private lemma chap9z_F_tendsto {u : ℝ} (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    Filter.Tendsto (fun n : ℕ => -2 * Real.log ‖1 - chap9z (chap9r n) u‖)
      Filter.atTop (nhds (-2 * Real.log ‖1 - chap9z 1 u‖)) := by
  have hsin_pos : 0 < Real.sin u := by
    have hpi := Real.pi_pos
    exact Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith)
  have hnorm_ne : ‖1 - chap9z 1 u‖ ≠ 0 := by
    rw [chap9z_one_norm_eq]
    have h2sin_ne : (2 * Real.sin u) ≠ 0 := ne_of_gt (by linarith)
    exact abs_ne_zero.mpr h2sin_ne
  have hr_coe : Filter.Tendsto (fun n : ℕ => ((chap9r n : ℝ) : ℂ))
      Filter.atTop (nhds 1) := by
    have h := (Complex.continuous_ofReal.tendsto 1).comp chap9r_tendsto
    have h1 : (((1 : ℝ) : ℂ)) = 1 := Complex.ofReal_one
    have hfun : (Complex.ofReal ∘ chap9r) = (fun n : ℕ => ((chap9r n : ℝ) : ℂ)) :=
      rfl
    rw [hfun, h1] at h
    exact h
  have hz_tendsto : Filter.Tendsto (fun n : ℕ => chap9z (chap9r n) u)
      Filter.atTop (nhds (chap9z 1 u)) := by
    unfold chap9z
    have hexp_const : ∀ n : ℕ,
        Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I) =
          Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I) := fun _ => rfl
    have hmul := hr_coe.mul_const (Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I))
    have h1 : (1 : ℂ) * Complex.exp (((2 * u : ℝ) : ℂ) * Complex.I) =
        chap9z 1 u := by
      unfold chap9z
      simp
    simpa [h1] using hmul
  have hsub : Filter.Tendsto (fun n : ℕ => (1 : ℂ) - chap9z (chap9r n) u)
      Filter.atTop (nhds (1 - chap9z 1 u)) :=
    Filter.Tendsto.const_sub 1 hz_tendsto
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖1 - chap9z (chap9r n) u‖)
      Filter.atTop (nhds ‖1 - chap9z 1 u‖) :=
    hsub.norm
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log ‖1 - chap9z (chap9r n) u‖)
      Filter.atTop (nhds (Real.log ‖1 - chap9z 1 u‖)) :=
    (Real.continuousAt_log hnorm_ne).tendsto.comp hnorm
  have hmul := Filter.Tendsto.const_mul (-2 : ℝ) hlog
  simpa using hmul

private lemma chap9z_integral_tendsto {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ Real.pi / 2) :
    Filter.Tendsto (fun n : ℕ => ∫ u in (0 : ℝ)..x,
      (-2 * Real.log ‖1 - chap9z (chap9r n) u‖))
      Filter.atTop (nhds (∫ u in (0 : ℝ)..x,
        (-2 * Real.log ‖1 - chap9z 1 u‖))) := by
  let μ : MeasureTheory.Measure ℝ :=
    MeasureTheory.volume.restrict (Set.Ioc 0 x)
  have hmeas : MeasurableSet (Set.Ioc (0 : ℝ) x) := measurableSet_Ioc
  have hF_meas : ∀ n : ℕ, MeasureTheory.AEStronglyMeasurable
      (fun u : ℝ => -2 * Real.log ‖1 - chap9z (chap9r n) u‖) μ := by
    intro n
    exact (chap9z_F_continuous_u (chap9r_nonneg n)
      (chap9r_lt_one n)).aestronglyMeasurable
  have hbound_int : MeasureTheory.Integrable
      (fun u : ℝ => 2 * |Real.log (Real.sin u)| +
        (2 * (|Real.log (Real.sqrt 2)| + |Real.log 2|))) μ :=
    chap9z_bound_integrable
  have h_bound : ∀ n : ℕ, ∀ᵐ a : ℝ ∂μ,
      ‖-2 * Real.log ‖1 - chap9z (chap9r n) a‖‖ ≤
        2 * |Real.log (Real.sin a)| +
          (2 * (|Real.log (Real.sqrt 2)| + |Real.log 2|)) := by
    intro n
    apply MeasureTheory.ae_restrict_of_forall_mem hmeas
    intro u hu
    rw [Set.mem_Ioc] at hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hux : u ≤ x := hu.2
    have hu_pi : u ≤ Real.pi / 2 := le_trans hux hx
    have hr_half : (1 / 2 : ℝ) ≤ chap9r n := (chap9r_mem_Ico n).1
    have hr1 : chap9r n < 1 := chap9r_lt_one n
    have hlog := chap9z_log_bound hr_half hr1 hu0 hu_pi
    rw [Real.norm_eq_abs]
    have habs : |-2 * Real.log ‖1 - chap9z (chap9r n) u‖| =
        2 * |Real.log ‖1 - chap9z (chap9r n) u‖| := by
      rw [abs_mul]
      simp only [abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [habs]
    linarith [hlog]
  have h_lim : ∀ᵐ a : ℝ ∂μ, Filter.Tendsto
      (fun n : ℕ => -2 * Real.log ‖1 - chap9z (chap9r n) a‖)
      Filter.atTop (nhds (-2 * Real.log ‖1 - chap9z 1 a‖)) := by
    apply MeasureTheory.ae_restrict_of_forall_mem hmeas
    intro u hu
    rw [Set.mem_Ioc] at hu
    have hu0 : (0 : ℝ) < u := hu.1
    have hux : u ≤ x := hu.2
    have hu_pi : u ≤ Real.pi / 2 := le_trans hux hx
    exact chap9z_F_tendsto hu0 hu_pi
  have htend := MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun u : ℝ => 2 * |Real.log (Real.sin u)| +
      (2 * (|Real.log (Real.sqrt 2)| + |Real.log 2|)))
    hF_meas hbound_int h_bound h_lim
  have hfun_n : ∀ n : ℕ, (∫ a : ℝ, -2 * Real.log ‖1 - chap9z (chap9r n) a‖ ∂μ) =
      (∫ u in (0 : ℝ)..x, -2 * Real.log ‖1 - chap9z (chap9r n) u‖) := by
    intro n
    unfold μ
    rw [← intervalIntegral.integral_of_le hx0]
  have hfun_lim : (∫ a : ℝ, -2 * Real.log ‖1 - chap9z 1 a‖ ∂μ) =
      (∫ u in (0 : ℝ)..x, -2 * Real.log ‖1 - chap9z 1 u‖) := by
    unfold μ
    rw [← intervalIntegral.integral_of_le hx0]
  have hfun_eq : (fun n : ℕ => ∫ a : ℝ, -2 * Real.log ‖1 - chap9z (chap9r n) a‖ ∂μ) =
      (fun n : ℕ => ∫ u in (0 : ℝ)..x, -2 * Real.log ‖1 - chap9z (chap9r n) u‖) := by
    funext n
    exact hfun_n n
  rw [hfun_eq, hfun_lim] at htend
  exact htend

private lemma chap9S_one_eq_neg_mul_log_integral {x : ℝ} (hx0 : 0 ≤ x)
    (hx : x ≤ Real.pi / 2) :
    chap9S 1 x = -2 * ∫ u in (0 : ℝ)..x, Real.log |2 * Real.sin u| := by
  have hS_tend := chap9S_tendsto x
  have hI_tend := chap9z_integral_tendsto hx0 hx
  have heq : ∀ n : ℕ, chap9S (chap9r n) x =
      ∫ u in (0 : ℝ)..x, -2 * Real.log ‖1 - chap9z (chap9r n) u‖ := by
    intro n
    exact chap9S_eq_log_integral (chap9r_nonneg n) (chap9r_lt_one n) hx0
  have hfun : (fun n : ℕ => chap9S (chap9r n) x) =
      (fun n : ℕ => ∫ u in (0 : ℝ)..x, -2 * Real.log ‖1 - chap9z (chap9r n) u‖) := by
    funext n
    exact heq n
  rw [← hfun] at hI_tend
  have hlim : chap9S 1 x =
      ∫ u in (0 : ℝ)..x, -2 * Real.log ‖1 - chap9z 1 u‖ :=
    tendsto_nhds_unique hS_tend hI_tend
  have hfun2 : (fun u : ℝ => -2 * Real.log ‖1 - chap9z 1 u‖) =
      (fun u : ℝ => -2 * Real.log |2 * Real.sin u|) := by
    funext u
    rw [chap9z_one_norm_eq]
  rw [hfun2] at hlim
  rw [hlim, intervalIntegral.integral_const_mul]

private lemma chap9_log_abs_eq {u : ℝ} (hu0 : 0 < u) (hu : u ≤ Real.pi / 2) :
    Real.log |2 * Real.sin u| = Real.log 2 + Real.log (Real.sin u) := by
  have hsin_pos : 0 < Real.sin u := by
    have hpi := Real.pi_pos
    exact Real.sin_pos_of_pos_of_lt_pi hu0 (by linarith)
  have h2sin_pos : (0 : ℝ) < 2 * Real.sin u := by linarith
  have habs : |2 * Real.sin u| = 2 * Real.sin u := abs_of_pos h2sin_pos
  rw [habs]
  exact Real.log_mul (by norm_num) (ne_of_gt hsin_pos)

private lemma chap9_main_nonneg {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 2) :
    chap9Phi x = chapter9Entry16LogTerm x +
      (1 / 2 : ℝ) * ∑' j : ℕ, chapter9SineFourierTwoTerm x j := by
  by_cases hx00 : x = 0
  · subst hx00
    rw [chap9Phi_zero]
    unfold chapter9Entry16LogTerm chapter9SineFourierTwoTerm
    simp only [ite_true, Real.sin_zero, mul_zero, zero_div]
    simp
  · have hxpos : (0 : ℝ) < x := lt_of_le_of_ne hx0 (Ne.symm hx00)
    have hsin_pos : 0 < Real.sin x := by
      have hpi := Real.pi_pos
      exact Real.sin_pos_of_pos_of_lt_pi hxpos (by linarith)
    have hPhi : chap9Phi x = ∫ θ in (0 : ℝ)..x, chap9D θ := by
      rw [chap9Phi_integral_general hx0 hx]
    have hA : chap9A x =
        ∫ θ in (0 : ℝ)..x, (Real.log (Real.sin θ) + chap9D θ) := by
      rw [chap9A_integral_general hx0 hx]
    have hS : chap9S 1 x = -2 * ∫ u in (0 : ℝ)..x, Real.log |2 * Real.sin u| :=
      chap9S_one_eq_neg_mul_log_integral hx0 hx
    have hFourier : (∑' j : ℕ, chapter9SineFourierTwoTerm x j) = chap9S 1 x := by
      rw [chap9S_one_eq_fourier]
    have hLogTerm : chapter9Entry16LogTerm x = x * Real.log |2 * Real.sin x| := by
      unfold chapter9Entry16LogTerm
      simp [hx00]
    have hlog_abs : ∀ u ∈ Set.Ioc (0 : ℝ) x,
        Real.log |2 * Real.sin u| = Real.log 2 + Real.log (Real.sin u) := by
      intro u hu
      rw [Set.mem_Ioc] at hu
      exact chap9_log_abs_eq hu.1 (le_trans hu.2 hx)
    have hlog_int : IntervalIntegrable (fun u : ℝ => Real.log (Real.sin u))
        MeasureTheory.volume 0 x :=
      intervalIntegrable_log_sin
    have hconst_int : IntervalIntegrable (fun _ : ℝ => Real.log 2)
        MeasureTheory.volume 0 x :=
      intervalIntegrable_const
    have hadd_int : IntervalIntegrable
        (fun u : ℝ => Real.log 2 + Real.log (Real.sin u))
        MeasureTheory.volume 0 x :=
      hconst_int.add hlog_int
    have hsplit : (∫ u in (0 : ℝ)..x, Real.log |2 * Real.sin u|) =
        (∫ u in (0 : ℝ)..x, Real.log 2) +
          (∫ u in (0 : ℝ)..x, Real.log (Real.sin u)) := by
      have heq : Set.EqOn (fun u : ℝ => Real.log |2 * Real.sin u|)
          (fun u : ℝ => Real.log 2 + Real.log (Real.sin u))
          (Set.Ioc 0 x) := hlog_abs
      have hae := heq.aeEq_restrict (μ := MeasureTheory.volume) measurableSet_Ioc
      have hset_eq : (∫ u in Set.Ioc (0 : ℝ) x, Real.log |2 * Real.sin u| ∂MeasureTheory.volume) =
          (∫ u in Set.Ioc (0 : ℝ) x, Real.log 2 + Real.log (Real.sin u) ∂MeasureTheory.volume) :=
        MeasureTheory.integral_congr_ae hae
      have h1 : (∫ u in (0 : ℝ)..x, Real.log |2 * Real.sin u|) =
          (∫ u in Set.Ioc (0 : ℝ) x, Real.log |2 * Real.sin u| ∂MeasureTheory.volume) :=
        intervalIntegral.integral_of_le hx0
      have h2 : (∫ u in (0 : ℝ)..x, Real.log 2 + Real.log (Real.sin u)) =
          (∫ u in Set.Ioc (0 : ℝ) x, Real.log 2 + Real.log (Real.sin u) ∂MeasureTheory.volume) :=
        intervalIntegral.integral_of_le hx0
      have h3 : (∫ u in (0 : ℝ)..x, Real.log |2 * Real.sin u|) =
          (∫ u in (0 : ℝ)..x, Real.log 2 + Real.log (Real.sin u)) :=
        h1.trans (hset_eq.trans h2.symm)
      have h4 : (∫ u in (0 : ℝ)..x, Real.log 2 + Real.log (Real.sin u)) =
          (∫ u in (0 : ℝ)..x, Real.log 2) +
            (∫ u in (0 : ℝ)..x, Real.log (Real.sin u)) :=
        intervalIntegral.integral_add hconst_int hlog_int
      exact h3.trans h4
    have hsub : Set.Icc (0 : ℝ) x ⊆ Set.Icc (0 : ℝ) (Real.pi / 2) := by
      intro y hy
      rw [Set.mem_Icc] at hy ⊢
      constructor <;> linarith [hy.1, hy.2, hx]
    have hD_int : IntervalIntegrable chap9D MeasureTheory.volume 0 x :=
      (chap9D_continuousOn.mono hsub).intervalIntegrable_of_Icc hx0
    have hA_split : (∫ θ in (0 : ℝ)..x, Real.log (Real.sin θ) + chap9D θ) =
        (∫ θ in (0 : ℝ)..x, Real.log (Real.sin θ)) +
          (∫ θ in (0 : ℝ)..x, chap9D θ) :=
      intervalIntegral.integral_add hlog_int hD_int
    have hconst_eq : (∫ _ in (0 : ℝ)..x, Real.log 2) = x * Real.log 2 := by
      rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    have hlogx_eq : Real.log |2 * Real.sin x| =
        Real.log 2 + Real.log (Real.sin x) :=
      chap9_log_abs_eq hxpos hx
    have hA_eq : chap9A x = x * Real.log (Real.sin x) := rfl
    rw [hPhi, hLogTerm, hFourier, hS, hsplit, hconst_eq, hlogx_eq]
    rw [hA_split] at hA
    rw [hA_eq] at hA
    linear_combination -hA

/-- **The central binomial series in $\sin x$ and $x \log|2\sin x|$.** Let $x$ be a real number
with $|x| \le \pi/2$, and let $L(x) = x \log|2\sin x|$ for $x \ne 0$ and $L(0) = 0$. Then
$|2\sin x| > 0$ if $x \ne 0$, the series
$S(x) = \sum_{k=0}^{\infty} \binom{2k}{k} \frac{\sin^{2k+1} x}{2^{2k} (2k+1)^2}$ and
$F(x) = \sum_{k=1}^{\infty} \frac{\sin 2kx}{k^2}$ are both summable, and
$S(x) = L(x) + \frac{1}{2} F(x)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry16_tan (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    (x ≠ 0 → 0 < |2 * Real.sin x|) ∧
      Summable (Entry16Tanseries.chapter9CentralSineTerm x) ∧
      Summable (chapter9SineFourierTwoTerm x) ∧
      (∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm x k) =
        chapter9Entry16LogTerm x +
          (1 / 2 : ℝ) * ∑' j : ℕ, chapter9SineFourierTwoTerm x j := by
  refine ⟨aux_pos x hx, aux_summable_central x, aux_summable_fourier x, ?_⟩
  by_cases hx0 : x = 0
  · subst hx0
    simp [Entry16Tanseries.chapter9CentralSineTerm, chapter9SineFourierTwoTerm,
      chapter9Entry16LogTerm, Real.sin_zero]
  · by_cases hx_nonneg : 0 ≤ x
    · have hx_le : x ≤ Real.pi / 2 := le_trans (le_abs_self x) hx
      rw [← chap9Phi_eq_central_tsum x]
      exact chap9_main_nonneg hx_nonneg hx_le
    · have hx_lt : x < 0 := lt_of_not_ge hx_nonneg
      have hy_nonneg : (0 : ℝ) ≤ -x := le_of_lt (neg_pos.mpr hx_lt)
      have hy_le : -x ≤ Real.pi / 2 := le_trans (neg_le_abs x) hx
      have hmain : chap9Phi (-x) = chapter9Entry16LogTerm (-x) +
          (1 / 2 : ℝ) * ∑' j : ℕ, chapter9SineFourierTwoTerm (-x) j :=
        chap9_main_nonneg hy_nonneg hy_le
      have hPhi : chap9Phi (-x) =
          ∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm (-x) k :=
        chap9Phi_eq_central_tsum (-x)
      have hC_odd : ∀ k : ℕ, Entry16Tanseries.chapter9CentralSineTerm (-x) k =
          -Entry16Tanseries.chapter9CentralSineTerm x k := by
        intro k
        unfold Entry16Tanseries.chapter9CentralSineTerm
        rw [Real.sin_neg]
        have h2 : (-Real.sin x) ^ (2 * k) = (Real.sin x) ^ (2 * k) := by
          rw [pow_mul, pow_mul]
          have hsq : (-Real.sin x) ^ 2 = (Real.sin x) ^ 2 := by ring
          rw [hsq]
        have hpow : (-Real.sin x) ^ (2 * k + 1) =
            -(Real.sin x ^ (2 * k + 1)) := by
          calc (-Real.sin x) ^ (2 * k + 1)
              = (-Real.sin x) ^ (2 * k) * (-Real.sin x) := by
                rw [pow_succ]
            _ = (Real.sin x) ^ (2 * k) * (-Real.sin x) := by rw [h2]
            _ = -((Real.sin x) ^ (2 * k) * Real.sin x) := by ring
            _ = -(Real.sin x ^ (2 * k + 1)) := by rw [pow_succ]
        rw [hpow]
        ring
      have hF_odd : ∀ j : ℕ, chapter9SineFourierTwoTerm (-x) j =
          -chapter9SineFourierTwoTerm x j := by
        intro j
        have h1 : chapter9SineFourierTwoTerm (-x) j =
            Real.sin (2 * ((((j + 1 : ℕ))) : ℝ) * (-x)) /
              ((((j + 1 : ℕ))) : ℝ) ^ 2 := rfl
        have h2 : chapter9SineFourierTwoTerm x j =
            Real.sin (2 * ((((j + 1 : ℕ))) : ℝ) * x) /
              ((((j + 1 : ℕ))) : ℝ) ^ 2 := rfl
        rw [h1, h2]
        have harg : 2 * ((((j + 1 : ℕ))) : ℝ) * (-x) =
            -(2 * ((((j + 1 : ℕ))) : ℝ) * x) := by ring
        rw [harg, Real.sin_neg]
        ring
      have hx_neg_ne : -x ≠ 0 := neg_ne_zero.mpr hx0
      have hL_odd : chapter9Entry16LogTerm (-x) =
          -chapter9Entry16LogTerm x := by
        unfold chapter9Entry16LogTerm
        simp [hx_neg_ne, hx0]
      have hC_tsum : (∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm (-x) k) =
          -(∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm x k) := by
        have hcongr : (∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm (-x) k) =
            ∑' k : ℕ, -Entry16Tanseries.chapter9CentralSineTerm x k :=
          tsum_congr hC_odd
        rw [hcongr, tsum_neg]
      have hF_tsum : (∑' j : ℕ, chapter9SineFourierTwoTerm (-x) j) =
          -(∑' j : ℕ, chapter9SineFourierTwoTerm x j) := by
        have hcongr : (∑' j : ℕ, chapter9SineFourierTwoTerm (-x) j) =
            ∑' j : ℕ, -chapter9SineFourierTwoTerm x j :=
          tsum_congr hF_odd
        rw [hcongr, tsum_neg]
      have heq_neg : (∑' k : ℕ, Entry16Tanseries.chapter9CentralSineTerm (-x) k) =
          chapter9Entry16LogTerm (-x) +
            (1 / 2 : ℝ) * ∑' j : ℕ, chapter9SineFourierTwoTerm (-x) j := by
        rw [← hPhi]
        exact hmain
      rw [hC_tsum, hL_odd, hF_tsum] at heq_neg
      linear_combination -heq_neg

end
end Entry16Tan
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
