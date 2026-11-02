/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry23Ramanujanpi2

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Filter Finset Topology MeasureTheory
open Entry8Arcsin (chapter9OddHarmonic)

noncomputable section

def chapter9Entry23LeftTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  (-1 : ℝ) ^ j * chapter9OddHarmonic k * Real.tan x ^ (2 * k) /
    (((2 * k : ℕ) : ℝ) ^ 2)

def chapter9Entry23FactorialTerm (u : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
    (((2 * k + 1).factorial : ℝ) * (((2 * k + 2 : ℕ) : ℝ) ^ 2))

private lemma oddHarmonic_nonneg (n : ℕ) : 0 ≤ chapter9OddHarmonic n := by
  unfold chapter9OddHarmonic
  apply Finset.sum_nonneg
  intro i _
  positivity

private lemma oddHarmonic_le_card (n : ℕ) : chapter9OddHarmonic n ≤ (n : ℝ) := by
  unfold chapter9OddHarmonic
  calc ∑ i ∈ Finset.range n, (1 : ℝ) / (((2 * i + 1 : ℕ)) : ℝ)
      ≤ ∑ _i ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [div_le_one (Nat.cast_pos.mpr (by omega : 0 < 2 * i + 1))]
        calc (1 : ℝ) = ((((1 : ℕ))) : ℝ) := by norm_num
          _ ≤ ((((2 * i + 1 : ℕ))) : ℝ) := Nat.cast_le.mpr (by omega)
    _ = (n : ℝ) := by simp

private lemma harmonic_cast_eq (n : ℕ) :
    ((harmonic n : ℚ) : ℝ) = ∑ i ∈ Finset.range n, 1 / ((((i + 1 : ℕ))) : ℝ) := by
  have hdef : harmonic n = ∑ i ∈ Finset.range n, ((i + 1 : ℕ) : ℚ)⁻¹ := rfl
  rw [hdef, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Rat.cast_inv, Rat.cast_natCast, Rat.cast_add, Rat.cast_one,
    Nat.cast_add, Nat.cast_one, one_div]

private lemma oddHarmonic_le_one_add_log (n : ℕ) :
    chapter9OddHarmonic n ≤ 1 + Real.log (n : ℝ) := by
  have hle : ∀ i ∈ Finset.range n,
      (1 : ℝ) / ((((2 * i + 1 : ℕ))) : ℝ) ≤ 1 / ((((i + 1 : ℕ))) : ℝ) := by
    intro i _
    apply one_div_le_one_div_of_le
    · exact Nat.cast_pos.mpr (by omega)
    · exact Nat.cast_le.mpr (by omega)
  calc chapter9OddHarmonic n
      = ∑ i ∈ Finset.range n, (1 : ℝ) / ((((2 * i + 1 : ℕ))) : ℝ) := rfl
    _ ≤ ∑ i ∈ Finset.range n, (1 : ℝ) / ((((i + 1 : ℕ))) : ℝ) :=
        Finset.sum_le_sum hle
    _ = ((harmonic n : ℚ) : ℝ) := (harmonic_cast_eq n).symm
    _ ≤ 1 + Real.log (n : ℝ) := harmonic_le_one_add_log n

private lemma one_add_log_le_three_rpow (m : ℝ) (hm : 1 ≤ m) :
    1 + Real.log m ≤ 3 * m ^ ((1 / 2 : ℝ)) := by
  have hm0 : (0 : ℝ) < m := by linarith
  have h2 : Real.log (Real.sqrt m) = Real.log m / 2 := Real.log_sqrt hm0.le
  have h1 : Real.log (Real.sqrt m) ≤ Real.sqrt m - 1 :=
    Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hm0)
  have h3 : (1 : ℝ) ≤ Real.sqrt m := Real.one_le_sqrt.mpr hm
  have hsqrt_eq : Real.sqrt m = m ^ ((1 / 2 : ℝ)) := Real.sqrt_eq_rpow m
  have hrw : (0 : ℝ) ≤ m ^ ((1 / 2 : ℝ)) := Real.rpow_nonneg hm0.le _
  linarith

private lemma rpow_half_mul_three_half (m : ℝ) (hm : 0 < m) :
    m ^ ((1 / 2 : ℝ)) * m ^ ((3 / 2 : ℝ)) = m ^ (2 : ℕ) := by
  have h1 : ((1 / 2 : ℝ)) + (3 / 2 : ℝ) = (2 : ℝ) := by norm_num
  calc m ^ ((1 / 2 : ℝ)) * m ^ ((3 / 2 : ℝ))
      = m ^ ((1 / 2 : ℝ) + (3 / 2 : ℝ)) := (Real.rpow_add hm _ _).symm
    _ = m ^ (2 : ℝ) := by rw [h1]
    _ = m ^ (2 : ℕ) := by
        rw [show (2 : ℝ) = ((((2 : ℕ))) : ℝ) by norm_num]
        exact Real.rpow_natCast m 2

private lemma sqrt2_lt_two : Real.sqrt 2 < 2 := by
  have h : Real.sqrt 2 < Real.sqrt 4 :=
    Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h

private lemma sqrt2d2_lt_one : Real.sqrt 2 / 2 < 1 := by
  have h2 := sqrt2_lt_two
  linarith

private lemma abs_tan_le_one_of_mem (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    |Real.tan x| ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx1 : -(Real.pi / 4) ≤ x := (abs_le.mp hx).1
  have hx2 : x ≤ Real.pi / 4 := (abs_le.mp hx).2
  have hmem1 : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmemPi : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmemN : -Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hle : Real.tan x ≤ 1 := by
    have h := (Real.strictMonoOn_tan.le_iff_le hmem1 hmemPi).mpr hx2
    rwa [Real.tan_pi_div_four] at h
  have hge : (-1 : ℝ) ≤ Real.tan x := by
    have h := (Real.strictMonoOn_tan.le_iff_le hmemN hmem1).mpr
      (by linarith : -Real.pi / 4 ≤ x)
    rw [show (-Real.pi / 4) = -(Real.pi / 4) by ring, Real.tan_neg,
      Real.tan_pi_div_four] at h
    linarith
  exact abs_le.mpr ⟨by linarith, hle⟩

private lemma abs_sin_le_sqrt2d2_of_mem (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    |Real.sin x| ≤ Real.sqrt 2 / 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx1 : -(Real.pi / 4) ≤ x := (abs_le.mp hx).1
  have hx2 : x ≤ Real.pi / 4 := (abs_le.mp hx).2
  have hmem1 : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hmemPi : Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hmemN : -Real.pi / 4 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hle : Real.sin x ≤ Real.sqrt 2 / 2 := by
    have h := (Real.strictMonoOn_sin.le_iff_le hmem1 hmemPi).mpr hx2
    rwa [Real.sin_pi_div_four] at h
  have hge : -(Real.sqrt 2 / 2) ≤ Real.sin x := by
    have h := (Real.strictMonoOn_sin.le_iff_le hmemN hmem1).mpr
      (by linarith : -Real.pi / 4 ≤ x)
    rw [show (-Real.pi / 4) = -(Real.pi / 4) by ring, Real.sin_neg,
      Real.sin_pi_div_four] at h
    linarith
  exact abs_le.mpr ⟨by linarith, hle⟩

private lemma factCoeff_le_one_aux : ∀ k : ℕ,
    (2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2
      ≤ ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
  intro k
  induction k with
  | zero => norm_num
  | succ k ih =>
    have e1 : (2 : ℝ) ^ (2 * (k + 1)) = 4 * (2 : ℝ) ^ (2 * k) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
      ring
    have e2 : ((((k + 1).factorial : ℕ)) : ℝ)
        = ((k : ℝ) + 1) * ((((k.factorial : ℕ))) : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have e3 : ((((2 * (k + 1) + 1).factorial : ℕ)) : ℝ)
        = (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2)
          * ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
      have h1 : 2 * (k + 1) + 1 = (2 * k + 1 + 1) + 1 := by omega
      have h2 : 2 * k + 1 + 1 = (2 * k + 1) + 1 := by omega
      rw [h1, Nat.factorial_succ, h2, Nat.factorial_succ]
      push_cast
      ring
    rw [e1, e2, e3]
    have h34 : (4 : ℝ) * ((k : ℝ) + 1) ^ 2 ≤ (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2) := by
      have hkk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      nlinarith
    have hpow : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2 := by
      positivity
    calc 4 * (2 : ℝ) ^ (2 * k) * (((k : ℝ) + 1) * ((((k.factorial : ℕ))) : ℝ)) ^ 2
        = (4 * ((k : ℝ) + 1) ^ 2)
          * ((2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2) := by ring
      _ ≤ ((2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2))
          * ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
          apply mul_le_mul h34 ih hpow (by positivity)
      _ = (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2)
          * ((((2 * k + 1).factorial : ℕ)) : ℝ) := by ring

private lemma factCoeff_le_one (k : ℕ) :
    (2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2
        / ((((2 * k + 1).factorial : ℕ)) : ℝ) ≤ 1 := by
  rw [div_le_one (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  exact factCoeff_le_one_aux k

private lemma factCoeff_eq_choose (k : ℕ) :
    (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / ((2 * k + 1).factorial : ℝ)
      = (4 : ℝ) ^ k / ((((2 * k + 1 : ℕ)) : ℝ) * (Nat.choose (2 * k) k : ℝ)) := by
  have hk2k : k ≤ 2 * k := by omega
  have hchoose_pos : 0 < Nat.choose (2 * k) k := Nat.choose_pos hk2k
  have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hchoose_pos.ne'
  have hfact1 : ((2 * k + 1).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have h2k1 : ((((2 * k + 1 : ℕ))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega : 2 * k + 1 ≠ 0)
  have h2kfact : (((2 * k).factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have hchoose_eq : (Nat.choose (2 * k) k : ℝ)
      = ((2 * k).factorial : ℝ) / ((k.factorial : ℝ) * (k.factorial : ℝ)) := by
    have h := Nat.choose_eq_factorial_div_factorial hk2k
    rw [show 2 * k - k = k by omega] at h
    have hdvd := Nat.factorial_mul_factorial_dvd_factorial hk2k
    rw [show 2 * k - k = k by omega] at hdvd
    rw [h, Nat.cast_div hdvd (by positivity)]
    push_cast
    ring
  have hfact_succ : ((2 * k + 1).factorial : ℝ)
      = (((2 * k + 1 : ℕ)) : ℝ) * ((2 * k).factorial : ℝ) := by
    conv_lhs => rw [show 2 * k + 1 = (2 * k) + 1 by omega, Nat.factorial_succ]
    push_cast
    ring
  rw [hfact_succ, hchoose_eq]
  field_simp
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul]

private lemma pow_two_mul_succ (t : ℝ) (j : ℕ) :
    t ^ (2 * (j + 1)) = t ^ 2 * (t ^ 2) ^ j := by
  have h : 2 * (j + 1) = 2 * j + 2 := by omega
  rw [h, pow_add, ← pow_mul]
  ring

private lemma summable_leftTerm (x : ℝ) (h : |Real.tan x| ≤ 1) :
    Summable (chapter9Entry23LeftTerm x) := by
  by_cases ht : |Real.tan x| = 1
  · have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ ((3 / 2 : ℝ)))) :=
      (Real.summable_one_div_nat_rpow).mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).mpr hbase
    have hmaj : Summable
        (fun k : ℕ => (3 / 4 : ℝ) * (1 / (((((k + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))))) :=
      Summable.mul_left _ hshift
    have hterm : ∀ j : ℕ, |chapter9Entry23LeftTerm x j|
        ≤ (3 / 4 : ℝ) * (1 / (((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)))) := by
      intro j
      have hH := oddHarmonic_le_one_add_log (j + 1)
      have hmj : (1 : ℝ) ≤ ((((j + 1 : ℕ))) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        have h0 := Nat.cast_nonneg (α := ℝ) j
        linarith
      have hm0 : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) :=
        Nat.cast_pos.mpr (by omega : 0 < j + 1)
      have hlog := one_add_log_le_three_rpow _ hmj
      have hM : ((((2 * (j + 1) : ℕ))) : ℝ) = 2 * ((((j + 1 : ℕ))) : ℝ) := by
        rw [show (2 * (j + 1)) = (j + 1) + (j + 1) from by omega, Nat.cast_add]
        ring
      have habs : |Real.tan x ^ (2 * (j + 1))| = 1 := by
        rw [abs_pow, ht, one_pow]
      have hHnn := oddHarmonic_nonneg (j + 1)
      have hden : (0 : ℝ) < ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 :=
        pow_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * (j + 1))) 2
      have hneg1 : (|(-1 : ℝ) ^ j| : ℝ) = 1 := by
        rw [abs_pow, abs_neg, abs_one, one_pow]
      have hrpow_pos : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) :=
        Real.rpow_pos_of_pos hm0 _
      have key : (3 / 4 : ℝ) * (1 / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)))
          * (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2
          = 3 * ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ)) := by
        have eA : ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) ≠ 0 := ne_of_gt hrpow_pos
        have ehalf := rpow_half_mul_three_half _ hm0
        have e2 : ((3 / 4 : ℝ) * (1 / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)))
              * (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2)
            = ((3 * ((((j + 1 : ℕ))) : ℝ) ^ (2 : ℕ))
              / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))) := by ring
        rw [e2, div_eq_iff eA,
          show (3 : ℝ) * ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ))
              * ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))
            = 3 * (((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ))
              * ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))) by ring, ehalf]
      simp only [chapter9Entry23LeftTerm]
      rw [abs_div, abs_mul, abs_mul, hneg1, one_mul, abs_of_nonneg hHnn, habs,
        abs_of_pos hden, mul_one, div_le_iff₀ hden, hM, key]
      linarith
    exact Summable.of_abs
      (Summable.of_nonneg_of_le (fun k => by positivity) hterm hmaj)
  · have ht1 : |Real.tan x| < 1 := lt_of_le_of_ne h ht
    have ht0 : (0 : ℝ) ≤ |Real.tan x| ^ 2 := by positivity
    have ht2 : |Real.tan x| ^ 2 < 1 := by
      have h1 := abs_nonneg (Real.tan x)
      nlinarith [ht1, h1, sq_nonneg (|Real.tan x|)]
    have hgeo : Summable
        (fun j : ℕ => (|Real.tan x| ^ 2 / 4) * (|Real.tan x| ^ 2) ^ j) :=
      Summable.mul_left _ (summable_geometric_of_lt_one ht0 ht2)
    have hterm : ∀ j : ℕ, |chapter9Entry23LeftTerm x j|
        ≤ (|Real.tan x| ^ 2 / 4) * (|Real.tan x| ^ 2) ^ j := by
      intro j
      have hH : chapter9OddHarmonic (j + 1) ≤ ((((j + 1 : ℕ))) : ℝ) :=
        oddHarmonic_le_card (j + 1)
      have hmj : (1 : ℝ) ≤ ((((j + 1 : ℕ))) : ℝ) := by
        rw [Nat.cast_add, Nat.cast_one]
        have h0 := Nat.cast_nonneg (α := ℝ) j
        linarith
      have hHnn := oddHarmonic_nonneg (j + 1)
      have hden : (0 : ℝ) < ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 :=
        pow_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * (j + 1))) 2
      have hneg1 : (|(-1 : ℝ) ^ j| : ℝ) = 1 := by
        rw [abs_pow, abs_neg, abs_one, one_pow]
      have htt : |Real.tan x ^ (2 * (j + 1))| = |Real.tan x| ^ (2 * (j + 1)) :=
        abs_pow _ _
      have hM : ((((2 * (j + 1) : ℕ))) : ℝ) = 2 * ((((j + 1 : ℕ))) : ℝ) := by
        rw [show (2 * (j + 1)) = (j + 1) + (j + 1) from by omega, Nat.cast_add]
        ring
      have hpow := pow_two_mul_succ |Real.tan x| j
      have hP : (0 : ℝ) ≤ |Real.tan x| ^ 2 * (|Real.tan x| ^ 2) ^ j := by positivity
      have e1 : chapter9OddHarmonic (j + 1)
            * (|Real.tan x| ^ 2 * (|Real.tan x| ^ 2) ^ j)
          ≤ ((((j + 1 : ℕ))) : ℝ)
            * (|Real.tan x| ^ 2 * (|Real.tan x| ^ 2) ^ j) :=
        mul_le_mul_of_nonneg_right hH hP
      have hmm : ((((j + 1 : ℕ))) : ℝ) ≤ ((((j + 1 : ℕ))) : ℝ) ^ 2 := by
        calc ((((j + 1 : ℕ))) : ℝ)
            = ((((j + 1 : ℕ))) : ℝ) * 1 := by ring
          _ ≤ ((((j + 1 : ℕ))) : ℝ) * ((((j + 1 : ℕ))) : ℝ) :=
              mul_le_mul_of_nonneg_left hmj (le_trans zero_le_one hmj)
          _ = ((((j + 1 : ℕ))) : ℝ) ^ 2 := by ring
      have e2 : ((((j + 1 : ℕ))) : ℝ)
            * (|Real.tan x| ^ 2 * (|Real.tan x| ^ 2) ^ j)
          ≤ ((|Real.tan x| ^ 2 / 4) * (|Real.tan x| ^ 2) ^ j)
            * (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2 := by
        calc ((((j + 1 : ℕ))) : ℝ)
              * (|Real.tan x| ^ 2 * (|Real.tan x| ^ 2) ^ j)
            = (|Real.tan x| ^ 2 * (|Real.tan x| ^ 2) ^ j)
              * ((((j + 1 : ℕ))) : ℝ) := by ring
          _ ≤ (|Real.tan x| ^ 2 * (|Real.tan x| ^ 2) ^ j)
              * (((((j + 1 : ℕ))) : ℝ) ^ 2) :=
              mul_le_mul_of_nonneg_left hmm hP
          _ = ((|Real.tan x| ^ 2 / 4) * (|Real.tan x| ^ 2) ^ j)
              * (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2 := by ring
      simp only [chapter9Entry23LeftTerm]
      rw [abs_div, abs_mul, abs_mul, hneg1, one_mul, abs_of_nonneg hHnn, htt,
        abs_of_pos hden, div_le_iff₀ hden, hM, hpow]
      linarith [e1, e2]
    exact Summable.of_abs
      (Summable.of_nonneg_of_le (fun k => by positivity) hterm hgeo)

private lemma summable_factTerm (u : ℝ) (hu : |Real.sin u| ≤ 1) :
    Summable (chapter9Entry23FactorialTerm u) := by
  have hterm : ∀ k : ℕ, |chapter9Entry23FactorialTerm u k|
      ≤ |Real.sin u| ^ (2 * k + 2) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) := by
    intro k
    have hF : (0 : ℝ) < ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    have hFnn : (0 : ℝ) ≤ ((((2 * k + 1).factorial : ℕ)) : ℝ) := hF.le
    have he : (0 : ℝ) < (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) :=
      pow_pos (Nat.cast_pos.mpr (by omega : 0 < k + 1)) 2
    have he_nn : (0 : ℝ) ≤ (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) := he.le
    have hD : (0 : ℝ) < ((((2 * k + 1).factorial : ℕ)) : ℝ)
        * ((((2 * k + 2 : ℕ))) : ℝ) ^ 2 :=
      mul_pos hF (pow_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * k + 2)) 2)
    have hsp : (0 : ℝ) ≤ |Real.sin u| ^ (2 * k + 2) := by positivity
    have hE2 : (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))
        ≤ ((((2 * k + 2 : ℕ))) : ℝ) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) _ 2
      exact_mod_cast (by omega : k + 1 ≤ 2 * k + 2)
    have haux := factCoeff_le_one_aux k
    have hN : |(2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2
          * Real.sin u ^ (2 * k + 2)|
        = ((2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2)
          * |Real.sin u| ^ (2 * k + 2) := by
      rw [abs_mul, abs_pow,
        abs_of_nonneg (by positivity :
          (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2)]
    have key' : ((2 : ℝ) ^ (2 * k) * ((((k.factorial : ℕ))) : ℝ) ^ 2)
          * |Real.sin u| ^ (2 * k + 2) * (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))
        ≤ |Real.sin u| ^ (2 * k + 2)
          * (((((2 * k + 1).factorial : ℕ)) : ℝ)
            * ((((2 * k + 2 : ℕ))) : ℝ) ^ 2) := by
      have g1 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right haux hsp) he_nn
      have g2 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hE2 hFnn) hsp
      linear_combination g1 + g2
    simp only [chapter9Entry23FactorialTerm]
    rw [abs_div, hN, abs_of_pos hD, div_le_iff₀ hD, div_mul_eq_mul_div,
      le_div_iff₀ he]
    exact key'
  by_cases hs : |Real.sin u| = 1
  · have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ (2 : ℕ))) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    have hshift := (summable_nat_add_iff 1).mpr hbase
    have hmaj : Summable
        (fun k : ℕ => (1 : ℝ) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))) := hshift
    have hterm1 : ∀ k : ℕ, |chapter9Entry23FactorialTerm u k|
        ≤ (1 : ℝ) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) := by
      intro k
      simpa [hs] using hterm k
    exact Summable.of_abs
      (Summable.of_nonneg_of_le (fun k => by positivity) hterm1 hmaj)
  · have hs1 : |Real.sin u| < 1 := lt_of_le_of_ne hu hs
    have hs0 : (0 : ℝ) ≤ |Real.sin u| ^ 2 := by positivity
    have hs2 : |Real.sin u| ^ 2 < 1 := by
      have h1 := abs_nonneg (Real.sin u)
      nlinarith [hs1, h1, sq_nonneg (|Real.sin u|)]
    have hgeo : Summable
        (fun k : ℕ => |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k) :=
      Summable.mul_left _ (summable_geometric_of_lt_one hs0 hs2)
    have he1 : ∀ k : ℕ, (1 : ℝ) ≤ (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) := by
      intro k
      calc (1 : ℝ) = 1 ^ (2 : ℕ) := by norm_num
        _ ≤ (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) := by
            apply pow_le_pow_left₀ (by norm_num) _ 2
            rw [Nat.cast_add, Nat.cast_one]
            have h0 := Nat.cast_nonneg (α := ℝ) k
            linarith
    have hterm2 : ∀ k : ℕ, |chapter9Entry23FactorialTerm u k|
        ≤ |Real.sin u| ^ (2 * k + 2) := by
      intro k
      have hsp : (0 : ℝ) ≤ |Real.sin u| ^ (2 * k + 2) := by positivity
      have he_pos : (0 : ℝ) < (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) :=
        pow_pos (Nat.cast_pos.mpr (by omega : 0 < k + 1)) 2
      have h1e : (1 : ℝ) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) ≤ 1 := by
        rw [div_le_one he_pos]
        exact he1 k
      have hdiv : |Real.sin u| ^ (2 * k + 2)
            / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))
          ≤ |Real.sin u| ^ (2 * k + 2) := by
        calc |Real.sin u| ^ (2 * k + 2) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))
            = |Real.sin u| ^ (2 * k + 2)
              * (1 / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))) := by ring
          _ ≤ |Real.sin u| ^ (2 * k + 2) * 1 :=
              mul_le_mul_of_nonneg_left h1e hsp
          _ = |Real.sin u| ^ (2 * k + 2) := mul_one _
      exact le_trans (hterm k) hdiv
    have epow : ∀ k : ℕ, |Real.sin u| ^ (2 * k + 2)
        = |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by
      intro k
      rw [show 2 * k + 2 = 2 * (k + 1) by omega]
      exact pow_two_mul_succ _ _
    have hterm3 : ∀ k : ℕ, |chapter9Entry23FactorialTerm u k|
        ≤ |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by
      intro k
      have h := hterm2 k
      rw [epow k] at h
      exact h
    exact Summable.of_abs
      (Summable.of_nonneg_of_le (fun k => by positivity) hterm3 hgeo)

private def chapter9Entry23Coeff (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / ((2 * k + 1).factorial : ℝ)

private lemma coeff_nonneg (k : ℕ) : 0 ≤ chapter9Entry23Coeff k := by
  unfold chapter9Entry23Coeff
  apply div_nonneg (by positivity) (by positivity)

private lemma coeff_le_one (k : ℕ) : chapter9Entry23Coeff k ≤ 1 := by
  unfold chapter9Entry23Coeff
  rw [div_le_one (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  exact factCoeff_le_one_aux k

private lemma coeff_zero : chapter9Entry23Coeff 0 = 1 := by
  unfold chapter9Entry23Coeff
  norm_num

private lemma coeff_succ_mul (k : ℕ) :
    chapter9Entry23Coeff (k + 1) * (((2 * k + 3 : ℕ)) : ℝ)
      = chapter9Entry23Coeff k * (((2 * k + 2 : ℕ)) : ℝ) := by
  unfold chapter9Entry23Coeff
  have h1 : (2 * (k + 1) + 1) = (2 * k + 3) := by omega
  have h2 : (2 * (k + 1)) = (2 * k + 2) := by omega
  have e1 : (2 : ℝ) ^ (2 * (k + 1)) = 4 * (2 : ℝ) ^ (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    ring
  have e2 : (((k + 1).factorial : ℕ) : ℝ)
      = ((k : ℝ) + 1) * ((k.factorial : ℝ)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have h23 : 2 * k + 3 = (2 * k + 2) + 1 := by omega
  have h22 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
  have e3 : ((((2 * (k + 1) + 1).factorial : ℕ)) : ℝ)
      = (2 * (k : ℝ) + 3) * (2 * (k : ℝ) + 2)
        * ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
    rw [h1, h23, Nat.factorial_succ, h22, Nat.factorial_succ]
    push_cast
    ring
  have hF1 : ((((2 * k + 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have h23' : ((2 * (k : ℝ) + 3)) ≠ 0 := by positivity
  have h22' : ((2 * (k : ℝ) + 2)) ≠ 0 := by positivity
  have hcast3 : ((((2 * k + 3 : ℕ))) : ℝ) = 2 * (k : ℝ) + 3 := by push_cast; ring
  have hcast2 : ((((2 * k + 2 : ℕ))) : ℝ) = 2 * (k : ℝ) + 2 := by push_cast; ring
  rw [e1, e2, e3, hcast3, hcast2]
  field_simp
  ring

private lemma oddHarmonic_succ (n : ℕ) :
    chapter9OddHarmonic (n + 1)
      = chapter9OddHarmonic n + 1 / (((2 * n + 1 : ℕ)) : ℝ) := by
  unfold chapter9OddHarmonic
  rw [Finset.sum_range_succ]

private lemma oddHarmonic_diff (n : ℕ) :
    chapter9OddHarmonic (n + 1 + 1) - chapter9OddHarmonic (n + 1)
      = 1 / (((2 * (n + 1) + 1 : ℕ)) : ℝ) := by
  rw [oddHarmonic_succ (n + 1)]
  ring

private lemma summable_succ_mul_geom {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have h := h1.add h2
  have e : (fun n : ℕ => (n : ℝ) * r ^ n + r ^ n)
      = (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
    funext n
    ring
  rwa [e] at h

private lemma summable_two_mul_add_one_geom {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => (2 * (n : ℝ) + 1) * r ^ n) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h2 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have h := (h1.mul_left 2).add h2
  have e : (fun n : ℕ => 2 * ((n : ℝ) * r ^ n) + r ^ n)
      = (fun n : ℕ => (2 * (n : ℝ) + 1) * r ^ n) := by
    funext n
    ring
  rwa [e] at h

private lemma one_add_tan_sq (x : ℝ) (hx : Real.cos x ≠ 0) :
    1 + Real.tan x ^ 2 = 1 / Real.cos x ^ 2 := by
  have htan : Real.tan x = Real.sin x / Real.cos x := Real.tan_eq_sin_div_cos x
  have hsc : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [htan, div_pow]
  field_simp
  linarith

private lemma cos_ne_zero_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) : Real.cos x ≠ 0 :=
  ne_of_gt (Real.cos_pos_of_mem_Ioo hx)

private lemma abs_tan_le_tan_of_mem {r y : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 2) (hy : y ∈ Set.Ioo (-r) r) :
    |Real.tan y| ≤ Real.tan r := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hy
    constructor <;> linarith
  have hrmem : r ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hnmem : -r ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hle : Real.tan y ≤ Real.tan r :=
    (Real.strictMonoOn_tan.le_iff_le hymem hrmem).mpr (le_of_lt (Set.mem_Ioo.mp hy).2)
  have hge : Real.tan (-r) ≤ Real.tan y :=
    (Real.strictMonoOn_tan.le_iff_le hnmem hymem).mpr (le_of_lt (Set.mem_Ioo.mp hy).1)
  rw [Real.tan_neg] at hge
  have htanr_nn : 0 ≤ Real.tan r := by
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have h := (Real.strictMonoOn_tan.le_iff_le h0mem hrmem).mpr (le_of_lt hr0)
    rwa [Real.tan_zero] at h
  rw [abs_le]
  constructor <;> linarith

private lemma tan_lt_one_of_le_pi_div_four {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r ≤ Real.pi / 4) : Real.tan r ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrmem : r ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hpmem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have h := (Real.strictMonoOn_tan.le_iff_le hrmem hpmem).mpr hr1
  rwa [Real.tan_pi_div_four] at h

private lemma abs_sin_lt_one_of_mem_Ioo {y : ℝ}
    (hy : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) : |Real.sin y| < 1 := by
  have hcos : 0 < Real.cos y := Real.cos_pos_of_mem_Ioo hy
  have hsc : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
  have hsin2 : Real.sin y ^ 2 < 1 := by nlinarith [sq_nonneg (Real.sin y)]
  have h : |Real.sin y| ^ 2 < 1 := by
    rw [sq_abs]
    exact hsin2
  nlinarith [abs_nonneg (Real.sin y), sq_nonneg (|Real.sin y|), h]

private lemma abs_sin_le_sin_of_mem {r y : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 2) (hy : y ∈ Set.Ioo (-r) r) :
    |Real.sin y| ≤ Real.sin r := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hymem : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hy
    constructor <;> linarith
  have hrmem : r ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hnmem : -r ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hle : Real.sin y ≤ Real.sin r :=
    (Real.strictMonoOn_sin.le_iff_le hymem hrmem).mpr (le_of_lt (Set.mem_Ioo.mp hy).2)
  have hge : Real.sin (-r) ≤ Real.sin y :=
    (Real.strictMonoOn_sin.le_iff_le hnmem hymem).mpr (le_of_lt (Set.mem_Ioo.mp hy).1)
  rw [Real.sin_neg] at hge
  have hsinr_nn : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith⟩
  rw [abs_le]
  constructor <;> linarith

private lemma sin_lt_one_of_mem_Ioo {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 2) : Real.sin r < 1 := by
  have hmem : r ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have h := abs_sin_lt_one_of_mem_Ioo hmem
  have hnn : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hab : |Real.sin r| = Real.sin r := abs_of_nonneg hnn
  rwa [hab] at h

private lemma inv_cos_sq_le_of_mem {r y : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 2) (hy : y ∈ Set.Ioo (-r) r) :
    1 / Real.cos y ^ 2 ≤ 1 + Real.tan r ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hy
    constructor <;> linarith
  have hcos : Real.cos y ≠ 0 := cos_ne_zero_of_mem_Ioo hymem
  rw [← one_add_tan_sq y hcos]
  have htan := abs_tan_le_tan_of_mem hr0 hr1 hy
  have hnn : 0 ≤ Real.tan r := by
    have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have hrmem : r ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith
    have h := (Real.strictMonoOn_tan.le_iff_le h0mem hrmem).mpr (le_of_lt hr0)
    rwa [Real.tan_zero] at h
  have hsq : Real.tan y ^ 2 ≤ Real.tan r ^ 2 := by
    have h1 : |Real.tan y| ^ 2 ≤ Real.tan r ^ 2 := by
      apply pow_le_pow_left₀ (abs_nonneg _) htan 2
    rwa [sq_abs] at h1
  linarith

private def chapter9Entry23ATerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * (j + 1))
    / (((2 * (j + 1) : ℕ)) : ℝ)

private def chapter9Entry23PTerm (t : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * t ^ (2 * j + 1)

private def chapter9Entry23ArctanTerm (t : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * t ^ (2 * n + 1) / (((2 * n + 1 : ℕ)) : ℝ)

private def chapter9Entry23KTerm (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 1)

private def chapter9Entry23NTerm (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 2) / (((2 * k + 2 : ℕ)) : ℝ)

private def chapter9Entry23ATerm' (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 1)
    / Real.cos x ^ 2

private def chapter9Entry23LTerm' (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 1)
    / ((((2 * (j + 1) : ℕ)) : ℝ) * Real.cos x ^ 2)

private def chapter9Entry23KTerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 1 : ℕ)) : ℝ) * Real.sin u ^ (2 * k)
    * Real.cos u

private def chapter9Entry23NTerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 1) * Real.cos u

private def chapter9Entry23STerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 1) * Real.cos u
    / (((2 * k + 2 : ℕ)) : ℝ)

private def chapter9Entry23CKTerm (u : ℝ) (k : ℕ) : ℝ :=
  Real.cos u * chapter9Entry23KTerm u k

private def chapter9Entry23CKTerm' (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 1 : ℕ)) : ℝ) * Real.sin u ^ (2 * k)
    - chapter9Entry23Coeff k * (((2 * k + 2 : ℕ)) : ℝ)
      * Real.sin u ^ (2 * k + 2)

private lemma factorialTerm_eq_coeff (u : ℝ) (k : ℕ) :
    chapter9Entry23FactorialTerm u k
      = chapter9Entry23Coeff k * Real.sin u ^ (2 * k + 2)
        / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
  unfold chapter9Entry23FactorialTerm chapter9Entry23Coeff
  have hF : ((((2 * k + 1).factorial : ℕ)) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos _).ne'
  have hD : ((((2 * k + 2 : ℕ))) : ℝ) ^ 2 ≠ 0 := by
    apply pow_ne_zero 2
    exact Nat.cast_ne_zero.mpr (by omega : 2 * k + 2 ≠ 0)
  field_simp

private lemma leftTerm_zero (j : ℕ) : chapter9Entry23LeftTerm 0 j = 0 := by
  unfold chapter9Entry23LeftTerm
  simp [Real.tan_zero]

private lemma factTerm_zero (k : ℕ) : chapter9Entry23FactorialTerm 0 k = 0 := by
  unfold chapter9Entry23FactorialTerm
  simp [Real.sin_zero]

private lemma aTerm_zero (j : ℕ) : chapter9Entry23ATerm 0 j = 0 := by
  unfold chapter9Entry23ATerm
  simp [Real.tan_zero]

private lemma kTerm_zero (k : ℕ) : chapter9Entry23KTerm 0 k = 0 := by
  unfold chapter9Entry23KTerm
  simp [Real.sin_zero]

private lemma nTerm_zero (k : ℕ) : chapter9Entry23NTerm 0 k = 0 := by
  unfold chapter9Entry23NTerm
  simp [Real.sin_zero]

private lemma ckTerm_zero (k : ℕ) : chapter9Entry23CKTerm 0 k = 0 := by
  unfold chapter9Entry23CKTerm
  rw [kTerm_zero]
  ring

private lemma aTerm'_zero (j : ℕ) : chapter9Entry23ATerm' 0 j = 0 := by
  unfold chapter9Entry23ATerm'
  simp [Real.tan_zero]

private lemma lTerm'_zero (j : ℕ) : chapter9Entry23LTerm' 0 j = 0 := by
  unfold chapter9Entry23LTerm'
  simp [Real.tan_zero]

private lemma nTerm'_zero (k : ℕ) : chapter9Entry23NTerm' 0 k = 0 := by
  unfold chapter9Entry23NTerm'
  simp [Real.sin_zero]

private lemma sTerm'_zero (k : ℕ) : chapter9Entry23STerm' 0 k = 0 := by
  unfold chapter9Entry23STerm'
  simp [Real.sin_zero]

private lemma hasDerivAt_aTerm {x : ℝ} (j : ℕ)
    (hcos : Real.cos x ≠ 0) :
    HasDerivAt (fun y => chapter9Entry23ATerm y j)
      (chapter9Entry23ATerm' x j) x := by
  have m_eq : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have hD : ((((2 * (j + 1) : ℕ))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega : 2 * (j + 1) ≠ 0)
  have htan := Real.hasDerivAt_tan hcos
  have hpow := htan.pow (2 * (j + 1))
  have hcm := hpow.const_mul ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1))
  have h := hcm.div_const ((((2 * (j + 1) : ℕ))) : ℝ)
  simp only [Pi.pow_apply] at h
  have efun : (fun y => ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1))
        * Real.tan y ^ (2 * (j + 1)) / ((((2 * (j + 1) : ℕ))) : ℝ))
      = (fun y => chapter9Entry23ATerm y j) := by
    funext y
    unfold chapter9Entry23ATerm
    ring
  rw [efun] at h
  have eval : ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1))
        * (↑(2 * (j + 1)) * Real.tan x ^ (2 * (j + 1) - 1)
          * (1 / Real.cos x ^ 2))
        / ((((2 * (j + 1) : ℕ))) : ℝ)
      = chapter9Entry23ATerm' x j := by
    unfold chapter9Entry23ATerm'
    rw [m_eq]
    field_simp
  rwa [eval] at h

private lemma hasDerivAt_leftTerm {x : ℝ} (j : ℕ)
    (hcos : Real.cos x ≠ 0) :
    HasDerivAt (fun y => chapter9Entry23LeftTerm y j)
      (chapter9Entry23LTerm' x j) x := by
  have m_eq : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have hD : ((((2 * (j + 1) : ℕ))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega : 2 * (j + 1) ≠ 0)
  have hcos2 : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have htan := Real.hasDerivAt_tan hcos
  have hpow := htan.pow (2 * (j + 1))
  have hcm := hpow.const_mul ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1))
  have h := hcm.div_const (((((2 * (j + 1) : ℕ))) : ℝ) ^ 2)
  simp only [Pi.pow_apply] at h
  have efun : (fun y => ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1))
        * Real.tan y ^ (2 * (j + 1)) / (((((2 * (j + 1) : ℕ))) : ℝ) ^ 2))
      = (fun y => chapter9Entry23LeftTerm y j) := by
    funext y
    simp only [chapter9Entry23LeftTerm]
  rw [efun] at h
  have eval : ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1))
        * (↑(2 * (j + 1)) * Real.tan x ^ (2 * (j + 1) - 1)
          * (1 / Real.cos x ^ 2))
        / (((((2 * (j + 1) : ℕ))) : ℝ) ^ 2)
      = chapter9Entry23LTerm' x j := by
    unfold chapter9Entry23LTerm'
    rw [m_eq]
    field_simp
  rwa [eval] at h

private lemma hasDerivAt_kTerm (u : ℝ) (k : ℕ) :
    HasDerivAt (fun v => chapter9Entry23KTerm v k)
      (chapter9Entry23KTerm' u k) u := by
  have m_eq : 2 * k + 1 - 1 = 2 * k := by omega
  have hsin := Real.hasDerivAt_sin u
  have hpow := hsin.pow (2 * k + 1)
  have hcm := hpow.const_mul (chapter9Entry23Coeff k)
  simp only [Pi.pow_apply] at hcm
  have efun : (fun v => chapter9Entry23Coeff k * Real.sin v ^ (2 * k + 1))
      = (fun v => chapter9Entry23KTerm v k) := by
    funext v
    unfold chapter9Entry23KTerm
    ring
  rw [efun] at hcm
  have eval : chapter9Entry23Coeff k
        * (↑(2 * k + 1) * Real.sin u ^ (2 * k + 1 - 1) * Real.cos u)
      = chapter9Entry23KTerm' u k := by
    unfold chapter9Entry23KTerm'
    rw [m_eq]
    ring
  rwa [eval] at hcm

private lemma hasDerivAt_nTerm (u : ℝ) (k : ℕ) :
    HasDerivAt (fun v => chapter9Entry23NTerm v k)
      (chapter9Entry23NTerm' u k) u := by
  have m_eq : 2 * k + 2 - 1 = 2 * k + 1 := by omega
  have hD : ((((2 * k + 2 : ℕ))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega : 2 * k + 2 ≠ 0)
  have hsin := Real.hasDerivAt_sin u
  have hpow := hsin.pow (2 * k + 2)
  have hcm := hpow.const_mul (chapter9Entry23Coeff k)
  have h := hcm.div_const ((((2 * k + 2 : ℕ))) : ℝ)
  simp only [Pi.pow_apply] at h
  have efun : (fun v => chapter9Entry23Coeff k * Real.sin v ^ (2 * k + 2)
        / ((((2 * k + 2 : ℕ))) : ℝ))
      = (fun v => chapter9Entry23NTerm v k) := by
    funext v
    unfold chapter9Entry23NTerm
    ring
  rw [efun] at h
  have eval : chapter9Entry23Coeff k
        * (↑(2 * k + 2) * Real.sin u ^ (2 * k + 2 - 1) * Real.cos u)
        / ((((2 * k + 2 : ℕ))) : ℝ)
      = chapter9Entry23NTerm' u k := by
    unfold chapter9Entry23NTerm'
    rw [m_eq]
    field_simp
  rwa [eval] at h

private lemma hasDerivAt_sTerm (u : ℝ) (k : ℕ) :
    HasDerivAt (fun v => chapter9Entry23FactorialTerm v k)
      (chapter9Entry23STerm' u k) u := by
  have m_eq : 2 * k + 2 - 1 = 2 * k + 1 := by omega
  have hD : ((((2 * k + 2 : ℕ))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega : 2 * k + 2 ≠ 0)
  have hsin := Real.hasDerivAt_sin u
  have hpow := hsin.pow (2 * k + 2)
  have hcm := hpow.const_mul (chapter9Entry23Coeff k)
  have h := hcm.div_const (((((2 * k + 2 : ℕ))) : ℝ) ^ 2)
  simp only [Pi.pow_apply] at h
  have efun : (fun v => chapter9Entry23Coeff k * Real.sin v ^ (2 * k + 2)
        / (((((2 * k + 2 : ℕ))) : ℝ) ^ 2))
      = (fun v => chapter9Entry23FactorialTerm v k) := by
    funext v
    rw [factorialTerm_eq_coeff]
  rw [efun] at h
  have eval : chapter9Entry23Coeff k
        * (↑(2 * k + 2) * Real.sin u ^ (2 * k + 2 - 1) * Real.cos u)
        / (((((2 * k + 2 : ℕ))) : ℝ) ^ 2)
      = chapter9Entry23STerm' u k := by
    unfold chapter9Entry23STerm'
    rw [m_eq]
    field_simp
  rwa [eval] at h

private lemma hasDerivAt_ckTerm (u : ℝ) (k : ℕ) :
    HasDerivAt (fun v => chapter9Entry23CKTerm v k)
      (chapter9Entry23CKTerm' u k) u := by
  have hcos := Real.hasDerivAt_cos u
  have hk := hasDerivAt_kTerm u k
  have h := hcos.mul hk
  have efun : (Real.cos * fun v => chapter9Entry23KTerm v k)
      = (fun v => chapter9Entry23CKTerm v k) := by
    funext v
    simp only [Pi.mul_apply, chapter9Entry23CKTerm]
  rw [efun] at h
  have hsc : Real.sin u ^ 2 + Real.cos u ^ 2 = 1 := Real.sin_sq_add_cos_sq u
  have hpow_add : Real.sin u ^ (2 * k) * Real.sin u ^ 2
      = Real.sin u ^ (2 * k + 2) := by
    rw [← pow_add]
  have hcast1 : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  have hcast2 : ((((2 * k + 2 : ℕ))) : ℝ) = 2 * (k : ℝ) + 2 := by
    push_cast
    ring
  have eval : -Real.sin u * chapter9Entry23KTerm u k
        + Real.cos u * chapter9Entry23KTerm' u k
      = chapter9Entry23CKTerm' u k := by
    unfold chapter9Entry23KTerm chapter9Entry23KTerm' chapter9Entry23CKTerm'
    rw [hcast1, hcast2]
    have e1 : Real.sin u ^ (2 * k + 1) = Real.sin u ^ (2 * k) * Real.sin u := by
      rw [pow_add, pow_one]
    rw [e1, ← hpow_add]
    linear_combination (chapter9Entry23Coeff k * (2 * (k : ℝ) + 1)
      * Real.sin u ^ (2 * k)) * hsc
  rwa [eval] at h

private lemma exists_r_of_mem_Ioo {a B : ℝ} (hB : 0 < B)
    (ha : a ∈ Set.Ioo (-B) B) : ∃ r, |a| < r ∧ r < B ∧ 0 < r ∧ a ∈ Set.Ioo (-r) r := by
  have hab : |a| < B := abs_lt.mpr (Set.mem_Ioo.mp ha)
  have ha0 : 0 ≤ |a| := abs_nonneg a
  have hr_mem : |a| < (|a| + B) / 2 := by linarith
  have hr_lt : (|a| + B) / 2 < B := by linarith
  have hr0 : 0 < (|a| + B) / 2 := by linarith
  refine ⟨(|a| + B) / 2, hr_mem, hr_lt, hr0, ?_⟩
  have h1 : -((|a| + B) / 2) < a := by
    have hle : -|a| ≤ a := neg_abs_le a
    linarith
  have h2 : a < (|a| + B) / 2 := by
    have hle : a ≤ |a| := le_abs_self a
    linarith
  exact Set.mem_Ioo.mpr ⟨h1, h2⟩

private lemma norm_nTerm'_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < Real.pi / 2)
    (hy : y ∈ Set.Ioo (-r) r) (k : ℕ) :
    ‖chapter9Entry23NTerm' y k‖
      ≤ Real.sin r * (Real.sin r ^ 2) ^ k := by
  have hq_nn : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hsin_le := abs_sin_le_sin_of_mem hr0 hr1 hy
  have hcos_le : |Real.cos y| ≤ 1 := Real.abs_cos_le_one y
  have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
  have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
  have hpow1 : |Real.sin y| ^ (2 * k + 1)
      ≤ Real.sin r * (Real.sin r ^ 2) ^ k := by
    have e2 : |Real.sin y| ^ (2 * k + 1)
        = |Real.sin y| * (|Real.sin y| ^ 2) ^ k := by
      rw [pow_add, pow_one, ← pow_mul]
      ring
    have h1 : |Real.sin y| ≤ Real.sin r := hsin_le
    have h2 : (|Real.sin y| ^ 2) ^ k ≤ (Real.sin r ^ 2) ^ k := by
      apply pow_le_pow_left₀ (by positivity) _ k
      exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
    calc |Real.sin y| ^ (2 * k + 1)
        = |Real.sin y| * (|Real.sin y| ^ 2) ^ k := e2
      _ ≤ Real.sin r * (Real.sin r ^ 2) ^ k := by
          exact mul_le_mul h1 h2 (by positivity) hq_nn
  have hb_nn : 0 ≤ Real.sin r * (Real.sin r ^ 2) ^ k :=
    mul_nonneg hq_nn (by positivity)
  have hpow_nn : 0 ≤ |Real.sin y| ^ (2 * k + 1) := by positivity
  unfold chapter9Entry23NTerm'
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
    abs_of_nonneg hc_nn
  rw [h1, abs_pow]
  have g1 : chapter9Entry23Coeff k * |Real.sin y| ^ (2 * k + 1)
      ≤ 1 * (Real.sin r * (Real.sin r ^ 2) ^ k) :=
    mul_le_mul hc_le hpow1 hpow_nn zero_le_one
  have g2 : chapter9Entry23Coeff k * |Real.sin y| ^ (2 * k + 1) * |Real.cos y|
      ≤ 1 * (Real.sin r * (Real.sin r ^ 2) ^ k) * 1 :=
    mul_le_mul g1 hcos_le (abs_nonneg _) (by linarith [hb_nn])
  calc chapter9Entry23Coeff k * |Real.sin y| ^ (2 * k + 1) * |Real.cos y|
      ≤ 1 * (Real.sin r * (Real.sin r ^ 2) ^ k) * 1 := g2
    _ = Real.sin r * (Real.sin r ^ 2) ^ k := by ring

private lemma summable_sin_bound {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 2) :
    Summable (fun k : ℕ => Real.sin r * (Real.sin r ^ 2) ^ k) := by
  have hq1 : Real.sin r < 1 := sin_lt_one_of_mem_Ioo hr0 hr1
  have hq_nn : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hr2 : (Real.sin r ^ 2) < 1 := by nlinarith [sq_nonneg (Real.sin r)]
  have hr2_nn : 0 ≤ (Real.sin r ^ 2) := by positivity
  have hnorm : ‖(Real.sin r ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr2_nn]
    exact hr2
  exact (summable_geometric_of_norm_lt_one hnorm).mul_left _

private lemma summable_nTerm_zero : Summable (fun k : ℕ => chapter9Entry23NTerm 0 k) := by
  simp only [nTerm_zero]
  exact summable_zero

private lemma hasDerivAt_N_tsum {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (fun v => ∑' k, chapter9Entry23NTerm v k)
      (∑' k, chapter9Entry23NTerm' u k) u := by
  have hpi : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hu_mem⟩ := exists_r_of_mem_Ioo hpi hu
  have hsumu' := summable_sin_bound hr0 hr1
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := Set.mem_Ioo.mpr ⟨by linarith, hr0⟩
  have hderiv : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      HasDerivAt (fun v => chapter9Entry23NTerm v k)
        (chapter9Entry23NTerm' y k) y := fun k y _ => hasDerivAt_nTerm y k
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      ‖chapter9Entry23NTerm' y k‖ ≤ Real.sin r * (Real.sin r ^ 2) ^ k :=
    fun k y hy => norm_nTerm'_le hr0 hr1 hy k
  exact hasDerivAt_tsum_of_isPreconnected hsumu' isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected hderiv hbound h0mem summable_nTerm_zero hu_mem

private lemma norm_sTerm'_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < Real.pi / 2)
    (hy : y ∈ Set.Ioo (-r) r) (k : ℕ) :
    ‖chapter9Entry23STerm' y k‖
      ≤ Real.sin r * (Real.sin r ^ 2) ^ k := by
  have hD1 : (1 : ℝ) ≤ ((((2 * k + 2 : ℕ))) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * k + 2)
  have hN := norm_nTerm'_le hr0 hr1 hy k
  have e : chapter9Entry23STerm' y k
      = chapter9Entry23NTerm' y k / ((((2 * k + 2 : ℕ))) : ℝ) := by
    unfold chapter9Entry23STerm' chapter9Entry23NTerm'
    ring
  rw [e]
  have hnn : 0 ≤ ‖chapter9Entry23NTerm' y k‖ := norm_nonneg _
  calc ‖chapter9Entry23NTerm' y k / ((((2 * k + 2 : ℕ))) : ℝ)‖
      = ‖chapter9Entry23NTerm' y k‖ / ((((2 * k + 2 : ℕ))) : ℝ) := by
        rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((((2 * k + 2 : ℕ))) : ℝ))]
    _ ≤ ‖chapter9Entry23NTerm' y k‖ := div_le_self hnn hD1
    _ ≤ Real.sin r * (Real.sin r ^ 2) ^ k := hN

private lemma summable_sTerm_zero :
    Summable (fun k : ℕ => chapter9Entry23FactorialTerm 0 k) := by
  simp only [factTerm_zero]
  exact summable_zero

private lemma hasDerivAt_S_tsum {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (fun v => ∑' k, chapter9Entry23FactorialTerm v k)
      (∑' k, chapter9Entry23STerm' u k) u := by
  have hpi : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hu_mem⟩ := exists_r_of_mem_Ioo hpi hu
  have hsumu' := summable_sin_bound hr0 hr1
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := Set.mem_Ioo.mpr ⟨by linarith, hr0⟩
  have hderiv : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      HasDerivAt (fun v => chapter9Entry23FactorialTerm v k)
        (chapter9Entry23STerm' y k) y := fun k y _ => hasDerivAt_sTerm y k
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      ‖chapter9Entry23STerm' y k‖ ≤ Real.sin r * (Real.sin r ^ 2) ^ k :=
    fun k y hy => norm_sTerm'_le hr0 hr1 hy k
  exact hasDerivAt_tsum_of_isPreconnected hsumu' isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected hderiv hbound h0mem summable_sTerm_zero hu_mem

private lemma norm_kTerm'_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < Real.pi / 2)
    (hy : y ∈ Set.Ioo (-r) r) (k : ℕ) :
    ‖chapter9Entry23KTerm' y k‖
      ≤ (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k := by
  have hsin_le := abs_sin_le_sin_of_mem hr0 hr1 hy
  have hcos_le : |Real.cos y| ≤ 1 := Real.abs_cos_le_one y
  have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
  have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
  have hq_nn : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hcast : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  have hpow : |Real.sin y| ^ (2 * k) ≤ (Real.sin r ^ 2) ^ k := by
    have e : |Real.sin y| ^ (2 * k) = (|Real.sin y| ^ 2) ^ k := by
      rw [← pow_mul]
    rw [e]
    apply pow_le_pow_left₀ (by positivity) _ k
    exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
  have h2k1_nn : 0 ≤ (2 * (k : ℝ) + 1) := by positivity
  unfold chapter9Entry23KTerm'
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
    abs_of_nonneg hc_nn
  have h2 : |((((2 * k + 1 : ℕ))) : ℝ)| = 2 * (k : ℝ) + 1 := by
    rw [hcast]
    exact abs_of_nonneg h2k1_nn
  rw [h1, h2, abs_pow]
  have g1 : chapter9Entry23Coeff k * (2 * (k : ℝ) + 1)
      ≤ 1 * (2 * (k : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hc_le h2k1_nn
  have hpow_nn : 0 ≤ |Real.sin y| ^ (2 * k) := by positivity
  have hb_nn : 0 ≤ (Real.sin r ^ 2) ^ k := by positivity
  have hB : 0 ≤ 1 * (2 * (k : ℝ) + 1) := by linarith [h2k1_nn]
  have g2 : chapter9Entry23Coeff k * (2 * (k : ℝ) + 1) * |Real.sin y| ^ (2 * k)
      ≤ 1 * (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k :=
    mul_le_mul g1 hpow hpow_nn hB
  have hB2 : 0 ≤ 1 * (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k :=
    mul_nonneg (by linarith [h2k1_nn]) hb_nn
  calc chapter9Entry23Coeff k * (2 * (k : ℝ) + 1) * |Real.sin y| ^ (2 * k)
        * |Real.cos y|
      ≤ 1 * (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k * 1 :=
        mul_le_mul g2 hcos_le (abs_nonneg _) hB2
    _ = (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k := by ring

private lemma summable_kTerm'_bound {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 2) :
    Summable (fun k : ℕ => (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k) := by
  have hq_nn : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hr2 : (Real.sin r ^ 2) < 1 := by
    have hq1 : Real.sin r < 1 := sin_lt_one_of_mem_Ioo hr0 hr1
    nlinarith [hq_nn, hq1, sq_nonneg (Real.sin r)]
  have hr2_nn : 0 ≤ (Real.sin r ^ 2) := by positivity
  have hnorm : ‖(Real.sin r ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr2_nn]
    exact hr2
  exact summable_two_mul_add_one_geom hnorm

private lemma summable_kTerm_zero :
    Summable (fun k : ℕ => chapter9Entry23KTerm 0 k) := by
  simp only [kTerm_zero]
  exact summable_zero

private lemma hasDerivAt_K_tsum {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (fun v => ∑' k, chapter9Entry23KTerm v k)
      (∑' k, chapter9Entry23KTerm' u k) u := by
  have hpi : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hu_mem⟩ := exists_r_of_mem_Ioo hpi hu
  have hsumu' := summable_kTerm'_bound hr0 hr1
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := Set.mem_Ioo.mpr ⟨by linarith, hr0⟩
  have hderiv : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      HasDerivAt (fun v => chapter9Entry23KTerm v k)
        (chapter9Entry23KTerm' y k) y := fun k y _ => hasDerivAt_kTerm y k
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      ‖chapter9Entry23KTerm' y k‖
        ≤ (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k :=
    fun k y hy => norm_kTerm'_le hr0 hr1 hy k
  exact hasDerivAt_tsum_of_isPreconnected hsumu' isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected hderiv hbound h0mem summable_kTerm_zero hu_mem

private lemma norm_ckTerm'_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < Real.pi / 2)
    (hy : y ∈ Set.Ioo (-r) r) (k : ℕ) :
    ‖chapter9Entry23CKTerm' y k‖
      ≤ (4 * (k : ℝ) + 3) * (Real.sin r ^ 2) ^ k := by
  have hsin_le := abs_sin_le_sin_of_mem hr0 hr1 hy
  have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
  have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
  have hq_nn : 0 ≤ Real.sin r :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
  have hq1 : Real.sin r ≤ 1 := le_of_lt (sin_lt_one_of_mem_Ioo hr0 hr1)
  have hcast1 : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  have hcast2 : ((((2 * k + 2 : ℕ))) : ℝ) = 2 * (k : ℝ) + 2 := by
    push_cast
    ring
  have hpow2k : |Real.sin y| ^ (2 * k) ≤ (Real.sin r ^ 2) ^ k := by
    have e : |Real.sin y| ^ (2 * k) = (|Real.sin y| ^ 2) ^ k := by
      rw [← pow_mul]
    rw [e]
    apply pow_le_pow_left₀ (by positivity) _ k
    exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
  have hpow2k2 : |Real.sin y| ^ (2 * k + 2) ≤ (Real.sin r ^ 2) ^ k := by
    have e : |Real.sin y| ^ (2 * k + 2)
        = |Real.sin y| ^ (2 * k) * |Real.sin y| ^ 2 := by
      rw [← pow_add]
    have hsq1 : |Real.sin y| ^ 2 ≤ 1 := by
      have h1 : |Real.sin y| ≤ 1 := le_trans hsin_le hq1
      nlinarith [abs_nonneg (Real.sin y), h1, sq_nonneg (|Real.sin y|)]
    calc |Real.sin y| ^ (2 * k + 2)
        = |Real.sin y| ^ (2 * k) * |Real.sin y| ^ 2 := e
      _ ≤ (Real.sin r ^ 2) ^ k * 1 :=
          mul_le_mul hpow2k hsq1 (by positivity) (by positivity)
      _ = (Real.sin r ^ 2) ^ k := by ring
  have h2k1_nn : 0 ≤ (2 * (k : ℝ) + 1) := by positivity
  have h2k2_nn : 0 ≤ (2 * (k : ℝ) + 2) := by positivity
  have ha : ‖chapter9Entry23Coeff k * (((2 * k + 1 : ℕ)) : ℝ)
        * Real.sin y ^ (2 * k)‖
      ≤ (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
      abs_of_nonneg hc_nn
    have h2 : |((((2 * k + 1 : ℕ))) : ℝ)| = 2 * (k : ℝ) + 1 := by
      rw [hcast1]
      exact abs_of_nonneg h2k1_nn
    rw [h1, h2]
    have g1 : chapter9Entry23Coeff k * (2 * (k : ℝ) + 1)
        ≤ 1 * (2 * (k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hc_le h2k1_nn
    have hB : 0 ≤ 1 * (2 * (k : ℝ) + 1) := by linarith [h2k1_nn]
    have hpow_nn : 0 ≤ |Real.sin y| ^ (2 * k) := by positivity
    calc chapter9Entry23Coeff k * (2 * (k : ℝ) + 1) * |Real.sin y| ^ (2 * k)
        ≤ 1 * (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k :=
          mul_le_mul g1 hpow2k hpow_nn hB
      _ = (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k := by ring
  have hb : ‖chapter9Entry23Coeff k * (((2 * k + 2 : ℕ)) : ℝ)
        * Real.sin y ^ (2 * k + 2)‖
      ≤ (2 * (k : ℝ) + 2) * (Real.sin r ^ 2) ^ k := by
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
      abs_of_nonneg hc_nn
    have h2 : |((((2 * k + 2 : ℕ))) : ℝ)| = 2 * (k : ℝ) + 2 := by
      rw [hcast2]
      exact abs_of_nonneg h2k2_nn
    rw [h1, h2]
    have g1 : chapter9Entry23Coeff k * (2 * (k : ℝ) + 2)
        ≤ 1 * (2 * (k : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hc_le h2k2_nn
    have hB : 0 ≤ 1 * (2 * (k : ℝ) + 2) := by linarith [h2k2_nn]
    have hpow_nn : 0 ≤ |Real.sin y| ^ (2 * k + 2) := by positivity
    calc chapter9Entry23Coeff k * (2 * (k : ℝ) + 2) * |Real.sin y| ^ (2 * k + 2)
        ≤ 1 * (2 * (k : ℝ) + 2) * (Real.sin r ^ 2) ^ k :=
          mul_le_mul g1 hpow2k2 hpow_nn hB
      _ = (2 * (k : ℝ) + 2) * (Real.sin r ^ 2) ^ k := by ring
  unfold chapter9Entry23CKTerm'
  calc ‖chapter9Entry23Coeff k * ↑(2 * k + 1) * Real.sin y ^ (2 * k)
          - chapter9Entry23Coeff k * ↑(2 * k + 2) * Real.sin y ^ (2 * k + 2)‖
      ≤ ‖chapter9Entry23Coeff k * ↑(2 * k + 1) * Real.sin y ^ (2 * k)‖
          + ‖chapter9Entry23Coeff k * ↑(2 * k + 2)
            * Real.sin y ^ (2 * k + 2)‖ := norm_sub_le _ _
    _ ≤ (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k
          + (2 * (k : ℝ) + 2) * (Real.sin r ^ 2) ^ k := add_le_add ha hb
    _ = (4 * (k : ℝ) + 3) * (Real.sin r ^ 2) ^ k := by ring

private lemma summable_ckTerm'_bound {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 2) :
    Summable (fun k : ℕ => (4 * (k : ℝ) + 3) * (Real.sin r ^ 2) ^ k) := by
  have hr2_nn : 0 ≤ (Real.sin r ^ 2) := by positivity
  have hr2 : (Real.sin r ^ 2) < 1 := by
    have hq_nn : 0 ≤ Real.sin r :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith, by linarith [Real.pi_pos]⟩
    have hq1 : Real.sin r < 1 := sin_lt_one_of_mem_Ioo hr0 hr1
    nlinarith [hq_nn, hq1, sq_nonneg (Real.sin r)]
  have hnorm : ‖(Real.sin r ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr2_nn]
    exact hr2
  have h1 : Summable (fun k : ℕ => (2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k) :=
    summable_two_mul_add_one_geom hnorm
  have h2 : Summable (fun k : ℕ => (Real.sin r ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one hnorm
  have h := (h1.mul_left 2).add h2
  have e : (fun k : ℕ => 2 * ((2 * (k : ℝ) + 1) * (Real.sin r ^ 2) ^ k)
        + (Real.sin r ^ 2) ^ k)
      = (fun k : ℕ => (4 * (k : ℝ) + 3) * (Real.sin r ^ 2) ^ k) := by
    funext k
    ring
  rwa [e] at h

private lemma summable_ckTerm_zero :
    Summable (fun k : ℕ => chapter9Entry23CKTerm 0 k) := by
  simp only [ckTerm_zero]
  exact summable_zero

private lemma hasDerivAt_CK_tsum {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (fun v => ∑' k, chapter9Entry23CKTerm v k)
      (∑' k, chapter9Entry23CKTerm' u k) u := by
  have hpi : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hu_mem⟩ := exists_r_of_mem_Ioo hpi hu
  have hsumu' := summable_ckTerm'_bound hr0 hr1
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := Set.mem_Ioo.mpr ⟨by linarith, hr0⟩
  have hderiv : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      HasDerivAt (fun v => chapter9Entry23CKTerm v k)
        (chapter9Entry23CKTerm' y k) y := fun k y _ => hasDerivAt_ckTerm y k
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      ‖chapter9Entry23CKTerm' y k‖
        ≤ (4 * (k : ℝ) + 3) * (Real.sin r ^ 2) ^ k :=
    fun k y hy => norm_ckTerm'_le hr0 hr1 hy k
  exact hasDerivAt_tsum_of_isPreconnected hsumu' isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected hderiv hbound h0mem summable_ckTerm_zero hu_mem

private lemma tan_nonneg_of_mem {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < Real.pi / 2) :
    0 ≤ Real.tan r := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hrmem : r ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have h := (Real.strictMonoOn_tan.le_iff_le h0mem hrmem).mpr hr0
  rwa [Real.tan_zero] at h

private lemma tan_lt_one_of_lt_pi_div_four {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < Real.pi / 4) : Real.tan r < 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hrmem : r ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hpmem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have h := (Real.strictMonoOn_tan.lt_iff_lt hrmem hpmem).mpr hr1
  rwa [Real.tan_pi_div_four] at h

private lemma norm_aTerm'_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < Real.pi / 4)
    (hy : y ∈ Set.Ioo (-r) r) (j : ℕ) :
    ‖chapter9Entry23ATerm' y j‖
      ≤ (Real.tan r * (1 + Real.tan r ^ 2))
        * (((j : ℝ) + 1) * (Real.tan r ^ 2) ^ j) := by
  have hr1' : r < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hy
    constructor <;> linarith
  have hcos : Real.cos y ≠ 0 := cos_ne_zero_of_mem_Ioo hymem
  have hcos2_pos : 0 < Real.cos y ^ 2 := by positivity
  have htan_le := abs_tan_le_tan_of_mem hr0 hr1' hy
  have hq_nn : 0 ≤ Real.tan r := tan_nonneg_of_mem (le_of_lt hr0) hr1'
  have hH : chapter9OddHarmonic (j + 1) ≤ ((((j + 1 : ℕ))) : ℝ) :=
    oddHarmonic_le_card (j + 1)
  have hHnn : 0 ≤ chapter9OddHarmonic (j + 1) := oddHarmonic_nonneg _
  have hcast : ((((j + 1 : ℕ))) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  have hinv_le := inv_cos_sq_le_of_mem hr0 hr1' hy
  have hinv_nn : 0 ≤ 1 / Real.cos y ^ 2 := by positivity
  have hpow : |Real.tan y| ^ (2 * j + 1)
      ≤ Real.tan r * (Real.tan r ^ 2) ^ j := by
    have e2 : |Real.tan y| ^ (2 * j + 1)
        = |Real.tan y| * (|Real.tan y| ^ 2) ^ j := by
      rw [pow_add, pow_one, ← pow_mul]
      ring
    have h1 : |Real.tan y| ≤ Real.tan r := htan_le
    have h2 : (|Real.tan y| ^ 2) ^ j ≤ (Real.tan r ^ 2) ^ j := by
      apply pow_le_pow_left₀ (by positivity) _ j
      exact pow_le_pow_left₀ (abs_nonneg _) htan_le 2
    calc |Real.tan y| ^ (2 * j + 1)
        = |Real.tan y| * (|Real.tan y| ^ 2) ^ j := e2
      _ ≤ Real.tan r * (Real.tan r ^ 2) ^ j :=
          mul_le_mul h1 h2 (by positivity) hq_nn
  have hneg1 : (|(-1 : ℝ) ^ j| : ℝ) = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  unfold chapter9Entry23ATerm'
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, hneg1, one_mul,
    abs_of_nonneg hHnn, abs_pow, abs_of_pos hcos2_pos]
  have hdiv_eq : chapter9OddHarmonic (j + 1) * |Real.tan y| ^ (2 * j + 1)
      / Real.cos y ^ 2
      = (chapter9OddHarmonic (j + 1) * |Real.tan y| ^ (2 * j + 1))
        * (1 / Real.cos y ^ 2) := by ring
  rw [hdiv_eq]
  have hb_nn : 0 ≤ ((j : ℝ) + 1) * (Real.tan r * (Real.tan r ^ 2) ^ j) := by
    have hj : 0 ≤ (j : ℝ) + 1 := by positivity
    have hq : 0 ≤ Real.tan r * (Real.tan r ^ 2) ^ j :=
      mul_nonneg hq_nn (by positivity)
    exact mul_nonneg hj hq
  have g1 : chapter9OddHarmonic (j + 1) * |Real.tan y| ^ (2 * j + 1)
      ≤ ((j : ℝ) + 1) * (Real.tan r * (Real.tan r ^ 2) ^ j) := by
    have hH' : chapter9OddHarmonic (j + 1) ≤ (j : ℝ) + 1 := by
      rw [← hcast]
      exact hH
    have hpow_nn : 0 ≤ |Real.tan y| ^ (2 * j + 1) := by positivity
    exact mul_le_mul hH' hpow hpow_nn (by linarith [hHnn])
  have g2 : chapter9OddHarmonic (j + 1) * |Real.tan y| ^ (2 * j + 1)
        * (1 / Real.cos y ^ 2)
      ≤ ((j : ℝ) + 1) * (Real.tan r * (Real.tan r ^ 2) ^ j)
        * (1 + Real.tan r ^ 2) :=
    mul_le_mul g1 hinv_le hinv_nn hb_nn
  calc chapter9OddHarmonic (j + 1) * |Real.tan y| ^ (2 * j + 1)
        * (1 / Real.cos y ^ 2)
      ≤ ((j : ℝ) + 1) * (Real.tan r * (Real.tan r ^ 2) ^ j)
        * (1 + Real.tan r ^ 2) := g2
    _ = Real.tan r * (1 + Real.tan r ^ 2)
          * (((j : ℝ) + 1) * (Real.tan r ^ 2) ^ j) := by ring

private lemma summable_aTerm'_bound {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 4) :
    Summable (fun j : ℕ => (Real.tan r * (1 + Real.tan r ^ 2))
      * (((j : ℝ) + 1) * (Real.tan r ^ 2) ^ j)) := by
  have hq_nn : 0 ≤ Real.tan r :=
    tan_nonneg_of_mem (le_of_lt hr0) (by linarith [Real.pi_pos])
  have hq1 : Real.tan r < 1 := tan_lt_one_of_lt_pi_div_four (le_of_lt hr0) hr1
  have hr2 : (Real.tan r ^ 2) < 1 := by nlinarith [hq_nn, hq1]
  have hr2_nn : 0 ≤ (Real.tan r ^ 2) := by positivity
  have hnorm : ‖(Real.tan r ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr2_nn]
    exact hr2
  have h := summable_succ_mul_geom hnorm
  have e : (fun j : ℕ => ((j : ℝ) + 1) * (Real.tan r ^ 2) ^ j)
      = (fun j : ℕ => ((j : ℝ) + 1) * (Real.tan r ^ 2) ^ j) := rfl
  exact h.mul_left _

private lemma summable_aTerm_zero :
    Summable (fun j : ℕ => chapter9Entry23ATerm 0 j) := by
  simp only [aTerm_zero]
  exact summable_zero

private lemma hasDerivAt_A_tsum {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    HasDerivAt (fun y => ∑' j, chapter9Entry23ATerm y j)
      (∑' j, chapter9Entry23ATerm' x j) x := by
  have hpi : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hx_mem⟩ := exists_r_of_mem_Ioo hpi hx
  have hsumu' := summable_aTerm'_bound hr0 hr1
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := Set.mem_Ioo.mpr ⟨by linarith, hr0⟩
  have hr1' : r < Real.pi / 2 := by linarith [Real.pi_pos]
  have hderiv : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      HasDerivAt (fun v => chapter9Entry23ATerm v j)
        (chapter9Entry23ATerm' y j) y := by
    intro j y hy
    have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have h := Set.mem_Ioo.mp hy
      constructor <;> linarith
    exact hasDerivAt_aTerm j (cos_ne_zero_of_mem_Ioo hymem)
  have hbound : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      ‖chapter9Entry23ATerm' y j‖
        ≤ Real.tan r * (1 + Real.tan r ^ 2)
          * (((j : ℝ) + 1) * (Real.tan r ^ 2) ^ j) :=
    fun j y hy => norm_aTerm'_le hr0 hr1 hy j
  exact hasDerivAt_tsum_of_isPreconnected hsumu' isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected hderiv hbound h0mem summable_aTerm_zero hx_mem

private lemma norm_lTerm'_le {r y : ℝ} (hr0 : 0 < r) (hr1 : r < Real.pi / 4)
    (hy : y ∈ Set.Ioo (-r) r) (j : ℕ) :
    ‖chapter9Entry23LTerm' y j‖
      ≤ (Real.tan r * (1 + Real.tan r ^ 2) / 2) * (Real.tan r ^ 2) ^ j := by
  have hr1' : r < Real.pi / 2 := by linarith [Real.pi_pos]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hy
    constructor <;> linarith
  have hcos : Real.cos y ≠ 0 := cos_ne_zero_of_mem_Ioo hymem
  have hD : (0 : ℝ) < ((((2 * (j + 1) : ℕ))) : ℝ) :=
    Nat.cast_pos.mpr (by omega : 0 < 2 * (j + 1))
  have hcos2_pos : 0 < Real.cos y ^ 2 := by positivity
  have hden_pos : 0 < ((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos y ^ 2 :=
    mul_pos hD hcos2_pos
  have htan_le := abs_tan_le_tan_of_mem hr0 hr1' hy
  have hq_nn : 0 ≤ Real.tan r := tan_nonneg_of_mem (le_of_lt hr0) hr1'
  have hH : chapter9OddHarmonic (j + 1) ≤ ((((j + 1 : ℕ))) : ℝ) :=
    oddHarmonic_le_card (j + 1)
  have hHnn : 0 ≤ chapter9OddHarmonic (j + 1) := oddHarmonic_nonneg _
  have hHD : chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ)
      ≤ 1 / 2 := by
    have hcast2 : ((((2 * (j + 1) : ℕ))) : ℝ) = 2 * ((((j + 1 : ℕ))) : ℝ) := by
      rw [show (2 * (j + 1)) = (j + 1) + (j + 1) from by omega, Nat.cast_add]
      ring
    have hj_pos : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) :=
      Nat.cast_pos.mpr (by omega : 0 < j + 1)
    rw [hcast2, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hH, hHnn, hj_pos]
  have hinv_le : 1 / (Real.cos y ^ 2) ≤ 1 + Real.tan r ^ 2 :=
    inv_cos_sq_le_of_mem hr0 hr1' hy
  have hpow : |Real.tan y| ^ (2 * j + 1)
      ≤ Real.tan r * (Real.tan r ^ 2) ^ j := by
    have e2 : |Real.tan y| ^ (2 * j + 1)
        = |Real.tan y| * (|Real.tan y| ^ 2) ^ j := by
      rw [pow_add, pow_one, ← pow_mul]
      ring
    have h1 : |Real.tan y| ≤ Real.tan r := htan_le
    have h2 : (|Real.tan y| ^ 2) ^ j ≤ (Real.tan r ^ 2) ^ j := by
      apply pow_le_pow_left₀ (by positivity) _ j
      exact pow_le_pow_left₀ (abs_nonneg _) htan_le 2
    calc |Real.tan y| ^ (2 * j + 1)
        = |Real.tan y| * (|Real.tan y| ^ 2) ^ j := e2
      _ ≤ Real.tan r * (Real.tan r ^ 2) ^ j :=
          mul_le_mul h1 h2 (by positivity) hq_nn
  have hneg1 : (|(-1 : ℝ) ^ j| : ℝ) = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  unfold chapter9Entry23LTerm'
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul, hneg1, one_mul,
    abs_of_nonneg hHnn, abs_pow, abs_of_pos hden_pos]
  have hdiv_eq : chapter9OddHarmonic (j + 1) * |Real.tan y| ^ (2 * j + 1)
      / (((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos y ^ 2)
      = (chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ))
        * |Real.tan y| ^ (2 * j + 1) * (1 / Real.cos y ^ 2) := by
    have hD' : ((((2 * (j + 1) : ℕ))) : ℝ) ≠ 0 := ne_of_gt hD
    have hc' : Real.cos y ^ 2 ≠ 0 := ne_of_gt hcos2_pos
    field_simp
  rw [hdiv_eq]
  have h1 : chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ)
      * |Real.tan y| ^ (2 * j + 1)
      ≤ (1 / 2) * (Real.tan r * (Real.tan r ^ 2) ^ j) := by
    have hpow_nn : 0 ≤ |Real.tan y| ^ (2 * j + 1) := by positivity
    exact mul_le_mul hHD hpow hpow_nn (by norm_num)
  have hb_nn : 0 ≤ (1 / 2 : ℝ) * (Real.tan r * (Real.tan r ^ 2) ^ j) := by
    have hq : 0 ≤ Real.tan r * (Real.tan r ^ 2) ^ j :=
      mul_nonneg hq_nn (by positivity)
    linarith
  have hinv_nn : 0 ≤ 1 / Real.cos y ^ 2 := by positivity
  calc chapter9OddHarmonic (j + 1) / ↑(2 * (j + 1)) * |Real.tan y| ^ (2 * j + 1)
        * (1 / Real.cos y ^ 2)
      ≤ (1 / 2) * (Real.tan r * (Real.tan r ^ 2) ^ j)
        * (1 + Real.tan r ^ 2) :=
        mul_le_mul h1 hinv_le hinv_nn hb_nn
    _ = Real.tan r * (1 + Real.tan r ^ 2) / 2 * (Real.tan r ^ 2) ^ j := by ring

private lemma summable_lTerm'_bound {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < Real.pi / 4) :
    Summable (fun j : ℕ => (Real.tan r * (1 + Real.tan r ^ 2) / 2)
      * (Real.tan r ^ 2) ^ j) := by
  have hq_nn : 0 ≤ Real.tan r :=
    tan_nonneg_of_mem (le_of_lt hr0) (by linarith [Real.pi_pos])
  have hq1 : Real.tan r < 1 := tan_lt_one_of_lt_pi_div_four (le_of_lt hr0) hr1
  have hr2 : (Real.tan r ^ 2) < 1 := by nlinarith [hq_nn, hq1]
  have hr2_nn : 0 ≤ (Real.tan r ^ 2) := by positivity
  have hnorm : ‖(Real.tan r ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hr2_nn]
    exact hr2
  exact (summable_geometric_of_norm_lt_one hnorm).mul_left _

private lemma summable_lTerm_zero :
    Summable (fun j : ℕ => chapter9Entry23LeftTerm 0 j) := by
  simp only [leftTerm_zero]
  exact summable_zero

private lemma hasDerivAt_L_tsum {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    HasDerivAt (fun y => ∑' j, chapter9Entry23LeftTerm y j)
      (∑' j, chapter9Entry23LTerm' x j) x := by
  have hpi : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hx_mem⟩ := exists_r_of_mem_Ioo hpi hx
  have hsumu' := summable_lTerm'_bound hr0 hr1
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-r) r := Set.mem_Ioo.mpr ⟨by linarith, hr0⟩
  have hderiv : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      HasDerivAt (fun v => chapter9Entry23LeftTerm v j)
        (chapter9Entry23LTerm' y j) y := by
    intro j y hy
    have hymem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have h := Set.mem_Ioo.mp hy
      constructor <;> linarith [Real.pi_pos]
    exact hasDerivAt_leftTerm j (cos_ne_zero_of_mem_Ioo hymem)
  have hbound : ∀ j : ℕ, ∀ y ∈ Set.Ioo (-r) r,
      ‖chapter9Entry23LTerm' y j‖
        ≤ Real.tan r * (1 + Real.tan r ^ 2) / 2 * (Real.tan r ^ 2) ^ j :=
    fun j y hy => norm_lTerm'_le hr0 hr1 hy j
  have hzero : Summable (fun j : ℕ => chapter9Entry23LeftTerm 0 j) :=
    summable_lTerm_zero
  exact hasDerivAt_tsum_of_isPreconnected hsumu' isOpen_Ioo
    (convex_Ioo (-r) r).isPreconnected hderiv hbound h0mem hzero hx_mem

private lemma oddHarmonic_one : chapter9OddHarmonic 1 = 1 := by
  unfold chapter9OddHarmonic
  simp

private lemma pTerm_zero (t : ℝ) : chapter9Entry23PTerm t 0 = t := by
  unfold chapter9Entry23PTerm
  simp [oddHarmonic_one]

private lemma arctanTerm_zero (t : ℝ) :
    chapter9Entry23ArctanTerm t 0 = t := by
  unfold chapter9Entry23ArctanTerm
  simp

private lemma summable_pTerm {t : ℝ} (ht : |t| < 1) :
    Summable (chapter9Entry23PTerm t) := by
  have ht2 : |t| ^ 2 < 1 := by
    nlinarith [ht, abs_nonneg t, sq_nonneg (|t|)]
  have ht2_nn : 0 ≤ |t| ^ 2 := by positivity
  have hnorm : ‖(|t| ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg ht2_nn]
    exact ht2
  have hbase := summable_succ_mul_geom hnorm
  have hmul := hbase.mul_left |t|
  have hbound : ∀ n : ℕ, ‖chapter9Entry23PTerm t n‖
      ≤ |t| * (((n : ℝ) + 1) * (|t| ^ 2) ^ n) := by
    intro n
    have hH : chapter9OddHarmonic (n + 1) ≤ ((((n + 1 : ℕ))) : ℝ) :=
      oddHarmonic_le_card (n + 1)
    have hHnn : 0 ≤ chapter9OddHarmonic (n + 1) := oddHarmonic_nonneg _
    have hcast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
    have hpow : |t| ^ (2 * n + 1) = |t| * (|t| ^ 2) ^ n := by
      rw [pow_add, pow_one, ← pow_mul]
      ring
    have hneg1 : (|(-1 : ℝ) ^ n| : ℝ) = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    unfold chapter9Entry23PTerm
    rw [Real.norm_eq_abs, abs_mul, abs_mul, hneg1, one_mul,
      abs_of_nonneg hHnn, abs_pow]
    calc chapter9OddHarmonic (n + 1) * |t| ^ (2 * n + 1)
        ≤ ((n : ℝ) + 1) * (|t| * (|t| ^ 2) ^ n) := by
          have hpow_nn : 0 ≤ |t| ^ (2 * n + 1) := by positivity
          have hH' : chapter9OddHarmonic (n + 1) ≤ (n : ℝ) + 1 := by
            rw [← hcast]
            exact hH
          have hpow' : |t| ^ (2 * n + 1) ≤ |t| * (|t| ^ 2) ^ n := by
            rw [hpow]
          exact mul_le_mul hH' hpow' hpow_nn (by linarith [hHnn])
      _ = |t| * (((n : ℝ) + 1) * (|t| ^ 2) ^ n) := by ring
  have e : (fun n : ℕ => |t| * (((n : ℝ) + 1) * (|t| ^ 2) ^ n))
      = (fun n : ℕ => |t| * (((n : ℝ) + 1) * (|t| ^ 2) ^ n)) := rfl
  have hmul' : Summable (fun n : ℕ => |t| * (((n : ℝ) + 1) * (|t| ^ 2) ^ n)) :=
    hmul
  exact Summable.of_norm_bounded hmul' hbound

private lemma summable_arctanTerm {t : ℝ} (ht : |t| < 1) :
    Summable (chapter9Entry23ArctanTerm t) := by
  have hnorm : ‖t‖ < 1 := by
    rwa [Real.norm_eq_abs]
  have h := (Real.hasSum_arctan hnorm).summable
  have e : (fun n : ℕ => (-1 : ℝ) ^ n * t ^ (2 * n + 1) / ↑(2 * n + 1))
      = chapter9Entry23ArctanTerm t := by
    funext n
    unfold chapter9Entry23ArctanTerm
    ring
  rwa [e] at h

private lemma arctan_hasSum {t : ℝ} (ht : |t| < 1) :
    HasSum (chapter9Entry23ArctanTerm t) (Real.arctan t) := by
  have hnorm : ‖t‖ < 1 := by
    rwa [Real.norm_eq_abs]
  have h := Real.hasSum_arctan hnorm
  have e : (fun n : ℕ => (-1 : ℝ) ^ n * t ^ (2 * n + 1) / ↑(2 * n + 1))
      = chapter9Entry23ArctanTerm t := by
    funext n
    unfold chapter9Entry23ArctanTerm
    ring
  rwa [e] at h

private lemma arctanTerm_succ_eq (t : ℝ) (n : ℕ) :
    chapter9Entry23ArctanTerm t (n + 1)
      = chapter9Entry23PTerm t (n + 1) + t ^ 2 * chapter9Entry23PTerm t n := by
  have eN : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
  have hD : ((((2 * n + 3 : ℕ))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega : 2 * n + 3 ≠ 0)
  have hdiff := oddHarmonic_diff n
  have hneg : (-1 : ℝ) ^ (n + 1) = -(-1 : ℝ) ^ n := by
    rw [pow_succ]
    ring
  have hdiff2 : chapter9OddHarmonic (n + 1 + 1)
      = chapter9OddHarmonic (n + 1) + 1 / ((((2 * n + 3 : ℕ))) : ℝ) := by
    have h := hdiff
    have hcast : ((((2 * (n + 1) + 1 : ℕ))) : ℝ)
        = ((((2 * n + 3 : ℕ))) : ℝ) := by
      rw [show 2 * (n + 1) + 1 = 2 * n + 3 from eN]
    rw [hcast] at h
    linarith
  unfold chapter9Entry23ArctanTerm chapter9Entry23PTerm
  rw [eN, hneg, hdiff2]
  field_simp
  ring

private lemma tsum_PTerm_eq {t : ℝ} (ht : |t| < 1) :
    ∑' j, chapter9Entry23PTerm t j = Real.arctan t / (1 + t ^ 2) := by
  have hP : Summable (chapter9Entry23PTerm t) := summable_pTerm ht
  have hA : Summable (chapter9Entry23ArctanTerm t) := summable_arctanTerm ht
  have hP0 := pTerm_zero t
  have hA0 := arctanTerm_zero t
  have hPshift : Summable (fun n => chapter9Entry23PTerm t (n + 1)) :=
    (summable_nat_add_iff 1).mpr hP
  have hAshift : Summable (fun n => chapter9Entry23ArctanTerm t (n + 1)) :=
    (summable_nat_add_iff 1).mpr hA
  have hPeq := hP.tsum_eq_zero_add
  have hAeq := hA.tsum_eq_zero_add
  have hAval : ∑' n, chapter9Entry23ArctanTerm t n = Real.arctan t :=
    (arctan_hasSum ht).tsum_eq
  have hterm : ∀ n : ℕ, chapter9Entry23ArctanTerm t (n + 1)
      = chapter9Entry23PTerm t (n + 1) + t ^ 2 * chapter9Entry23PTerm t n :=
    fun n => arctanTerm_succ_eq t n
  have hcongr : (∑' n, chapter9Entry23ArctanTerm t (n + 1))
      = ∑' n, (chapter9Entry23PTerm t (n + 1)
        + t ^ 2 * chapter9Entry23PTerm t n) :=
    tsum_congr hterm
  have hmul : Summable (fun n => t ^ 2 * chapter9Entry23PTerm t n) :=
    hP.mul_left _
  have hadd := hPshift.add hmul
  have htsum_add := Summable.tsum_add hPshift hmul
  have htsum_mul := Summable.tsum_mul_left (t ^ 2) hP
  have hshift_eq : (∑' n, chapter9Entry23ArctanTerm t (n + 1))
      = (∑' n, chapter9Entry23PTerm t (n + 1))
        + t ^ 2 * (∑' n, chapter9Entry23PTerm t n) := by
    rw [hcongr, htsum_add, htsum_mul]
  have h1t2 : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hP_eq : ∑' j, chapter9Entry23PTerm t j
      = chapter9Entry23PTerm t 0 + ∑' n, chapter9Entry23PTerm t (n + 1) := hPeq
  have hA_eq : ∑' n, chapter9Entry23ArctanTerm t n
      = chapter9Entry23ArctanTerm t 0
        + ∑' n, chapter9Entry23ArctanTerm t (n + 1) := hAeq
  rw [hP0] at hP_eq
  rw [hA0] at hA_eq
  rw [hAval] at hA_eq
  have hmain : Real.arctan t
      = (∑' n, chapter9Entry23PTerm t n) * (1 + t ^ 2) := by
    linarith [hP_eq, hA_eq, hshift_eq]
  have hne : (1 : ℝ) + t ^ 2 ≠ 0 := ne_of_gt h1t2
  rw [hmain]
  field_simp

private lemma abs_tan_lt_one_of_mem_Ioo {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) : |Real.tan x| < 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hxmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith
  have hpmem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hnm : (-(Real.pi / 4)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have h1 : Real.tan x < 1 := by
    have h := (Real.strictMonoOn_tan.lt_iff_lt hxmem hpmem).mpr
      (Set.mem_Ioo.mp hx).2
    rwa [Real.tan_pi_div_four] at h
  have h2 : (-1 : ℝ) < Real.tan x := by
    have h := (Real.strictMonoOn_tan.lt_iff_lt hnm hxmem).mpr
      (Set.mem_Ioo.mp hx).1
    rw [Real.tan_neg, Real.tan_pi_div_four] at h
    linarith
  exact abs_lt.mpr ⟨by linarith, h1⟩

private lemma tsum_aTerm'_eq {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    ∑' j, chapter9Entry23ATerm' x j = x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx2 : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith
  have hcos : Real.cos x ≠ 0 := cos_ne_zero_of_mem_Ioo hx2
  have hcos2 : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have htan1 := abs_tan_lt_one_of_mem_Ioo hx
  have hP : Summable (chapter9Entry23PTerm (Real.tan x)) :=
    summable_pTerm htan1
  have e : ∀ j : ℕ, chapter9Entry23ATerm' x j
      = chapter9Entry23PTerm (Real.tan x) j / Real.cos x ^ 2 := by
    intro j
    unfold chapter9Entry23ATerm' chapter9Entry23PTerm
    ring
  have hcongr : (∑' j, chapter9Entry23ATerm' x j)
      = ∑' j, chapter9Entry23PTerm (Real.tan x) j / Real.cos x ^ 2 :=
    tsum_congr e
  have e2 : (fun j : ℕ => chapter9Entry23PTerm (Real.tan x) j / Real.cos x ^ 2)
      = (fun j : ℕ => chapter9Entry23PTerm (Real.tan x) j
        * (Real.cos x ^ 2)⁻¹) := by
    funext j
    rw [div_eq_mul_inv]
  have hdiv : (∑' j, chapter9Entry23PTerm (Real.tan x) j / Real.cos x ^ 2)
      = (∑' j, chapter9Entry23PTerm (Real.tan x) j) / Real.cos x ^ 2 := by
    rw [e2, hP.tsum_mul_right, ← div_eq_mul_inv]
  rw [hcongr, hdiv, tsum_PTerm_eq htan1]
  have harctan : Real.arctan (Real.tan x) = x :=
    Real.arctan_tan (Set.mem_Ioo.mp hx2).1 (Set.mem_Ioo.mp hx2).2
  rw [harctan]
  have h1t : 1 + Real.tan x ^ 2 = 1 / Real.cos x ^ 2 :=
    one_add_tan_sq x hcos
  rw [h1t]
  field_simp

private lemma hasDerivAt_sq_div_two (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
  have h := ((hasDerivAt_id' x).pow 2).div_const (2 : ℝ)
  simp only [Pi.pow_apply] at h
  have eval : (((2 : ℕ)) : ℝ) * x ^ (2 - 1) * 1 / 2 = x := by
    norm_num
  rwa [eval] at h

private lemma A_eq_sq {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    (∑' j, chapter9Entry23ATerm x j) = x ^ 2 / 2 := by
  have hs : IsOpen (Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) := isOpen_Ioo
  have hs' : IsPreconnected (Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :=
    isPreconnected_Ioo
  have hf : DifferentiableOn ℝ (fun y => ∑' j, chapter9Entry23ATerm y j)
      (Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) := by
    intro y hy
    exact (hasDerivAt_A_tsum hy).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ (fun y : ℝ => y ^ 2 / 2)
      (Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) := by
    intro y hy
    exact (hasDerivAt_sq_div_two y).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv (fun y => ∑' j, chapter9Entry23ATerm y j))
      (deriv (fun y : ℝ => y ^ 2 / 2))
      (Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) := by
    intro y hy
    rw [(hasDerivAt_A_tsum hy).deriv, (hasDerivAt_sq_div_two y).deriv]
    exact tsum_aTerm'_eq hy
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4) := by
    constructor <;> linarith [Real.pi_pos]
  have hfg0 : (∑' j, chapter9Entry23ATerm (0 : ℝ) j) = (0 : ℝ) ^ 2 / 2 := by
    have h1 : (∑' j, chapter9Entry23ATerm (0 : ℝ) j) = 0 := by
      have e : (fun j : ℕ => chapter9Entry23ATerm (0 : ℝ) j) = 0 := by
        funext j
        exact aTerm_zero j
      rw [e]
      exact tsum_zero
    rw [h1]
    norm_num
  have heq := hs.eqOn_of_deriv_eq hs' hf hg hderiv h0mem hfg0
  exact heq hx

private lemma summable_lTerm'_at {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    Summable (chapter9Entry23LTerm' x) := by
  have hpi : 0 < Real.pi / 4 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hx_mem⟩ := exists_r_of_mem_Ioo hpi hx
  exact Summable.of_norm_bounded (summable_lTerm'_bound hr0 hr1)
    (fun j => norm_lTerm'_le hr0 hr1 hx_mem j)

private lemma lTerm'_mul_eq_aTerm {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) (j : ℕ) :
    Real.tan x * Real.cos x ^ 2 * chapter9Entry23LTerm' x j
      = chapter9Entry23ATerm x j := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx2 : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith
  have hcos : Real.cos x ≠ 0 := cos_ne_zero_of_mem_Ioo hx2
  have hcos2 : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have hD : ((((2 * (j + 1) : ℕ))) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega : 2 * (j + 1) ≠ 0)
  have eN : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
  unfold chapter9Entry23LTerm' chapter9Entry23ATerm
  field_simp
  ring

private lemma tsum_lTerm'_mul_eq {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    Real.tan x * Real.cos x ^ 2 * (∑' j, chapter9Entry23LTerm' x j)
      = x ^ 2 / 2 := by
  have hsum := summable_lTerm'_at hx
  have e : ∀ j : ℕ, Real.tan x * Real.cos x ^ 2 * chapter9Entry23LTerm' x j
      = chapter9Entry23ATerm x j := fun j => lTerm'_mul_eq_aTerm hx j
  have hcongr : (∑' j, Real.tan x * Real.cos x ^ 2 * chapter9Entry23LTerm' x j)
      = ∑' j, chapter9Entry23ATerm x j :=
    tsum_congr e
  have htsum := Summable.tsum_mul_left (Real.tan x * Real.cos x ^ 2) hsum
  have h1 : (∑' j, Real.tan x * Real.cos x ^ 2 * chapter9Entry23LTerm' x j)
      = Real.tan x * Real.cos x ^ 2 * (∑' j, chapter9Entry23LTerm' x j) := htsum
  rw [h1] at hcongr
  rw [hcongr]
  exact A_eq_sq hx

private lemma sin_two_mul_LTerm' {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    Real.sin (2 * x) * (∑' j, chapter9Entry23LTerm' x j) = x ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx2 : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith
  have hcos : Real.cos x ≠ 0 := cos_ne_zero_of_mem_Ioo hx2
  have htan : Real.tan x = Real.sin x / Real.cos x :=
    Real.tan_eq_sin_div_cos x
  have hsin2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  have hmain := tsum_lTerm'_mul_eq hx
  have hcos2_ne : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have e : Real.sin (2 * x)
      = 2 * (Real.tan x * Real.cos x ^ 2) := by
    rw [htan, hsin2]
    field_simp
  rw [e]
  linarith [hmain]

private def chapter9Entry23ASeq (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 1 : ℕ)) : ℝ) * Real.sin u ^ (2 * k)

private def chapter9Entry23BSeq (u : ℝ) (k : ℕ) : ℝ :=
  chapter9Entry23Coeff k * (((2 * k + 2 : ℕ)) : ℝ) * Real.sin u ^ (2 * k + 2)

private lemma ckTerm'_eq_sub (u : ℝ) (k : ℕ) :
    chapter9Entry23CKTerm' u k
      = chapter9Entry23ASeq u k - chapter9Entry23BSeq u k := by
  unfold chapter9Entry23CKTerm' chapter9Entry23ASeq chapter9Entry23BSeq
  ring

private lemma summable_aSeq {u : ℝ} (hu : |Real.sin u| < 1) :
    Summable (chapter9Entry23ASeq u) := by
  have hq2 : |Real.sin u| ^ 2 < 1 := by
    nlinarith [hu, abs_nonneg (Real.sin u), sq_nonneg (|Real.sin u|)]
  have hq2_nn : 0 ≤ |Real.sin u| ^ 2 := by positivity
  have hnorm : ‖(|Real.sin u| ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq2_nn]
    exact hq2
  have hbase := summable_two_mul_add_one_geom hnorm
  have hbound : ∀ k : ℕ, ‖chapter9Entry23ASeq u k‖
      ≤ (2 * (k : ℝ) + 1) * (|Real.sin u| ^ 2) ^ k := by
    intro k
    have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
    have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
    have hcast : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
      push_cast
      ring
    have h2k1_nn : 0 ≤ (2 * (k : ℝ) + 1) := by positivity
    have hpow : |Real.sin u| ^ (2 * k) ≤ (|Real.sin u| ^ 2) ^ k := by
      rw [← pow_mul]
    unfold chapter9Entry23ASeq
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
      abs_of_nonneg hc_nn
    have h2 : |((((2 * k + 1 : ℕ))) : ℝ)| = 2 * (k : ℝ) + 1 := by
      rw [hcast]
      exact abs_of_nonneg h2k1_nn
    rw [h1, h2]
    have g1 : chapter9Entry23Coeff k * (2 * (k : ℝ) + 1)
        ≤ 1 * (2 * (k : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hc_le h2k1_nn
    have hB : 0 ≤ 1 * (2 * (k : ℝ) + 1) := by linarith [h2k1_nn]
    have hpow_nn : 0 ≤ |Real.sin u| ^ (2 * k) := by positivity
    calc chapter9Entry23Coeff k * (2 * (k : ℝ) + 1) * |Real.sin u| ^ (2 * k)
        ≤ 1 * (2 * (k : ℝ) + 1) * (|Real.sin u| ^ 2) ^ k :=
          mul_le_mul g1 hpow hpow_nn hB
      _ = (2 * (k : ℝ) + 1) * (|Real.sin u| ^ 2) ^ k := by ring
  exact Summable.of_norm_bounded hbase hbound

private lemma summable_bSeq {u : ℝ} (hu : |Real.sin u| < 1) :
    Summable (chapter9Entry23BSeq u) := by
  have hq2 : |Real.sin u| ^ 2 < 1 := by
    nlinarith [hu, abs_nonneg (Real.sin u), sq_nonneg (|Real.sin u|)]
  have hq2_nn : 0 ≤ |Real.sin u| ^ 2 := by positivity
  have hnorm : ‖(|Real.sin u| ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq2_nn]
    exact hq2
  have hbase := summable_succ_mul_geom hnorm
  have hC : (0 : ℝ) ≤ 2 * |Real.sin u| ^ 2 := by positivity
  have hmul := hbase.mul_left (2 * |Real.sin u| ^ 2)
  have hbound : ∀ k : ℕ, ‖chapter9Entry23BSeq u k‖
      ≤ (2 * |Real.sin u| ^ 2) * (((k : ℝ) + 1) * (|Real.sin u| ^ 2) ^ k) := by
    intro k
    have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
    have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
    have hcast : ((((2 * k + 2 : ℕ))) : ℝ) = 2 * ((k : ℝ) + 1) := by
      push_cast
      ring
    have h2k2_nn : 0 ≤ (2 * (k : ℝ) + 2) := by positivity
    have hpow : |Real.sin u| ^ (2 * k + 2)
        = |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by
      rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add, ← pow_mul]
    unfold chapter9Entry23BSeq
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow]
    have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
      abs_of_nonneg hc_nn
    have h2 : |((((2 * k + 2 : ℕ))) : ℝ)| = 2 * ((k : ℝ) + 1) := by
      rw [hcast]
      have hnn : 0 ≤ (2 : ℝ) * ((k : ℝ) + 1) := by positivity
      exact abs_of_nonneg hnn
    rw [h1, h2, hpow]
    have g1 : chapter9Entry23Coeff k * (2 * ((k : ℝ) + 1))
        ≤ 1 * (2 * ((k : ℝ) + 1)) := by
      have hnn : 0 ≤ (2 : ℝ) * ((k : ℝ) + 1) := by positivity
      exact mul_le_mul_of_nonneg_right hc_le hnn
    have hB : 0 ≤ 1 * (2 * ((k : ℝ) + 1)) := by positivity
    have hpow_nn : 0 ≤ |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by positivity
    have hle : chapter9Entry23Coeff k * (2 * ((k : ℝ) + 1))
          * (|Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k)
        ≤ 1 * (2 * ((k : ℝ) + 1))
          * (|Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k) :=
      mul_le_mul g1 (le_refl _) hpow_nn hB
    calc chapter9Entry23Coeff k * (2 * ((k : ℝ) + 1))
          * (|Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k)
        ≤ 1 * (2 * ((k : ℝ) + 1))
          * (|Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k) := hle
      _ = (2 * |Real.sin u| ^ 2) * (((k : ℝ) + 1) * (|Real.sin u| ^ 2) ^ k) := by
          ring
  exact Summable.of_norm_bounded hmul hbound

private lemma aSeq_zero (u : ℝ) : chapter9Entry23ASeq u 0 = 1 := by
  unfold chapter9Entry23ASeq
  simp [coeff_zero]

private lemma aSeq_succ_eq_bSeq (u : ℝ) (k : ℕ) :
    chapter9Entry23ASeq u (k + 1) = chapter9Entry23BSeq u k := by
  have eN : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  have eP : 2 * (k + 1) = 2 * k + 2 := by omega
  have hrec := coeff_succ_mul k
  unfold chapter9Entry23ASeq chapter9Entry23BSeq
  rw [eN, eP]
  linear_combination hrec * Real.sin u ^ (2 * k + 2)

private lemma tsum_ckTerm'_eq_one {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    ∑' k, chapter9Entry23CKTerm' u k = 1 := by
  have hsin1 : |Real.sin u| < 1 := abs_sin_lt_one_of_mem_Ioo hu
  have hA : Summable (chapter9Entry23ASeq u) := summable_aSeq hsin1
  have hB : Summable (chapter9Entry23BSeq u) := summable_bSeq hsin1
  have hcongr : (∑' k, chapter9Entry23CKTerm' u k)
      = ∑' k, (chapter9Entry23ASeq u k - chapter9Entry23BSeq u k) :=
    tsum_congr (ckTerm'_eq_sub u)
  have htsub := Summable.tsum_sub hA hB
  have hAeq := hA.tsum_eq_zero_add
  have hA0 := aSeq_zero u
  have hshift : (∑' k, chapter9Entry23ASeq u (k + 1))
      = ∑' k, chapter9Entry23BSeq u k :=
    tsum_congr (aSeq_succ_eq_bSeq u)
  have hA_eq : ∑' k, chapter9Entry23ASeq u k
      = chapter9Entry23ASeq u 0 + ∑' k, chapter9Entry23ASeq u (k + 1) := hAeq
  rw [hA0] at hA_eq
  linarith [hcongr, htsub, hA_eq, hshift]

private lemma summable_kTerm_at {u : ℝ} (hu : |Real.sin u| < 1) :
    Summable (chapter9Entry23KTerm u) := by
  have hq2 : |Real.sin u| ^ 2 < 1 := by
    nlinarith [hu, abs_nonneg (Real.sin u), sq_nonneg (|Real.sin u|)]
  have hq2_nn : 0 ≤ |Real.sin u| ^ 2 := by positivity
  have hnorm : ‖(|Real.sin u| ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq2_nn]
    exact hq2
  have hbase := summable_geometric_of_norm_lt_one hnorm
  have hmul := hbase.mul_left |Real.sin u|
  have hbound : ∀ k : ℕ, ‖chapter9Entry23KTerm u k‖
      ≤ |Real.sin u| * (|Real.sin u| ^ 2) ^ k := by
    intro k
    have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
    have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
    have hpow : |Real.sin u| ^ (2 * k + 1)
        = |Real.sin u| * (|Real.sin u| ^ 2) ^ k := by
      rw [pow_add, pow_one, ← pow_mul]
      ring
    unfold chapter9Entry23KTerm
    rw [Real.norm_eq_abs, abs_mul, abs_pow]
    have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
      abs_of_nonneg hc_nn
    rw [h1]
    calc chapter9Entry23Coeff k * |Real.sin u| ^ (2 * k + 1)
        ≤ 1 * (|Real.sin u| * (|Real.sin u| ^ 2) ^ k) := by
          have hpow_nn : 0 ≤ |Real.sin u| ^ (2 * k + 1) := by positivity
          have hpow' : |Real.sin u| ^ (2 * k + 1)
              ≤ |Real.sin u| * (|Real.sin u| ^ 2) ^ k := by rw [hpow]
          exact mul_le_mul hc_le hpow' hpow_nn (by linarith [hc_nn])
      _ = |Real.sin u| * (|Real.sin u| ^ 2) ^ k := by ring
  exact Summable.of_norm_bounded hmul hbound

private lemma ck_tsum_eq_id {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (∑' k, chapter9Entry23CKTerm u k) = u := by
  have hs : IsOpen (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := isOpen_Ioo
  have hs' : IsPreconnected (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    isPreconnected_Ioo
  have hf : DifferentiableOn ℝ (fun v => ∑' k, chapter9Entry23CKTerm v k)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro y hy
    exact (hasDerivAt_CK_tsum hy).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ (fun v : ℝ => v)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro y hy
    exact (hasDerivAt_id' y).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv (fun v => ∑' k, chapter9Entry23CKTerm v k))
      (deriv (fun v : ℝ => v))
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro y hy
    rw [(hasDerivAt_CK_tsum hy).deriv, (hasDerivAt_id' y).deriv]
    exact tsum_ckTerm'_eq_one hy
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hfg0 : (∑' k, chapter9Entry23CKTerm (0 : ℝ) k) = (0 : ℝ) := by
    have e : (fun k : ℕ => chapter9Entry23CKTerm (0 : ℝ) k) = 0 := by
      funext k
      exact ckTerm_zero k
    rw [e]
    exact tsum_zero
  have heq := hs.eqOn_of_deriv_eq hs' hf hg hderiv h0mem hfg0
  exact heq hu

private lemma cos_mul_K_eq {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Real.cos u * (∑' k, chapter9Entry23KTerm u k) = u := by
  have hsin1 : |Real.sin u| < 1 := abs_sin_lt_one_of_mem_Ioo hu
  have hK : Summable (chapter9Entry23KTerm u) := summable_kTerm_at hsin1
  have e : (chapter9Entry23CKTerm u)
      = (fun k => Real.cos u * chapter9Entry23KTerm u k) := rfl
  have hmul : (∑' k, chapter9Entry23CKTerm u k)
      = Real.cos u * (∑' k, chapter9Entry23KTerm u k) := by
    rw [e]
    exact Summable.tsum_mul_left _ hK
  have hck := ck_tsum_eq_id hu
  rw [hmul] at hck
  exact hck

private lemma tsum_nTerm'_eq {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    ∑' k, chapter9Entry23NTerm' u k = u := by
  have hsin1 : |Real.sin u| < 1 := abs_sin_lt_one_of_mem_Ioo hu
  have hK : Summable (chapter9Entry23KTerm u) := summable_kTerm_at hsin1
  have e : ∀ k : ℕ, chapter9Entry23NTerm' u k
      = Real.cos u * chapter9Entry23KTerm u k := by
    intro k
    unfold chapter9Entry23NTerm' chapter9Entry23KTerm
    ring
  have hcongr : (∑' k, chapter9Entry23NTerm' u k)
      = ∑' k, Real.cos u * chapter9Entry23KTerm u k :=
    tsum_congr e
  rw [hcongr, Summable.tsum_mul_left _ hK]
  exact cos_mul_K_eq hu

private lemma N_eq_sq {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (∑' k, chapter9Entry23NTerm u k) = u ^ 2 / 2 := by
  have hs : IsOpen (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := isOpen_Ioo
  have hs' : IsPreconnected (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :=
    isPreconnected_Ioo
  have hf : DifferentiableOn ℝ (fun v => ∑' k, chapter9Entry23NTerm v k)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro y hy
    exact (hasDerivAt_N_tsum hy).differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ (fun v : ℝ => v ^ 2 / 2)
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro y hy
    exact (hasDerivAt_sq_div_two y).differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv (fun v => ∑' k, chapter9Entry23NTerm v k))
      (deriv (fun v : ℝ => v ^ 2 / 2))
      (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
    intro y hy
    rw [(hasDerivAt_N_tsum hy).deriv, (hasDerivAt_sq_div_two y).deriv]
    exact tsum_nTerm'_eq hy
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hfg0 : (∑' k, chapter9Entry23NTerm (0 : ℝ) k) = (0 : ℝ) ^ 2 / 2 := by
    have h1 : (∑' k, chapter9Entry23NTerm (0 : ℝ) k) = 0 := by
      have e : (fun k : ℕ => chapter9Entry23NTerm (0 : ℝ) k) = 0 := by
        funext k
        exact nTerm_zero k
      rw [e]
      exact tsum_zero
    rw [h1]
    norm_num
  have heq := hs.eqOn_of_deriv_eq hs' hf hg hderiv h0mem hfg0
  exact heq hu

private lemma summable_nTerm_at {u : ℝ} (hu : |Real.sin u| < 1) :
    Summable (chapter9Entry23NTerm u) := by
  have hq2 : |Real.sin u| ^ 2 < 1 := by
    nlinarith [hu, abs_nonneg (Real.sin u), sq_nonneg (|Real.sin u|)]
  have hq2_nn : 0 ≤ |Real.sin u| ^ 2 := by positivity
  have hnorm : ‖(|Real.sin u| ^ 2 : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq2_nn]
    exact hq2
  have hbase := summable_geometric_of_norm_lt_one hnorm
  have hmul := hbase.mul_left (|Real.sin u| ^ 2)
  have hbound : ∀ k : ℕ, ‖chapter9Entry23NTerm u k‖
      ≤ |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by
    intro k
    have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
    have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
    have hD1 : (1 : ℝ) ≤ ((((2 * k + 2 : ℕ))) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ 2 * k + 2)
    have hpow : |Real.sin u| ^ (2 * k + 2)
        = |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by
      rw [show 2 * k + 2 = 2 + 2 * k by omega, pow_add, ← pow_mul]
    have hN_le : ‖chapter9Entry23NTerm u k‖
        ≤ chapter9Entry23Coeff k * |Real.sin u| ^ (2 * k + 2) := by
      unfold chapter9Entry23NTerm
      rw [Real.norm_eq_abs, abs_div]
      have hD_nn : 0 ≤ ((((2 * k + 2 : ℕ))) : ℝ) := Nat.cast_nonneg _
      have habs : |((((2 * k + 2 : ℕ))) : ℝ)| = ((((2 * k + 2 : ℕ))) : ℝ) :=
        abs_of_nonneg hD_nn
      rw [habs, abs_mul, abs_pow]
      have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
        abs_of_nonneg hc_nn
      rw [h1]
      have hnn : 0 ≤ chapter9Entry23Coeff k * |Real.sin u| ^ (2 * k + 2) := by
        positivity
      exact div_le_self hnn hD1
    calc ‖chapter9Entry23NTerm u k‖
        ≤ chapter9Entry23Coeff k * |Real.sin u| ^ (2 * k + 2) := hN_le
      _ ≤ 1 * (|Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k) := by
          have hpow_nn : 0 ≤ |Real.sin u| ^ (2 * k + 2) := by positivity
          have hpow' : |Real.sin u| ^ (2 * k + 2)
              ≤ |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by rw [hpow]
          exact mul_le_mul hc_le hpow' hpow_nn (by linarith [hc_nn])
      _ = |Real.sin u| ^ 2 * (|Real.sin u| ^ 2) ^ k := by ring
  exact Summable.of_norm_bounded hmul hbound

private lemma summable_sTerm'_at {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Summable (chapter9Entry23STerm' u) := by
  have hpi : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  obtain ⟨r, hr_mem, hr1, hr0, hu_mem⟩ := exists_r_of_mem_Ioo hpi hu
  exact Summable.of_norm_bounded (summable_sin_bound hr0 hr1)
    (fun k => norm_sTerm'_le hr0 hr1 hu_mem k)

private lemma sin_mul_sTerm'_eq {u : ℝ}
    (hu : u ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Real.sin u * (∑' k, chapter9Entry23STerm' u k)
      = Real.cos u * (u ^ 2 / 2) := by
  have hsin1 : |Real.sin u| < 1 := abs_sin_lt_one_of_mem_Ioo hu
  have hS : Summable (chapter9Entry23STerm' u) := summable_sTerm'_at hu
  have hN : Summable (chapter9Entry23NTerm u) := summable_nTerm_at hsin1
  have e : ∀ k : ℕ, Real.sin u * chapter9Entry23STerm' u k
      = Real.cos u * chapter9Entry23NTerm u k := by
    intro k
    have hD : ((((2 * k + 2 : ℕ))) : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (by omega : 2 * k + 2 ≠ 0)
    unfold chapter9Entry23STerm' chapter9Entry23NTerm
    field_simp
    ring
  have hcongr : (∑' k, Real.sin u * chapter9Entry23STerm' u k)
      = ∑' k, Real.cos u * chapter9Entry23NTerm u k :=
    tsum_congr e
  have hL := Summable.tsum_mul_left (Real.sin u) hS
  have hR := Summable.tsum_mul_left (Real.cos u) hN
  rw [hL, hR, N_eq_sq hu] at hcongr
  exact hcongr

private lemma continuous_factTerm (k : ℕ) :
    Continuous (fun u => chapter9Entry23FactorialTerm u k) := by
  unfold chapter9Entry23FactorialTerm
  fun_prop

private lemma norm_factTerm_le_one_div (u : ℝ) (k : ℕ) :
    ‖chapter9Entry23FactorialTerm u k‖ ≤ 1 / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) := by
  have hc_le : chapter9Entry23Coeff k ≤ 1 := coeff_le_one k
  have hc_nn : 0 ≤ chapter9Entry23Coeff k := coeff_nonneg k
  have hsin_le : |Real.sin u| ^ (2 * k + 2) ≤ 1 := by
    have h1 : |Real.sin u| ≤ 1 := Real.abs_sin_le_one u
    exact pow_le_one₀ (abs_nonneg _) h1
  have hden_le : ((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)
      ≤ ((((2 * k + 2 : ℕ))) : ℝ) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) _ 2
    exact_mod_cast (by omega : k + 1 ≤ 2 * k + 2)
  have hden_pos : (0 : ℝ) < ((((2 * k + 2 : ℕ))) : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * k + 2)) 2
  have hden1_pos : (0 : ℝ) < (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < k + 1)) 2
  have hnum : chapter9Entry23Coeff k * |Real.sin u| ^ (2 * k + 2) ≤ 1 := by
    have hpow_nn : 0 ≤ |Real.sin u| ^ (2 * k + 2) := by positivity
    calc chapter9Entry23Coeff k * |Real.sin u| ^ (2 * k + 2)
        ≤ 1 * 1 := mul_le_mul hc_le hsin_le hpow_nn zero_le_one
      _ = 1 := mul_one 1
  rw [factorialTerm_eq_coeff]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
  have h1 : |chapter9Entry23Coeff k| = chapter9Entry23Coeff k :=
    abs_of_nonneg hc_nn
  have h2 : |((((2 * k + 2 : ℕ))) : ℝ) ^ 2|
      = ((((2 * k + 2 : ℕ))) : ℝ) ^ 2 :=
    abs_of_nonneg (le_of_lt hden_pos)
  rw [h1, h2]
  calc chapter9Entry23Coeff k * |Real.sin u| ^ (2 * k + 2)
        / ((((2 * k + 2 : ℕ))) : ℝ) ^ 2
      ≤ 1 / ((((2 * k + 2 : ℕ))) : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hnum (le_of_lt hden_pos)
    _ ≤ 1 / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)) :=
        one_div_le_one_div_of_le hden1_pos hden_le

private lemma summable_one_div_sq_shift :
    Summable (fun k : ℕ => (1 : ℝ) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ (2 : ℕ))) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  have e : (fun k : ℕ => (1 : ℝ) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ)))
      = (fun k : ℕ => (1 : ℝ) / (((((k + 1 : ℕ))) : ℝ) ^ (2 : ℕ))) := rfl
  exact hshift

private lemma continuousOn_S (s : Set ℝ) :
    ContinuousOn (fun u => ∑' k, chapter9Entry23FactorialTerm u k) s := by
  apply continuousOn_tsum (fun k => (continuous_factTerm k).continuousOn)
    summable_one_div_sq_shift
  intro k u _
  exact norm_factTerm_le_one_div u k

private lemma norm_leftTerm_le_uniform {x : ℝ} (h : |Real.tan x| ≤ 1) (j : ℕ) :
    ‖chapter9Entry23LeftTerm x j‖
      ≤ (3 / 4 : ℝ) * (1 / (((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)))) := by
  have hH := oddHarmonic_le_one_add_log (j + 1)
  have hmj : (1 : ℝ) ≤ ((((j + 1 : ℕ))) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one]
    have h0 := Nat.cast_nonneg (α := ℝ) j
    linarith
  have hm0 : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) :=
    Nat.cast_pos.mpr (by omega : 0 < j + 1)
  have hlog := one_add_log_le_three_rpow _ hmj
  have hM : ((((2 * (j + 1) : ℕ))) : ℝ) = 2 * ((((j + 1 : ℕ))) : ℝ) := by
    rw [show (2 * (j + 1)) = (j + 1) + (j + 1) from by omega, Nat.cast_add]
    ring
  have htan_pow : |Real.tan x| ^ (2 * (j + 1)) ≤ 1 := by
    exact pow_le_one₀ (abs_nonneg _) h
  have habs : |Real.tan x ^ (2 * (j + 1))| ≤ 1 := by
    rw [abs_pow]
    exact htan_pow
  have hHnn := oddHarmonic_nonneg (j + 1)
  have hden : (0 : ℝ) < ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (by omega : 0 < 2 * (j + 1))) 2
  have hneg1 : (|(-1 : ℝ) ^ j| : ℝ) = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  have hrpow_pos : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) :=
    Real.rpow_pos_of_pos hm0 _
  have key : (3 / 4 : ℝ) * (1 / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)))
      * (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2
      = 3 * ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ)) := by
    have eA : ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) ≠ 0 := ne_of_gt hrpow_pos
    have ehalf := rpow_half_mul_three_half _ hm0
    have e2 : ((3 / 4 : ℝ) * (1 / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)))
          * (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2)
        = ((3 * ((((j + 1 : ℕ))) : ℝ) ^ (2 : ℕ))
          / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))) := by ring
    rw [e2, div_eq_iff eA,
      show (3 : ℝ) * ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ))
          * ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))
        = 3 * (((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ))
          * ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))) by ring, ehalf]
  have hH3 : chapter9OddHarmonic (j + 1)
      ≤ 3 * ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ)) := by linarith
  have h3nn : (0 : ℝ) ≤ 3 * ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ)) := by
    have hrw : (0 : ℝ) ≤ ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ)) :=
      Real.rpow_nonneg (Nat.cast_nonneg _) _
    linarith
  have hle : chapter9OddHarmonic (j + 1) * |Real.tan x ^ (2 * (j + 1))|
      ≤ 3 * ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ)) * 1 := by
    have hpow_nn : 0 ≤ |Real.tan x ^ (2 * (j + 1))| := abs_nonneg _
    exact mul_le_mul hH3 habs hpow_nn h3nn
  rw [Real.norm_eq_abs]
  simp only [chapter9Entry23LeftTerm]
  rw [abs_div, abs_mul, abs_mul, hneg1, one_mul, abs_of_nonneg hHnn,
    abs_of_pos hden, div_le_iff₀ hden, hM, key]
  linarith [hle]

private lemma summable_left_bound :
    Summable (fun k : ℕ => (3 / 4 : ℝ)
      * (1 / (((((k + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))))) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ ((3 / 2 : ℝ)))) :=
    (Real.summable_one_div_nat_rpow).mpr (by norm_num)
  have hshift := (summable_nat_add_iff 1).mpr hbase
  exact Summable.mul_left _ hshift

private lemma continuousOn_leftTerm (j : ℕ) :
    ContinuousOn (fun x => chapter9Entry23LeftTerm x j)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 4)
      ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x hx
    have h := Set.mem_Icc.mp hx
    constructor <;> linarith [Real.pi_pos]
  have htan : ContinuousOn Real.tan (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuousOn_tan_Ioo.mono hsub
  have e : (fun x => chapter9Entry23LeftTerm x j)
      = (fun x => ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1))
        * Real.tan x ^ (2 * (j + 1)) / ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2) := by
    funext x
    simp only [chapter9Entry23LeftTerm]
  rw [e]
  exact ((htan.pow (2 * (j + 1))).const_mul _).div_const _

private lemma continuousOn_L :
    ContinuousOn (fun x => ∑' j, chapter9Entry23LeftTerm x j)
      (Set.Icc 0 (Real.pi / 4)) := by
  apply continuousOn_tsum continuousOn_leftTerm summable_left_bound
  intro j x hx
  have habs : |x| ≤ Real.pi / 4 := by
    have h := Set.mem_Icc.mp hx
    rw [abs_of_nonneg h.1]
    exact h.2
  have htan := abs_tan_le_one_of_mem x habs
  have h := norm_leftTerm_le_uniform htan j
  simpa [Real.norm_eq_abs] using h

private lemma continuousOn_R :
    ContinuousOn
      (fun x => 2 * (∑' k, chapter9Entry23FactorialTerm x k)
        - (∑' k, chapter9Entry23FactorialTerm (2 * x) k) / 4)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hS1 : ContinuousOn (fun x => ∑' k, chapter9Entry23FactorialTerm x k)
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_S _
  have hS2 : ContinuousOn (fun u => ∑' k, chapter9Entry23FactorialTerm u k)
      (Set.Icc 0 (Real.pi / 2)) :=
    continuousOn_S _
  have hmaps : Set.MapsTo (fun x : ℝ => 2 * x)
      (Set.Icc 0 (Real.pi / 4)) (Set.Icc 0 (Real.pi / 2)) := by
    intro x hx
    have h := Set.mem_Icc.mp hx
    constructor <;> linarith [Real.pi_pos]
  have h2cont : ContinuousOn (fun x : ℝ => 2 * x) (Set.Icc 0 (Real.pi / 4)) :=
    (continuous_id.const_mul 2).continuousOn
  have hcomp : ContinuousOn
      (fun x => ∑' k, chapter9Entry23FactorialTerm (2 * x) k)
      (Set.Icc 0 (Real.pi / 4)) := by
    have h := hS2.comp h2cont hmaps
    simpa [Function.comp_def] using h
  exact (hS1.const_mul 2).sub (hcomp.div_const 4)

private lemma leftTerm_neg (x : ℝ) (j : ℕ) :
    chapter9Entry23LeftTerm (-x) j = chapter9Entry23LeftTerm x j := by
  have heven : Even (2 * (j + 1)) := ⟨j + 1, by ring⟩
  have htan : Real.tan (-x) = -Real.tan x := Real.tan_neg x
  simp only [chapter9Entry23LeftTerm, htan, Even.neg_pow heven]

private lemma factTerm_neg (u : ℝ) (k : ℕ) :
    chapter9Entry23FactorialTerm (-u) k
      = chapter9Entry23FactorialTerm u k := by
  have heven : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  have hsin : Real.sin (-u) = -Real.sin u := Real.sin_neg u
  simp only [chapter9Entry23FactorialTerm, hsin, Even.neg_pow heven]

private lemma tsum_left_neg (x : ℝ) :
    (∑' j, chapter9Entry23LeftTerm (-x) j)
      = ∑' j, chapter9Entry23LeftTerm x j :=
  tsum_congr (leftTerm_neg x)

private lemma tsum_fact_neg (u : ℝ) :
    (∑' k, chapter9Entry23FactorialTerm (-u) k)
      = ∑' k, chapter9Entry23FactorialTerm u k :=
  tsum_congr (factTerm_neg u)

private lemma L_zero : (∑' j, chapter9Entry23LeftTerm (0 : ℝ) j) = 0 := by
  have e : (fun j : ℕ => chapter9Entry23LeftTerm (0 : ℝ) j) = 0 := by
    funext j
    exact leftTerm_zero j
  rw [e]
  exact tsum_zero

private lemma S_zero : (∑' k, chapter9Entry23FactorialTerm (0 : ℝ) k) = 0 := by
  have e : (fun k : ℕ => chapter9Entry23FactorialTerm (0 : ℝ) k) = 0 := by
    funext k
    exact factTerm_zero k
  rw [e]
  exact tsum_zero

private lemma R_zero :
    (2 * (∑' k, chapter9Entry23FactorialTerm (0 : ℝ) k)
      - (∑' k, chapter9Entry23FactorialTerm (2 * (0 : ℝ)) k) / 4) = 0 := by
  rw [S_zero]
  have h2 : (2 : ℝ) * (0 : ℝ) = 0 := by ring
  rw [h2, S_zero]
  ring

private lemma tsum_lTerm'_zero : (∑' j, chapter9Entry23LTerm' (0 : ℝ) j) = 0 := by
  have e : (fun j : ℕ => chapter9Entry23LTerm' (0 : ℝ) j) = 0 := by
    funext j
    exact lTerm'_zero j
  rw [e]
  exact tsum_zero

private lemma tsum_sTerm'_zero :
    (∑' k, chapter9Entry23STerm' (0 : ℝ) k) = 0 := by
  have e : (fun k : ℕ => chapter9Entry23STerm' (0 : ℝ) k) = 0 := by
    funext k
    exact sTerm'_zero k
  rw [e]
  exact tsum_zero

private lemma hasDerivAt_R {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    HasDerivAt (fun y => 2 * (∑' k, chapter9Entry23FactorialTerm y k)
        - (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4)
      (2 * (∑' k, chapter9Entry23STerm' x k)
        - ((∑' k, chapter9Entry23STerm' (2 * x) k) * 2) / 4) x := by
  have hx1 : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith [Real.pi_pos]
  have hx2 : (2 * x) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith [Real.pi_pos]
  have hS1 := hasDerivAt_S_tsum hx1
  have hS2 := hasDerivAt_S_tsum hx2
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    have h := HasDerivAt.const_mul 2 (hasDerivAt_id' x)
    simpa using h
  have hcomp : HasDerivAt (fun y => ∑' k, chapter9Entry23FactorialTerm (2 * y) k)
      ((∑' k, chapter9Entry23STerm' (2 * x) k) * 2) x := by
    have h := hS2.comp x h2x
    simpa [Function.comp_def] using h
  have h2S : HasDerivAt (fun y => 2 * (∑' k, chapter9Entry23FactorialTerm y k))
      (2 * (∑' k, chapter9Entry23STerm' x k)) x :=
    HasDerivAt.const_mul 2 hS1
  have hdiv : HasDerivAt
      (fun y => (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4)
      (((∑' k, chapter9Entry23STerm' (2 * x) k) * 2) / 4) x :=
    hcomp.div_const 4
  have hsub := h2S.sub hdiv
  have e : (fun y => 2 * (∑' k, chapter9Entry23FactorialTerm y k)
        - (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4)
      = (fun y => 2 * (∑' k, chapter9Entry23FactorialTerm y k)
        - (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4) := rfl
  exact hsub

private lemma sin_two_mul_RTerm' {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) :
    Real.sin (2 * x)
        * (2 * (∑' k, chapter9Entry23STerm' x k)
          - ((∑' k, chapter9Entry23STerm' (2 * x) k) * 2) / 4)
      = x ^ 2 := by
  have hx1 : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith [Real.pi_pos]
  have hx2 : (2 * x) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have h := Set.mem_Ioo.mp hx
    constructor <;> linarith [Real.pi_pos]
  have h1 := sin_mul_sTerm'_eq hx1
  have h2 := sin_mul_sTerm'_eq hx2
  have hsin2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    rw [Real.sin_two_mul]
  have hcos2 : Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 := Real.cos_two_mul x
  have h2sq : (2 * x) ^ 2 / 2 = 2 * x ^ 2 := by ring
  rw [h2sq] at h2
  linear_combination 4 * Real.cos x * h1
    + 2 * (∑' k, chapter9Entry23STerm' x k) * hsin2
    - (1 / 2) * h2 - x ^ 2 * hcos2

private lemma deriv_eq_of_mem_Ico {x : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) (Real.pi / 4)) :
    2 * (∑' k, chapter9Entry23STerm' x k)
        - ((∑' k, chapter9Entry23STerm' (2 * x) k) * 2) / 4
      = ∑' j, chapter9Entry23LTerm' x j := by
  have hx_mem : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4) := by
    have h := Set.mem_Ico.mp hx
    constructor <;> linarith [Real.pi_pos]
  by_cases hx0 : x = 0
  · subst hx0
    rw [tsum_lTerm'_zero]
    have h1 : (∑' k, chapter9Entry23STerm' (0 : ℝ) k) = 0 := tsum_sTerm'_zero
    have h2 : (2 : ℝ) * (0 : ℝ) = 0 := by ring
    have h3 : (∑' k, chapter9Entry23STerm' (2 * (0 : ℝ)) k) = 0 := by
      rw [h2]
      exact tsum_sTerm'_zero
    rw [h1, h3]
    ring
  · have hx_pos : 0 < x := lt_of_le_of_ne (Set.mem_Ico.mp hx).1 (Ne.symm hx0)
    have h2mem : (2 * x) ∈ Set.Ioo (0 : ℝ) Real.pi := by
      have h := Set.mem_Ico.mp hx
      constructor <;> linarith [Real.pi_pos]
    have hsin_pos : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_mem_Ioo h2mem
    have hsin_ne : Real.sin (2 * x) ≠ 0 := ne_of_gt hsin_pos
    have hL := sin_two_mul_LTerm' hx_mem
    have hR := sin_two_mul_RTerm' hx_mem
    have heq : Real.sin (2 * x) * (∑' j, chapter9Entry23LTerm' x j)
        = Real.sin (2 * x)
          * (2 * (∑' k, chapter9Entry23STerm' x k)
            - ((∑' k, chapter9Entry23STerm' (2 * x) k) * 2) / 4) := by
      rw [hL, hR]
    exact mul_left_cancel₀ hsin_ne heq.symm

private lemma L_eq_R_of_mem_Icc {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) (Real.pi / 4)) :
    (∑' j, chapter9Entry23LeftTerm y j)
      = 2 * (∑' k, chapter9Entry23FactorialTerm y k)
        - (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4 := by
  have derivf : ∀ x ∈ Set.Ico (0 : ℝ) (Real.pi / 4),
      HasDerivWithinAt (fun y => ∑' j, chapter9Entry23LeftTerm y j)
        ((∑' j, chapter9Entry23LTerm' x j)) (Set.Ici x) x := by
    intro x hx
    have hx_mem : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4) := by
      have h := Set.mem_Ico.mp hx
      constructor <;> linarith [Real.pi_pos]
    exact (hasDerivAt_L_tsum hx_mem).hasDerivWithinAt
  have derivg : ∀ x ∈ Set.Ico (0 : ℝ) (Real.pi / 4),
      HasDerivWithinAt
        (fun y => 2 * (∑' k, chapter9Entry23FactorialTerm y k)
          - (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4)
        ((∑' j, chapter9Entry23LTerm' x j)) (Set.Ici x) x := by
    intro x hx
    have hx_mem : x ∈ Set.Ioo (-(Real.pi / 4)) (Real.pi / 4) := by
      have h := Set.mem_Ico.mp hx
      constructor <;> linarith [Real.pi_pos]
    have hR := hasDerivAt_R hx_mem
    have heq := deriv_eq_of_mem_Ico hx
    have hR' : HasDerivAt
        (fun y => 2 * (∑' k, chapter9Entry23FactorialTerm y k)
          - (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4)
        ((∑' j, chapter9Entry23LTerm' x j)) x := by
      rw [← heq]
      exact hR
    exact hR'.hasDerivWithinAt
  have hi : (∑' j, chapter9Entry23LeftTerm (0 : ℝ) j)
      = 2 * (∑' k, chapter9Entry23FactorialTerm (0 : ℝ) k)
        - (∑' k, chapter9Entry23FactorialTerm (2 * (0 : ℝ)) k) / 4 := by
    rw [L_zero, R_zero]
  have heq := eq_of_has_deriv_right_eq derivf derivg continuousOn_L
    continuousOn_R hi
  exact heq y hy

/-- **Entry 23 of Chapter 9 of Ramanujan's notebooks.** For real $u$ and $k \ge 0$ let
$T_k(u) = \frac{2^{2k} (k!)^2 \sin^{2k+2} u}{(2k+1)! \, (2k+2)^2}$, and for $k \ge 1$ let
$O_k = 1 + \frac{1}{3} + \dots + \frac{1}{2k-1}$. Let $x$ be real with $|x| \le \pi/4$. Then the
series $\sum_{k \ge 1} \frac{(-1)^{k-1} O_k \tan^{2k} x}{(2k)^2}$, $\sum_{k \ge 0} T_k(x)$ and
$\sum_{k \ge 0} T_k(2x)$ converge absolutely, and

$$
\sum_{k \ge 1} \frac{(-1)^{k-1} O_k \tan^{2k} x}{(2k)^2} =
2 \sum_{k \ge 0} T_k(x) - \frac{1}{4} \sum_{k \ge 0} T_k(2x).
$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9,
Entry 23, p. 271.
-/
theorem ramanujan_part1_ch9_entry23_ramanujanpi2 (x : ℝ)
    (hx : |x| ≤ Real.pi / 4) :
    Summable (chapter9Entry23LeftTerm x) ∧
      Summable (chapter9Entry23FactorialTerm x) ∧
      Summable (chapter9Entry23FactorialTerm (2 * x)) ∧
      (∑' j : ℕ, chapter9Entry23LeftTerm x j) =
        2 * ∑' k : ℕ, chapter9Entry23FactorialTerm x k -
          (1 / 4 : ℝ) *
            ∑' k : ℕ, chapter9Entry23FactorialTerm (2 * x) k := by
  have htan := abs_tan_le_one_of_mem x hx
  have hsinx : |Real.sin x| ≤ 1 :=
    le_trans (abs_sin_le_sqrt2d2_of_mem x hx) (le_of_lt sqrt2d2_lt_one)
  have hsin2x : |Real.sin (2 * x)| ≤ 1 := Real.abs_sin_le_one _
  refine ⟨summable_leftTerm x htan, summable_factTerm x hsinx,
    summable_factTerm (2 * x) hsin2x, ?_⟩
  have hform : ∀ y : ℝ, 2 * (∑' k, chapter9Entry23FactorialTerm y k)
        - (∑' k, chapter9Entry23FactorialTerm (2 * y) k) / 4
      = 2 * (∑' k, chapter9Entry23FactorialTerm y k)
        - (1 / 4 : ℝ) * (∑' k, chapter9Entry23FactorialTerm (2 * y) k) := by
    intro y
    ring
  by_cases hx0 : 0 ≤ x
  · have hx_mem : x ∈ Set.Icc (0 : ℝ) (Real.pi / 4) := by
      have habs : |x| = x := abs_of_nonneg hx0
      have h1 : x ≤ Real.pi / 4 := habs ▸ hx
      exact ⟨hx0, h1⟩
    have h := L_eq_R_of_mem_Icc hx_mem
    rw [hform] at h
    exact h
  · have hx_neg : x < 0 := lt_of_not_ge hx0
    have hnx_mem : (-x) ∈ Set.Icc (0 : ℝ) (Real.pi / 4) := by
      have habs : |x| = -x := abs_of_neg hx_neg
      have h1 : -x ≤ Real.pi / 4 := habs ▸ hx
      constructor <;> linarith
    have h := L_eq_R_of_mem_Icc hnx_mem
    rw [hform] at h
    have hL : (∑' j, chapter9Entry23LeftTerm x j)
        = ∑' j, chapter9Entry23LeftTerm (-x) j :=
      (tsum_left_neg x).symm
    have hS1 : (∑' k, chapter9Entry23FactorialTerm (-x) k)
        = ∑' k, chapter9Entry23FactorialTerm x k :=
      tsum_fact_neg x
    have hS2 : (∑' k, chapter9Entry23FactorialTerm (2 * (-x)) k)
        = ∑' k, chapter9Entry23FactorialTerm (2 * x) k := by
      have e21 : (2 : ℝ) * (-x) = -(2 * x) := by ring
      rw [e21]
      exact tsum_fact_neg (2 * x)
    calc (∑' j, chapter9Entry23LeftTerm x j)
        = ∑' j, chapter9Entry23LeftTerm (-x) j := hL
      _ = 2 * (∑' k, chapter9Entry23FactorialTerm (-x) k)
          - (1 / 4 : ℝ) * (∑' k, chapter9Entry23FactorialTerm (2 * (-x)) k) := h
      _ = 2 * (∑' k, chapter9Entry23FactorialTerm x k)
          - (1 / 4 : ℝ) * (∑' k, chapter9Entry23FactorialTerm (2 * x) k) := by
          rw [hS1, hS2]

end
end Entry23Ramanujanpi2
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
