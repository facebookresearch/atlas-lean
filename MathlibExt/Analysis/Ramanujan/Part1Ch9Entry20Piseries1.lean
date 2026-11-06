/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
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

namespace Entry20Piseries1

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9CosineFourierThreeTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  Real.cos (2 * (k : ℝ) * x) / ((k : ℝ) ^ 3)

def chapter9Entry20LogTerm (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 / 2 * Real.log |2 * Real.sin x|

def chapter9Entry23FactorialTerm (u : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
    (((2 * k + 1).factorial : ℝ) * (((2 * k + 2 : ℕ) : ℝ) ^ 2))

def chapter9SineFourierTwoTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  Real.sin (2 * (k : ℝ) * x) / ((k : ℝ) ^ 2)

def chapter9ZetaThreeTerm (j : ℕ) : ℝ :=
  let k := j + 1
  1 / ((k : ℝ) ^ 3)

def chapter9ZetaThree : ℝ :=
  ∑' j : ℕ, chapter9ZetaThreeTerm j

private theorem aux_zetaThree_summable : Summable chapter9ZetaThreeTerm := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have h2 : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) :=
    (summable_nat_add_iff 1).mpr h
  unfold chapter9ZetaThreeTerm
  exact h2

private theorem aux_sineTwo_summable (x : ℝ) : Summable (chapter9SineFourierTwoTerm x) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have h2 : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff 1).mpr h
  apply Summable.of_norm_bounded h2
  intro j
  change ‖chapter9SineFourierTwoTerm x j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)
  change ‖Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div]
  have hsin : |Real.sin (2 * (((j + 1 : ℕ)) : ℝ) * x)| ≤ 1 := Real.abs_sin_le_one _
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (Nat.succ_pos j)
  rw [abs_of_pos hpos]
  gcongr

private theorem aux_cosineThree_summable (x : ℝ) :
    Summable (chapter9CosineFourierThreeTerm x) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  have h2 : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) :=
    (summable_nat_add_iff 1).mpr h
  apply Summable.of_norm_bounded h2
  intro j
  change ‖chapter9CosineFourierThreeTerm x j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)
  change ‖Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 3)‖ ≤ _
  rw [Real.norm_eq_abs, abs_div]
  have hcos : |Real.cos (2 * (((j + 1 : ℕ)) : ℝ) * x)| ≤ 1 := Real.abs_cos_le_one _
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 3) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (Nat.succ_pos j)
  rw [abs_of_pos hpos]
  gcongr

private theorem aux_coeff_le_one (k : ℕ) :
    (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)) ≤ 1 := by
  have hnat : 4 ^ k * (k.factorial ^ 2) ≤ (2 * k + 1).factorial := by
    have h4 : 4 ^ k ≤ (2 * k + 1) * k.centralBinom :=
      Nat.four_pow_le_two_mul_add_one_mul_centralBinom k
    rw [Nat.centralBinom_eq_two_mul_choose] at h4
    have hchoose : (2 * k).choose k * k.factorial * (k.factorial) = (2 * k).factorial := by
      have hle : k ≤ 2 * k := Nat.le_mul_of_pos_left k (by norm_num)
      have h := Nat.choose_mul_factorial_mul_factorial hle
      have hsub : 2 * k - k = k := by omega
      rwa [hsub] at h
    have hfact : (2 * k + 1).factorial = (2 * k + 1) * (2 * k).factorial := by
      have : 2 * k + 1 = (2 * k) + 1 := by omega
      rw [this, Nat.factorial_succ]
    have hmul : 4 ^ k * (k.factorial ^ 2)
        ≤ ((2 * k + 1) * (2 * k).choose k) * (k.factorial ^ 2) :=
      Nat.mul_le_mul_right _ h4
    rw [hfact]
    rw [← hchoose]
    have hrw : ((2 * k + 1) * (2 * k).choose k) * k.factorial ^ 2
        = (2 * k + 1) * ((2 * k).choose k * k.factorial * k.factorial) := by ring
    rwa [hrw] at hmul
  have h24 : (2 : ℝ) ^ (2 * k) = (4 : ℝ) ^ k := by
    have h : ((2 : ℝ) ^ 2) ^ k = (2 : ℝ) ^ (2 * k) := by rw [pow_mul]
    rw [← h]
    norm_num
  have hcast : (4 : ℝ) ^ k * ((k.factorial : ℝ) ^ 2) ≤ (((2 * k + 1).factorial : ℝ)) := by
    have hcast0 : (((4 ^ k * (k.factorial ^ 2) : ℕ)) : ℝ)
        ≤ ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
      Nat.cast_le.mpr hnat
    push_cast at hcast0
    exact hcast0
  rw [h24]
  have hpos : (0 : ℝ) < (((2 * k + 1).factorial : ℝ)) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  rw [div_le_one hpos]
  exact hcast

private theorem aux_factorial_summable (u : ℝ) : Summable (chapter9Entry23FactorialTerm u) := by
  have hbase : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr h
  apply Summable.of_norm_bounded hbase
  intro k
  have hsin_le : |Real.sin u ^ (2 * k + 2)| ≤ 1 := by
    have h1 : |Real.sin u| ≤ 1 := Real.abs_sin_le_one _
    have h0 : 0 ≤ |Real.sin u| := abs_nonneg _
    calc |Real.sin u ^ (2 * k + 2)| = |Real.sin u| ^ (2 * k + 2) := by rw [abs_pow]
      _ ≤ 1 := pow_le_one₀ h0 h1
  have hden_pos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (by omega)
  have hfact_pos : (0 : ℝ) < ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
    Nat.cast_pos.mpr (Nat.factorial_pos _)
  change ‖chapter9Entry23FactorialTerm u k‖ ≤ (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)
  unfold chapter9Entry23FactorialTerm
  rw [Real.norm_eq_abs]
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by positivity
  have hkpos : (0 : ℝ) ≤ ((k.factorial : ℝ) ^ 2) := by positivity
  have hnum_abs : |(2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin u ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * (((2 * k + 2 : ℕ)) : ℝ) ^ 2)|
      = ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)))
        * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
    rw [abs_div, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg h2pos, abs_of_nonneg hkpos,
      abs_of_pos hfact_pos, abs_of_nonneg (le_of_lt hden_pos)]
    ring
  rw [hnum_abs]
  have hstep1 : |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2
      ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by
    gcongr
  have hnn_sin_div : (0 : ℝ) ≤ |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 :=
    div_nonneg (abs_nonneg _) (le_of_lt hden_pos)
  have hcoeff := aux_coeff_le_one k
  have hmid : ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)))
        * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
      ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
    exact mul_le_mul_of_nonneg_right hcoeff hnn_sin_div
  have hstep2 : ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ)))
        * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
      ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by
    calc _ ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := hmid
      _ = |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by ring
      _ ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := hstep1
  have hstep3 : (1 : ℝ) / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 ≤ 1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
    apply one_div_le_one_div_of_le
    · positivity
    · have hle : ((((k + 1 : ℕ)) : ℝ)) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
        apply Nat.cast_le.mpr
        omega
      gcongr
  calc _ ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := hstep2
    _ ≤ 1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := hstep3

private theorem aux_factorial_term_zero (k : ℕ) :
    chapter9Entry23FactorialTerm 0 k = 0 := by
  have h : (2 * k + 2 : ℕ) ≠ 0 := by omega
  change (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin 0 ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)) = 0
  rw [Real.sin_zero, zero_pow h, mul_zero, zero_div]

private theorem aux_factorial_tsum_zero :
    (∑' k : ℕ, chapter9Entry23FactorialTerm 0 k) = 0 := by
  simp [aux_factorial_term_zero]

private theorem aux_cosine_term_zero (j : ℕ) :
    chapter9CosineFourierThreeTerm 0 j = chapter9ZetaThreeTerm j := by
  change Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * 0) / ((((j + 1 : ℕ)) : ℝ) ^ 3) =
    1 / ((((j + 1 : ℕ)) : ℝ) ^ 3)
  simp

private theorem aux_cosine_tsum_zero :
    (∑' j : ℕ, chapter9CosineFourierThreeTerm 0 j) = chapter9ZetaThree := by
  unfold chapter9ZetaThree
  have h : ∀ j : ℕ, chapter9CosineFourierThreeTerm 0 j = chapter9ZetaThreeTerm j :=
    aux_cosine_term_zero
  rw [tsum_congr h]

private theorem aux_rhs_zero :
    chapter9Entry20LogTerm 0 +
        (0 : ℝ) / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm 0 j +
        (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm 0 j -
        chapter9ZetaThree / 4 = 0 := by
  have hlog : chapter9Entry20LogTerm 0 = 0 := by
    unfold chapter9Entry20LogTerm
    simp
  rw [hlog, aux_cosine_tsum_zero]
  ring

private theorem aux_factorial_term_even (y : ℝ) (k : ℕ) :
    chapter9Entry23FactorialTerm (-y) k = chapter9Entry23FactorialTerm y k := by
  have he : Even (2 * k + 2) := ⟨k + 1, by ring⟩
  change (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin (-y) ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)) =
    (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin y ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2))
  rw [Real.sin_neg, he.neg_pow (Real.sin y)]

private theorem aux_factorial_tsum_even (y : ℝ) :
    (∑' k : ℕ, chapter9Entry23FactorialTerm (-y) k) =
      (∑' k : ℕ, chapter9Entry23FactorialTerm y k) :=
  tsum_congr (aux_factorial_term_even y)

private theorem aux_sine_term_odd (y : ℝ) (j : ℕ) :
    chapter9SineFourierTwoTerm (-y) j = -chapter9SineFourierTwoTerm y j := by
  have harg : (2 : ℝ) * ((((j + 1 : ℕ)) : ℝ)) * (-y) =
      -(2 * ((((j + 1 : ℕ)) : ℝ)) * y) := by ring
  change Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * (-y)) / ((((j + 1 : ℕ)) : ℝ) ^ 2) =
    -(Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
  rw [harg, Real.sin_neg, neg_div]

private theorem aux_cosine_term_even (y : ℝ) (j : ℕ) :
    chapter9CosineFourierThreeTerm (-y) j = chapter9CosineFourierThreeTerm y j := by
  have harg : (2 : ℝ) * ((((j + 1 : ℕ)) : ℝ)) * (-y) =
      -(2 * ((((j + 1 : ℕ)) : ℝ)) * y) := by ring
  change Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * (-y)) / ((((j + 1 : ℕ)) : ℝ) ^ 3) =
    Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3)
  rw [harg, Real.cos_neg]

private theorem aux_logterm_even (y : ℝ) :
    chapter9Entry20LogTerm (-y) = chapter9Entry20LogTerm y := by
  unfold chapter9Entry20LogTerm
  by_cases hy : y = 0
  · subst hy
    rw [neg_zero]
  · have hny : -y ≠ 0 := neg_ne_zero.mpr hy
    have h1 : (-y) ^ 2 = y ^ 2 := by ring
    have h2 : |2 * Real.sin (-y)| = |2 * Real.sin y| := by
      rw [Real.sin_neg]
      have harg : (2 : ℝ) * (-Real.sin y) = -(2 * Real.sin y) := by ring
      rw [harg, abs_neg]
    simp only [hny, hy, ite_false, h1, h2]

private theorem aux_rhs_even (y : ℝ) :
    chapter9Entry20LogTerm (-y) +
        (-y) / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm (-y) j +
        (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm (-y) j -
        chapter9ZetaThree / 4 =
      chapter9Entry20LogTerm y +
        y / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm y j +
        (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm y j -
        chapter9ZetaThree / 4 := by
  have hA : (∑' j : ℕ, chapter9SineFourierTwoTerm (-y) j) =
      -(∑' j : ℕ, chapter9SineFourierTwoTerm y j) := by
    have hcon : (∑' j : ℕ, chapter9SineFourierTwoTerm (-y) j) =
        (∑' j : ℕ, -(chapter9SineFourierTwoTerm y j)) :=
      tsum_congr (aux_sine_term_odd y)
    rw [hcon, tsum_neg]
  have hB : (∑' j : ℕ, chapter9CosineFourierThreeTerm (-y) j) =
      (∑' j : ℕ, chapter9CosineFourierThreeTerm y j) :=
    tsum_congr (aux_cosine_term_even y)
  rw [aux_logterm_even y, hA, hB]
  ring

private theorem aux_cosine_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => ∑' j : ℕ, chapter9CosineFourierThreeTerm y j)
      (-2 * ∑' j : ℕ, chapter9SineFourierTwoTerm x j) x := by
  have hbase : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
      (Real.summable_one_div_nat_pow).mpr (by norm_num)
    exact (summable_nat_add_iff 1).mpr h
  have hu : Summable (fun j : ℕ => 2 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h2 := hbase.mul_left 2
    simp only [mul_one_div] at h2
    exact h2
  have hterm : ∀ j : ℕ, ∀ y : ℝ,
      HasDerivAt (fun y => chapter9CosineFourierThreeTerm y j)
        (-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
          ((((j + 1 : ℕ)) : ℝ) ^ 3)) y := by
    intro j y
    change HasDerivAt
      (fun y => Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3))
      (-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3)) y
    have hlin : HasDerivAt (fun y : ℝ => 2 * ((((j + 1 : ℕ)) : ℝ)) * y)
        (2 * ((((j + 1 : ℕ)) : ℝ))) y := by
      have h := (hasDerivAt_id y).const_mul (2 * ((((j + 1 : ℕ)) : ℝ)))
      simpa using h
    exact (hlin.cos).div_const _
  have hbound : ∀ j : ℕ, ∀ y : ℝ,
      ‖-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3)‖ ≤ 2 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    intro j y
    have hk : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) :=
      Nat.cast_pos.mpr (Nat.succ_pos j)
    have hk2 : (0 : ℝ) < 2 * ((((j + 1 : ℕ)) : ℝ)) := mul_pos (by norm_num) hk
    have hden : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 3) := pow_pos hk 3
    have hsin : |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| ≤ 1 :=
      Real.abs_sin_le_one _
    have hnum : |-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) *
        (2 * ((((j + 1 : ℕ)) : ℝ)))| ≤ 2 * ((((j + 1 : ℕ)) : ℝ)) := by
      rw [abs_mul, abs_neg, abs_of_pos hk2]
      calc |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| * (2 * ((((j + 1 : ℕ)) : ℝ)))
          ≤ 1 * (2 * ((((j + 1 : ℕ)) : ℝ))) :=
            mul_le_mul_of_nonneg_right hsin (le_of_lt hk2)
        _ = 2 * ((((j + 1 : ℕ)) : ℝ)) := one_mul _
    calc ‖-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
          ((((j + 1 : ℕ)) : ℝ) ^ 3)‖
        = |-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ)))| /
          |((((j + 1 : ℕ)) : ℝ) ^ 3)| := by rw [Real.norm_eq_abs, abs_div]
      _ = |-Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ)))| /
          ((((j + 1 : ℕ)) : ℝ) ^ 3) := by rw [abs_of_pos hden]
      _ ≤ 2 * ((((j + 1 : ℕ)) : ℝ)) / ((((j + 1 : ℕ)) : ℝ) ^ 3) :=
          div_le_div_of_nonneg_right hnum (le_of_lt hden)
      _ = 2 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
          have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hk
          field_simp
  have hmain := hasDerivAt_tsum hu hterm hbound (aux_cosineThree_summable x) x
  have hderiv : (∑' j : ℕ, -Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) *
      (2 * ((((j + 1 : ℕ)) : ℝ))) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) =
      -2 * ∑' j : ℕ, chapter9SineFourierTwoTerm x j := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    change -Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3) =
      -2 * chapter9SineFourierTwoTerm x j
    change -Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) * (2 * ((((j + 1 : ℕ)) : ℝ))) /
        ((((j + 1 : ℕ)) : ℝ) ^ 3) =
      -2 * (Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
    have hk : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) :=
      Nat.cast_pos.mpr (Nat.succ_pos j)
    have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt hk
    field_simp
  rw [hderiv] at hmain
  exact hmain

private theorem aux_one_div_sq_summable :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr h

private theorem aux_one_div_cube_summable :
    Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 3)) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr h

private theorem aux_factorial_continuous :
    Continuous (fun u => ∑' k : ℕ, chapter9Entry23FactorialTerm u k) := by
  refine continuous_tsum ?_ aux_one_div_sq_summable ?_
  · intro k
    change Continuous (fun u => (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
      Real.sin u ^ (2 * k + 2) /
      ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)))
    apply Continuous.div_const
    apply Continuous.mul
    · exact continuous_const
    · exact Real.continuous_sin.pow _
  · intro k u
    have hsin_le : |Real.sin u ^ (2 * k + 2)| ≤ 1 := by
      have h1 : |Real.sin u| ≤ 1 := Real.abs_sin_le_one _
      have h0 : 0 ≤ |Real.sin u| := abs_nonneg _
      calc |Real.sin u ^ (2 * k + 2)| = |Real.sin u| ^ (2 * k + 2) := by rw [abs_pow]
        _ ≤ 1 := pow_le_one₀ h0 h1
    have hden_pos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (by omega)
    have hfact_pos : (0 : ℝ) < ((((2 * k + 1).factorial : ℕ)) : ℝ) :=
      Nat.cast_pos.mpr (Nat.factorial_pos _)
    change ‖chapter9Entry23FactorialTerm u k‖ ≤ (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)
    have hpoint : ‖chapter9Entry23FactorialTerm u k‖ ≤
        1 / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
      change ‖(2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) * Real.sin u ^ (2 * k + 2) /
        ((((2 * k + 1).factorial : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ) ^ 2))‖ ≤ _
      have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by positivity
      have hkpos : (0 : ℝ) ≤ ((k.factorial : ℝ) ^ 2) := by positivity
      have hnum_abs : |(2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) *
          Real.sin u ^ (2 * k + 2) /
          ((((2 * k + 1).factorial : ℝ)) * (((2 * k + 2 : ℕ)) : ℝ) ^ 2)|
          = ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
            (((2 * k + 1).factorial : ℝ))) *
            (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
        rw [abs_div, abs_mul, abs_mul, abs_mul,
          abs_of_nonneg h2pos, abs_of_nonneg hkpos,
          abs_of_pos hfact_pos, abs_of_nonneg (le_of_lt hden_pos)]
        ring
      rw [Real.norm_eq_abs, hnum_abs]
      have hstep1 : |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2
          ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by
        gcongr
      have hnn_sin_div : (0 : ℝ) ≤
          |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 :=
        div_nonneg (abs_nonneg _) (le_of_lt hden_pos)
      have hcoeff := aux_coeff_le_one k
      have hmid : ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
          (((2 * k + 1).factorial : ℝ))) *
            (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
          ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hcoeff hnn_sin_div
      calc ((2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) /
          (((2 * k + 1).factorial : ℝ))) *
            (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2)
          ≤ 1 * (|Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2) := hmid
        _ = |Real.sin u ^ (2 * k + 2)| / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := by ring
        _ ≤ 1 / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 := hstep1
    have hstep3 : (1 : ℝ) / (((2 * k + 2 : ℕ)) : ℝ) ^ 2 ≤
        1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply one_div_le_one_div_of_le
      · positivity
      · have hle : ((((k + 1 : ℕ)) : ℝ)) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
          apply Nat.cast_le.mpr
          omega
        gcongr
    exact le_trans hpoint hstep3

private theorem aux_sine_continuous :
    Continuous (fun y => ∑' j : ℕ, chapter9SineFourierTwoTerm y j) := by
  refine continuous_tsum ?_ aux_one_div_sq_summable ?_
  · intro j
    change Continuous (fun y =>
      Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
    apply Continuous.div_const
    exact Real.continuous_sin.comp (continuous_const.mul continuous_id')
  · intro j y
    change ‖chapter9SineFourierTwoTerm y j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)
    change ‖Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 2)‖ ≤ _
    rw [Real.norm_eq_abs, abs_div]
    have hsin : |Real.sin (2 * (((j + 1 : ℕ)) : ℝ) * y)| ≤ 1 :=
      Real.abs_sin_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (Nat.succ_pos j)
    rw [abs_of_pos hpos]
    gcongr

private theorem aux_cosine_continuous :
    Continuous (fun y => ∑' j : ℕ, chapter9CosineFourierThreeTerm y j) := by
  refine continuous_tsum ?_ aux_one_div_cube_summable ?_
  · intro j
    change Continuous (fun y =>
      Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3))
    apply Continuous.div_const
    exact Real.continuous_cos.comp (continuous_const.mul continuous_id')
  · intro j y
    change ‖chapter9CosineFourierThreeTerm y j‖ ≤
      (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 3)
    change ‖Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) / ((((j + 1 : ℕ)) : ℝ) ^ 3)‖ ≤ _
    rw [Real.norm_eq_abs, abs_div]
    have hcos : |Real.cos (2 * (((j + 1 : ℕ)) : ℝ) * y)| ≤ 1 :=
      Real.abs_cos_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 3) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (Nat.succ_pos j)
    rw [abs_of_pos hpos]
    gcongr

private def auxA (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k + 1).factorial : ℝ))

private theorem auxA_nonneg (k : ℕ) : 0 ≤ auxA k := by
  unfold auxA
  apply div_nonneg _ (Nat.cast_nonneg _)
  apply mul_nonneg _ (sq_nonneg _)
  positivity

private theorem auxA_le_one (k : ℕ) : auxA k ≤ 1 := by
  unfold auxA
  exact aux_coeff_le_one k

private theorem auxA_zero : auxA 0 = 1 := by
  unfold auxA
  norm_num

private theorem auxA_succ (k : ℕ) :
    auxA (k + 1) = auxA k * ((((2 * k + 2 : ℕ)) : ℝ) / ((((2 * k + 3 : ℕ)) : ℝ))) := by
  unfold auxA
  have hfact1 : (((k + 1).factorial : ℕ) : ℝ) = ((((k + 1 : ℕ)) : ℝ)) * ((k.factorial : ℝ)) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  have heq : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
  have h3232 : (2 * k + 3 : ℕ) = (2 * k + 2) + 1 := by omega
  have h2221 : (2 * k + 2 : ℕ) = (2 * k + 1) + 1 := by omega
  have hfact2 : ((((2 * (k + 1) + 1).factorial : ℕ)) : ℝ) =
      ((((2 * k + 3 : ℕ)) : ℝ)) * ((((2 * k + 2 : ℕ)) : ℝ)) *
        ((((2 * k + 1).factorial : ℕ)) : ℝ) := by
    rw [heq, h3232, Nat.factorial_succ, h2221, Nat.factorial_succ]
    push_cast
    ring
  have hexp : 2 * (k + 1) = 2 * k + 2 := by ring
  have hpow : (2 : ℝ) ^ (2 * (k + 1)) = (2 : ℝ) ^ (2 * k) * 4 := by
    rw [hexp, pow_add]
    norm_num
  have hfk : ((((k + 1 : ℕ)) : ℝ)) = ((k : ℝ) + 1) := by push_cast; ring
  have h2k2 : ((((2 * k + 2 : ℕ)) : ℝ)) = 2 * ((k : ℝ) + 1) := by push_cast; ring
  have h2k3 : ((((2 * k + 3 : ℕ)) : ℝ)) = 2 * ((k : ℝ) + 1) + 1 := by push_cast; ring
  have hfact_ne : ((((2 * k + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2k2_ne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  have h2k3_ne : ((((2 * k + 3 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  rw [hfact1, hfact2, hpow, hfk, h2k2, h2k3]
  field_simp
  ring

private theorem auxA_rec (k : ℕ) :
    ((((2 * k + 3 : ℕ)) : ℝ)) * auxA (k + 1) = ((((2 * k + 2 : ℕ)) : ℝ)) * auxA k := by
  have h2k3_ne : ((((2 * k + 3 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  rw [auxA_succ]
  field_simp

private theorem aux_factorial_eq (u : ℝ) (k : ℕ) :
    chapter9Entry23FactorialTerm u k =
      auxA k * Real.sin u ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) := by
  unfold chapter9Entry23FactorialTerm auxA
  have hfact_ne : ((((2 * k + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2k2_ne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    omega
  field_simp

private def auxP_term (s : ℝ) (k : ℕ) : ℝ := auxA k * s ^ (2 * k + 1)

private def auxP (s : ℝ) : ℝ := ∑' k : ℕ, auxP_term s k

private def auxPderiv_term (s : ℝ) (k : ℕ) : ℝ :=
  auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k)

private theorem auxP_summable {s : ℝ} (hs : |s| < 1) :
    Summable (auxP_term s) := by
  have hr : |(|s| ^ 2)| < 1 := by
    have hsq : |s| ^ 2 < 1 := by nlinarith [hs, abs_nonneg s]
    have hnn : (0 : ℝ) ≤ |s| ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (|s| ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr
  have hbound : Summable (fun k : ℕ => |s| * (|s| ^ 2) ^ k) := hgeo.mul_left |s|
  apply Summable.of_norm_bounded hbound
  intro k
  have hA : ‖auxA k‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
    exact auxA_le_one k
  have hpow : (‖s ^ (2 * k + 1)‖) = |s| * (|s| ^ 2) ^ k := by
    rw [norm_pow, Real.norm_eq_abs]
    have e : |s| ^ (2 * k + 1) = |s| * (|s| ^ 2) ^ k := by
      rw [pow_succ, ← pow_mul, mul_comm]
    exact e
  calc ‖auxP_term s k‖ = ‖auxA k‖ * ‖s ^ (2 * k + 1)‖ := by
        unfold auxP_term
        rw [norm_mul]
    _ ≤ 1 * (|s| * (|s| ^ 2) ^ k) := by
        rw [hpow]
        exact mul_le_mul hA le_rfl (by positivity) (by positivity)
    _ = |s| * (|s| ^ 2) ^ k := one_mul _

private theorem auxPderiv_bound_summable {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1) :
    Summable (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k)) := by
  have hr1 : |rho ^ 2| < 1 := by
    have hsq : rho ^ 2 < 1 := by nlinarith [h0, h1, sq_nonneg rho]
    have hnn : (0 : ℝ) ≤ rho ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (rho ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr1
  have hnorm : ‖rho ^ 2‖ < 1 := by
    rwa [Real.norm_eq_abs]
  have hpow1 : Summable (fun k : ℕ => (k : ℝ) * (rho ^ 2) ^ k) := by
    simpa [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have h2k : Summable (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k) := by
    have h := hpow1.mul_left 2
    have heq : (fun k : ℕ => 2 * ((k : ℝ) * (rho ^ 2) ^ k)) =
        (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k) := by
      funext k
      ring
    rwa [heq] at h
  have hsum : Summable (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k + (rho ^ 2) ^ k) :=
    h2k.add hgeo
  have heq : (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k)) =
      (fun k : ℕ => 2 * (k : ℝ) * (rho ^ 2) ^ k + (rho ^ 2) ^ k) := by
    funext k
    have hcast : ((((2 * k + 1 : ℕ)) : ℝ)) = 2 * (k : ℝ) + 1 := by
      push_cast
      ring
    have hpow : rho ^ (2 * k) = (rho ^ 2) ^ k := by
      rw [← pow_mul]
    rw [hcast, hpow]
    ring
  rw [heq]
  exact hsum

private theorem auxP_hasDerivAt {s : ℝ} (hs : |s| < 1) :
    HasDerivAt auxP (∑' k : ℕ, auxPderiv_term s k) s := by
  set rho : ℝ := (|s| + 1) / 2 with hrhodef
  have hrho0 : 0 ≤ rho := by
    unfold rho
    have h : (0 : ℝ) ≤ |s| + 1 := by
      have hnn : (0 : ℝ) ≤ |s| := abs_nonneg _
      linarith
    linarith
  have hrho1 : rho < 1 := by
    unfold rho
    linarith
  have hsmem : s ∈ Set.Ioo (-rho) rho := by
    have hlt : |s| < rho := by
      unfold rho
      linarith
    exact Set.mem_Ioo.mpr (abs_lt.mp hlt)
  have hu : Summable (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k)) :=
    auxPderiv_bound_summable hrho0 hrho1
  have hterm : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-rho) rho,
      HasDerivAt (fun y => auxP_term y k) (auxPderiv_term y k) y := by
    intro k y _
    unfold auxP_term auxPderiv_term
    have hpow : HasDerivAt (fun y : ℝ => y ^ (2 * k + 1))
        ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k + 1 - 1)) y :=
      hasDerivAt_pow (2 * k + 1) y
    have hsub : 2 * k + 1 - 1 = 2 * k := Nat.add_sub_cancel _ _
    rw [hsub] at hpow
    have hmul := hpow.const_mul (auxA k)
    have heq : auxA k * ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k)) =
        auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * y ^ (2 * k) := by ring
    rw [heq] at hmul
    exact hmul
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-rho) rho,
      ‖auxPderiv_term y k‖ ≤ ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k) := by
    intro k y hy
    have hyabs : |y| < rho := abs_lt.mpr (Set.mem_Ioo.mp hy)
    have hyle : |y| ≤ rho := le_of_lt hyabs
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hnn1 : (0 : ℝ) ≤ ((((2 * k + 1 : ℕ)) : ℝ)) := Nat.cast_nonneg _
    have hpow_le : |y| ^ (2 * k) ≤ rho ^ (2 * k) :=
      pow_le_pow_left₀ (abs_nonneg _) hyle _
    unfold auxPderiv_term
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs]
    have h2 : ‖((((2 * k + 1 : ℕ)) : ℝ))‖ = ((((2 * k + 1 : ℕ)) : ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    rw [h2]
    calc ‖auxA k‖ * ((((2 * k + 1 : ℕ)) : ℝ)) * |y| ^ (2 * k)
        ≤ 1 * ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k) := by
          apply mul_le_mul _ hpow_le (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hA hnn1
      _ = ((((2 * k + 1 : ℕ)) : ℝ)) * rho ^ (2 * k) := by ring
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo (-rho) rho).isPreconnected hterm hbound hsmem
    (auxP_summable hs) hsmem
  have efun : (fun z => ∑' k : ℕ, auxP_term z k) = auxP := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

private theorem auxPderiv_summable {s : ℝ} (hs : |s| < 1) :
    Summable (auxPderiv_term s) := by
  have hbound : Summable (fun k : ℕ => ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k)) :=
    auxPderiv_bound_summable (abs_nonneg _) hs
  apply Summable.of_norm_bounded hbound
  intro k
  have hA : ‖auxA k‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
    exact auxA_le_one k
  have hnn1 : (0 : ℝ) ≤ ((((2 * k + 1 : ℕ)) : ℝ)) := Nat.cast_nonneg _
  have h2 : ‖((((2 * k + 1 : ℕ)) : ℝ))‖ = ((((2 * k + 1 : ℕ)) : ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
  have hpow : (‖s ^ (2 * k)‖) = |s| ^ (2 * k) := by
    rw [norm_pow, Real.norm_eq_abs]
  unfold auxPderiv_term
  rw [norm_mul, norm_mul, h2, hpow]
  calc ‖auxA k‖ * ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k)
      ≤ 1 * ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hA hnn1
    _ = ((((2 * k + 1 : ℕ)) : ℝ)) * |s| ^ (2 * k) := by ring

private theorem auxP_ode {s : ℝ} (hs : |s| < 1) :
    (1 - s ^ 2) * (∑' k : ℕ, auxPderiv_term s k) - s * (∑' k : ℕ, auxP_term s k) = 1 := by
  have hf : Summable (auxPderiv_term s) := auxPderiv_summable hs
  have hp : Summable (auxP_term s) := auxP_summable hs
  have hg : Summable (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    have h := hf.mul_right (s ^ 2)
    have heq : (fun k : ℕ => auxPderiv_term s k * s ^ 2) =
        (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
      funext k
      unfold auxPderiv_term
      have e : s ^ (2 * k) * s ^ 2 = s ^ (2 * k + 2) := by
        rw [← pow_add]
      calc auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k) * s ^ 2
          = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * (s ^ (2 * k) * s ^ 2) := by ring
        _ = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) := by rw [e]
    rwa [heq] at h
  have hh : Summable (fun k : ℕ => auxA k * s ^ (2 * k + 2)) := by
    have h := hp.mul_right s
    have heq : (fun k : ℕ => auxP_term s k * s) =
        (fun k : ℕ => auxA k * s ^ (2 * k + 2)) := by
      funext k
      unfold auxP_term
      have e : s ^ (2 * k + 1) * s = s ^ (2 * k + 2) := by
        have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
        rw [h2]
        exact (pow_succ s _).symm
      calc auxA k * s ^ (2 * k + 1) * s
          = auxA k * (s ^ (2 * k + 1) * s) := by ring
        _ = auxA k * s ^ (2 * k + 2) := by rw [e]
    rwa [heq] at h
  have hj : Summable (fun k : ℕ => auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    have h := hg.add hh
    have heq : (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) +
        auxA k * s ^ (2 * k + 2)) =
        (fun k : ℕ => auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
      funext k
      have hcast : ((((2 * k + 2 : ℕ)) : ℝ)) = ((((2 * k + 1 : ℕ)) : ℝ)) + 1 := by
        have h2 : (2 * k + 2 : ℕ) = (2 * k + 1) + 1 := by omega
        rw [h2]
        push_cast
        ring
      rw [hcast]
      ring
    rwa [heq] at h
  have hs2 : s ^ 2 * (∑' k : ℕ, auxPderiv_term s k) =
      ∑' k : ℕ, (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    unfold auxPderiv_term
    have e : s ^ 2 * s ^ (2 * k) = s ^ (2 * k + 2) := by
      have h2 : 2 + 2 * k = 2 * k + 2 := by ring
      calc s ^ 2 * s ^ (2 * k) = s ^ (2 + 2 * k) := by rw [← pow_add]
        _ = s ^ (2 * k + 2) := by rw [h2]
    calc s ^ 2 * (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k))
        = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * (s ^ 2 * s ^ (2 * k)) := by ring
      _ = auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) := by rw [e]
  have hsp : s * (∑' k : ℕ, auxP_term s k) =
      ∑' k : ℕ, (auxA k * s ^ (2 * k + 2)) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro k
    unfold auxP_term
    have e : s * s ^ (2 * k + 1) = s ^ (2 * k + 2) := by
      have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
      calc s * s ^ (2 * k + 1) = s ^ (2 * k + 1) * s := by ring
        _ = s ^ ((2 * k + 1) + 1) := (pow_succ s _).symm
        _ = s ^ (2 * k + 2) := by rw [← h2]
    calc s * (auxA k * s ^ (2 * k + 1))
        = auxA k * (s * s ^ (2 * k + 1)) := by ring
      _ = auxA k * s ^ (2 * k + 2) := by rw [e]
  have hgh : (∑' k : ℕ, (auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2))) =
      (∑' k : ℕ, (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2))) +
        ∑' k : ℕ, (auxA k * s ^ (2 * k + 2)) := by
    have h := hg.tsum_add hh
    have heq : (fun k : ℕ => auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2) +
        auxA k * s ^ (2 * k + 2)) =
        (fun k : ℕ => auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
      funext k
      have hcast : ((((2 * k + 2 : ℕ)) : ℝ)) = ((((2 * k + 1 : ℕ)) : ℝ)) + 1 := by
        have h2 : (2 * k + 2 : ℕ) = (2 * k + 1) + 1 := by omega
        rw [h2]
        push_cast
        ring
      rw [hcast]
      ring
    rw [← heq, h]
  have hf0 : auxPderiv_term s 0 = 1 := by
    unfold auxPderiv_term
    rw [auxA_zero]
    norm_num
  have hshift := hf.tsum_eq_zero_add
  rw [hf0] at hshift
  have htail : (∑' k : ℕ, auxPderiv_term s (k + 1)) =
      ∑' k : ℕ, (auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
    apply tsum_congr
    intro k
    unfold auxPderiv_term
    have hn : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    have hcast : ((((2 * (k + 1) + 1 : ℕ)) : ℝ)) = ((((2 * k + 3 : ℕ)) : ℝ)) := by
      rw [hn]
    have hexp : 2 * (k + 1) = 2 * k + 2 := by ring
    rw [hcast, hexp]
    have hrec := auxA_rec k
    calc auxA (k + 1) * ((((2 * k + 3 : ℕ)) : ℝ)) * s ^ (2 * k + 2)
        = ((((2 * k + 3 : ℕ)) : ℝ)) * auxA (k + 1) * s ^ (2 * k + 2) := by ring
      _ = ((((2 * k + 2 : ℕ)) : ℝ)) * auxA k * s ^ (2 * k + 2) := by rw [hrec]
      _ = auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2) := by ring
  rw [htail] at hshift
  calc (1 - s ^ 2) * (∑' k : ℕ, auxPderiv_term s k) - s * (∑' k : ℕ, auxP_term s k)
      = (∑' k : ℕ, auxPderiv_term s k) - s ^ 2 * (∑' k : ℕ, auxPderiv_term s k) -
        s * (∑' k : ℕ, auxP_term s k) := by ring
    _ = (∑' k : ℕ, auxPderiv_term s k) -
        (∑' k : ℕ, (auxA k * ((((2 * k + 1 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) +
          ∑' k : ℕ, (auxA k * s ^ (2 * k + 2))) := by
        rw [hs2, hsp]
        ring
    _ = (∑' k : ℕ, auxPderiv_term s k) -
        ∑' k : ℕ, (auxA k * ((((2 * k + 2 : ℕ)) : ℝ)) * s ^ (2 * k + 2)) := by
        rw [← hgh]
    _ = 1 := by
        rw [hshift]
        ring

private theorem aux_sin_abs_lt_one {x : ℝ} (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    |Real.sin x| < 1 := by
  have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
  have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
  have hle1 : -(Real.pi / 2) ≤ x := le_of_lt hx1
  have hle2 : x ≤ Real.pi / 2 := le_of_lt hx2
  have hupper : Real.sin x < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two hle1 (le_refl _) hx2
    rwa [Real.sin_pi_div_two] at h
  have hlower : (-1 : ℝ) < Real.sin x := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (le_refl _) hle2 hx1
    have hsin : Real.sin (-(Real.pi / 2)) = -1 := by
      rw [Real.sin_neg, Real.sin_pi_div_two]
    rwa [hsin] at h
  exact abs_lt.mpr ⟨hlower, hupper⟩

private theorem auxP_zero : auxP 0 = 0 := by
  unfold auxP
  have h0 : ∀ k : ℕ, auxP_term 0 k = 0 := by
    intro k
    unfold auxP_term
    have hne : 2 * k + 1 ≠ 0 := by omega
    rw [zero_pow hne, mul_zero]
  rw [tsum_congr h0]
  exact tsum_zero

private def auxK (x : ℝ) : ℝ := Real.cos x * auxP (Real.sin x)

private theorem auxK_zero : auxK 0 = 0 := by
  unfold auxK
  rw [Real.sin_zero, auxP_zero, mul_zero]

private theorem auxK_hasDerivAt {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt auxK 1 x := by
  have hsin : |Real.sin x| < 1 := aux_sin_abs_lt_one hx
  have hP : HasDerivAt auxP (∑' k : ℕ, auxPderiv_term (Real.sin x) k) (Real.sin x) :=
    auxP_hasDerivAt hsin
  have hcomp0 := hP.comp x (Real.hasDerivAt_sin x)
  simp only [Function.comp_def] at hcomp0
  rw [mul_comm (∑' k : ℕ, auxPderiv_term (Real.sin x) k) (Real.cos x)] at hcomp0
  have hcomp : HasDerivAt (fun y => auxP (Real.sin y))
      (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k)) x :=
    hcomp0
  have hmul : HasDerivAt (fun y => Real.cos y * auxP (Real.sin y))
      (-Real.sin x * auxP (Real.sin x) +
        Real.cos x * (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k))) x :=
    (Real.hasDerivAt_cos x).mul hcomp
  have efun : (fun y => Real.cos y * auxP (Real.sin y)) = auxK := by
    funext y
    rfl
  rw [efun] at hmul
  have hode := auxP_ode hsin
  have hcos : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    have h := Real.sin_sq_add_cos_sq x
    linarith
  have hval : -Real.sin x * auxP (Real.sin x) +
      Real.cos x * (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k)) = 1 := by
    have h1 : Real.cos x * (Real.cos x * (∑' k : ℕ, auxPderiv_term (Real.sin x) k)) =
        (Real.cos x ^ 2) * (∑' k : ℕ, auxPderiv_term (Real.sin x) k) := by ring
    rw [h1, hcos]
    have hPeq : auxP (Real.sin x) = ∑' k : ℕ, auxP_term (Real.sin x) k := rfl
    rw [hPeq]
    linear_combination hode
  rw [hval] at hmul
  exact hmul

private theorem auxK_eq {x : ℝ} (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    auxK x = x := by
  have hDderiv : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun y => auxK y - y) 0 y := by
    intro y hy
    have h := (auxK_hasDerivAt hy).sub (hasDerivAt_id y)
    simp only [sub_self] at h
    exact h
  have hDcont : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      ContinuousAt (fun y => auxK y - y) y := fun y hy => (hDderiv y hy).continuousAt
  by_cases hx0 : x = 0
  · subst hx0
    exact auxK_zero
  · rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hIcc_sub : Set.Icc x 0 ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : x ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ 0 := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxK y - y) (Set.Icc x 0) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo x 0, HasDerivAt (fun y => auxK y - y) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc x 0 :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxK y - y) (fun _ => 0) hneg hcont hderiv
      rw [auxK_zero, sub_self (0 : ℝ), zero_sub (auxK x - x)] at hc
      have hne : (0 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      have h0 : (-(auxK x - x)) / (0 - x) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : -(auxK x - x) = 0 := h0.resolve_right hne
      have hDx : auxK x - x = 0 := neg_eq_zero.mp hnum
      exact sub_eq_zero.mp hDx
    · have hIcc_sub : Set.Icc 0 x ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : 0 ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ x := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxK y - y) (Set.Icc 0 x) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo 0 x, HasDerivAt (fun y => auxK y - y) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc 0 x :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxK y - y) (fun _ => 0) hpos hcont hderiv
      rw [auxK_zero, sub_self (0 : ℝ), sub_zero (auxK x - x)] at hc
      have hne : (x : ℝ) - 0 ≠ 0 := ne_of_gt (by linarith)
      have h0 : (auxK x - x) / (x - 0) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : auxK x - x = 0 := h0.resolve_right hne
      exact sub_eq_zero.mp hnum

private theorem aux_sin_abs_le_sin_c {c : ℝ} (hc0 : 0 < c) (hc1 : c < Real.pi / 2)
    {y : ℝ} (hy : y ∈ Set.Ioo (-c) c) : |Real.sin y| ≤ Real.sin c := by
  have hyabs : |y| < c := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hyle : |y| ≤ c := le_of_lt hyabs
  have hpi : |y| ≤ Real.pi := by
    have h1 : |y| < Real.pi / 2 := lt_of_lt_of_le hyabs (le_of_lt hc1)
    linarith [Real.pi_pos]
  have heq : |Real.sin y| = Real.sin |y| := Real.abs_sin_eq_sin_abs_of_abs_le_pi hpi
  rw [heq]
  have h1 : -(Real.pi / 2) ≤ |y| := by
    have hnn : (0 : ℝ) ≤ |y| := abs_nonneg _
    linarith [Real.pi_pos]
  have h2 : c ≤ Real.pi / 2 := le_of_lt hc1
  exact Real.sin_le_sin_of_le_of_le_pi_div_two h1 h2 hyle

private theorem aux_sin_c_bounds {c : ℝ} (hc0 : 0 < c) (hc1 : c < Real.pi / 2) :
    0 ≤ Real.sin c ∧ Real.sin c < 1 := by
  have hpos : 0 < Real.sin c := by
    have hlt : c < Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hc0 hlt
  have hlt1 : Real.sin c < 1 := by
    have hle1 : -(Real.pi / 2) ≤ c := by linarith [Real.pi_pos, hc0]
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two hle1 (le_refl _) hc1
    rwa [Real.sin_pi_div_two] at h
  exact ⟨le_of_lt hpos, hlt1⟩

private def auxH_term (x : ℝ) (k : ℕ) : ℝ :=
  auxA k * Real.sin x ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ))

private def auxH (x : ℝ) : ℝ := ∑' k : ℕ, auxH_term x k

private theorem auxH_summable {x : ℝ}
    (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    Summable (auxH_term x) := by
  have hsin : |Real.sin x| < 1 := aux_sin_abs_lt_one hx
  have hr : |(|Real.sin x| ^ 2)| < 1 := by
    have hsq : |Real.sin x| ^ 2 < 1 := by nlinarith [hsin, abs_nonneg (Real.sin x)]
    have hnn : (0 : ℝ) ≤ |Real.sin x| ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (|Real.sin x| ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr
  have hbound : Summable (fun k : ℕ => |Real.sin x| ^ (2 * k + 2)) := by
    have h := hgeo.mul_left (|Real.sin x| ^ 2)
    have heq : (fun k : ℕ => |Real.sin x| ^ 2 * (|Real.sin x| ^ 2) ^ k) =
        (fun k : ℕ => |Real.sin x| ^ (2 * k + 2)) := by
      funext k
      have e1 : (|Real.sin x| ^ 2) ^ k = |Real.sin x| ^ (2 * k) := by
        rw [← pow_mul]
      rw [e1]
      have e2 : (2 : ℕ) + 2 * k = 2 * k + 2 := by ring
      calc |Real.sin x| ^ 2 * |Real.sin x| ^ (2 * k)
          = |Real.sin x| ^ (2 + 2 * k) := by rw [← pow_add]
        _ = |Real.sin x| ^ (2 * k + 2) := by rw [e2]
    rwa [heq] at h
  apply Summable.of_norm_bounded hbound
  intro k
  have hA : ‖auxA k‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
    exact auxA_le_one k
  have hpos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ)) := by
    apply Nat.cast_pos.mpr
    omega
  have hle1 : (1 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
    have h : (1 : ℕ) ≤ 2 * k + 2 := by omega
    exact_mod_cast h
  have hdiv : (1 : ℝ) / ((((2 * k + 2 : ℕ)) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hle1
  have hnn1 : (0 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := le_of_lt hpos
  have hnormb : ‖((((2 * k + 2 : ℕ)) : ℝ))‖ = ((((2 * k + 2 : ℕ)) : ℝ)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
  have hpow : (‖Real.sin x ^ (2 * k + 2)‖) = |Real.sin x| ^ (2 * k + 2) := by
    rw [norm_pow, Real.norm_eq_abs]
  unfold auxH_term
  rw [norm_div, norm_mul, hnormb, hpow]
  have hnn_pow : (0 : ℝ) ≤ |Real.sin x| ^ (2 * k + 2) := by positivity
  calc ‖auxA k‖ * |Real.sin x| ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ))
      = (‖auxA k‖ * |Real.sin x| ^ (2 * k + 2)) * (1 / ((((2 * k + 2 : ℕ)) : ℝ))) := by
        ring
    _ ≤ (1 * |Real.sin x| ^ (2 * k + 2)) * 1 := by
        apply mul_le_mul _ hdiv (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hA hnn_pow
    _ = |Real.sin x| ^ (2 * k + 2) := by ring

private theorem aux_pow_odd_summable {rho : ℝ} (h0 : 0 ≤ rho) (h1 : rho < 1) :
    Summable (fun k : ℕ => rho ^ (2 * k + 1)) := by
  have hr : |(rho ^ 2)| < 1 := by
    have hsq : rho ^ 2 < 1 := by nlinarith [h0, h1, sq_nonneg rho]
    have hnn : (0 : ℝ) ≤ rho ^ 2 := by positivity
    rwa [abs_of_nonneg hnn]
  have hgeo : Summable (fun k : ℕ => (rho ^ 2) ^ k) :=
    summable_geometric_of_abs_lt_one hr
  have h := hgeo.mul_left rho
  have heq : (fun k : ℕ => rho * (rho ^ 2) ^ k) =
      (fun k : ℕ => rho ^ (2 * k + 1)) := by
    funext k
    have e1 : (rho ^ 2) ^ k = rho ^ (2 * k) := by
      rw [← pow_mul]
    rw [e1]
    calc rho * rho ^ (2 * k) = rho ^ (2 * k) * rho := by ring
      _ = rho ^ (2 * k + 1) := (pow_succ rho _).symm
  rwa [heq] at h

private theorem auxH_hasDerivAt {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt auxH x₀ x₀ := by
  have habs : |x₀| < Real.pi / 2 := abs_lt.mpr (Set.mem_Ioo.mp hx₀)
  set c : ℝ := (|x₀| + Real.pi / 2) / 2 with hcdef
  have hc0 : 0 < c := by
    have hnn : (0 : ℝ) ≤ |x₀| := abs_nonneg _
    have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
    linarith
  have hc1 : c < Real.pi / 2 := by
    unfold c
    linarith
  have hxc : |x₀| < c := by
    unfold c
    linarith
  have hxmem : x₀ ∈ Set.Ioo (-c) c := Set.mem_Ioo.mpr (abs_lt.mp hxc)
  have hsin_b := aux_sin_c_bounds hc0 hc1
  set rho : ℝ := Real.sin c with hrhodef
  have hrho0 : 0 ≤ rho := hsin_b.1
  have hrho1 : rho < 1 := hsin_b.2
  have hu : Summable (fun k : ℕ => rho ^ (2 * k + 1)) :=
    aux_pow_odd_summable hrho0 hrho1
  have hterm : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-c) c,
      HasDerivAt (fun y => auxH_term y k)
        (Real.cos y * auxP_term (Real.sin y) k) y := by
    intro k y _
    unfold auxH_term auxP_term
    have hDne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      omega
    have hsub : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    have hpow0 := (Real.hasDerivAt_sin y).pow (2 * k + 2)
    rw [hsub] at hpow0
    have hmul := hpow0.const_mul (auxA k)
    have hdiv := hmul.div_const ((((2 * k + 2 : ℕ)) : ℝ))
    have heq : (auxA k * ((((2 * k + 2 : ℕ)) : ℝ) * Real.sin y ^ (2 * k + 1) *
        Real.cos y)) / ((((2 * k + 2 : ℕ)) : ℝ)) =
        Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1)) := by
      field_simp
    rw [heq] at hdiv
    exact hdiv
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo (-c) c,
      ‖Real.cos y * auxP_term (Real.sin y) k‖ ≤ rho ^ (2 * k + 1) := by
    intro k y hy
    have hsin_le : |Real.sin y| ≤ rho := aux_sin_abs_le_sin_c hc0 hc1 hy
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hcos : ‖Real.cos y‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have hpow_le : |Real.sin y| ^ (2 * k + 1) ≤ rho ^ (2 * k + 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hsin_le _
    unfold auxP_term
    rw [norm_mul, norm_mul, norm_pow, Real.norm_eq_abs]
    calc ‖Real.cos y‖ * (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1))
        ≤ 1 * (1 * rho ^ (2 * k + 1)) := by
          apply mul_le_mul hcos _ (by positivity) (by positivity)
          apply mul_le_mul hA hpow_le (by positivity) (by positivity)
      _ = rho ^ (2 * k + 1) := by ring
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo (-c) c).isPreconnected hterm hbound hxmem
    (auxH_summable (by
      have hsub : Set.Ioo (-c) c ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : -c < y := (Set.mem_Ioo.mp hy).1
        have hy2 : y < c := (Set.mem_Ioo.mp hy).2
        constructor <;> linarith [Real.pi_pos]
      exact hsub hxmem)) hxmem
  have efun : (fun z => ∑' k : ℕ, auxH_term z k) = auxH := by
    funext z
    rfl
  rw [efun] at hmain
  have htsum : (∑' k : ℕ, Real.cos x₀ * auxP_term (Real.sin x₀) k) = x₀ := by
    rw [tsum_mul_left]
    have hPeq : (∑' k : ℕ, auxP_term (Real.sin x₀) k) = auxP (Real.sin x₀) := rfl
    rw [hPeq]
    have hK : Real.cos x₀ * auxP (Real.sin x₀) = x₀ := auxK_eq hx₀
    exact hK
  rw [htsum] at hmain
  exact hmain

private theorem auxH_zero : auxH 0 = 0 := by
  unfold auxH
  have h0 : ∀ k : ℕ, auxH_term 0 k = 0 := by
    intro k
    unfold auxH_term
    have hne : 2 * k + 2 ≠ 0 := by omega
    rw [Real.sin_zero, zero_pow hne, mul_zero, zero_div]
  rw [tsum_congr h0]
  exact tsum_zero

private theorem auxH_eq {x : ℝ} (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    auxH x = x ^ 2 / 2 := by
  have hsq : ∀ y : ℝ, HasDerivAt (fun y => y ^ 2 / 2) y y := by
    intro y
    have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * y) y := by
      have h := hasDerivAt_pow 2 y
      simpa [pow_one] using h
    have hdiv := hpow.div_const 2
    have heq : (2 * y) / 2 = y := by ring
    rw [heq] at hdiv
    exact hdiv
  have hDderiv : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      HasDerivAt (fun y => auxH y - y ^ 2 / 2) 0 y := by
    intro y hy
    have h := (auxH_hasDerivAt hy).sub (hsq y)
    simp only [sub_self] at h
    exact h
  have hDcont : ∀ y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2),
      ContinuousAt (fun y => auxH y - y ^ 2 / 2) y :=
    fun y hy => (hDderiv y hy).continuousAt
  have hD0 : (fun y => auxH y - y ^ 2 / 2) 0 = 0 := by
    simp [auxH_zero]
  by_cases hx0 : x = 0
  · subst hx0
    simp [auxH_zero]
  · rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · have hIcc_sub : Set.Icc x 0 ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : x ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ 0 := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxH y - y ^ 2 / 2) (Set.Icc x 0) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo x 0,
          HasDerivAt (fun y => auxH y - y ^ 2 / 2) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc x 0 :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxH y - y ^ 2 / 2) (fun _ => 0)
          hneg hcont hderiv
      have hD0' : auxH 0 - (0 : ℝ) ^ 2 / 2 = 0 := by simp [auxH_zero]
      rw [hD0', zero_sub (auxH x - x ^ 2 / 2)] at hc
      have hne : (0 : ℝ) - x ≠ 0 := ne_of_gt (by linarith)
      have h0 : (-(auxH x - x ^ 2 / 2)) / (0 - x) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : -(auxH x - x ^ 2 / 2) = 0 := h0.resolve_right hne
      have hDx : auxH x - x ^ 2 / 2 = 0 := neg_eq_zero.mp hnum
      exact sub_eq_zero.mp hDx
    · have hIcc_sub : Set.Icc 0 x ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
        intro y hy
        have hy1 : 0 ≤ y := (Set.mem_Icc.mp hy).1
        have hy2 : y ≤ x := (Set.mem_Icc.mp hy).2
        have hx1 : -(Real.pi / 2) < x := (Set.mem_Ioo.mp hx).1
        have hx2 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
        constructor <;> linarith [Real.pi_pos]
      have hcont : ContinuousOn (fun y => auxH y - y ^ 2 / 2) (Set.Icc 0 x) := by
        intro y hy
        exact (hDcont y (hIcc_sub hy)).continuousWithinAt
      have hderiv : ∀ y ∈ Set.Ioo 0 x,
          HasDerivAt (fun y => auxH y - y ^ 2 / 2) 0 y := by
        intro y hy
        have hyIcc : y ∈ Set.Icc 0 x :=
          ⟨le_of_lt (Set.mem_Ioo.mp hy).1, le_of_lt (Set.mem_Ioo.mp hy).2⟩
        exact hDderiv y (hIcc_sub hyIcc)
      obtain ⟨c, _, hc⟩ :=
        exists_hasDerivAt_eq_slope (fun y => auxH y - y ^ 2 / 2) (fun _ => 0)
          hpos hcont hderiv
      have hD0' : auxH 0 - (0 : ℝ) ^ 2 / 2 = 0 := by simp [auxH_zero]
      rw [hD0', sub_zero (auxH x - x ^ 2 / 2)] at hc
      have hne : (x : ℝ) - 0 ≠ 0 := ne_of_gt (by linarith)
      have h0 : (auxH x - x ^ 2 / 2) / (x - 0) = 0 := hc.symm
      rw [div_eq_zero_iff] at h0
      have hnum : auxH x - x ^ 2 / 2 = 0 := h0.resolve_right hne
      exact sub_eq_zero.mp hnum

private def auxF (x : ℝ) : ℝ := ∑' k : ℕ, chapter9Entry23FactorialTerm x k

private theorem auxF_hasDerivAt {x₀ : ℝ} (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt auxF ((x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀)) x₀ := by
  have hx0_pos : 0 < x₀ := (Set.mem_Ioo.mp hx₀).1
  have hx0_lt : x₀ < Real.pi / 2 := (Set.mem_Ioo.mp hx₀).2
  have hxIoo : x₀ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hsin_pos : 0 < Real.sin x₀ := by
    have hlt : x₀ < Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hx0_pos hlt
  have hsin_ne : Real.sin x₀ ≠ 0 := ne_of_gt hsin_pos
  have hsin_abs : |Real.sin x₀| < 1 := aux_sin_abs_lt_one hxIoo
  set c : ℝ := (x₀ + Real.pi / 2) / 2 with hcdef
  have hc0 : 0 < c := by linarith [Real.pi_pos]
  have hc1 : c < Real.pi / 2 := by unfold c; linarith
  have hxc : x₀ < c := by unfold c; linarith
  have hxmem : x₀ ∈ Set.Ioo 0 c := ⟨hx0_pos, hxc⟩
  have hsub : Set.Ioo 0 c ⊆ Set.Ioo (-c) c := by
    intro y hy
    have hy1 : 0 < y := (Set.mem_Ioo.mp hy).1
    have hy2 : y < c := (Set.mem_Ioo.mp hy).2
    constructor <;> linarith
  have hsin_b := aux_sin_c_bounds hc0 hc1
  set rho : ℝ := Real.sin c with hrhodef
  have hrho0 : 0 ≤ rho := hsin_b.1
  have hrho1 : rho < 1 := hsin_b.2
  have hu : Summable (fun k : ℕ => rho ^ (2 * k + 1)) :=
    aux_pow_odd_summable hrho0 hrho1
  have hterm : ∀ k : ℕ, ∀ y ∈ Set.Ioo 0 c,
      HasDerivAt (fun y => chapter9Entry23FactorialTerm y k)
        (Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))))
        y := by
    intro k y _
    have efun : (fun y => chapter9Entry23FactorialTerm y k) =
        (fun y => auxA k * Real.sin y ^ (2 * k + 2) / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)) :=
      funext (fun y => aux_factorial_eq y k)
    rw [efun]
    have hDne : ((((2 * k + 2 : ℕ)) : ℝ)) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      omega
    have hsub2 : 2 * k + 2 - 1 = 2 * k + 1 := by omega
    have hpow0 := (Real.hasDerivAt_sin y).pow (2 * k + 2)
    rw [hsub2] at hpow0
    have hmul := hpow0.const_mul (auxA k)
    have hdiv := hmul.div_const ((((2 * k + 2 : ℕ)) : ℝ) ^ 2)
    have heq : (auxA k * ((((2 * k + 2 : ℕ)) : ℝ) * Real.sin y ^ (2 * k + 1) *
        Real.cos y)) / ((((2 * k + 2 : ℕ)) : ℝ) ^ 2) =
        Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
      field_simp
    rw [heq] at hdiv
    exact hdiv
  have hbound : ∀ k : ℕ, ∀ y ∈ Set.Ioo 0 c,
      ‖Real.cos y * (auxA k * Real.sin y ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))‖ ≤
        rho ^ (2 * k + 1) := by
    intro k y hy
    have hymem : y ∈ Set.Ioo (-c) c := hsub hy
    have hsin_le : |Real.sin y| ≤ rho := aux_sin_abs_le_sin_c hc0 hc1 hymem
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hcos : ‖Real.cos y‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
    have hpow_le : |Real.sin y| ^ (2 * k + 1) ≤ rho ^ (2 * k + 1) :=
      pow_le_pow_left₀ (abs_nonneg _) hsin_le _
    have hpos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ)) := by
      apply Nat.cast_pos.mpr
      omega
    have hle1 : (1 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ 2 * k + 2 := by omega
      exact_mod_cast h
    have hdiv : (1 : ℝ) / ((((2 * k + 2 : ℕ)) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hle1
    have hnn1 : (0 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := le_of_lt hpos
    have hnormb : ‖((((2 * k + 2 : ℕ)) : ℝ))‖ = ((((2 * k + 2 : ℕ)) : ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    have hpow : (‖Real.sin y ^ (2 * k + 1)‖) = |Real.sin y| ^ (2 * k + 1) := by
      rw [norm_pow, Real.norm_eq_abs]
    rw [norm_mul, norm_div, norm_mul, hnormb, hpow]
    have hnn_pow : (0 : ℝ) ≤ |Real.sin y| ^ (2 * k + 1) := by positivity
    have hmid : ‖auxA k‖ * |Real.sin y| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))
        ≤ rho ^ (2 * k + 1) := by
      have e : ‖auxA k‖ * |Real.sin y| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))
          = (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1)) *
            (1 / ((((2 * k + 2 : ℕ)) : ℝ))) := by ring
      rw [e]
      calc (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1)) * (1 / ((((2 * k + 2 : ℕ)) : ℝ)))
          ≤ (1 * rho ^ (2 * k + 1)) * 1 := by
            apply mul_le_mul _ hdiv (by positivity) (by positivity)
            exact mul_le_mul hA hpow_le (by positivity) (by positivity)
        _ = rho ^ (2 * k + 1) := by ring
    calc ‖Real.cos y‖ * (‖auxA k‖ * |Real.sin y| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))
        ≤ 1 * rho ^ (2 * k + 1) := mul_le_mul hcos hmid (by positivity) (by positivity)
      _ = rho ^ (2 * k + 1) := one_mul _
  have hmain := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo
    (convex_Ioo 0 c).isPreconnected hterm hbound hxmem
    (aux_factorial_summable x₀) hxmem
  have efun : (fun z => ∑' k : ℕ, chapter9Entry23FactorialTerm z k) = auxF := by
    funext z
    rfl
  rw [efun] at hmain
  have hS_summ : Summable
      (fun k : ℕ => auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
    have hboundS : Summable (fun k : ℕ => |Real.sin x₀| ^ (2 * k + 1)) := by
      have hr : |(|Real.sin x₀| ^ 2)| < 1 := by
        have hsq : |Real.sin x₀| ^ 2 < 1 := by nlinarith [hsin_abs, abs_nonneg (Real.sin x₀)]
        have hnn : (0 : ℝ) ≤ |Real.sin x₀| ^ 2 := by positivity
        rwa [abs_of_nonneg hnn]
      have hgeo : Summable (fun k : ℕ => (|Real.sin x₀| ^ 2) ^ k) :=
        summable_geometric_of_abs_lt_one hr
      have h := hgeo.mul_left |Real.sin x₀|
      have heq : (fun k : ℕ => |Real.sin x₀| * (|Real.sin x₀| ^ 2) ^ k) =
          (fun k : ℕ => |Real.sin x₀| ^ (2 * k + 1)) := by
        funext k
        have e1 : (|Real.sin x₀| ^ 2) ^ k = |Real.sin x₀| ^ (2 * k) := by
          rw [← pow_mul]
        rw [e1]
        calc |Real.sin x₀| * |Real.sin x₀| ^ (2 * k)
            = |Real.sin x₀| ^ (2 * k) * |Real.sin x₀| := by ring
          _ = |Real.sin x₀| ^ (2 * k + 1) := (pow_succ _ _).symm
      rwa [heq] at h
    apply Summable.of_norm_bounded hboundS
    intro k
    have hA : ‖auxA k‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_of_nonneg (auxA_nonneg k)]
      exact auxA_le_one k
    have hpos : (0 : ℝ) < ((((2 * k + 2 : ℕ)) : ℝ)) := by
      apply Nat.cast_pos.mpr
      omega
    have hle1 : (1 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ 2 * k + 2 := by omega
      exact_mod_cast h
    have hdiv : (1 : ℝ) / ((((2 * k + 2 : ℕ)) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hle1
    have hnn1 : (0 : ℝ) ≤ ((((2 * k + 2 : ℕ)) : ℝ)) := le_of_lt hpos
    have hnormb : ‖((((2 * k + 2 : ℕ)) : ℝ))‖ = ((((2 * k + 2 : ℕ)) : ℝ)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hnn1]
    have hpow : (‖Real.sin x₀ ^ (2 * k + 1)‖) = |Real.sin x₀| ^ (2 * k + 1) := by
      rw [norm_pow, Real.norm_eq_abs]
    rw [norm_div, norm_mul, hnormb, hpow]
    have hnn_pow : (0 : ℝ) ≤ |Real.sin x₀| ^ (2 * k + 1) := by positivity
    calc ‖auxA k‖ * |Real.sin x₀| ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))
        = (‖auxA k‖ * |Real.sin x₀| ^ (2 * k + 1)) * (1 / ((((2 * k + 2 : ℕ)) : ℝ))) := by
          ring
      _ ≤ (1 * |Real.sin x₀| ^ (2 * k + 1)) * 1 := by
          apply mul_le_mul _ hdiv (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_right hA hnn_pow
      _ = |Real.sin x₀| ^ (2 * k + 1) := by ring
  have hH_eq : auxH x₀ = Real.sin x₀ *
      (∑' k : ℕ, auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
    have hcongr : (fun k : ℕ => auxH_term x₀ k) =
        (fun k : ℕ => Real.sin x₀ *
          (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))) := by
      funext k
      unfold auxH_term
      have e : Real.sin x₀ ^ (2 * k + 2) =
          Real.sin x₀ * Real.sin x₀ ^ (2 * k + 1) := by
        have h2 : 2 * k + 2 = (2 * k + 1) + 1 := by omega
        calc Real.sin x₀ ^ (2 * k + 2) = Real.sin x₀ ^ ((2 * k + 1) + 1) := by rw [← h2]
          _ = Real.sin x₀ ^ (2 * k + 1) * Real.sin x₀ := pow_succ _ _
          _ = Real.sin x₀ * Real.sin x₀ ^ (2 * k + 1) := by ring
      rw [e]
      ring
    have htsum : (∑' k : ℕ, auxH_term x₀ k) =
        ∑' k : ℕ, Real.sin x₀ *
          (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
      rw [hcongr]
    have hmul : (∑' k : ℕ, Real.sin x₀ *
        (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))) =
        Real.sin x₀ * (∑' k : ℕ,
          auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) := by
      rw [tsum_mul_left]
    have hPeq : (∑' k : ℕ, auxH_term x₀ k) = auxH x₀ := rfl
    rw [hPeq] at htsum
    rw [htsum, hmul]
  have hHval : auxH x₀ = x₀ ^ 2 / 2 := auxH_eq hxIoo
  have hS_eq : (∑' k : ℕ,
      auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ))) =
      (x₀ ^ 2 / 2) / Real.sin x₀ := by
    rw [← hHval, hH_eq]
    field_simp
  have hF_eq : (∑' k : ℕ, Real.cos x₀ *
      (auxA k * Real.sin x₀ ^ (2 * k + 1) / ((((2 * k + 2 : ℕ)) : ℝ)))) =
      (x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀) := by
    rw [tsum_mul_left, hS_eq]
    ring
  rw [hF_eq] at hmain
  exact hmain

private def auxAr_term (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (j + 1) * Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ) ^ 2)

private def auxAr (r x : ℝ) : ℝ := ∑' j : ℕ, auxAr_term r x j

private def auxAr_deriv_term (r x : ℝ) (j : ℕ) : ℝ :=
  2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))

private theorem auxAr_summable {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    Summable (auxAr_term r x) := by
  have habs : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_abs_lt_one habs
  have hshift : Summable (fun j : ℕ => r ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  apply Summable.of_norm_bounded hshift
  intro j
  have hsin : |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    exact Nat.cast_pos.mpr (Nat.succ_pos j)
  have hle1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    have h1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
      exact_mod_cast h
    calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ ((((j + 1 : ℕ)) : ℝ) ^ 2) := pow_le_pow_left₀ zero_le_one h1 2
  have hdiv : (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) ≤ 1 := (div_le_one hpos).mpr hle1
  have hnn_pow : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
  unfold auxAr_term
  rw [Real.norm_eq_abs, abs_div, abs_mul]
  have habs2 : |((((j + 1 : ℕ)) : ℝ) ^ 2)| = ((((j + 1 : ℕ)) : ℝ) ^ 2) :=
    abs_of_pos hpos
  rw [habs2]
  have hr_abs : |r ^ (j + 1)| = r ^ (j + 1) := abs_of_nonneg hnn_pow
  rw [hr_abs]
  calc r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| /
        ((((j + 1 : ℕ)) : ℝ) ^ 2)
      = (r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)|) *
        (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by ring
    _ ≤ (r ^ (j + 1) * 1) * 1 := by
        apply mul_le_mul _ hdiv (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hsin hnn_pow
    _ = r ^ (j + 1) := by ring

private theorem auxAr_hasDerivAt {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasDerivAt (auxAr r) (∑' j : ℕ, auxAr_deriv_term r x j) x := by
  have habs : |r| < 1 := by rwa [abs_of_nonneg hr0]
  have hgeo : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_abs_lt_one habs
  have hshift : Summable (fun j : ℕ => r ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hgeo
  have hu : Summable (fun j : ℕ => 2 * r ^ (j + 1)) := hshift.mul_left 2
  have hterm : ∀ j : ℕ, ∀ y : ℝ,
      HasDerivAt (fun y => auxAr_term r y j) (auxAr_deriv_term r y j) y := by
    intro j y
    unfold auxAr_term auxAr_deriv_term
    have hkne : ((((j + 1 : ℕ)) : ℝ)) ≠ 0 := by
      apply Nat.cast_ne_zero.mpr
      omega
    have hlin : HasDerivAt (fun y : ℝ => 2 * ((((j + 1 : ℕ)) : ℝ)) * y)
        (2 * ((((j + 1 : ℕ)) : ℝ))) y := by
      have h := (hasDerivAt_id y).const_mul (2 * ((((j + 1 : ℕ)) : ℝ)))
      simpa using h
    have hsin := hlin.sin
    have hmul := hsin.const_mul (r ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2))
    have heq_fun : (fun y => r ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2) *
        Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y)) =
        (fun y => r ^ (j + 1) * Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * y) /
          ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
      funext y
      ring
    rw [heq_fun] at hmul
    have heq_deriv : (r ^ (j + 1) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) *
        (Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) * (2 * ((((j + 1 : ℕ)) : ℝ)))) =
        2 * r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y) /
          ((((j + 1 : ℕ)) : ℝ)) := by
      field_simp
    rw [heq_deriv] at hmul
    exact hmul
  have hbound : ∀ j : ℕ, ∀ y : ℝ,
      ‖auxAr_deriv_term r y j‖ ≤ 2 * r ^ (j + 1) := by
    intro j y
    have hcos : |Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| ≤ 1 :=
      Real.abs_cos_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ)) :=
      Nat.cast_pos.mpr (Nat.succ_pos j)
    have hle1 : (1 : ℝ) ≤ ((((j + 1 : ℕ)) : ℝ)) := by
      have h : (1 : ℕ) ≤ j + 1 := Nat.succ_le_succ (Nat.zero_le j)
      exact_mod_cast h
    have hdiv : (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ)) ≤ 1 := (div_le_one hpos).mpr hle1
    have hnn : (0 : ℝ) ≤ 2 * r ^ (j + 1) := by positivity
    unfold auxAr_deriv_term
    rw [Real.norm_eq_abs, abs_div, abs_mul, abs_mul]
    have habs2 : |((((j + 1 : ℕ)) : ℝ))| = ((((j + 1 : ℕ)) : ℝ)) := abs_of_pos hpos
    rw [habs2]
    have hr_abs : |r ^ (j + 1)| = r ^ (j + 1) := abs_of_nonneg (pow_nonneg hr0 _)
    rw [hr_abs, show |(2 : ℝ)| = 2 from abs_of_pos (by norm_num)]
    calc 2 * r ^ (j + 1) * |Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y)| /
          ((((j + 1 : ℕ)) : ℝ))
        = (2 * r ^ (j + 1) * |Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * y)|) *
          (1 / ((((j + 1 : ℕ)) : ℝ))) := by ring
      _ ≤ (2 * r ^ (j + 1) * 1) * 1 := by
          apply mul_le_mul _ hdiv (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = 2 * r ^ (j + 1) := by ring
  have hmain := hasDerivAt_tsum hu hterm hbound (auxAr_summable hr0 hr1 x) x
  have efun : (fun z => ∑' j : ℕ, auxAr_term r z j) = auxAr r := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

private def auxZ (r x : ℝ) : ℂ := ⟨r * Real.cos (2 * x), r * Real.sin (2 * x)⟩

private theorem auxZ_normSq (r x : ℝ) : Complex.normSq (auxZ r x) = r ^ 2 := by
  unfold auxZ
  rw [Complex.normSq_apply]
  have h : Real.cos (2 * x) ^ 2 + Real.sin (2 * x) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  calc (r * Real.cos (2 * x)) * (r * Real.cos (2 * x)) +
        (r * Real.sin (2 * x)) * (r * Real.sin (2 * x))
      = r ^ 2 * (Real.cos (2 * x) ^ 2 + Real.sin (2 * x) ^ 2) := by ring
    _ = r ^ 2 * 1 := by rw [h]
    _ = r ^ 2 := by ring

private theorem auxZ_norm_lt_one {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    ‖auxZ r x‖ < 1 := by
  have hsq : ‖auxZ r x‖ ^ 2 < 1 := by
    rw [Complex.sq_norm, auxZ_normSq]
    nlinarith [hr0, hr1, sq_nonneg r]
  exact (sq_lt_one_iff₀ (norm_nonneg _)).mp hsq

private theorem auxZ_pow_re_im (r x : ℝ) (k : ℕ) :
    ((auxZ r x) ^ k).re = r ^ k * Real.cos ((k : ℝ) * (2 * x)) ∧
      ((auxZ r x) ^ k).im = r ^ k * Real.sin ((k : ℝ) * (2 * x)) := by
  induction k with
  | zero =>
    simp [auxZ, pow_zero]
  | succ k ih =>
    have hz_re : (auxZ r x).re = r * Real.cos (2 * x) := rfl
    have hz_im : (auxZ r x).im = r * Real.sin (2 * x) := rfl
    have hpow : (auxZ r x) ^ (k + 1) = (auxZ r x) ^ k * auxZ r x := pow_succ _ _
    have hcast : (((k + 1 : ℕ)) : ℝ) * (2 * x) = (k : ℝ) * (2 * x) + 2 * x := by
      push_cast
      ring
    rw [hpow, Complex.mul_re, Complex.mul_im, ih.1, ih.2, hz_re, hz_im, hcast,
      Real.cos_add, Real.sin_add]
    have hpow_succ : r ^ (k + 1) = r ^ k * r := pow_succ _ _
    rw [hpow_succ]
    constructor <;> ring

private theorem auxZ_one_sub_normSq (r x : ℝ) :
    Complex.normSq (1 - auxZ r x) = (1 - r) ^ 2 + 4 * r * Real.sin x ^ 2 := by
  have hre : (1 - auxZ r x).re = 1 - r * Real.cos (2 * x) := by
    simp [auxZ]
  have him : (1 - auxZ r x).im = -(r * Real.sin (2 * x)) := by
    simp [auxZ]
  have hcos2 : Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2 := by
    have h1 := Real.cos_two_mul x
    have h2 := Real.sin_sq_add_cos_sq x
    linarith
  have htrig : Real.cos (2 * x) ^ 2 + Real.sin (2 * x) ^ 2 = 1 :=
    Real.cos_sq_add_sin_sq _
  rw [Complex.normSq_apply, hre, him]
  linear_combination r ^ 2 * htrig + (-2 * r) * hcos2

private theorem auxAr_deriv_eq_log {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    (∑' j : ℕ, auxAr_deriv_term r x j) =
      -Real.log ((1 - r) ^ 2 + 4 * r * Real.sin x ^ 2) := by
  set z : ℂ := auxZ r x with hzdef
  have hz : ‖z‖ < 1 := auxZ_norm_lt_one hr0 hr1 x
  have hcomplex := Complex.hasSum_taylorSeries_neg_log' hz
  have hre := Complex.hasSum_re hcomplex
  have hterm_eq : ∀ j : ℕ,
      (((z ^ (j + 1) / ((j : ℂ) + 1))).re) =
        r ^ (j + 1) * Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) /
          ((((j + 1 : ℕ)) : ℝ)) := by
    intro j
    have hcast1 : ((j : ℂ) + 1) = ((((j + 1 : ℕ)) : ℂ)) := by
      rw [Nat.cast_add, Nat.cast_one]
    have hcast2 : ((((j + 1 : ℕ)) : ℂ)) = (((((j + 1 : ℕ)) : ℝ)) : ℂ) :=
      (Complex.ofReal_natCast _).symm
    rw [hcast1, hcast2, Complex.div_ofReal_re]
    have hpow := (auxZ_pow_re_im r x (j + 1)).1
    rw [hpow]
    have hang : ((((j + 1 : ℕ)) : ℝ)) * (2 * x) =
        2 * ((((j + 1 : ℕ)) : ℝ)) * x := by ring
    rw [hang]
  have htsum_re := hre.tsum_eq
  have htsum_real : (∑' j : ℕ, r ^ (j + 1) *
      Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) =
      (-Complex.log (1 - z)).re := by
    have hcongr : (fun j : ℕ => r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) =
        (fun j : ℕ => ((z ^ (j + 1) / ((j : ℂ) + 1))).re) := by
      funext j
      exact (hterm_eq j).symm
    rw [hcongr]
    exact htsum_re
  have hderiv_congr : (fun j : ℕ => auxAr_deriv_term r x j) =
      (fun j : ℕ => 2 * (r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ)))) := by
    funext j
    unfold auxAr_deriv_term
    ring
  have htsum_deriv : (∑' j : ℕ, auxAr_deriv_term r x j) =
      2 * (∑' j : ℕ, r ^ (j + 1) *
        Real.cos (2 * ((((j + 1 : ℕ)) : ℝ)) * x) / ((((j + 1 : ℕ)) : ℝ))) := by
    rw [hderiv_congr, tsum_mul_left]
  rw [htsum_deriv, htsum_real]
  have hre_neg : (-Complex.log (1 - z)).re = -Real.log ‖1 - z‖ := by
    rw [Complex.neg_re, Complex.log_re]
  rw [hre_neg]
  have hlog : Real.log (‖1 - z‖ ^ 2) = 2 * Real.log ‖1 - z‖ := Real.log_pow _ _
  have hnorm : ‖1 - z‖ ^ 2 = (1 - r) ^ 2 + 4 * r * Real.sin x ^ 2 := by
    rw [Complex.sq_norm, auxZ_one_sub_normSq]
  calc 2 * -Real.log ‖1 - z‖ = -Real.log (‖1 - z‖ ^ 2) := by
        rw [hlog]
        ring
    _ = -Real.log ((1 - r) ^ 2 + 4 * r * Real.sin x ^ 2) := by rw [hnorm]

private def auxA_fourier (x : ℝ) : ℝ := ∑' j : ℕ, chapter9SineFourierTwoTerm x j

private theorem auxAr_tendsto (x : ℝ) :
    Filter.Tendsto (fun r => auxAr r x) (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (auxA_fourier x)) := by
  have hbound : Summable (fun j : ℕ => (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2)) :=
    aux_one_div_sq_summable
  have hab : ∀ j : ℕ, Filter.Tendsto (fun r => auxAr_term r x j)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (chapter9SineFourierTwoTerm x j)) := by
    intro j
    have hpow : Filter.Tendsto (fun r : ℝ => r ^ (j + 1)) (nhds (1 : ℝ)) (nhds 1) := by
      have hcont : ContinuousAt (fun r : ℝ => r ^ (j + 1)) 1 :=
        continuousAt_id.pow _
      simpa using hcont.tendsto
    have hpowW : Filter.Tendsto (fun r : ℝ => r ^ (j + 1))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 1) :=
      hpow.mono_left nhdsWithin_le_nhds
    have hmul := hpowW.mul_const (chapter9SineFourierTwoTerm x j)
    have hone : (1 : ℝ) * chapter9SineFourierTwoTerm x j =
        chapter9SineFourierTwoTerm x j := one_mul _
    rw [hone] at hmul
    have heq : (fun r => r ^ (j + 1) * chapter9SineFourierTwoTerm x j) =
        (fun r => auxAr_term r x j) := by
      funext r
      unfold auxAr_term chapter9SineFourierTwoTerm
      simp only
      ring
    rwa [heq] at hmul
  have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hIooW : Set.Ioo 0 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin_of_mem_nhds hIoo
  have hIioW : Set.Iio (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    self_mem_nhdsWithin
  have h_bound : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ j : ℕ, ‖auxAr_term r x j‖ ≤ (1 : ℝ) / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
    filter_upwards [hIooW, hIioW] with r hrIoo hrIio j
    have hr0 : 0 ≤ r := le_of_lt (Set.mem_Ioo.mp hrIoo).1
    have hr1 : r ≤ 1 := le_of_lt hrIio
    have hpow_le : r ^ (j + 1) ≤ 1 := pow_le_one₀ hr0 hr1
    have hpow_nn : (0 : ℝ) ≤ r ^ (j + 1) := pow_nonneg hr0 _
    have hsin : |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| ≤ 1 :=
      Real.abs_sin_le_one _
    have hpos : (0 : ℝ) < ((((j + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      exact Nat.cast_pos.mpr (Nat.succ_pos j)
    unfold auxAr_term
    rw [Real.norm_eq_abs, abs_div, abs_mul]
    have habs2 : |((((j + 1 : ℕ)) : ℝ) ^ 2)| = ((((j + 1 : ℕ)) : ℝ) ^ 2) :=
      abs_of_pos hpos
    rw [habs2, abs_of_nonneg hpow_nn]
    calc r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)| /
          ((((j + 1 : ℕ)) : ℝ) ^ 2)
        = (r ^ (j + 1) * |Real.sin (2 * ((((j + 1 : ℕ)) : ℝ)) * x)|) *
          (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by ring
      _ ≤ (1 * 1) * (1 / ((((j + 1 : ℕ)) : ℝ) ^ 2)) := by
          apply mul_le_mul _ le_rfl (by positivity) (by positivity)
          exact mul_le_mul hpow_le hsin (by positivity) (by positivity)
      _ = 1 / ((((j + 1 : ℕ)) : ℝ) ^ 2) := by ring
  have hmain := tendsto_tsum_of_dominated_convergence hbound hab h_bound
  have efun1 : (fun r => ∑' j : ℕ, auxAr_term r x j) = (fun r => auxAr r x) := by
    funext r
    rfl
  have efun2 : (∑' j : ℕ, chapter9SineFourierTwoTerm x j) = auxA_fourier x := rfl
  rw [efun1, efun2] at hmain
  exact hmain

private theorem aux_sin_ge_sin_a {a b : ℝ} (ha0 : 0 < a)
    (hb1 : b < Real.pi / 2) {x : ℝ} (hx : x ∈ Set.Ioo a b) :
    Real.sin a ≤ Real.sin x := by
  have hx1 : a < x := (Set.mem_Ioo.mp hx).1
  have hx2 : x < b := (Set.mem_Ioo.mp hx).2
  have h1 : -(Real.pi / 2) ≤ a := by linarith [Real.pi_pos]
  have h2 : x ≤ Real.pi / 2 := le_of_lt (lt_trans hx2 hb1)
  have h3 : a ≤ x := le_of_lt hx1
  exact Real.sin_le_sin_of_le_of_le_pi_div_two h1 h2 h3

private def auxAr_deriv (r x : ℝ) : ℝ := ∑' j : ℕ, auxAr_deriv_term r x j

private def auxA_deriv_lim (x : ℝ) : ℝ := -Real.log (4 * Real.sin x ^ 2)

private theorem auxAr_deriv_tendstoUniformlyOn_Ioo {a b : ℝ} (ha0 : 0 < a)
    (hab : a < b) (hb1 : b < Real.pi / 2) :
    TendstoUniformlyOn (fun r x => auxAr_deriv r x) auxA_deriv_lim
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (Set.Ioo a b) := by
  have ha_pi : a < Real.pi := by linarith [Real.pi_pos]
  have hsin_a_pos : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha0 ha_pi
  have hsin_a_nn : (0 : ℝ) ≤ Real.sin a := le_of_lt hsin_a_pos
  set m : ℝ := 2 * Real.sin a ^ 2 with hmdef
  have hmpos : 0 < m := by
    unfold m
    have hsq : 0 < Real.sin a ^ 2 := pow_pos hsin_a_pos 2
    linarith
  set M : ℝ := 5 with hMdef
  have hsub : Set.Icc m M ⊆ {0}ᶜ := by
    intro y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    have hy1 : m ≤ y := (Set.mem_Icc.mp hy).1
    have hpos : (0 : ℝ) < y := lt_of_lt_of_le hmpos hy1
    exact ne_of_gt hpos
  have hcont : ContinuousOn Real.log (Set.Icc m M) :=
    Real.continuousOn_log.mono hsub
  have hunif : UniformContinuousOn Real.log (Set.Icc m M) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hcont
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ := (Metric.uniformContinuousOn_iff.mp hunif) ε hε
  have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
  have hIooW : Set.Ioo 0 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin_of_mem_nhds hIoo
  have hIioW : Set.Iio (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    self_mem_nhdsWithin
  have hHalf : Set.Ioo (1 / 2 : ℝ) 2 ∈ nhds (1 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hHalfW : Set.Ioo (1 / 2 : ℝ) 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
    mem_nhdsWithin_of_mem_nhds hHalf
  have htendsto_id : Filter.Tendsto id (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (1 : ℝ)) :=
    continuousWithinAt_id.tendsto
  have hcont_abs : ContinuousAt (fun r : ℝ => |1 - r|) 1 := by fun_prop
  have htendsto_abs : Filter.Tendsto (fun r : ℝ => |1 - r|)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds 0) := by
    have h : Filter.Tendsto (fun r : ℝ => |1 - r|)
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds |1 - 1|) :=
      hcont_abs.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have hmem_delta : Set.Iio (δ / 5) ∈ nhds (0 : ℝ) := by
    apply Iio_mem_nhds
    linarith
  have hdelta : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), |1 - r| < δ / 5 :=
    htendsto_abs.eventually hmem_delta
  filter_upwards [hIooW, hIioW, hHalfW, hdelta] with r hrIoo hrIio hrHalf hrδ x hx
  have hr0 : (0 : ℝ) ≤ r := le_of_lt (Set.mem_Ioo.mp hrIoo).1
  have hr1 : r < 1 := hrIio
  have hrhalf : (1 / 2 : ℝ) < r := (Set.mem_Ioo.mp hrHalf).1
  have hrhalf_le : (1 / 2 : ℝ) ≤ r := le_of_lt hrhalf
  have hr_le1 : r ≤ 1 := le_of_lt hr1
  have hclosed : auxAr_deriv r x = -Real.log ((1 - r) ^ 2 + 4 * r * Real.sin x ^ 2) := by
    unfold auxAr_deriv
    exact auxAr_deriv_eq_log hr0 hr1 x
  have hx1 : a < x := (Set.mem_Ioo.mp hx).1
  have hx2 : x < b := (Set.mem_Ioo.mp hx).2
  have hsin_ge : Real.sin a ≤ Real.sin x := aux_sin_ge_sin_a ha0 hb1 hx
  have hsin_x_pos : 0 < Real.sin x := by
    have hx0 : (0 : ℝ) < x := lt_trans ha0 hx1
    have hxpi : x < Real.pi := by linarith [Real.pi_pos]
    exact Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  have hsin_x_nn : (0 : ℝ) ≤ Real.sin x := le_of_lt hsin_x_pos
  have hsq_ge : Real.sin a ^ 2 ≤ Real.sin x ^ 2 :=
    pow_le_pow_left₀ hsin_a_nn hsin_ge 2
  have hsq_x_nn : (0 : ℝ) ≤ Real.sin x ^ 2 := sq_nonneg _
  have hsq_x_le1 : Real.sin x ^ 2 ≤ 1 := by
    have h1 := Real.abs_sin_le_one x
    have h2 := abs_le.mp h1
    nlinarith [h2.1, h2.2, sq_nonneg (Real.sin x)]
  have hsq_a_le1 : Real.sin a ^ 2 ≤ 1 := by
    have h1 := Real.abs_sin_le_one a
    have h2 := abs_le.mp h1
    nlinarith [h2.1, h2.2, sq_nonneg (Real.sin a)]
  have h1r_nn : (0 : ℝ) ≤ 1 - r := by linarith
  have h1r_le1 : 1 - r ≤ 1 := by linarith
  have h1r_sq_le1 : (1 - r) ^ 2 ≤ 1 := pow_le_one₀ h1r_nn h1r_le1
  have h1r_sq_nn : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
  set u : ℝ := 4 * Real.sin x ^ 2 with hudef
  set ur : ℝ := (1 - r) ^ 2 + 4 * r * Real.sin x ^ 2 with hurdef
  have hu_mem : u ∈ Set.Icc m M := by
    constructor
    · unfold m u
      nlinarith [hsq_ge, hsq_x_nn, hsq_a_le1]
    · unfold M u
      nlinarith [hsq_x_le1, hsq_x_nn]
  have hur_mem : ur ∈ Set.Icc m M := by
    constructor
    · unfold m ur
      have h1 : (0 : ℝ) ≤ (1 - r) ^ 2 := h1r_sq_nn
      have h2 : 2 * Real.sin a ^ 2 ≤ 4 * r * Real.sin x ^ 2 := by
        have hmul : (1 / 2 : ℝ) * Real.sin a ^ 2 ≤ r * Real.sin x ^ 2 := by
          apply mul_le_mul hrhalf_le hsq_ge (sq_nonneg _) (by linarith)
        linarith
      linarith
    · unfold M ur
      have h1 : (1 - r) ^ 2 ≤ 1 := h1r_sq_le1
      have h2 : 4 * r * Real.sin x ^ 2 ≤ 4 := by
        have hr_nn : (0 : ℝ) ≤ r := hr0
        nlinarith [hr_le1, hsq_x_le1, hsq_x_nn, hr_nn, sq_nonneg r]
      linarith
  have hdiff_eq : u - ur = (1 - r) * (4 * Real.sin x ^ 2 - (1 - r)) := by
    unfold u ur
    ring
  have hfactor_le5 : |4 * Real.sin x ^ 2 - (1 - r)| ≤ 5 := by
    rw [abs_le]
    constructor <;> nlinarith [hsq_x_nn, hsq_x_le1, h1r_nn, h1r_le1]
  have hdiff_le : |u - ur| ≤ 5 * |1 - r| := by
    rw [hdiff_eq, abs_mul]
    calc |1 - r| * |4 * Real.sin x ^ 2 - (1 - r)|
        ≤ |1 - r| * 5 := mul_le_mul_of_nonneg_left hfactor_le5 (abs_nonneg _)
      _ = 5 * |1 - r| := by ring
  have hdist_lt : dist u ur < δ := by
    rw [Real.dist_eq]
    calc |u - ur| ≤ 5 * |1 - r| := hdiff_le
      _ < 5 * (δ / 5) := by
          apply mul_lt_mul_of_pos_left hrδ (by norm_num)
      _ = δ := by ring
  have hlog_dist : dist (Real.log u) (Real.log ur) < ε := hδ _ hu_mem _ hur_mem hdist_lt
  have hgoal_eq : dist (auxA_deriv_lim x) (auxAr_deriv r x) =
      dist (Real.log u) (Real.log ur) := by
    rw [hclosed]
    unfold auxA_deriv_lim
    rw [Real.dist_eq, Real.dist_eq]
    have heq : (-Real.log u) - (-Real.log ur) =
        -(Real.log u - Real.log ur) := by ring
    rw [heq, abs_neg]
  rw [hgoal_eq]
  exact hlog_dist

private theorem auxA_fourier_hasDerivAt {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt auxA_fourier (auxA_deriv_lim x₀) x₀ := by
  have hx0_pos : 0 < x₀ := (Set.mem_Ioo.mp hx₀).1
  have hx0_lt : x₀ < Real.pi / 2 := (Set.mem_Ioo.mp hx₀).2
  set a : ℝ := x₀ / 2 with hadef
  set b : ℝ := (x₀ + Real.pi / 2) / 2 with hbdef
  have ha0 : 0 < a := by unfold a; linarith
  have hab : a < b := by unfold a b; linarith [Real.pi_pos]
  have hb1 : b < Real.pi / 2 := by unfold b; linarith
  have hax : a < x₀ := by unfold a; linarith
  have hxb : x₀ < b := by unfold b; linarith
  have hxmem : x₀ ∈ Set.Ioo a b := ⟨hax, hxb⟩
  have hf' : TendstoUniformlyOn (fun r x => auxAr_deriv r x) auxA_deriv_lim
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (Set.Ioo a b) :=
    auxAr_deriv_tendstoUniformlyOn_Ioo ha0 hab hb1
  have hf : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ x : ℝ, x ∈ Set.Ioo a b → HasDerivAt (auxAr r) (auxAr_deriv r x) x := by
    have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) :=
      Ioo_mem_nhds (by norm_num) (by norm_num)
    have hIooW : Set.Ioo 0 2 ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
      mem_nhdsWithin_of_mem_nhds hIoo
    have hIioW : Set.Iio (1 : ℝ) ∈ nhdsWithin (1 : ℝ) (Set.Iio 1) :=
      self_mem_nhdsWithin
    filter_upwards [hIooW, hIioW] with r hrIoo hrIio x hx
    have hr0 : (0 : ℝ) ≤ r := le_of_lt (Set.mem_Ioo.mp hrIoo).1
    have hr1 : r < 1 := hrIio
    exact auxAr_hasDerivAt hr0 hr1 x
  have hfg : ∀ x : ℝ, x ∈ Set.Ioo a b →
      Filter.Tendsto (fun r => auxAr r x) (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (auxA_fourier x)) :=
    fun x _ => auxAr_tendsto x
  exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo hf' hf hfg hxmem

private theorem aux_logterm_tendsto_nhdsGT :
    Filter.Tendsto chapter9Entry20LogTerm (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have ha : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hcont : Continuous (fun x : ℝ => x ^ 2 / 2 * Real.log 2) :=
      ((continuous_id'.pow 2).div_const 2).mul continuous_const
    have h : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((0 : ℝ) ^ 2 / 2 * Real.log 2)) :=
      (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using h
  have hb : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (show (0 : ℝ) < 2 by norm_num)
    simp only [Real.rpow_two] at h
    have h2 := h.div_const (2 : ℝ)
    have heq : (fun x : ℝ => x ^ 2 / 2 * Real.log x) =
        (fun x : ℝ => Real.log x * x ^ 2 / 2) := by
      funext x
      ring
    rw [heq]
    simpa using h2
  have hc : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2 * Real.log (Real.sinc x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have hc0 : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hcont : Continuous (fun x : ℝ => x ^ 2 / 2) :=
        (continuous_id'.pow 2).div_const 2
      have h : Filter.Tendsto (fun x : ℝ => x ^ 2 / 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds ((0 : ℝ) ^ 2 / 2)) :=
        (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
      simpa using h
    have hc1 : Filter.Tendsto (fun x : ℝ => Real.log (Real.sinc x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hsinc : Filter.Tendsto Real.sinc
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 1) := by
        have h : Filter.Tendsto Real.sinc (nhds (0 : ℝ)) (nhds (Real.sinc 0)) :=
          Real.continuous_sinc.tendsto 0
        rw [Real.sinc_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      have hlog : Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds 0) := by
        have h : Filter.Tendsto Real.log (nhds (1 : ℝ)) (nhds (Real.log 1)) :=
          (Real.continuousAt_log one_ne_zero).tendsto
        simpa using h
      exact hlog.comp hsinc
    have hmul := hc0.mul hc1
    simpa using hmul
  have hsum : Filter.Tendsto
      (fun x : ℝ => (x ^ 2 / 2 * Real.log 2 + x ^ 2 / 2 * Real.log x) +
        x ^ 2 / 2 * Real.log (Real.sinc x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h := (ha.add hb).add hc
    simpa using h
  have heq : chapter9Entry20LogTerm =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun x : ℝ => (x ^ 2 / 2 * Real.log 2 + x ^ 2 / 2 * Real.log x) +
        x ^ 2 / 2 * Real.log (Real.sinc x)) := by
    have hlt : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), x < Real.pi :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hpi)
    have hsinc_ne : ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), Real.sinc x ≠ 0 := by
      have h : ∀ᶠ x in nhds (0 : ℝ), Real.sinc x ≠ 0 := by
        have hs : Filter.Tendsto Real.sinc (nhds (0 : ℝ)) (nhds 1) := by
          have h : Filter.Tendsto Real.sinc (nhds (0 : ℝ)) (nhds (Real.sinc 0)) :=
            Real.continuous_sinc.tendsto 0
          rwa [Real.sinc_zero] at h
        exact hs.eventually (eventually_ne_nhds one_ne_zero)
      exact eventually_nhdsWithin_of_eventually_nhds h
    filter_upwards [self_mem_nhdsWithin, hlt, hsinc_ne] with x hx0 hxpi hxne
    have hxpos : (0 : ℝ) < x := hx0
    have hxne0 : x ≠ 0 := ne_of_gt hxpos
    have hsin_pos : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hxpos hxpi
    have h2sin_pos : (0 : ℝ) < 2 * Real.sin x := by linarith
    have habs : |2 * Real.sin x| = 2 * Real.sin x := abs_of_pos h2sin_pos
    have hsinc_eq : x * Real.sinc x = Real.sin x := by
      rw [Real.sinc_of_ne_zero hxne0]
      field_simp
    have hx_sinc_ne : x * Real.sinc x ≠ 0 := mul_ne_zero hxne0 hxne
    have e : (2 : ℝ) * Real.sin x = 2 * (x * Real.sinc x) := by rw [hsinc_eq]
    have hsplit : Real.log (2 * Real.sin x) =
        Real.log 2 + (Real.log x + Real.log (Real.sinc x)) := by
      rw [e, Real.log_mul (by norm_num) hx_sinc_ne, Real.log_mul hxne0 hxne]
    have hif : chapter9Entry20LogTerm x =
        x ^ 2 / 2 * (Real.log 2 + (Real.log x + Real.log (Real.sinc x))) := by
      unfold chapter9Entry20LogTerm
      simp only [hxne0, ite_false, habs, hsplit]
    rw [hif]
    ring
  exact Filter.Tendsto.congr' heq.symm hsum

private theorem aux_sin_pos_of_Ioo {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin x₀ := by
  have hx0_pos : 0 < x₀ := (Set.mem_Ioo.mp hx₀).1
  have hx0_lt : x₀ < Real.pi := by
    have h := (Set.mem_Ioo.mp hx₀).2
    linarith [Real.pi_pos]
  exact Real.sin_pos_of_pos_of_lt_pi hx0_pos hx0_lt

private theorem aux_logterm_eventuallyEq {x₀ : ℝ} (hx0_ne : x₀ ≠ 0)
    (h2sin_pos : (0 : ℝ) < 2 * Real.sin x₀) :
    chapter9Entry20LogTerm =ᶠ[nhds x₀]
      fun x => x ^ 2 / 2 * Real.log (2 * Real.sin x) := by
  have hne : ∀ᶠ x in nhds x₀, x ≠ 0 := eventually_ne_nhds hx0_ne
  have hpos : ∀ᶠ x in nhds x₀, (0 : ℝ) < 2 * Real.sin x := by
    have hsin : ContinuousAt Real.sin x₀ := Real.continuous_sin.continuousAt
    have hcont : ContinuousAt (fun x : ℝ => 2 * Real.sin x) x₀ :=
      hsin.const_mul 2
    exact hcont.tendsto.eventually (eventually_gt_nhds h2sin_pos)
  filter_upwards [hne, hpos] with x hxne hxpos
  unfold chapter9Entry20LogTerm
  simp only [hxne, ite_false, abs_of_pos hxpos]

private theorem aux_logterm_smooth_hasDerivAt {x₀ : ℝ}
    (h2sin_ne : (2 : ℝ) * Real.sin x₀ ≠ 0) :
    HasDerivAt (fun x => x ^ 2 / 2 * Real.log (2 * Real.sin x))
      (x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀))
      x₀ := by
  have hsin_ne : Real.sin x₀ ≠ 0 := fun h => h2sin_ne (by rw [h, mul_zero])
  have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x₀ x₀ := by
    have hpow : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x₀) x₀ := by
      have h := hasDerivAt_pow 2 x₀
      simpa [pow_one] using h
    have hdiv := hpow.div_const (2 : ℝ)
    have heq : (2 * x₀) / 2 = x₀ := by ring
    rw [heq] at hdiv
    exact hdiv
  have h2 : HasDerivAt (fun x : ℝ => 2 * Real.sin x) (2 * Real.cos x₀) x₀ :=
    (Real.hasDerivAt_sin x₀).const_mul 2
  have h3 : HasDerivAt (fun x : ℝ => Real.log (2 * Real.sin x))
      ((2 * Real.cos x₀) / (2 * Real.sin x₀)) x₀ := h2.log h2sin_ne
  have hmul : HasDerivAt (fun x : ℝ => x ^ 2 / 2 * Real.log (2 * Real.sin x))
      (x₀ * Real.log (2 * Real.sin x₀) +
        x₀ ^ 2 / 2 * ((2 * Real.cos x₀) / (2 * Real.sin x₀))) x₀ :=
    h1.mul h3
  have heq : x₀ * Real.log (2 * Real.sin x₀) +
      x₀ ^ 2 / 2 * ((2 * Real.cos x₀) / (2 * Real.sin x₀)) =
      x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀) := by
    congr 1
    congr 1
    field_simp
  rw [heq] at hmul
  exact hmul

private theorem aux_logterm_hasDerivAt {x₀ : ℝ} (hx0_ne : x₀ ≠ 0)
    (h2sin_pos : (0 : ℝ) < 2 * Real.sin x₀) :
    HasDerivAt chapter9Entry20LogTerm
      (x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀))
      x₀ :=
  (aux_logterm_smooth_hasDerivAt (ne_of_gt h2sin_pos)).congr_of_eventuallyEq
    (aux_logterm_eventuallyEq hx0_ne h2sin_pos)

private theorem auxA_deriv_lim_eq (x₀ : ℝ) :
    auxA_deriv_lim x₀ = -2 * Real.log (2 * Real.sin x₀) := by
  unfold auxA_deriv_lim
  have hsq : (4 : ℝ) * Real.sin x₀ ^ 2 = (2 * Real.sin x₀) ^ 2 := by ring
  rw [hsq, Real.log_pow]
  ring

private def auxB_fourier (x : ℝ) : ℝ :=
  ∑' j : ℕ, chapter9CosineFourierThreeTerm x j

private def auxG (x : ℝ) : ℝ :=
  chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
    (1 / 4 : ℝ) * auxB_fourier x - chapter9ZetaThree / 4

private theorem auxG_hasDerivAt {x₀ : ℝ}
    (hx₀ : x₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    HasDerivAt auxG ((x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀)) x₀ := by
  have hx0_ne : x₀ ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hx₀).1
  have h2sin_pos : (0 : ℝ) < 2 * Real.sin x₀ := by
    have h := aux_sin_pos_of_Ioo hx₀
    linarith
  have hlog := aux_logterm_hasDerivAt hx0_ne h2sin_pos
  have hA : HasDerivAt auxA_fourier (auxA_deriv_lim x₀) x₀ :=
    auxA_fourier_hasDerivAt hx₀
  have hid : HasDerivAt (fun x : ℝ => x / 2) ((1 : ℝ) / 2) x₀ := by
    have h := (hasDerivAt_id x₀).div_const (2 : ℝ)
    simpa using h
  have hleft : HasDerivAt (fun x : ℝ => x / 2 * auxA_fourier x)
      ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) x₀ :=
    hid.mul hA
  have hB : HasDerivAt auxB_fourier (-2 * auxA_fourier x₀) x₀ :=
    aux_cosine_hasDerivAt x₀
  have hB4 : HasDerivAt (fun x : ℝ => (1 / 4 : ℝ) * auxB_fourier x)
      ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀)) x₀ :=
    hB.const_mul (1 / 4 : ℝ)
  have hsum : HasDerivAt
      (fun x : ℝ => chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
        (1 / 4 : ℝ) * auxB_fourier x)
      ((x₀ * Real.log (2 * Real.sin x₀) + x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀)) +
        ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) +
        ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀))) x₀ :=
    (hlog.add hleft).add hB4
  have hconst : HasDerivAt (fun _ : ℝ => chapter9ZetaThree / 4) 0 x₀ :=
    hasDerivAt_const x₀ (chapter9ZetaThree / 4)
  have hfull : HasDerivAt auxG
      (((x₀ * Real.log (2 * Real.sin x₀) +
        x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀)) +
        ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) +
        ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀))) - 0) x₀ :=
    hsum.sub hconst
  have hval : (((x₀ * Real.log (2 * Real.sin x₀) +
      x₀ ^ 2 / 2 * (Real.cos x₀ / Real.sin x₀)) +
        ((1 : ℝ) / 2 * auxA_fourier x₀ + x₀ / 2 * auxA_deriv_lim x₀) +
        ((1 / 4 : ℝ) * (-2 * auxA_fourier x₀))) - 0) =
      (x₀ ^ 2 / 2) * (Real.cos x₀ / Real.sin x₀) := by
    rw [auxA_deriv_lim_eq x₀]
    ring
  rw [hval] at hfull
  exact hfull

private theorem aux_logterm_continuousOn_Icc {y : ℝ}
    (hy : y ≤ Real.pi / 2) :
    ContinuousOn chapter9Entry20LogTerm (Set.Icc 0 y) := by
  intro z hz
  by_cases hz0 : z = 0
  · subst hz0
    have h0 : chapter9Entry20LogTerm 0 = 0 := by
      unfold chapter9Entry20LogTerm
      simp
    rw [Metric.continuousWithinAt_iff', h0]
    intro ε hε
    have hlim := Metric.tendsto_nhds.mp aux_logterm_tendsto_nhdsGT ε hε
    rw [eventually_nhdsWithin_iff] at hlim ⊢
    filter_upwards [hlim] with x hx
    intro hxIcc
    by_cases hx0 : x = 0
    · subst hx0
      rw [h0, dist_self]
      exact hε
    · exact hx (Set.mem_Ioi.mpr (lt_of_le_of_ne' (Set.mem_Icc.mp hxIcc).1 hx0))
  · have hzpos : 0 < z := lt_of_le_of_ne' (Set.mem_Icc.mp hz).1 hz0
    have hzlt : z < Real.pi := by
      have h2 : z ≤ y := (Set.mem_Icc.mp hz).2
      linarith [Real.pi_pos]
    have hsin_pos : 0 < Real.sin z := Real.sin_pos_of_pos_of_lt_pi hzpos hzlt
    have h2sin_pos : (0 : ℝ) < 2 * Real.sin z := by linarith
    exact (aux_logterm_hasDerivAt hz0 h2sin_pos).continuousAt.continuousWithinAt

private theorem auxG_continuousOn_Icc {y : ℝ}
    (hy : y ≤ Real.pi / 2) :
    ContinuousOn auxG (Set.Icc 0 y) := by
  have hlog := aux_logterm_continuousOn_Icc hy
  have hA : ContinuousOn (fun x : ℝ => x / 2 * auxA_fourier x)
      (Set.Icc 0 y) := by
    have h1 : ContinuousOn (fun x : ℝ => x / 2) (Set.Icc 0 y) :=
      (continuous_id'.div_const 2).continuousOn
    have h2 : ContinuousOn auxA_fourier (Set.Icc 0 y) :=
      aux_sine_continuous.continuousOn
    exact h1.mul h2
  have hB : ContinuousOn (fun x : ℝ => (1 / 4 : ℝ) * auxB_fourier x)
      (Set.Icc 0 y) := by
    have h : ContinuousOn auxB_fourier (Set.Icc 0 y) :=
      aux_cosine_continuous.continuousOn
    have hc : ContinuousOn (fun _ : ℝ => (1 / 4 : ℝ)) (Set.Icc 0 y) :=
      continuousOn_const
    exact hc.mul h
  have hsum : ContinuousOn
      (fun x : ℝ => chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
        (1 / 4 : ℝ) * auxB_fourier x) (Set.Icc 0 y) :=
    (hlog.add hA).add hB
  have h : ContinuousOn
      (fun x : ℝ => (chapter9Entry20LogTerm x + x / 2 * auxA_fourier x +
        (1 / 4 : ℝ) * auxB_fourier x) - chapter9ZetaThree / 4)
      (Set.Icc 0 y) :=
    hsum.sub continuousOn_const
  exact h

/-- **A series in even powers of $\sin x$ involving $\zeta(3)$.** Let $x$ be a real number with
$|x| \le \pi/2$, let $M(x) = \frac{x^2}{2} \log|2\sin x|$ for $x \ne 0$ and $M(0) = 0$, and let
$\zeta(3) = \sum_{k=1}^{\infty} k^{-3}$. Then $|2\sin x| > 0$ if $x \ne 0$, the series
$\sum_{k=1}^{\infty} k^{-3}$,
$A(x) = \sum_{k=0}^{\infty} \frac{2^{2k} (k!)^2 \sin^{2k+2} x}{(2k+1)! \, (2k+2)^2}$,
$B(x) = \sum_{k=1}^{\infty} \frac{\sin 2kx}{k^2}$ and
$E(x) = \sum_{k=1}^{\infty} \frac{\cos 2kx}{k^3}$ are all summable, and
$A(x) = M(x) + \frac{x}{2} B(x) + \frac{1}{4} E(x) - \frac{\zeta(3)}{4}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry20_piseries1 (x : ℝ) (hx : |x| ≤ Real.pi / 2) :
    (x ≠ 0 → 0 < |2 * Real.sin x|) ∧
      Summable chapter9ZetaThreeTerm ∧
      Summable (chapter9Entry23FactorialTerm x) ∧
      Summable (chapter9SineFourierTwoTerm x) ∧
      Summable (chapter9CosineFourierThreeTerm x) ∧
      (∑' k : ℕ, chapter9Entry23FactorialTerm x k) =
        chapter9Entry20LogTerm x +
          x / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm x j +
          (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm x j -
          chapter9ZetaThree / 4 := by
  refine ⟨?_, aux_zetaThree_summable, aux_factorial_summable x,
    aux_sineTwo_summable x, aux_cosineThree_summable x, ?_⟩
  · intro hx0
    have hsin_ne : Real.sin x ≠ 0 := by
      rcases lt_or_gt_of_ne hx0 with hneg | hpos
      · have hpos : 0 < -x := neg_pos.mpr hneg
        have habs : |-x| ≤ Real.pi / 2 := by rwa [abs_neg]
        have hle : -x ≤ Real.pi / 2 := le_trans (le_abs_self _) habs
        have hlt : -x < Real.pi := by linarith [Real.pi_pos]
        have h := Real.sin_pos_of_pos_of_lt_pi hpos hlt
        rw [Real.sin_neg] at h
        intro hcon
        rw [hcon, neg_zero] at h
        exact lt_irrefl 0 h
      · have hle : x ≤ Real.pi / 2 := le_trans (le_abs_self _) hx
        have hlt : x < Real.pi := by linarith [Real.pi_pos]
        have h := Real.sin_pos_of_pos_of_lt_pi hpos hlt
        exact ne_of_gt h
    have hpos : 0 < |Real.sin x| := abs_pos.mpr hsin_ne
    have heq : |2 * Real.sin x| = 2 * |Real.sin x| := by
      rw [abs_mul]
      norm_num
    rw [heq]
    linarith
  · -- Series equality: both sides are even, so it suffices to prove it for `0 ≤ x`.
    have hcore : ∀ y : ℝ, 0 ≤ y → |y| ≤ Real.pi / 2 →
        (∑' k : ℕ, chapter9Entry23FactorialTerm y k) =
          chapter9Entry20LogTerm y +
            y / 2 * ∑' j : ℕ, chapter9SineFourierTwoTerm y j +
            (1 / 4 : ℝ) * ∑' j : ℕ, chapter9CosineFourierThreeTerm y j -
            chapter9ZetaThree / 4 := by
      intro y hy0 hy
      by_cases hy0' : y = 0
      · subst hy0'
        rw [aux_factorial_tsum_zero]
        exact aux_rhs_zero.symm
      · have hypos : 0 < y := lt_of_le_of_ne' hy0 hy0'
        have hy_le : y ≤ Real.pi / 2 := le_trans (le_abs_self y) hy
        have hF0 : auxF 0 = 0 := aux_factorial_tsum_zero
        have hG0 : auxG 0 = 0 := aux_rhs_zero
        have hcont : ContinuousOn (fun z => auxF z - auxG z) (Set.Icc 0 y) :=
          aux_factorial_continuous.continuousOn.sub
            (auxG_continuousOn_Icc hy_le)
        have hderiv : ∀ z ∈ Set.Ioo 0 y,
            HasDerivAt (fun z => auxF z - auxG z) 0 z := by
          intro z hz
          have hzIoo : z ∈ Set.Ioo 0 (Real.pi / 2) := by
            have h1 : 0 < z := (Set.mem_Ioo.mp hz).1
            have h2 : z < y := (Set.mem_Ioo.mp hz).2
            exact ⟨h1, lt_of_lt_of_le h2 hy_le⟩
          have hF := auxF_hasDerivAt hzIoo
          have hG := auxG_hasDerivAt hzIoo
          have h := hF.sub hG
          simp only [sub_self] at h
          exact h
        obtain ⟨c, _, hc⟩ :=
          exists_hasDerivAt_eq_slope (fun z => auxF z - auxG z) (fun _ => 0)
            hypos hcont hderiv
        simp only [hF0, hG0, sub_self (0 : ℝ), sub_zero (auxF y - auxG y)] at hc
        have hne : y - 0 ≠ 0 := ne_of_gt (by linarith)
        have h0 : (auxF y - auxG y) / (y - 0) = 0 := hc.symm
        rw [div_eq_zero_iff] at h0
        have hnum : auxF y - auxG y = 0 := h0.resolve_right hne
        have heq : auxF y = auxG y := sub_eq_zero.mp hnum
        exact heq
    by_cases hx0 : 0 ≤ x
    · exact hcore x hx0 hx
    · have hnx : 0 ≤ -x := le_of_lt (neg_pos.mpr (lt_of_not_ge hx0))
      have habs : |-x| ≤ Real.pi / 2 := by rwa [abs_neg]
      have h := hcore (-x) hnx habs
      rw [← aux_factorial_tsum_even x, ← aux_rhs_even x]
      exact h

end
end Entry20Piseries1
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
