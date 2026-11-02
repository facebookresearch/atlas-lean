/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 8, Entry 14

Closed form for ∫₀ˣ 1/(1+u¹⁰) du via arctan and log terms.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry14Qreflection
open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory
noncomputable section
def chapter8Entry14A (n : ℕ) (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, 1 / (1 + u ^ n)
def chapter8Entry14A10Closed (x : ℝ) : ℝ :=
  Real.arctan x / 5 +
    Real.sqrt (6 + 2 * Real.sqrt 5) / 20 *
      Real.arctan (x * Real.sqrt (6 + 2 * Real.sqrt 5) /
        (2 * (1 - x ^ 2))) +
    Real.sqrt (6 - 2 * Real.sqrt 5) / 20 *
      Real.arctan (x * Real.sqrt (6 - 2 * Real.sqrt 5) /
        (2 * (1 - x ^ 2))) +
    Real.sqrt (10 + 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + x * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + x ^ 2) /
        (1 - x * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + x ^ 2)) +
    Real.sqrt (10 - 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + x * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + x ^ 2) /
        (1 - x * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + x ^ 2))

private lemma sqrt5_sq : (Real.sqrt 5 : ℝ) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
private lemma sqrt5_pos : (0 : ℝ) < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
private lemma sqrt5_gt1 : (1 : ℝ) < Real.sqrt 5 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
private lemma sqrt5_lt3 : Real.sqrt 5 < 3 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
private lemma S1_sq : (Real.sqrt (6 + 2 * Real.sqrt 5)) ^ 2 = 6 + 2 * Real.sqrt 5 := by apply Real.sq_sqrt; have h := sqrt5_pos; linarith
private lemma S2_sq : (Real.sqrt (6 - 2 * Real.sqrt 5)) ^ 2 = 6 - 2 * Real.sqrt 5 := by apply Real.sq_sqrt; have h := sqrt5_lt3; linarith
private lemma T1_sq : (Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 = 10 + 2 * Real.sqrt 5 := by apply Real.sq_sqrt; have h := sqrt5_pos; linarith
private lemma T2_sq : (Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 = 10 - 2 * Real.sqrt 5 := by apply Real.sq_sqrt; have h := sqrt5_lt3; have h2 := sqrt5_pos; linarith
private lemma T1_pos : (0:ℝ) < Real.sqrt (10 + 2 * Real.sqrt 5) := by apply Real.sqrt_pos.mpr; have h := sqrt5_pos; linarith
private lemma T2_pos : (0:ℝ) < Real.sqrt (10 - 2 * Real.sqrt 5) := by apply Real.sqrt_pos.mpr; have h := sqrt5_lt3; linarith
private lemma T1_lt4 : Real.sqrt (10 + 2 * Real.sqrt 5) < 4 := by rw [Real.sqrt_lt' (by norm_num)]; have h := sqrt5_lt3; nlinarith
private lemma T2_lt4 : Real.sqrt (10 - 2 * Real.sqrt 5) < 4 := by rw [Real.sqrt_lt' (by norm_num)]; have h := sqrt5_pos; nlinarith
private lemma one_sub_sq_pos {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) : (0:ℝ) < 1 - y ^ 2 := by
  have h : y ^ 2 < 1 := by calc y ^ 2 < 1 ^ 2 := by apply sq_lt_sq' _ hy1; linarith
      _ = 1 := by ring
  linarith

private lemma term0_hd (y : ℝ) : HasDerivAt (fun t => Real.arctan t / 5) (1 / (5 * (1 + y ^ 2))) y := by
  have h := (Real.hasDerivAt_arctan y).div_const (5 : ℝ)
  have heq : (1 / (1 + y ^ 2)) / 5 = 1 / (5 * (1 + y ^ 2)) := by rw [div_div]; congr 1; ring
  rwa [heq] at h

private lemma term1_hd (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasDerivAt (fun t => Real.sqrt (6 + 2 * Real.sqrt 5) / 20 *
      Real.arctan (t * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - t ^ 2))))
      ((6 + 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4))) y := by
  have h1y : (1 : ℝ) - y ^ 2 ≠ 0 := by
    have h : y ^ 2 < 1 := by calc y ^ 2 < 1 ^ 2 := by apply sq_lt_sq' _ hy1; linarith
      _ = 1 := by ring
    linarith
  have h2 : (2 : ℝ) * (1 - y ^ 2) ≠ 0 := mul_ne_zero (by norm_num) h1y
  have hnum : HasDerivAt (fun t : ℝ => t * Real.sqrt (6 + 2 * Real.sqrt 5)) (Real.sqrt (6 + 2 * Real.sqrt 5)) y := by
    have h := (hasDerivAt_id y).mul_const (Real.sqrt (6 + 2 * Real.sqrt 5))
    simpa using h
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have hsub : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y :=
    HasDerivAt.const_sub (1 : ℝ) hpow
  have hden : HasDerivAt (fun t : ℝ => 2 * (1 - t ^ 2)) (2 * (-(2 * y))) y :=
    HasDerivAt.const_mul (2 : ℝ) hsub
  have hdiv : HasDerivAt (fun t : ℝ => t * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - t ^ 2)))
      ((Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2) y :=
    HasDerivAt.div hnum hden h2
  have harctan : HasDerivAt (fun t => Real.arctan (t * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - t ^ 2))))
      (1 / (1 + (y * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2) *
       ((Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2)) y :=
    HasDerivAt.arctan hdiv
  have hmul : HasDerivAt (fun t => Real.sqrt (6 + 2 * Real.sqrt 5) / 20 * Real.arctan (t * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - t ^ 2))))
      (Real.sqrt (6 + 2 * Real.sqrt 5) / 20 * (1 / (1 + (y * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2) *
       ((Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2))) y :=
    HasDerivAt.const_mul _ harctan
  have hA : ((Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 + 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2) =
      Real.sqrt (6 + 2 * Real.sqrt 5) / 2 * (1 + y ^ 2) / (1 - y ^ 2) ^ 2 := by
    have h3 : (1 - y ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h1y
    field_simp
    ring
  rw [hA] at hmul
  have hB : Real.sqrt (6 + 2 * Real.sqrt 5) / 20 * (1 / (1 + (y * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2) *
      (Real.sqrt (6 + 2 * Real.sqrt 5) / 2 * (1 + y ^ 2) / (1 - y ^ 2) ^ 2)) =
      (Real.sqrt (6 + 2 * Real.sqrt 5)) ^ 2 * (1 + y ^ 2) / (10 * (4 * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 + 2 * Real.sqrt 5)) ^ 2)) := by
    have h3 : (1 - y ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h1y
    have h4 : (1 : ℝ) + (y * Real.sqrt (6 + 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2 ≠ 0 := by positivity
    have h5 : (4 : ℝ) * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 + 2 * Real.sqrt 5)) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hB] at hmul
  have hS := S1_sq
  have hden_eq : 4 * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 + 2 * Real.sqrt 5)) ^ 2 = 4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4 := by
    conv_lhs => rw [hS]
    ring
  have hC : (Real.sqrt (6 + 2 * Real.sqrt 5)) ^ 2 * (1 + y ^ 2) / (10 * (4 * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 + 2 * Real.sqrt 5)) ^ 2)) =
      (6 + 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4)) := by
    rw [hden_eq, hS]
  rwa [hC] at hmul

private lemma term2_hd (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasDerivAt (fun t => Real.sqrt (6 - 2 * Real.sqrt 5) / 20 *
      Real.arctan (t * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - t ^ 2))))
      ((6 - 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4))) y := by
  have h1y : (1 : ℝ) - y ^ 2 ≠ 0 := by
    have h : y ^ 2 < 1 := by calc y ^ 2 < 1 ^ 2 := by apply sq_lt_sq' _ hy1; linarith
      _ = 1 := by ring
    linarith
  have h2 : (2 : ℝ) * (1 - y ^ 2) ≠ 0 := mul_ne_zero (by norm_num) h1y
  have hnum : HasDerivAt (fun t : ℝ => t * Real.sqrt (6 - 2 * Real.sqrt 5)) (Real.sqrt (6 - 2 * Real.sqrt 5)) y := by
    have h := (hasDerivAt_id y).mul_const (Real.sqrt (6 - 2 * Real.sqrt 5))
    simpa using h
  have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
  have hsub : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * y)) y :=
    HasDerivAt.const_sub (1 : ℝ) hpow
  have hden : HasDerivAt (fun t : ℝ => 2 * (1 - t ^ 2)) (2 * (-(2 * y))) y :=
    HasDerivAt.const_mul (2 : ℝ) hsub
  have hdiv : HasDerivAt (fun t : ℝ => t * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - t ^ 2)))
      ((Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2) y :=
    HasDerivAt.div hnum hden h2
  have harctan : HasDerivAt (fun t => Real.arctan (t * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - t ^ 2))))
      (1 / (1 + (y * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2) *
       ((Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2)) y :=
    HasDerivAt.arctan hdiv
  have hmul : HasDerivAt (fun t => Real.sqrt (6 - 2 * Real.sqrt 5) / 20 * Real.arctan (t * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - t ^ 2))))
      (Real.sqrt (6 - 2 * Real.sqrt 5) / 20 * (1 / (1 + (y * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2) *
       ((Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2))) y :=
    HasDerivAt.const_mul _ harctan
  have hA : ((Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (1 - y ^ 2)) - y * Real.sqrt (6 - 2 * Real.sqrt 5) * (2 * (-(2 * y)))) / (2 * (1 - y ^ 2)) ^ 2) =
      Real.sqrt (6 - 2 * Real.sqrt 5) / 2 * (1 + y ^ 2) / (1 - y ^ 2) ^ 2 := by
    have h3 : (1 - y ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h1y
    field_simp
    ring
  rw [hA] at hmul
  have hB : Real.sqrt (6 - 2 * Real.sqrt 5) / 20 * (1 / (1 + (y * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2) *
      (Real.sqrt (6 - 2 * Real.sqrt 5) / 2 * (1 + y ^ 2) / (1 - y ^ 2) ^ 2)) =
      (Real.sqrt (6 - 2 * Real.sqrt 5)) ^ 2 * (1 + y ^ 2) / (10 * (4 * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 - 2 * Real.sqrt 5)) ^ 2)) := by
    have h3 : (1 - y ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h1y
    have h4 : (1 : ℝ) + (y * Real.sqrt (6 - 2 * Real.sqrt 5) / (2 * (1 - y ^ 2))) ^ 2 ≠ 0 := by positivity
    have h5 : (4 : ℝ) * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 - 2 * Real.sqrt 5)) ^ 2 ≠ 0 := by positivity
    field_simp
    ring
  rw [hB] at hmul
  have hS := S2_sq
  have hden_eq : 4 * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 - 2 * Real.sqrt 5)) ^ 2 = 4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4 := by
    conv_lhs => rw [hS]
    ring
  have hC : (Real.sqrt (6 - 2 * Real.sqrt 5)) ^ 2 * (1 + y ^ 2) / (10 * (4 * (1 - y ^ 2) ^ 2 + y ^ 2 * (Real.sqrt (6 - 2 * Real.sqrt 5)) ^ 2)) =
      (6 - 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4)) := by
    rw [hden_eq, hS]
  rwa [hC] at hmul

private lemma term3_hd (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasDerivAt (fun t => Real.sqrt (10 + 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2) /
        (1 - t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2)))
      ((10 + 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4))) y := by
  have hnum : HasDerivAt (fun t : ℝ => 1 + t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2)
      (Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) y := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have hmul : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 + 2 * Real.sqrt 5)) (Real.sqrt (10 + 2 * Real.sqrt 5)) y := by
      have h := (hasDerivAt_id y).mul_const (Real.sqrt (10 + 2 * Real.sqrt 5))
      simpa using h
    have hdiv : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2) (Real.sqrt (10 + 2 * Real.sqrt 5) / 2) y :=
      HasDerivAt.div_const hmul (2 : ℝ)
    have hadd : HasDerivAt (fun t : ℝ => 1 + t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2) (Real.sqrt (10 + 2 * Real.sqrt 5) / 2) y :=
      HasDerivAt.const_add (1 : ℝ) hdiv
    exact HasDerivAt.add hadd hpow
  have hden : HasDerivAt (fun t : ℝ => 1 - t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2)
      (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y) y := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have hmul : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 + 2 * Real.sqrt 5)) (Real.sqrt (10 + 2 * Real.sqrt 5)) y := by
      have h := (hasDerivAt_id y).mul_const (Real.sqrt (10 + 2 * Real.sqrt 5))
      simpa using h
    have hdiv : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2) (Real.sqrt (10 + 2 * Real.sqrt 5) / 2) y :=
      HasDerivAt.div_const hmul (2 : ℝ)
    have hsub : HasDerivAt (fun t : ℝ => 1 - t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2) (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2)) y :=
      HasDerivAt.const_sub (1 : ℝ) hdiv
    exact HasDerivAt.add hsub hpow
  have hnum_ne : (1 : ℝ) + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2 ≠ 0 := by
    have h : (0:ℝ) < 1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2 := by
      have h1 : (0:ℝ) ≤ y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 := by positivity
      have h2 : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
      linarith
    linarith
  have hden_ne : (1 : ℝ) - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2 ≠ 0 := by
    have h10 : (0:ℝ) < 1 - y := by linarith
    have hsq : (0:ℝ) < (1 - y) ^ 2 := sq_pos_of_ne_zero (ne_of_gt h10)
    have hrem : (0:ℝ) ≤ y * (2 - Real.sqrt (10 + 2 * Real.sqrt 5) / 2) := by
      apply mul_nonneg hy0; have h4 := T1_lt4; linarith
    have heq : 1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2 = (1 - y) ^ 2 + y * (2 - Real.sqrt (10 + 2 * Real.sqrt 5) / 2) := by ring
    have h : (0:ℝ) < 1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2 := by rw [heq]; linarith
    linarith
  have hdiv : HasDerivAt (fun t : ℝ => (1 + t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2) /
      (1 - t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2))
      (((Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) -
        (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y)) /
       (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) y :=
    HasDerivAt.div hnum hden hden_ne
  have hdiv_ne : (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) /
      (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) ≠ 0 :=
    div_ne_zero hnum_ne hden_ne
  have hlog : HasDerivAt (fun t => Real.log ((1 + t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2) /
      (1 - t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2)))
      ((((Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) -
        (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y)) /
       (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) /
      ((1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) /
        (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2))) y :=
    HasDerivAt.log hdiv hdiv_ne
  have hmul : HasDerivAt (fun t => Real.sqrt (10 + 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2) /
        (1 - t * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + t ^ 2)))
      (Real.sqrt (10 + 2 * Real.sqrt 5) / 40 * ((((Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) -
        (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y)) /
       (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) /
      ((1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) /
        (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2)))) y :=
    HasDerivAt.const_mul _ hlog
  have hN : (Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) - (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y) = Real.sqrt (10 + 2 * Real.sqrt 5) * (1 - y ^ 2) := by ring
  have h_eq1 : ((((Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) - (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y)) / (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) / ((1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) / (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2))) = (Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) / (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) - (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y) / (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) := by
    rw [div_sub_div _ _ hnum_ne hden_ne]
    field_simp
  rw [h_eq1] at hmul
  have h_single : Real.sqrt (10 + 2 * Real.sqrt 5) / 40 * ((Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + 2 * y) / (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) - (-(Real.sqrt (10 + 2 * Real.sqrt 5) / 2) + 2 * y) / (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2)) = (Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 * (1 - y ^ 2) / (40 * ((1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2))) := by
    rw [div_sub_div _ _ hnum_ne hden_ne, hN]
    have hD : (40 : ℝ) * ((1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2)) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hnum_ne hden_ne)
    field_simp
  rw [h_single] at hmul
  have hT := T1_sq
  have hprod : (1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) = 1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4 := by
    have hT2 : (Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 = 10 + 2 * Real.sqrt 5 := T1_sq
    linear_combination (-y ^ 2 / 4) * hT2
  have hC : (Real.sqrt (10 + 2 * Real.sqrt 5)) ^ 2 * (1 - y ^ 2) / (40 * ((1 + y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 + y ^ 2))) = (10 + 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4)) := by
    rw [hprod, hT]
  rwa [hC] at hmul

private lemma term4_hd (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasDerivAt (fun t => Real.sqrt (10 - 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2) /
        (1 - t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2)))
      ((10 - 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4))) y := by
  have hnum : HasDerivAt (fun t : ℝ => 1 + t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2)
      (Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) y := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have hmul : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 - 2 * Real.sqrt 5)) (Real.sqrt (10 - 2 * Real.sqrt 5)) y := by
      have h := (hasDerivAt_id y).mul_const (Real.sqrt (10 - 2 * Real.sqrt 5))
      simpa using h
    have hdiv : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2) (Real.sqrt (10 - 2 * Real.sqrt 5) / 2) y :=
      HasDerivAt.div_const hmul (2 : ℝ)
    have hadd : HasDerivAt (fun t : ℝ => 1 + t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2) (Real.sqrt (10 - 2 * Real.sqrt 5) / 2) y :=
      HasDerivAt.const_add (1 : ℝ) hdiv
    exact HasDerivAt.add hadd hpow
  have hden : HasDerivAt (fun t : ℝ => 1 - t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2)
      (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y) y := by
    have hpow : HasDerivAt (fun t : ℝ => t ^ 2) (2 * y) y := by simpa using hasDerivAt_pow 2 y
    have hmul : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 - 2 * Real.sqrt 5)) (Real.sqrt (10 - 2 * Real.sqrt 5)) y := by
      have h := (hasDerivAt_id y).mul_const (Real.sqrt (10 - 2 * Real.sqrt 5))
      simpa using h
    have hdiv : HasDerivAt (fun t : ℝ => t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2) (Real.sqrt (10 - 2 * Real.sqrt 5) / 2) y :=
      HasDerivAt.div_const hmul (2 : ℝ)
    have hsub : HasDerivAt (fun t : ℝ => 1 - t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2) (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2)) y :=
      HasDerivAt.const_sub (1 : ℝ) hdiv
    exact HasDerivAt.add hsub hpow
  have hnum_ne : (1 : ℝ) + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2 ≠ 0 := by
    have h : (0:ℝ) < 1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2 := by
      have h1 : (0:ℝ) ≤ y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 := by positivity
      have h2 : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
      linarith
    linarith
  have hden_ne : (1 : ℝ) - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2 ≠ 0 := by
    have h10 : (0:ℝ) < 1 - y := by linarith
    have hsq : (0:ℝ) < (1 - y) ^ 2 := sq_pos_of_ne_zero (ne_of_gt h10)
    have hrem : (0:ℝ) ≤ y * (2 - Real.sqrt (10 - 2 * Real.sqrt 5) / 2) := by
      apply mul_nonneg hy0; have h4 := T2_lt4; linarith
    have heq : 1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2 = (1 - y) ^ 2 + y * (2 - Real.sqrt (10 - 2 * Real.sqrt 5) / 2) := by ring
    have h : (0:ℝ) < 1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2 := by rw [heq]; linarith
    linarith
  have hdiv : HasDerivAt (fun t : ℝ => (1 + t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2) /
      (1 - t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2))
      (((Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) -
        (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y)) /
       (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) y :=
    HasDerivAt.div hnum hden hden_ne
  have hdiv_ne : (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) /
      (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) ≠ 0 :=
    div_ne_zero hnum_ne hden_ne
  have hlog : HasDerivAt (fun t => Real.log ((1 + t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2) /
      (1 - t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2)))
      ((((Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) -
        (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y)) /
       (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) /
      ((1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) /
        (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2))) y :=
    HasDerivAt.log hdiv hdiv_ne
  have hmul : HasDerivAt (fun t => Real.sqrt (10 - 2 * Real.sqrt 5) / 40 *
      Real.log ((1 + t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2) /
        (1 - t * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + t ^ 2)))
      (Real.sqrt (10 - 2 * Real.sqrt 5) / 40 * ((((Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) -
        (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y)) /
       (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) /
      ((1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) /
        (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2)))) y :=
    HasDerivAt.const_mul _ hlog
  have hN : (Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) - (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y) = Real.sqrt (10 - 2 * Real.sqrt 5) * (1 - y ^ 2) := by ring
  have h_eq1 : ((((Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) - (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y)) / (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) ^ 2) / ((1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) / (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2))) = (Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) / (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) - (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y) / (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) := by
    rw [div_sub_div _ _ hnum_ne hden_ne]
    field_simp
  rw [h_eq1] at hmul
  have h_single : Real.sqrt (10 - 2 * Real.sqrt 5) / 40 * ((Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + 2 * y) / (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) - (-(Real.sqrt (10 - 2 * Real.sqrt 5) / 2) + 2 * y) / (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2)) = (Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 * (1 - y ^ 2) / (40 * ((1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2))) := by
    rw [div_sub_div _ _ hnum_ne hden_ne, hN]
    have hD : (40 : ℝ) * ((1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2)) ≠ 0 := mul_ne_zero (by norm_num) (mul_ne_zero hnum_ne hden_ne)
    field_simp
  rw [h_single] at hmul
  have hT := T2_sq
  have hprod : (1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) = 1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4 := by
    have hT2 : (Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 = 10 - 2 * Real.sqrt 5 := T2_sq
    linear_combination (-y ^ 2 / 4) * hT2
  have hC : (Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 * (1 - y ^ 2) / (40 * ((1 + y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2) * (1 - y * Real.sqrt (10 - 2 * Real.sqrt 5) / 2 + y ^ 2))) = (10 - 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4)) := by
    rw [hprod, hT]
  rwa [hC] at hmul

private lemma alg_identity (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    1 / (5 * (1 + y ^ 2)) +
    (6 + 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4)) +
    (6 - 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4)) +
    (10 + 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4)) +
    (10 - 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4)) =
    1 / (1 + y ^ 10) := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := sqrt5_sq
  have hs1 : (1:ℝ) < Real.sqrt 5 := sqrt5_gt1
  have h1 : (0:ℝ) < 1 + y ^ 2 := by positivity
  have h2 : (0:ℝ) < 4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4 := by
    have hy2 : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
    have hpos : (0:ℝ) < 2 * Real.sqrt 5 - 2 := by linarith
    nlinarith
  have h3 : (0:ℝ) < 4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4 := by
    have hy2lt : y ^ 2 < 1 := by
      have h := one_sub_sq_pos hy0 hy1
      linarith
    have hy2nn : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
    have hspos : (0:ℝ) < Real.sqrt 5 := sqrt5_pos
    nlinarith [sq_nonneg (y ^ 2), sq_nonneg y]
  have h4 : (0:ℝ) < 1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4 := by
    have hy2lt : y ^ 2 < 1 := by
      have h := one_sub_sq_pos hy0 hy1
      linarith
    have hspos : (0:ℝ) < Real.sqrt 5 := sqrt5_pos
    have hslt : Real.sqrt 5 < 3 := sqrt5_lt3
    nlinarith [sq_nonneg (y ^ 2 - 1 / 2), sq_nonneg y]
  have h5 : (0:ℝ) < 1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4 := by
    have hy2nn : (0:ℝ) ≤ y ^ 2 := sq_nonneg y
    nlinarith [sq_nonneg y]
  have e1 : (5 : ℝ) * (1 + y ^ 2) ≠ 0 := by positivity
  have e2 : (10 : ℝ) * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4) ≠ 0 := by positivity
  have e3 : (10 : ℝ) * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4) ≠ 0 := by positivity
  have e4 : (40 : ℝ) * (1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4) ≠ 0 := by positivity
  have e5 : (40 : ℝ) * (1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4) ≠ 0 := by positivity
  have e6 : (1 : ℝ) + y ^ 10 ≠ 0 := by positivity
  have d12 : (5 * (1 + y ^ 2)) * (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4)) ≠ 0 := mul_ne_zero e1 e2
  have d123 : ((5 * (1 + y ^ 2)) * (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4))) * (10 * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4)) ≠ 0 := mul_ne_zero d12 e3
  have d1234 : (((5 * (1 + y ^ 2)) * (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4))) * (10 * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4))) * (40 * (1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4)) ≠ 0 := mul_ne_zero d123 e4
  have d12345 : ((((5 * (1 + y ^ 2)) * (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4))) * (10 * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4))) * (40 * (1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4))) * (40 * (1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4)) ≠ 0 := mul_ne_zero d1234 e5
  have hs4 : (Real.sqrt 5) ^ 4 = 25 := by calc (Real.sqrt 5) ^ 4 = ((Real.sqrt 5) ^ 2) ^ 2 := by ring
    _ = 25 := by rw [hs]; norm_num
  rw [div_add_div _ _ e1 e2, div_add_div _ _ d12 e3, div_add_div _ _ d123 e4, div_add_div _ _ d1234 e5]
  rw [div_eq_div_iff d12345 e6]
  ring_nf
  rw [hs4, hs]
  ring

private lemma hasDerivAt_closed (y : ℝ) (hy0 : 0 ≤ y) (hy1 : y < 1) :
    HasDerivAt chapter8Entry14A10Closed (1 / (1 + y ^ 10)) y := by
  have h0 := term0_hd y
  have h1 := term1_hd y hy0 hy1
  have h2 := term2_hd y hy0 hy1
  have h3 := term3_hd y hy0 hy1
  have h4 := term4_hd y hy0 hy1
  have hall : HasDerivAt chapter8Entry14A10Closed
      (1 / (5 * (1 + y ^ 2)) +
       (6 + 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (2 * Real.sqrt 5 - 2) * y ^ 2 + 4 * y ^ 4)) +
       (6 - 2 * Real.sqrt 5) * (1 + y ^ 2) / (10 * (4 + (-2 - 2 * Real.sqrt 5) * y ^ 2 + 4 * y ^ 4)) +
       (10 + 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 - (1 + Real.sqrt 5) / 2 * y ^ 2 + y ^ 4)) +
       (10 - 2 * Real.sqrt 5) * (1 - y ^ 2) / (40 * (1 + (Real.sqrt 5 - 1) / 2 * y ^ 2 + y ^ 4))) y := by
    unfold chapter8Entry14A10Closed
    exact (((h0.add h1).add h2).add h3).add h4
  have halg := alg_identity y hy0 hy1
  rwa [halg] at hall

/-- **Ramanujan's closed form for $\int_0^x du/(1 + u^{10})$ (Chapter 8, Entry 14).** Put
$a_\pm = \sqrt{6 \pm 2\sqrt5}$ and $b_\pm = \sqrt{10 \pm 2\sqrt5}$. For every real $x$ with
$0 \le x < 1$,
$$\int_0^x \frac{du}{1 + u^{10}} = \frac{\arctan x}{5} +
\frac{a_+}{20} \arctan \frac{a_+ x}{2(1 - x^2)} + \frac{a_-}{20} \arctan \frac{a_- x}{2(1 - x^2)} +
\frac{b_+}{40} \log \frac{1 + b_+ x/2 + x^2}{1 - b_+ x/2 + x^2} +
\frac{b_-}{40} \log \frac{1 + b_- x/2 + x^2}{1 - b_- x/2 + x^2}.$$

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 8.
Proves `Wanted` entry `ramanujan_part1_ch8_entry14_qreflection`.
-/
theorem ramanujan_part1_ch8_entry14_qreflection (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    chapter8Entry14A 10 x = chapter8Entry14A10Closed x := by
  unfold chapter8Entry14A
  have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) x, HasDerivAt chapter8Entry14A10Closed ((fun y => 1 / (1 + y ^ 10)) y) y := by
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    obtain ⟨hy0, hyx⟩ := Set.mem_Icc.mp hy
    have hy1 : y < 1 := lt_of_le_of_lt hyx hx1
    exact hasDerivAt_closed y hy0 hy1
  have hint : IntervalIntegrable (fun y => 1 / (1 + y ^ 10)) MeasureTheory.volume 0 x := by
    apply Continuous.intervalIntegrable
    have hcont : Continuous (fun y : ℝ => 1 / (1 + y ^ 10)) := by
      apply Continuous.div continuous_const (Continuous.add continuous_const (Continuous.pow continuous_id 10))
      intro y
      exact ne_of_gt (by positivity : (0:ℝ) < 1 + y ^ 10)
    exact hcont
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have hF0 : chapter8Entry14A10Closed 0 = 0 := by
    unfold chapter8Entry14A10Closed
    simp [Real.arctan_zero]
  show (∫ y in (0:ℝ)..x, (fun y => 1 / (1 + y ^ 10)) y) = chapter8Entry14A10Closed x
  rw [hFTC, hF0, sub_zero]

end

end Entry14Qreflection

end MathlibExt.Analysis.Ramanujan.Part1Ch8
