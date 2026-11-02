/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` (Mathlib):
Copyright (c) 2018 Chris Hughes. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry8Arcsin
import Mathlib.Topology.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence
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

namespace Entry21Piseries2

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Filter Finset MeasureTheory
open Entry8Arcsin (chapter9OddHarmonic)

noncomputable section

def chapter9Chi3Term (j : ℕ) : ℝ :=
  1 / (((2 * j + 1 : ℕ) : ℝ) ^ 3)

def chapter9Chi3AtOne : ℝ :=
  ∑' j : ℕ, chapter9Chi3Term j

def chapter9Entry21CosineTerm (x : ℝ) (j : ℕ) : ℝ :=
  Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 3)

def chapter9Entry21LeftTerm (x : ℝ) (j : ℕ) : ℝ :=
  let k := j + 1
  (-1 : ℝ) ^ j * chapter9OddHarmonic k * Real.tan x ^ (2 * k) /
    (((2 * k : ℕ) : ℝ) ^ 2)

def chapter9Entry21SineTerm (x : ℝ) (j : ℕ) : ℝ :=
  Real.sin (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 2)

def chapter9TanLogTerm (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 / 2 * Real.log |Real.tan x|

private lemma aux_summable_shift_three :
    Summable (fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 3)) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (((3 : ℕ)) : ℝ))) :=
    (Real.summable_one_div_nat_rpow (p := (((3 : ℕ)) : ℝ))).mpr (by norm_num)
  have hshift :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ (((3 : ℕ)) : ℝ))) 1).mpr
      hbase
  apply hshift.congr
  intro j
  show 1 / ((((j + 1 : ℕ)) : ℝ) ^ ((((3 : ℕ))) : ℝ)) = 1 / (((j : ℝ) + 1) ^ 3)
  rw [Nat.cast_add_one, Real.rpow_natCast]

private lemma summable_chi3 : Summable chapter9Chi3Term := by
  refine Summable.of_nonneg_of_le
    (f := fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 3)) ?_ ?_ aux_summable_shift_three
  · intro j
    change 0 ≤ 1 / (((2 * j + 1 : ℕ) : ℝ) ^ 3)
    exact one_div_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _)
  · intro j
    change 1 / (((2 * j + 1 : ℕ) : ℝ) ^ 3) ≤ 1 / (((j : ℝ) + 1) ^ 3)
    have hpos : (0 : ℝ) < ((j : ℝ) + 1) ^ 3 := by positivity
    have hle : (((j : ℝ) + 1) ^ 3) ≤ ((((2 * j + 1 : ℕ)) : ℝ) ^ 3) := by
      apply pow_le_pow_left₀ (by positivity)
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      push_cast
      linarith
    exact one_div_le_one_div_of_le hpos hle

private lemma aux_summable_shift_two :
    Summable (fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 2)) := by
  have hbase : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (((2 : ℕ)) : ℝ))) :=
    (Real.summable_one_div_nat_rpow (p := (((2 : ℕ)) : ℝ))).mpr (by norm_num)
  have hshift :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / ((n : ℝ) ^ (((2 : ℕ)) : ℝ))) 1).mpr
      hbase
  apply hshift.congr
  intro j
  show 1 / ((((j + 1 : ℕ)) : ℝ) ^ ((((2 : ℕ))) : ℝ)) = 1 / (((j : ℝ) + 1) ^ 2)
  rw [Nat.cast_add_one, Real.rpow_natCast]

private lemma aux_base_le (j : ℕ) : ((j : ℝ) + 1) ≤ ((((2 * j + 1 : ℕ))) : ℝ) := by
  have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  push_cast
  linarith

private lemma summable_sine (x : ℝ) : Summable (chapter9Entry21SineTerm x) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le
    (f := fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 2)) ?_ ?_ aux_summable_shift_two
  · intro j
    exact norm_nonneg _
  · intro j
    change ‖Real.sin ((((4 * j + 2 : ℕ)) : ℝ) * x) / ((((2 * j + 1 : ℕ)) : ℝ) ^ 2)‖ ≤
      1 / (((j : ℝ) + 1) ^ 2)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    have hB : (0 : ℝ) < ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 :=
      pow_pos (Nat.cast_pos.mpr (by omega)) 2
    have habs : |((((2 * j + 1 : ℕ))) : ℝ) ^ 2| = ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 :=
      abs_of_pos hB
    have hle : (((j : ℝ) + 1) ^ 2) ≤ ((((2 * j + 1 : ℕ)) : ℝ) ^ 2) :=
      pow_le_pow_left₀ (by positivity) (aux_base_le j) 2
    calc |Real.sin ((((4 * j + 2 : ℕ)) : ℝ) * x)| / |((((2 * j + 1 : ℕ))) : ℝ) ^ 2|
          ≤ 1 / |((((2 * j + 1 : ℕ))) : ℝ) ^ 2| := by
            have hBpos : (0 : ℝ) < |((((2 * j + 1 : ℕ))) : ℝ) ^ 2| := by
              rw [habs]
              exact hB
            rw [div_le_iff₀ hBpos, one_div_mul_cancel (ne_of_gt hBpos)]
            exact Real.abs_sin_le_one _
        _ = 1 / ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 := by rw [habs]
        _ ≤ 1 / (((j : ℝ) + 1) ^ 2) :=
            one_div_le_one_div_of_le (by positivity) hle

private lemma summable_cosine (x : ℝ) : Summable (chapter9Entry21CosineTerm x) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le
    (f := fun j : ℕ => 1 / (((j : ℝ) + 1) ^ 3)) ?_ ?_ aux_summable_shift_three
  · intro j
    exact norm_nonneg _
  · intro j
    change ‖Real.cos ((((4 * j + 2 : ℕ)) : ℝ) * x) / ((((2 * j + 1 : ℕ)) : ℝ) ^ 3)‖ ≤
      1 / (((j : ℝ) + 1) ^ 3)
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    have hB : (0 : ℝ) < ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 :=
      pow_pos (Nat.cast_pos.mpr (by omega)) 3
    have habs : |((((2 * j + 1 : ℕ))) : ℝ) ^ 3| = ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 :=
      abs_of_pos hB
    have hle : (((j : ℝ) + 1) ^ 3) ≤ ((((2 * j + 1 : ℕ)) : ℝ) ^ 3) :=
      pow_le_pow_left₀ (by positivity) (aux_base_le j) 3
    calc |Real.cos ((((4 * j + 2 : ℕ)) : ℝ) * x)| / |((((2 * j + 1 : ℕ))) : ℝ) ^ 3|
          ≤ 1 / |((((2 * j + 1 : ℕ))) : ℝ) ^ 3| := by
            have hBpos : (0 : ℝ) < |((((2 * j + 1 : ℕ))) : ℝ) ^ 3| := by
              rw [habs]
              exact hB
            rw [div_le_iff₀ hBpos, one_div_mul_cancel (ne_of_gt hBpos)]
            exact Real.abs_cos_le_one _
        _ = 1 / ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 := by rw [habs]
        _ ≤ 1 / (((j : ℝ) + 1) ^ 3) :=
            one_div_le_one_div_of_le (by positivity) hle

private lemma aux_abs_tan_le_one (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    |Real.tan x| ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx1 : -(Real.pi / 4) ≤ x := (abs_le.mp hx).1
  have hx2 : x ≤ Real.pi / 4 := (abs_le.mp hx).2
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem1 : -(Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem2 : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hneg : Real.tan (-(Real.pi / 4)) = -1 := by
    rw [Real.tan_neg, Real.tan_pi_div_four]
  have hlo : -1 ≤ Real.tan x := by
    rw [← hneg]
    exact (Real.strictMonoOn_tan.le_iff_le hmem1 hmem).mpr hx1
  have hhi : Real.tan x ≤ 1 := by
    rw [← Real.tan_pi_div_four]
    exact (Real.strictMonoOn_tan.le_iff_le hmem hmem2).mpr hx2
  exact abs_le.mpr ⟨hlo, hhi⟩

private lemma aux_oddHarmonic_nonneg (n : ℕ) : 0 ≤ chapter9OddHarmonic n := by
  change 0 ≤ ∑ j ∈ Finset.range n, 1 / ((((2 * j + 1 : ℕ))) : ℝ)
  apply Finset.sum_nonneg
  intro i _
  apply one_div_nonneg.mpr
  exact le_of_lt (Nat.cast_pos.mpr (by omega))

private lemma aux_sqrt_self_le (n : ℕ) : Real.sqrt ((n : ℝ)) ≤ (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · simp
  · rw [Real.sqrt_le_left (Nat.cast_nonneg n)]
    have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpos
    calc (n : ℝ) = 1 * (n : ℝ) := by ring
      _ ≤ (n : ℝ) * (n : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg n)
      _ = (n : ℝ) ^ 2 := by ring

private lemma aux_oddHarmonic_le (n : ℕ) :
    chapter9OddHarmonic n ≤ 2 * Real.sqrt ((n : ℝ)) := by
  induction n with
  | zero => simp [chapter9OddHarmonic]
  | succ n ih =>
    have heq : chapter9OddHarmonic (n + 1)
        = chapter9OddHarmonic n + 1 / ((((2 * n + 1 : ℕ))) : ℝ) :=
      Finset.sum_range_succ _ n
    have hcast : ((((n + 1 : ℕ))) : ℝ) = (n : ℝ) + 1 := Nat.cast_add_one n
    rw [heq, hcast]
    have h2n1 : (0 : ℝ) < ((((2 * n + 1 : ℕ))) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have hS : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ) := by
      have hsqrt1 : (0 : ℝ) < Real.sqrt ((n : ℝ) + 1) :=
        Real.sqrt_pos.mpr (by positivity)
      linarith [Real.sqrt_nonneg (n : ℝ)]
    have hsq1 : (Real.sqrt ((n : ℝ) + 1)) ^ 2 = (n : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have hsq2 : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg n)
    have hdiff : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) *
        (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) = 1 := by
      have hring : (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) *
          (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ))
          = (Real.sqrt ((n : ℝ) + 1)) ^ 2 - (Real.sqrt (n : ℝ)) ^ 2 := by ring
      rw [hring, hsq1, hsq2]
      ring
    have hratio : Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)
        = 1 / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) := by
      rw [eq_div_iff (ne_of_gt hS)]
      exact hdiff
    have hle2 : Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)
        ≤ 2 * ((((2 * n + 1 : ℕ))) : ℝ) := by
      have h1 : Real.sqrt ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := by
        have h := aux_sqrt_self_le (n + 1)
        rwa [Nat.cast_add_one] at h
      have h2 : Real.sqrt (n : ℝ) ≤ (n : ℝ) := aux_sqrt_self_le n
      have hcast2 : ((((2 * n + 1 : ℕ))) : ℝ) = 2 * (n : ℝ) + 1 := by
        push_cast
        ring
      linarith
    have key : 1 / ((((2 * n + 1 : ℕ))) : ℝ)
        ≤ 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) := by
      rw [hratio, ← div_eq_mul_one_div]
      have h2S : (2 : ℝ) / (Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ))
          = 1 / ((Real.sqrt ((n : ℝ) + 1) + Real.sqrt (n : ℝ)) / 2) :=
        (one_div_div _ _).symm
      rw [h2S]
      apply one_div_le_one_div_of_le
      · linarith [hS]
      · linarith [hle2]
    calc chapter9OddHarmonic n + 1 / ((((2 * n + 1 : ℕ))) : ℝ)
        ≤ 2 * Real.sqrt (n : ℝ)
            + 2 * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt (n : ℝ)) :=
          add_le_add ih key
      _ = 2 * Real.sqrt ((n : ℝ) + 1) := by ring

private lemma aux_summable_shift_threehalves :
    Summable (fun j : ℕ => (1 / 2 : ℝ) / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))) := by
  have hbase : Summable (fun n : ℕ => (1 / 2 : ℝ) / ((n : ℝ) ^ ((3 / 2 : ℝ)))) := by
    have h :=
      (Real.summable_one_div_nat_rpow (p := (3 / 2 : ℝ))).mpr (by norm_num)
    have h2 : Summable (fun n : ℕ => (1 / 2 : ℝ) * (1 / ((n : ℝ) ^ ((3 / 2 : ℝ))))) :=
      Summable.mul_left _ h
    apply h2.congr
    intro n
    exact (div_eq_mul_one_div _ _).symm
  have hshift :=
    (summable_nat_add_iff
      (f := fun n : ℕ => (1 / 2 : ℝ) / ((n : ℝ) ^ ((3 / 2 : ℝ)))) 1).mpr hbase
  apply hshift.congr
  intro j
  rfl

private lemma aux_left_norm_le (x : ℝ) (j : ℕ) (hx : |x| ≤ Real.pi / 4) :
    ‖chapter9Entry21LeftTerm x j‖ ≤
      (1 / 2 : ℝ) / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) := by
    have htan : |Real.tan x| ≤ 1 := aux_abs_tan_le_one x hx
    have hH : chapter9OddHarmonic (j + 1)
        ≤ 2 * Real.sqrt ((((j + 1 : ℕ))) : ℝ) :=
      aux_oddHarmonic_le (j + 1)
    have hHnn : 0 ≤ chapter9OddHarmonic (j + 1) := aux_oddHarmonic_nonneg (j + 1)
    have htpos : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have h2kcast : ((((2 * (j + 1) : ℕ))) : ℝ) = 2 * ((((j + 1 : ℕ))) : ℝ) := by
      push_cast
      ring
    have h2t : (0 : ℝ) < 2 * ((((j + 1 : ℕ))) : ℝ) := by linarith
    have hD : (0 : ℝ) < ((((2 * (j + 1) : ℕ))) : ℝ) :=
      Nat.cast_pos.mpr (by omega)
    have h2k : (0 : ℝ) < ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 := pow_pos hD 2
    have e1 : ‖chapter9Entry21LeftTerm x j‖
        = chapter9OddHarmonic (j + 1) * |Real.tan x| ^ (2 * (j + 1))
          / ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 := by
      change ‖(-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * (j + 1))
        / ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2‖ = _
      simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs,
        abs_of_nonneg hHnn, abs_neg, abs_one, one_pow, one_mul]
      rw [abs_of_pos hD]
    rw [e1]
    have step1 : chapter9OddHarmonic (j + 1) * |Real.tan x| ^ (2 * (j + 1))
        / ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2
        ≤ chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 := by
      apply (div_le_iff₀ h2k).mpr
      have hpow : |Real.tan x| ^ (2 * (j + 1)) ≤ 1 :=
        pow_le_one₀ (abs_nonneg _) htan
      calc chapter9OddHarmonic (j + 1) * |Real.tan x| ^ (2 * (j + 1))
          ≤ chapter9OddHarmonic (j + 1) * 1 :=
            mul_le_mul_of_nonneg_left hpow hHnn
        _ = chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 *
            ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2 := by
              rw [mul_one, div_mul_cancel₀ _ (ne_of_gt h2k)]
    have step2 : chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ) ^ 2
        ≤ (2 * Real.sqrt ((((j + 1 : ℕ))) : ℝ))
          / (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2 := by
      rw [h2kcast]
      apply (div_le_iff₀ (pow_pos h2t 2)).mpr
      rw [div_mul_cancel₀ _ (ne_of_gt (pow_pos h2t 2))]
      exact hH
    have hsqrt : Real.sqrt ((((j + 1 : ℕ))) : ℝ)
        = ((((j + 1 : ℕ))) : ℝ) ^ ((1 / 2 : ℝ)) := Real.sqrt_eq_rpow _
    have hexp : ((1 / 2 : ℝ) + (3 / 2 : ℝ)) = 2 := by norm_num
    have hmul : Real.sqrt ((((j + 1 : ℕ))) : ℝ)
        * ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) = ((((j + 1 : ℕ))) : ℝ) ^ 2 := by
      rw [hsqrt, ← Real.rpow_add htpos, hexp, Real.rpow_two]
    have hfinal : (2 * Real.sqrt ((((j + 1 : ℕ))) : ℝ))
        / (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2
        ≤ (1 / 2 : ℝ) / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) := by
      have hd : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ)) :=
        Real.rpow_pos_of_pos htpos _
      rw [div_le_iff₀ (pow_pos h2t 2), div_mul_eq_mul_div, le_div_iff₀ hd]
      have hring : ((1 / 2 : ℝ)) * (2 * ((((j + 1 : ℕ))) : ℝ)) ^ 2
          = 2 * ((((j + 1 : ℕ))) : ℝ) ^ 2 := by ring
      rw [show (2 : ℝ) * Real.sqrt ((((j + 1 : ℕ))) : ℝ)
          * ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))
          = 2 * (Real.sqrt ((((j + 1 : ℕ))) : ℝ)
            * ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))) from by ring, hmul, hring]
    exact le_trans step1 (le_trans step2 hfinal)

private lemma summable_left (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Summable (chapter9Entry21LeftTerm x) := by
  apply Summable.of_norm
  refine Summable.of_nonneg_of_le
    (f := fun j : ℕ => (1 / 2 : ℝ) / ((((j + 1 : ℕ))) : ℝ) ^ ((3 / 2 : ℝ))) ?_ ?_
    aux_summable_shift_threehalves
  · intro j
    exact norm_nonneg _
  · intro j
    exact aux_left_norm_le x j hx

private lemma aux_partial_fraction (A B : ℝ) (hA : A ≠ 0) (hB : B ≠ 0)
    (hAB : A + B ≠ 0) : 1 / (A * B) = (1 / (A + B)) * (1 / A + 1 / B) := by
  field_simp
  ring

private lemma aux_antidiag_fst (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, (1 / ((((2 * p.1 + 1 : ℕ))) : ℝ)) =
      chapter9OddHarmonic (n + 1) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [Nat.succ_eq_add_one]
  rfl

private lemma aux_antidiag_snd (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, (1 / ((((2 * p.2 + 1 : ℕ))) : ℝ)) =
      chapter9OddHarmonic (n + 1) := by
  have hswap := Finset.Nat.sum_antidiagonal_swap (n := n)
    (f := fun p : ℕ × ℕ => (1 / ((((2 * p.1 + 1 : ℕ))) : ℝ)))
  have hcongr : (∑ p ∈ Finset.antidiagonal n, (1 / ((((2 * p.2 + 1 : ℕ))) : ℝ))) =
      ∑ p ∈ Finset.antidiagonal n,
        (fun p : ℕ × ℕ => (1 / ((((2 * p.1 + 1 : ℕ))) : ℝ))) p.swap := by
    apply Finset.sum_congr rfl
    intro p _
    rfl
  rw [hcongr, hswap]
  exact aux_antidiag_fst n

private lemma aux_antidiag_inv_mul (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n,
        (1 / (((((2 * p.1 + 1 : ℕ))) : ℝ) * ((((2 * p.2 + 1 : ℕ))) : ℝ))) =
      chapter9OddHarmonic (n + 1) / ((((n + 1 : ℕ))) : ℝ) := by
  have hSpos : (0 : ℝ) < 2 * (n : ℝ) + 2 := by positivity
  have hSne : (2 * (n : ℝ) + 2) ≠ 0 := ne_of_gt hSpos
  have hNne : ((((n + 1 : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hSeq : 2 * (n : ℝ) + 2 = 2 * ((((n + 1 : ℕ))) : ℝ) := by
    push_cast
    ring
  have hterm : ∀ p ∈ Finset.antidiagonal n,
      (1 / (((((2 * p.1 + 1 : ℕ))) : ℝ) * ((((2 * p.2 + 1 : ℕ))) : ℝ))) =
        (1 / (2 * (n : ℝ) + 2)) *
          (1 / ((((2 * p.1 + 1 : ℕ))) : ℝ) + 1 / ((((2 * p.2 + 1 : ℕ))) : ℝ)) := by
    intro p hp
    have hmem : p.1 + p.2 = n := Finset.mem_antidiagonal.mp hp
    have hA : ((((2 * p.1 + 1 : ℕ))) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_zero_of_lt (by omega : 0 < 2 * p.1 + 1)
    have hB : ((((2 * p.2 + 1 : ℕ))) : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_zero_of_lt (by omega : 0 < 2 * p.2 + 1)
    have hcast : ((p.1 : ℝ) + (p.2 : ℝ)) = (n : ℝ) := by
      have h2 : ((((p.1 + p.2 : ℕ))) : ℝ) = (n : ℝ) := by exact_mod_cast hmem
      push_cast at h2
      linarith
    have hAB : ((((2 * p.1 + 1 : ℕ))) : ℝ) + ((((2 * p.2 + 1 : ℕ))) : ℝ)
        = 2 * (n : ℝ) + 2 := by
      push_cast
      linarith
    have hABne : ((((2 * p.1 + 1 : ℕ))) : ℝ) + ((((2 * p.2 + 1 : ℕ))) : ℝ) ≠ 0 := by
      rw [hAB]
      exact hSne
    have hpf := aux_partial_fraction _ _ hA hB hABne
    rw [hAB] at hpf
    exact hpf
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_add_distrib,
    aux_antidiag_fst, aux_antidiag_snd, hSeq]
  field_simp
  ring

private def arctanTerm (t : ℝ) (i : ℕ) : ℝ :=
  (-1) ^ i * t ^ (2 * i + 1) / ((2 * i + 1 : ℕ) : ℝ)

private lemma aux_arctanTerm_norm_le (t : ℝ) (i : ℕ) :
    ‖arctanTerm t i‖ ≤ |t| ^ (2 * i + 1) := by
  have hDpos : (0 : ℝ) < ((((2 * i + 1 : ℕ))) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hD1 : (1 : ℝ) ≤ ((((2 * i + 1 : ℕ))) : ℝ) := by
    have h : (1 : ℕ) ≤ 2 * i + 1 := by omega
    exact_mod_cast h
  have hnorm : ‖arctanTerm t i‖ = |t| ^ (2 * i + 1) / ((((2 * i + 1 : ℕ))) : ℝ) := by
    unfold arctanTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    have hnum : |(-1 : ℝ) ^ i * t ^ (2 * i + 1)| = |t| ^ (2 * i + 1) := by
      rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_pow]
    have hden : |((((2 * i + 1 : ℕ))) : ℝ)| = ((((2 * i + 1 : ℕ))) : ℝ) :=
      abs_of_pos hDpos
    rw [hnum, hden]
  rw [hnorm]
  have hnn : (0 : ℝ) ≤ |t| ^ (2 * i + 1) := pow_nonneg (abs_nonneg _) _
  calc |t| ^ (2 * i + 1) / ((((2 * i + 1 : ℕ))) : ℝ)
      ≤ |t| ^ (2 * i + 1) / 1 := by
        apply div_le_div_of_nonneg_left hnn (by norm_num) hD1
    _ = |t| ^ (2 * i + 1) := div_one _

private lemma aux_abs_pow_split (t : ℝ) (i : ℕ) :
    |t| ^ (2 * i + 1) = |t| * (|t| ^ 2) ^ i := by
  rw [pow_add, pow_one, pow_mul, mul_comm]

private lemma aux_arctan_norm_summable (t : ℝ) (ht : |t| < 1) :
    Summable (fun i => ‖arctanTerm t i‖) := by
  have hr0 : (0 : ℝ) ≤ |t| ^ 2 := sq_nonneg _
  have hr1 : |t| ^ 2 < 1 := by
    have h1 : (0 : ℝ) < 1 - |t| := by linarith
    have h2 : (0 : ℝ) < 1 + |t| := by
      have hnn := abs_nonneg t
      linarith
    have hmul : (0 : ℝ) < (1 - |t|) * (1 + |t|) := mul_pos h1 h2
    have hexpand : (1 - |t|) * (1 + |t|) = 1 - |t| ^ 2 := by ring
    linarith
  have hgeom : Summable (fun i : ℕ => |t| * (|t| ^ 2) ^ i) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  refine Summable.of_nonneg_of_le
    (f := fun i : ℕ => |t| * (|t| ^ 2) ^ i) ?_ ?_ hgeom
  · intro i
    exact norm_nonneg _
  · intro i
    calc ‖arctanTerm t i‖ ≤ |t| ^ (2 * i + 1) := aux_arctanTerm_norm_le t i
      _ = |t| * (|t| ^ 2) ^ i := aux_abs_pow_split t i

private lemma aux_hasSum_arctan (t : ℝ) (ht : |t| < 1) :
    HasSum (arctanTerm t) (Real.arctan t) := by
  have hnorm : ‖t‖ < 1 := by
    rw [Real.norm_eq_abs]
    exact ht
  exact Real.hasSum_arctan (x := t) hnorm

private lemma aux_tsum_arctan (t : ℝ) (ht : |t| < 1) :
    (∑' i, arctanTerm t i) = Real.arctan t :=
  (aux_hasSum_arctan t ht).tsum_eq

private lemma aux_arctan_sq_tsum (t : ℝ) (ht : |t| < 1) :
    (∑' n, ∑ kl ∈ Finset.antidiagonal n,
      arctanTerm t kl.1 * arctanTerm t kl.2) = Real.arctan t ^ 2 := by
  have hnorm := aux_arctan_norm_summable t ht
  have hmul := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (f := arctanTerm t) (g := arctanTerm t) hnorm hnorm
  rw [aux_tsum_arctan t ht] at hmul
  calc (∑' n, ∑ kl ∈ Finset.antidiagonal n,
        arctanTerm t kl.1 * arctanTerm t kl.2)
      = Real.arctan t * Real.arctan t := hmul.symm
    _ = Real.arctan t ^ 2 := (pow_two _).symm

private lemma aux_arctanTerm_mul (t : ℝ) (i l n : ℕ) (h : i + l = n) :
    arctanTerm t i * arctanTerm t l =
      (-1) ^ n * t ^ (2 * n + 2) /
        (((((2 * i + 1 : ℕ))) : ℝ) * ((((2 * l + 1 : ℕ))) : ℝ)) := by
  unfold arctanTerm
  have hpow1 : (-1 : ℝ) ^ i * (-1 : ℝ) ^ l = (-1 : ℝ) ^ n := by
    rw [← pow_add, h]
  have hexp : 2 * i + 1 + (2 * l + 1) = 2 * n + 2 := by omega
  have hpow2 : t ^ (2 * i + 1) * t ^ (2 * l + 1) = t ^ (2 * n + 2) := by
    rw [← pow_add, hexp]
  have hnum : (-1 : ℝ) ^ i * t ^ (2 * i + 1) * ((-1 : ℝ) ^ l * t ^ (2 * l + 1)) =
      (-1 : ℝ) ^ n * t ^ (2 * n + 2) := by
    calc (-1 : ℝ) ^ i * t ^ (2 * i + 1) * ((-1 : ℝ) ^ l * t ^ (2 * l + 1))
        = ((-1 : ℝ) ^ i * (-1 : ℝ) ^ l) *
          (t ^ (2 * i + 1) * t ^ (2 * l + 1)) := by ring
      _ = (-1 : ℝ) ^ n * t ^ (2 * n + 2) := by rw [hpow1, hpow2]
  rw [div_mul_div_comm, hnum]

private lemma aux_inner_sum (t : ℝ) (n : ℕ) :
    ∑ kl ∈ Finset.antidiagonal n, arctanTerm t kl.1 * arctanTerm t kl.2 =
      (-1) ^ n * chapter9OddHarmonic (n + 1) * t ^ (2 * n + 2) /
        ((((n + 1 : ℕ))) : ℝ) := by
  have hC : ∀ kl ∈ Finset.antidiagonal n,
      arctanTerm t kl.1 * arctanTerm t kl.2 =
        ((-1) ^ n * t ^ (2 * n + 2)) *
          (1 / (((((2 * kl.1 + 1 : ℕ))) : ℝ) * ((((2 * kl.2 + 1 : ℕ))) : ℝ))) := by
    intro kl hkl
    have hmem : kl.1 + kl.2 = n := Finset.mem_antidiagonal.mp hkl
    have hmul := aux_arctanTerm_mul t kl.1 kl.2 n hmem
    rw [hmul, div_eq_mul_one_div]
  rw [Finset.sum_congr rfl hC, ← Finset.mul_sum, aux_antidiag_inv_mul]
  ring

private lemma aux_inner_summable (t : ℝ) (ht : |t| < 1) :
    Summable (fun n => ∑ kl ∈ Finset.antidiagonal n,
      arctanTerm t kl.1 * arctanTerm t kl.2) := by
  have hnorm := aux_arctan_norm_summable t ht
  have h := summable_norm_sum_mul_antidiagonal_of_summable_norm
    (f := arctanTerm t) (g := arctanTerm t) hnorm hnorm
  exact Summable.of_norm h

private lemma aux_arctan_sq_hasSum (t : ℝ) (ht : |t| < 1) :
    HasSum (fun j => (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * t ^ (2 * j + 2) /
      ((((j + 1 : ℕ))) : ℝ)) (Real.arctan t ^ 2) := by
  have hinner_summ := aux_inner_summable t ht
  have hinner_has : HasSum (fun n => ∑ kl ∈ Finset.antidiagonal n,
      arctanTerm t kl.1 * arctanTerm t kl.2) (Real.arctan t ^ 2) := by
    have h := hinner_summ.hasSum
    rwa [aux_arctan_sq_tsum t ht] at h
  exact HasSum.congr_fun hinner_has (fun n => (aux_inner_sum t n).symm)

private lemma aux_arctan_sq_series (t : ℝ) (ht : |t| < 1) :
    (∑' j, (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * t ^ (2 * j + 2) /
      ((((j + 1 : ℕ))) : ℝ)) = Real.arctan t ^ 2 :=
  (aux_arctan_sq_hasSum t ht).tsum_eq

private def chapF (u : ℝ) : ℝ := u ^ 2 / Real.sin (2 * u)

private def leftDerivTerm (x : ℝ) (j : ℕ) : ℝ :=
  (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 1) /
    (((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos x ^ 2)

private lemma aux_leftTerm_eq (x : ℝ) (j : ℕ) :
    chapter9Entry21LeftTerm x j =
      (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * (j + 1)) /
        (((((2 * (j + 1) : ℕ))) : ℝ) ^ 2) :=
  rfl

private lemma aux_left_hasDerivAt (x : ℝ) (j : ℕ)
    (hx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    HasDerivAt (fun y => chapter9Entry21LeftTerm y j) (leftDerivTerm x j) x := by
  have hcos : Real.cos x ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo hx)
  have hcos2 : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos
  have hN : ((((2 * (j + 1) : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_zero_of_lt (by omega : 0 < 2 * (j + 1))
  have hsub : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
  have htan : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
    Real.hasDerivAt_tan hcos
  have hpow := HasDerivAt.pow htan (2 * (j + 1))
  have hfun_pow : (Real.tan ^ (2 * (j + 1))) =
      (fun y => Real.tan y ^ (2 * (j + 1))) := by
    funext y
    simp
  rw [hfun_pow, hsub] at hpow
  have hmul := HasDerivAt.const_mul
    ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) / (((((2 * (j + 1) : ℕ))) : ℝ) ^ 2))
    hpow
  have hfun : (fun y => chapter9Entry21LeftTerm y j) =
      (fun y => ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) /
        (((((2 * (j + 1) : ℕ))) : ℝ) ^ 2)) * Real.tan y ^ (2 * (j + 1))) := by
    funext y
    rw [aux_leftTerm_eq]
    ring
  have hval : ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) /
        (((((2 * (j + 1) : ℕ))) : ℝ) ^ 2)) *
        (((((2 * (j + 1) : ℕ))) : ℝ) * Real.tan x ^ (2 * j + 1) *
          (1 / Real.cos x ^ 2)) = leftDerivTerm x j := by
    unfold leftDerivTerm
    field_simp
  rw [hfun]
  rw [hval] at hmul
  exact hmul

private lemma aux_oddHarmonic_le_card (n : ℕ) :
    chapter9OddHarmonic n ≤ (n : ℝ) := by
  unfold chapter9OddHarmonic
  calc ∑ j ∈ Finset.range n, 1 / ((((2 * j + 1 : ℕ))) : ℝ)
      ≤ ∑ j ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have h1 : (1 : ℝ) ≤ ((((2 * i + 1 : ℕ))) : ℝ) := by
          have h : (1 : ℕ) ≤ 2 * i + 1 := by omega
          exact_mod_cast h
        have hle : 1 / ((((2 * i + 1 : ℕ))) : ℝ) ≤ 1 / (1 : ℝ) :=
          one_div_le_one_div_of_le (by norm_num) h1
        simpa using hle
    _ = (n : ℝ) := by simp

private lemma aux_oddHarmonic_div_le (j : ℕ) :
    chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ) ≤ 1 / 2 := by
  have hle : chapter9OddHarmonic (j + 1) ≤ ((((j + 1 : ℕ))) : ℝ) :=
    aux_oddHarmonic_le_card _
  have h2 : ((((2 * (j + 1) : ℕ))) : ℝ) = 2 * ((((j + 1 : ℕ))) : ℝ) := by
    push_cast
    ring
  have hj : (0 : ℝ) < ((((j + 1 : ℕ))) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have h2pos : (0 : ℝ) < 2 * ((((j + 1 : ℕ))) : ℝ) := by linarith
  rw [h2]
  calc chapter9OddHarmonic (j + 1) / (2 * ((((j + 1 : ℕ))) : ℝ))
      ≤ ((((j + 1 : ℕ))) : ℝ) / (2 * ((((j + 1 : ℕ))) : ℝ)) :=
        div_le_div_of_nonneg_right hle (le_of_lt h2pos)
    _ = 1 / 2 := by
        field_simp

private lemma aux_abs_tan_le_tan_b (b x : ℝ) (hb : b < Real.pi / 2)
    (hx : x ∈ Set.Ioo (-b) b) : |Real.tan x| ≤ Real.tan b := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx1 : -b < x := hx.1
  have hx2 : x < b := hx.2
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem1 : (-b) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem2 : b ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hneg : Real.tan (-b) = -Real.tan b := Real.tan_neg b
  have hlo : -Real.tan b ≤ Real.tan x := by
    rw [← hneg]
    exact (Real.strictMonoOn_tan.le_iff_le hmem1 hmem).mpr (le_of_lt hx1)
  have hhi : Real.tan x ≤ Real.tan b :=
    (Real.strictMonoOn_tan.le_iff_le hmem hmem2).mpr (le_of_lt hx2)
  exact abs_le.mpr ⟨hlo, hhi⟩

private lemma aux_tan_b_bounds (b : ℝ) (hb0 : 0 ≤ b) (hb : b < Real.pi / 4) :
    0 ≤ Real.tan b ∧ Real.tan b < 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem : b ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem4 : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hnonneg : 0 ≤ Real.tan b := by
    have h0 : Real.tan 0 = 0 := Real.tan_zero
    rw [← h0]
    exact (Real.strictMonoOn_tan.le_iff_le hmem0 hmem).mpr hb0
  have hlt : Real.tan b < 1 := by
    have h := Real.strictMonoOn_tan hmem hmem4 hb
    rwa [Real.tan_pi_div_four] at h
  exact ⟨hnonneg, hlt⟩

private lemma aux_cos_inv_sq_le (b x : ℝ) (hb : b < Real.pi / 2)
    (hx : x ∈ Set.Ioo (-b) b) :
    1 / Real.cos x ^ 2 ≤ 1 / Real.cos b ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have habs : |x| < b := abs_lt.mpr ⟨hx.1, hx.2⟩
  have hle : |x| ≤ b := le_of_lt habs
  have hcos_le : Real.cos b ≤ Real.cos |x| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg x) (by linarith) hle
  have hcos_abs : Real.cos |x| = Real.cos x := Real.cos_abs x
  rw [hcos_abs] at hcos_le
  have hmem_x : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := hx.1; have := hx.2; linarith)
  have hmem_b : b ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := hx.1; have := hx.2; linarith)
  have hpos_x : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hmem_x
  have hpos_b : 0 < Real.cos b := Real.cos_pos_of_mem_Ioo hmem_b
  have hsq_le : Real.cos b ^ 2 ≤ Real.cos x ^ 2 :=
    pow_le_pow_left₀ (le_of_lt hpos_b) hcos_le 2
  exact one_div_le_one_div_of_le (pow_pos hpos_b 2) hsq_le

private lemma aux_deriv_norm_le (b x : ℝ) (j : ℕ) (hb0 : 0 ≤ b)
    (hb : b < Real.pi / 4) (hx : x ∈ Set.Ioo (-b) b) :
    ‖leftDerivTerm x j‖ ≤
      (1 / (2 * Real.cos b ^ 2)) * Real.tan b ^ (2 * j + 1) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hb2 : b < Real.pi / 2 := by linarith
  have htan_b := aux_tan_b_bounds b hb0 hb
  have htan_le := aux_abs_tan_le_tan_b b x hb2 hx
  have hcos_le := aux_cos_inv_sq_le b x hb2 hx
  have hdiv_le := aux_oddHarmonic_div_le j
  have hHnn := aux_oddHarmonic_nonneg (j + 1)
  have hNpos : (0 : ℝ) < ((((2 * (j + 1) : ℕ))) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hmem_x : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := hx.1; have := hx.2; linarith)
  have hpos_x : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hmem_x
  have hcosx2pos : (0 : ℝ) < Real.cos x ^ 2 := pow_pos hpos_x 2
  have hnorm : ‖leftDerivTerm x j‖ =
      chapter9OddHarmonic (j + 1) * |Real.tan x| ^ (2 * j + 1) /
        (((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos x ^ 2) := by
    unfold leftDerivTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    have hnum : |(-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) *
        Real.tan x ^ (2 * j + 1)| =
        chapter9OddHarmonic (j + 1) * |Real.tan x| ^ (2 * j + 1) := by
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg hHnn, abs_pow]
    have hden : |((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos x ^ 2| =
        ((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos x ^ 2 :=
      abs_of_pos (mul_pos hNpos hcosx2pos)
    rw [hnum, hden]
  rw [hnorm]
  have hprod : chapter9OddHarmonic (j + 1) * |Real.tan x| ^ (2 * j + 1) /
      (((((2 * (j + 1) : ℕ))) : ℝ) * Real.cos x ^ 2) =
      (chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ)) *
        |Real.tan x| ^ (2 * j + 1) * (1 / Real.cos x ^ 2) := by
    ring
  rw [hprod]
  have hpow_le : |Real.tan x| ^ (2 * j + 1) ≤ Real.tan b ^ (2 * j + 1) :=
    pow_le_pow_left₀ (abs_nonneg _) htan_le _
  calc (chapter9OddHarmonic (j + 1) / ((((2 * (j + 1) : ℕ))) : ℝ)) *
        |Real.tan x| ^ (2 * j + 1) * (1 / Real.cos x ^ 2)
        ≤ (1 / 2) * Real.tan b ^ (2 * j + 1) * (1 / Real.cos b ^ 2) := by
          gcongr
          exact mul_nonneg (by norm_num) (pow_nonneg htan_b.1 _)
      _ = (1 / (2 * Real.cos b ^ 2)) * Real.tan b ^ (2 * j + 1) := by
          ring

private lemma aux_tan_pow_split (b : ℝ) (j : ℕ) :
    Real.tan b ^ (2 * j + 1) = Real.tan b * (Real.tan b ^ 2) ^ j := by
  rw [pow_add, pow_one, pow_mul, mul_comm]

private lemma aux_majorant_summable (b : ℝ) (hb0 : 0 ≤ b) (hb : b < Real.pi / 4) :
    Summable (fun j => (1 / (2 * Real.cos b ^ 2)) * Real.tan b ^ (2 * j + 1)) := by
  have htan := aux_tan_b_bounds b hb0 hb
  have hnn := htan.1
  have hlt := htan.2
  have hr0 : (0 : ℝ) ≤ Real.tan b ^ 2 := sq_nonneg _
  have hr1 : Real.tan b ^ 2 < 1 := by
    have h1 : (0 : ℝ) < 1 - Real.tan b := by linarith
    have h2 : (0 : ℝ) < 1 + Real.tan b := by linarith
    have hmul : (0 : ℝ) < (1 - Real.tan b) * (1 + Real.tan b) := mul_pos h1 h2
    have hexpand : (1 - Real.tan b) * (1 + Real.tan b) = 1 - Real.tan b ^ 2 := by
      ring
    linarith
  have hgeom : Summable (fun j : ℕ => (Real.tan b ^ 2) ^ j) :=
    summable_geometric_of_lt_one hr0 hr1
  have hcongr : (fun j => (1 / (2 * Real.cos b ^ 2)) * Real.tan b ^ (2 * j + 1)) =
      (fun j => ((1 / (2 * Real.cos b ^ 2)) * Real.tan b) *
        (Real.tan b ^ 2) ^ j) := by
    funext j
    rw [aux_tan_pow_split]
    ring
  rw [hcongr]
  exact hgeom.mul_left _

private lemma aux_left_hasDerivAt_tsum (b x : ℝ) (hb0 : 0 < b)
    (hb : b < Real.pi / 4) (hx : x ∈ Set.Ioo (-b) b) :
    HasDerivAt (fun z => ∑' j, chapter9Entry21LeftTerm z j)
      (∑' j, leftDerivTerm x j) x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hb0' : 0 ≤ b := le_of_lt hb0
  have hu := aux_majorant_summable b hb0' hb
  have ht : IsOpen (Set.Ioo (-b) b) := isOpen_Ioo
  have h't : IsPreconnected (Set.Ioo (-b : ℝ) b) := isPreconnected_Ioo
  have hg : ∀ n y, y ∈ Set.Ioo (-b) b →
      HasDerivAt (fun z => chapter9Entry21LeftTerm z n) (leftDerivTerm y n) y := by
    intro n y hy
    have hmem : y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> (have := hy.1; have := hy.2; linarith)
    exact aux_left_hasDerivAt y n hmem
  have hg' : ∀ n y, y ∈ Set.Ioo (-b) b →
      ‖leftDerivTerm y n‖ ≤
        (1 / (2 * Real.cos b ^ 2)) * Real.tan b ^ (2 * n + 1) := by
    intro n y hy
    exact aux_deriv_norm_le b y n hb0' hb hy
  have hy₀ : (0 : ℝ) ∈ Set.Ioo (-b) b := ⟨by linarith, by linarith⟩
  have h0 : |(0 : ℝ)| ≤ Real.pi / 4 := by
    rw [abs_zero]
    have hpi4 : (0 : ℝ) < Real.pi / 4 := by linarith
    exact le_of_lt hpi4
  have hg0 : Summable (fun n => chapter9Entry21LeftTerm 0 n) :=
    summable_left 0 h0
  exact hasDerivAt_tsum_of_isPreconnected hu ht h't hg hg' hy₀ hg0 hx

private lemma aux_abs_tan_lt_one (x : ℝ) (hx : |x| < Real.pi / 4) :
    |Real.tan x| < 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx1 : -(Real.pi / 4) < x := (abs_lt.mp hx).1
  have hx2 : x < Real.pi / 4 := (abs_lt.mp hx).2
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem1 : (-(Real.pi / 4)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hmem2 : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hlo : -1 < Real.tan x := by
    have h := Real.strictMonoOn_tan hmem1 hmem hx1
    rwa [Real.tan_neg, Real.tan_pi_div_four] at h
  have hhi : Real.tan x < 1 := by
    have h := Real.strictMonoOn_tan hmem hmem2 hx2
    rwa [Real.tan_pi_div_four] at h
  exact abs_lt.mpr ⟨hlo, hhi⟩

private lemma aux_deriv_sum_zero : (∑' j, leftDerivTerm 0 j) = 0 := by
  have hzero : (fun j => leftDerivTerm 0 j) = fun _ => 0 := by
    funext j
    unfold leftDerivTerm
    rw [Real.tan_zero]
    have hexp : 2 * j + 1 ≠ 0 := by omega
    rw [zero_pow hexp, mul_zero, zero_div]
  rw [hzero]
  exact tsum_zero

private lemma aux_chapF_zero : chapF 0 = 0 := by
  unfold chapF
  simp

private lemma aux_tan_ne_zero (x : ℝ) (hx0 : x ≠ 0)
    (hx : |x| < Real.pi / 4) : Real.tan x ≠ 0 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have habs := abs_lt.mp hx
    constructor <;> linarith [habs.1, habs.2]
  have hmem0 : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  intro hcon
  have h0 : Real.tan 0 = 0 := Real.tan_zero
  have heq : Real.tan x = Real.tan 0 := hcon.trans h0.symm
  have hinj := Real.strictMonoOn_tan.injOn
  have hx_eq : x = 0 := hinj hmem hmem0 heq
  exact hx0 hx_eq

private lemma aux_tan_mul_deriv (x : ℝ) (j : ℕ) :
    Real.tan x * leftDerivTerm x j =
      (1 / (2 * Real.cos x ^ 2)) *
        ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 2) /
          ((((j + 1 : ℕ))) : ℝ)) := by
  have hpow : Real.tan x * Real.tan x ^ (2 * j + 1) = Real.tan x ^ (2 * j + 2) := by
    have hexp : 2 * j + 2 = (2 * j + 1) + 1 := by omega
    conv_rhs => rw [hexp, pow_succ]
    exact mul_comm _ _
  have hN2 : ((((2 * (j + 1) : ℕ))) : ℝ) = 2 * ((((j + 1 : ℕ))) : ℝ) := by
    push_cast
    ring
  unfold leftDerivTerm
  rw [hN2, ← mul_div_assoc]
  have hnum : Real.tan x * ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) *
      Real.tan x ^ (2 * j + 1)) =
      (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) * Real.tan x ^ (2 * j + 2) := by
    rw [← hpow]
    ring
  rw [hnum, div_mul_div_comm, one_mul]
  congr 1
  ring

private lemma aux_sin_ne_zero (y : ℝ) (hy0 : y ≠ 0) (hy : |y| < Real.pi) :
    Real.sin y ≠ 0 := by
  by_cases hpos : 0 < y
  · have hmem : y ∈ Set.Ioo 0 Real.pi := by
      have habs := abs_lt.mp hy
      exact ⟨hpos, by linarith [habs.2]⟩
    exact ne_of_gt (Real.sin_pos_of_mem_Ioo hmem)
  · have hneg : y < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hy0
    have hmem : -y ∈ Set.Ioo 0 Real.pi := by
      have habs := abs_lt.mp hy
      constructor <;> linarith [habs.1, hneg]
    have hpos_neg := Real.sin_pos_of_mem_Ioo hmem
    rw [Real.sin_neg] at hpos_neg
    have : Real.sin y < 0 := by linarith
    exact ne_of_lt this

private lemma aux_deriv_sum_eq_chapF (x : ℝ) (hx : |x| < Real.pi / 4) :
    (∑' j, leftDerivTerm x j) = chapF x := by
  by_cases hx0 : x = 0
  · subst hx0
    rw [aux_deriv_sum_zero, aux_chapF_zero]
  · have hpi : 0 < Real.pi := Real.pi_pos
    have htan1 : |Real.tan x| < 1 := aux_abs_tan_lt_one x hx
    have htan_ne := aux_tan_ne_zero x hx0 hx
    have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      have habs := abs_lt.mp hx
      constructor <;> linarith [habs.1, habs.2]
    have hcos : Real.cos x ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
    have hcos2 : Real.cos x ^ 2 ≠ 0 := pow_ne_zero 2 hcos
    have hsinx : Real.sin x ≠ 0 := by
      apply aux_sin_ne_zero x hx0
      calc |x| < Real.pi / 4 := hx
        _ < Real.pi := by linarith
    have hsin2x : Real.sin (2 * x) ≠ 0 := by
      apply aux_sin_ne_zero (2 * x) (mul_ne_zero (by norm_num) hx0)
      calc |2 * x| = 2 * |x| := by rw [abs_mul, abs_two]
        _ < 2 * (Real.pi / 4) := by
            apply mul_lt_mul_of_pos_left hx (by norm_num)
        _ = Real.pi / 2 := by ring
        _ < Real.pi := by linarith
    have htarget_tsum := aux_arctan_sq_series (Real.tan x) htan1
    have harctan : Real.arctan (Real.tan x) = x := Real.arctan_tan hmem.1 hmem.2
    have hT : (∑' j, (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) *
        Real.tan x ^ (2 * j + 2) / ((((j + 1 : ℕ))) : ℝ)) = x ^ 2 := by
      rw [htarget_tsum, harctan]
    have hmul : Real.tan x * (∑' j, leftDerivTerm x j) =
        (1 / (2 * Real.cos x ^ 2)) *
          (∑' j, (-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) *
            Real.tan x ^ (2 * j + 2) / ((((j + 1 : ℕ))) : ℝ)) := by
      have h2 : (∑' j, Real.tan x * leftDerivTerm x j) =
          ∑' j, (1 / (2 * Real.cos x ^ 2)) *
            ((-1 : ℝ) ^ j * chapter9OddHarmonic (j + 1) *
              Real.tan x ^ (2 * j + 2) / ((((j + 1 : ℕ))) : ℝ)) :=
        tsum_congr (fun j => aux_tan_mul_deriv x j)
      rw [← tsum_mul_left, h2, tsum_mul_left]
    rw [hT] at hmul
    have htan_chapF : Real.tan x * chapF x = (1 / (2 * Real.cos x ^ 2)) * x ^ 2 := by
      unfold chapF
      have htan_eq : Real.tan x = Real.sin x / Real.cos x :=
        Real.tan_eq_sin_div_cos x
      have hsin2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
        rw [Real.sin_two_mul]
      rw [htan_eq, hsin2]
      field_simp
    have hcancel : Real.tan x * (∑' j, leftDerivTerm x j) = Real.tan x * chapF x := by
      rw [hmul, htan_chapF]
    exact mul_left_cancel₀ htan_ne hcancel

private lemma aux_chapF_eq_sinc (u : ℝ) :
    chapF u = u / (2 * Real.sinc (2 * u)) := by
  unfold chapF
  by_cases hu : u = 0
  · subst hu
    simp
  · by_cases hsin : Real.sin (2 * u) = 0
    · have h2u : (2 : ℝ) * u ≠ 0 := mul_ne_zero (by norm_num) hu
      rw [hsin, Real.sinc_of_ne_zero h2u, hsin]
      simp
    · have h2u : (2 : ℝ) * u ≠ 0 := mul_ne_zero (by norm_num) hu
      rw [Real.sinc_of_ne_zero h2u]
      field_simp

private lemma aux_chapF_continuousOn :
    ContinuousOn chapF (Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) := by
  have hfun : chapF = fun u => u / (2 * Real.sinc (2 * u)) :=
    funext aux_chapF_eq_sinc
  rw [hfun]
  apply ContinuousOn.div continuous_id.continuousOn _ _
  · have h1 : Continuous (fun u : ℝ => (2 : ℝ) * u) :=
      continuous_const.mul continuous_id
    have h2 : Continuous (fun u : ℝ => Real.sinc (2 * u)) :=
      Real.continuous_sinc.comp h1
    have h3 : Continuous (fun u : ℝ => 2 * Real.sinc (2 * u)) :=
      continuous_const.mul h2
    exact h3.continuousOn
  · intro u hu
    have hpi : 0 < Real.pi := Real.pi_pos
    have habs_u : |u| < Real.pi / 2 := abs_lt.mpr ⟨hu.1, hu.2⟩
    have h2u_abs : |2 * u| < Real.pi := by
      calc |2 * u| = 2 * |u| := by rw [abs_mul, abs_two]
        _ < 2 * (Real.pi / 2) := by
            apply mul_lt_mul_of_pos_left habs_u (by norm_num)
        _ = Real.pi := by ring
    by_cases h2u0 : (2 : ℝ) * u = 0
    · rw [h2u0, Real.sinc_zero]
      norm_num
    · have hsinc : Real.sinc (2 * u) = Real.sin (2 * u) / (2 * u) :=
        Real.sinc_of_ne_zero h2u0
      have hsin : Real.sin (2 * u) ≠ 0 := aux_sin_ne_zero (2 * u) h2u0 h2u_abs
      rw [hsinc]
      exact mul_ne_zero (by norm_num) (div_ne_zero hsin h2u0)

private lemma aux_mem_uIcc_abs_le (x y : ℝ) (hy : y ∈ Set.uIcc 0 x) :
    |y| ≤ |x| := by
  rw [Set.mem_uIcc] at hy
  rcases hy with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have hx_nn : 0 ≤ x := le_trans h1 h2
    rw [abs_of_nonneg h1, abs_of_nonneg hx_nn]
    exact h2
  · have hx_np : x ≤ 0 := le_trans h1 h2
    rw [abs_of_nonpos h2, abs_of_nonpos hx_np]
    linarith

private lemma aux_exists_b (y : ℝ) (hy : |y| < Real.pi / 4) :
    ∃ b, 0 < b ∧ b < Real.pi / 4 ∧ y ∈ Set.Ioo (-b) b := by
  refine ⟨(|y| + Real.pi / 4) / 2, by linarith [abs_nonneg y, Real.pi_pos],
    by linarith [hy], ?_⟩
  have hb : |y| < (|y| + Real.pi / 4) / 2 := by linarith [hy]
  exact abs_lt.mp hb

private lemma aux_left_tsum_zero :
    (∑' j, chapter9Entry21LeftTerm 0 j) = 0 := by
  have hzero : (fun j => chapter9Entry21LeftTerm 0 j) = fun _ => 0 := by
    funext j
    rw [aux_leftTerm_eq, Real.tan_zero]
    have hexp : 2 * (j + 1) ≠ 0 := by omega
    rw [zero_pow hexp, mul_zero, zero_div]
  rw [hzero]
  exact tsum_zero

private lemma aux_left_eq_integral_open (x : ℝ) (hx : |x| < Real.pi / 4) :
    (∑' j, chapter9Entry21LeftTerm x j) = ∫ u in (0 : ℝ)..x, chapF u := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hderiv : ∀ y ∈ Set.uIcc 0 x,
      HasDerivAt (fun z => ∑' j, chapter9Entry21LeftTerm z j) (chapF y) y := by
    intro y hy
    have hy_abs : |y| ≤ |x| := aux_mem_uIcc_abs_le x y hy
    have hy_lt : |y| < Real.pi / 4 := lt_of_le_of_lt hy_abs hx
    obtain ⟨b, hb0, hb, hyb⟩ := aux_exists_b y hy_lt
    have hderiv_tsum := aux_left_hasDerivAt_tsum b y hb0 hb hyb
    rwa [aux_deriv_sum_eq_chapF y hy_lt] at hderiv_tsum
  have hint : IntervalIntegrable chapF MeasureTheory.volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    have hsub : Set.uIcc 0 x ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro y hy
      have hy_abs : |y| ≤ |x| := aux_mem_uIcc_abs_le x y hy
      have hy_lt : |y| < Real.pi / 2 := by
        calc |y| ≤ |x| := hy_abs
          _ < Real.pi / 4 := hx
          _ < Real.pi / 2 := by linarith
      exact abs_lt.mp hy_lt
    exact aux_chapF_continuousOn.mono hsub
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [aux_left_tsum_zero, sub_zero] at hftc
  exact hftc.symm

private lemma aux_leftTerm_continuousOn (j : ℕ) :
    ContinuousOn (fun x => chapter9Entry21LeftTerm x j)
      (Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsub : Set.Icc (-(Real.pi / 4)) (Real.pi / 4) ⊆ {x | Real.cos x ≠ 0} := by
    intro x hx
    have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [hx.1, hx.2]
    exact ne_of_gt (Real.cos_pos_of_mem_Ioo hmem)
  have htan := Real.continuousOn_tan.mono hsub
  simp only [aux_leftTerm_eq]
  exact ((htan.pow _).const_mul _).div_const _

private lemma aux_left_continuousOn :
    ContinuousOn (fun x => ∑' j, chapter9Entry21LeftTerm x j)
      (Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) := by
  refine continuousOn_tsum (fun j => aux_leftTerm_continuousOn j)
    aux_summable_shift_threehalves ?_
  intro j x hx
  have hx_abs : |x| ≤ Real.pi / 4 := abs_le.mpr ⟨hx.1, hx.2⟩
  exact aux_left_norm_le x j hx_abs

private lemma aux_integral_continuousOn :
    ContinuousOn (fun x => ∫ u in (0 : ℝ)..x, chapF u)
      (Set.Icc (-(Real.pi / 4)) (Real.pi / 4)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hle : -(Real.pi / 4) ≤ Real.pi / 4 := by linarith
  have hsub : Set.uIcc (-(Real.pi / 4)) (Real.pi / 4) ⊆
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro y hy
    rw [Set.uIcc_of_le hle] at hy
    constructor <;> linarith [hy.1, hy.2]
  have hcont : ContinuousOn chapF (Set.uIcc (-(Real.pi / 4)) (Real.pi / 4)) :=
    aux_chapF_continuousOn.mono hsub
  have hint : IntervalIntegrable chapF MeasureTheory.volume
      (-(Real.pi / 4)) (Real.pi / 4) := hcont.intervalIntegrable
  have h0mem : (0 : ℝ) ∈ Set.uIcc (-(Real.pi / 4)) (Real.pi / 4) := by
    rw [Set.uIcc_of_le hle]
    constructor <;> linarith
  have hprim := intervalIntegral.continuousOn_primitive_interval' hint h0mem
  rwa [Set.uIcc_of_le hle] at hprim

private lemma aux_left_eq_integral_closed (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    (∑' j, chapter9Entry21LeftTerm x j) = ∫ u in (0 : ℝ)..x, chapF u := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hEq : Set.EqOn (fun z => ∑' j, chapter9Entry21LeftTerm z j)
      (fun z => ∫ u in (0 : ℝ)..z, chapF u)
      (Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) := by
    intro z hz
    have hz_abs : |z| < Real.pi / 4 := abs_lt.mpr ⟨hz.1, hz.2⟩
    exact aux_left_eq_integral_open z hz_abs
  have hne : -(Real.pi / 4) ≠ Real.pi / 4 := by
    intro hcon
    have : Real.pi = 0 := by linarith
    exact ne_of_gt hpi this
  have hsub2 : Set.Icc (-(Real.pi / 4)) (Real.pi / 4) ⊆
      closure (Set.Ioo (-(Real.pi / 4)) (Real.pi / 4)) := by
    rw [closure_Ioo hne]
  have hEqClosed := Set.EqOn.of_subset_closure hEq aux_left_continuousOn
    aux_integral_continuousOn Set.Ioo_subset_Icc_self hsub2
  have hx_mem : x ∈ Set.Icc (-(Real.pi / 4)) (Real.pi / 4) := abs_le.mp hx
  exact hEqClosed hx_mem

private def SrTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.sin (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 2)

private def CrTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    (((2 * j + 1 : ℕ) : ℝ) ^ 3)

private def ArTerm (r x : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) * Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) /
    ((2 * j + 1 : ℕ) : ℝ)

private lemma aux_SrTerm_norm_le (r x : ℝ) (j : ℕ) :
    ‖SrTerm r x j‖ ≤ |r| ^ (2 * j + 1) := by
  have hD1 : (1 : ℝ) ≤ (((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
    have h1 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ 2 * j + 1 := by omega
      exact_mod_cast h
    calc (1 : ℝ) = 1 ^ 2 := (one_pow 2).symm
      _ ≤ (((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
        pow_le_pow_left₀ (by norm_num) h1 2
  have hDpos : (0 : ℝ) < (((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
    pow_pos (Nat.cast_pos.mpr (by omega)) 2
  have hnorm : ‖SrTerm r x j‖ =
      |r| ^ (2 * j + 1) *
        (|Real.sin (((4 * j + 2 : ℕ) : ℝ) * x)| /
          (((2 * j + 1 : ℕ) : ℝ) ^ 2)) := by
    unfold SrTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hDpos]
    ring
  have htrig : |Real.sin (((4 * j + 2 : ℕ) : ℝ) * x)| /
      (((2 * j + 1 : ℕ) : ℝ) ^ 2) ≤ 1 := by
    have hle : |Real.sin (((4 * j + 2 : ℕ) : ℝ) * x)| ≤
        (((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
      le_trans (Real.abs_sin_le_one _) hD1
    calc |Real.sin (((4 * j + 2 : ℕ) : ℝ) * x)| / (((2 * j + 1 : ℕ) : ℝ) ^ 2)
        ≤ (((2 * j + 1 : ℕ) : ℝ) ^ 2) / (((2 * j + 1 : ℕ) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hle (le_of_lt hDpos)
      _ = 1 := div_self (ne_of_gt hDpos)
  calc ‖SrTerm r x j‖
      = |r| ^ (2 * j + 1) *
          (|Real.sin (((4 * j + 2 : ℕ) : ℝ) * x)| /
            (((2 * j + 1 : ℕ) : ℝ) ^ 2)) := hnorm
    _ ≤ |r| ^ (2 * j + 1) * 1 :=
        mul_le_mul_of_nonneg_left htrig (pow_nonneg (abs_nonneg _) _)
    _ = |r| ^ (2 * j + 1) := mul_one _

private lemma aux_CrTerm_norm_le (r x : ℝ) (j : ℕ) :
    ‖CrTerm r x j‖ ≤ |r| ^ (2 * j + 1) := by
  have hD1 : (1 : ℝ) ≤ (((2 * j + 1 : ℕ) : ℝ) ^ 3) := by
    have h1 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
      have h : (1 : ℕ) ≤ 2 * j + 1 := by omega
      exact_mod_cast h
    calc (1 : ℝ) = 1 ^ 3 := (one_pow 3).symm
      _ ≤ (((2 * j + 1 : ℕ) : ℝ) ^ 3) :=
        pow_le_pow_left₀ (by norm_num) h1 3
  have hDpos : (0 : ℝ) < (((2 * j + 1 : ℕ) : ℝ) ^ 3) :=
    pow_pos (Nat.cast_pos.mpr (by omega)) 3
  have hnorm : ‖CrTerm r x j‖ =
      |r| ^ (2 * j + 1) *
        (|Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| /
          (((2 * j + 1 : ℕ) : ℝ) ^ 3)) := by
    unfold CrTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hDpos]
    ring
  have htrig : |Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| /
      (((2 * j + 1 : ℕ) : ℝ) ^ 3) ≤ 1 := by
    have hle : |Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| ≤
        (((2 * j + 1 : ℕ) : ℝ) ^ 3) :=
      le_trans (Real.abs_cos_le_one _) hD1
    calc |Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| / (((2 * j + 1 : ℕ) : ℝ) ^ 3)
        ≤ (((2 * j + 1 : ℕ) : ℝ) ^ 3) / (((2 * j + 1 : ℕ) : ℝ) ^ 3) :=
          div_le_div_of_nonneg_right hle (le_of_lt hDpos)
      _ = 1 := div_self (ne_of_gt hDpos)
  calc ‖CrTerm r x j‖
      = |r| ^ (2 * j + 1) *
          (|Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| /
            (((2 * j + 1 : ℕ) : ℝ) ^ 3)) := hnorm
    _ ≤ |r| ^ (2 * j + 1) * 1 :=
        mul_le_mul_of_nonneg_left htrig (pow_nonneg (abs_nonneg _) _)
    _ = |r| ^ (2 * j + 1) := mul_one _

private lemma aux_ArTerm_norm_le (r x : ℝ) (j : ℕ) :
    ‖ArTerm r x j‖ ≤ |r| ^ (2 * j + 1) := by
  have hD1 : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by
    have h : (1 : ℕ) ≤ 2 * j + 1 := by omega
    exact_mod_cast h
  have hDpos : (0 : ℝ) < ((2 * j + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hnorm : ‖ArTerm r x j‖ =
      |r| ^ (2 * j + 1) *
        (|Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| / ((2 * j + 1 : ℕ) : ℝ)) := by
    unfold ArTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hDpos]
    ring
  have htrig : |Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| /
      ((2 * j + 1 : ℕ) : ℝ) ≤ 1 := by
    have hle : |Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| ≤
        ((2 * j + 1 : ℕ) : ℝ) :=
      le_trans (Real.abs_cos_le_one _) hD1
    calc |Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| / ((2 * j + 1 : ℕ) : ℝ)
        ≤ ((2 * j + 1 : ℕ) : ℝ) / ((2 * j + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hle (le_of_lt hDpos)
      _ = 1 := div_self (ne_of_gt hDpos)
  calc ‖ArTerm r x j‖
      = |r| ^ (2 * j + 1) *
          (|Real.cos (((4 * j + 2 : ℕ) : ℝ) * x)| / ((2 * j + 1 : ℕ) : ℝ)) :=
        hnorm
    _ ≤ |r| ^ (2 * j + 1) * 1 :=
        mul_le_mul_of_nonneg_left htrig (pow_nonneg (abs_nonneg _) _)
    _ = |r| ^ (2 * j + 1) := mul_one _

private lemma aux_rpow_geom_summable (r : ℝ) (hr : |r| < 1) :
    Summable (fun j : ℕ => |r| * (|r| ^ 2) ^ j) := by
  have hr0 : (0 : ℝ) ≤ |r| ^ 2 := sq_nonneg _
  have hr1 : |r| ^ 2 < 1 := by
    have h1 : (0 : ℝ) < 1 - |r| := by linarith
    have h2 : (0 : ℝ) < 1 + |r| := by
      have hnn := abs_nonneg r
      linarith
    have hmul : (0 : ℝ) < (1 - |r|) * (1 + |r|) := mul_pos h1 h2
    have hexpand : (1 - |r|) * (1 + |r|) = 1 - |r| ^ 2 := by ring
    linarith
  exact (summable_geometric_of_lt_one hr0 hr1).mul_left _

private lemma aux_Sr_summable (r x : ℝ) (hr : |r| < 1) :
    Summable (SrTerm r x) := by
  apply Summable.of_norm
  have hgeom := aux_rpow_geom_summable r hr
  refine Summable.of_nonneg_of_le (f := fun j : ℕ => |r| * (|r| ^ 2) ^ j)
    (fun j => norm_nonneg _) ?_ hgeom
  intro j
  calc ‖SrTerm r x j‖ ≤ |r| ^ (2 * j + 1) := aux_SrTerm_norm_le r x j
    _ = |r| * (|r| ^ 2) ^ j := aux_abs_pow_split r j

private lemma aux_Cr_summable (r x : ℝ) (hr : |r| < 1) :
    Summable (CrTerm r x) := by
  apply Summable.of_norm
  have hgeom := aux_rpow_geom_summable r hr
  refine Summable.of_nonneg_of_le (f := fun j : ℕ => |r| * (|r| ^ 2) ^ j)
    (fun j => norm_nonneg _) ?_ hgeom
  intro j
  calc ‖CrTerm r x j‖ ≤ |r| ^ (2 * j + 1) := aux_CrTerm_norm_le r x j
    _ = |r| * (|r| ^ 2) ^ j := aux_abs_pow_split r j

private lemma aux_Ar_summable (r x : ℝ) (hr : |r| < 1) :
    Summable (ArTerm r x) := by
  apply Summable.of_norm
  have hgeom := aux_rpow_geom_summable r hr
  refine Summable.of_nonneg_of_le (f := fun j : ℕ => |r| * (|r| ^ 2) ^ j)
    (fun j => norm_nonneg _) ?_ hgeom
  intro j
  calc ‖ArTerm r x j‖ ≤ |r| ^ (2 * j + 1) := aux_ArTerm_norm_le r x j
    _ = |r| * (|r| ^ 2) ^ j := aux_abs_pow_split r j

private def abelW (r x : ℝ) : ℂ :=
  (r : ℂ) * Complex.exp ((2 * x : ℝ) * Complex.I)

private lemma aux_abelW_norm (r x : ℝ) : ‖abelW r x‖ = |r| := by
  unfold abelW
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_exp_ofReal_mul_I,
    mul_one, Real.norm_eq_abs]

private lemma aux_abelW_pow_re (r x : ℝ) (j : ℕ) :
    (abelW r x ^ (2 * j + 1)).re =
      r ^ (2 * j + 1) * Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) := by
  unfold abelW
  rw [mul_pow]
  have hpow_r : (r : ℂ) ^ (2 * j + 1) = (((r ^ (2 * j + 1) : ℝ)) : ℂ) :=
    (Complex.ofReal_pow _ _).symm
  rw [hpow_r]
  have hexp_pow : Complex.exp ((2 * x : ℝ) * Complex.I) ^ (2 * j + 1) =
      Complex.exp ((((4 * j + 2 : ℕ) : ℝ) * x : ℝ) * Complex.I) := by
    have harg : ((2 * j + 1 : ℕ) : ℂ) * (((2 * x : ℝ) : ℂ) * Complex.I) =
        ((((4 * j + 2 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have h := (Complex.exp_nat_mul (((2 * x : ℝ) : ℂ) * Complex.I) (2 * j + 1)).symm
    rwa [harg] at h
  rw [hexp_pow, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [Complex.exp_re]
  have hre : (((((4 * j + 2 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I).re = 0 := by
    simp
  have him : (((((4 * j + 2 : ℕ) : ℝ) * x : ℝ) : ℂ) * Complex.I).im =
      (((4 * j + 2 : ℕ) : ℝ) * x) := by
    simp
  rw [hre, him, Real.exp_zero, one_mul]

private lemma aux_log_sub_hasSum (r x : ℝ) (hr : |r| < 1) :
    HasSum (fun k : ℕ => (2 : ℂ) * (abelW r x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)))
      (Complex.log (1 + abelW r x) - Complex.log (1 - abelW r x)) := by
  have hw : ‖abelW r x‖ < 1 := by
    rw [aux_abelW_norm]
    exact hr
  have hwn : ‖-abelW r x‖ < 1 := by
    rw [norm_neg]
    exact hw
  set w := abelW r x with hwdef
  set term : ℕ → ℂ := fun n : ℕ =>
    -1 * ((-w) ^ (n + 1) / ((n : ℂ) + 1)) + w ^ (n + 1) / (n + 1) with htermdef
  have h_term_eq_goal :
      term ∘ (2 * ·) =
        fun k : ℕ => (2 : ℂ) * (w ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)) := by
    ext n
    dsimp only [term, (· ∘ ·)]
    rw [Odd.neg_pow (⟨n, rfl⟩ : Odd (2 * n + 1)) w]
    push_cast
    ring_nf
  rw [← h_term_eq_goal, (mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff]
  · have h₁ := (Complex.hasSum_taylorSeries_neg_log' hwn).mul_left (-1)
    have h₂ := Complex.hasSum_taylorSeries_neg_log' hw
    convert! h₁.add h₂ using 1
    ring_nf
  · intro m hm
    rw [range_two_mul, Set.mem_ofPred_eq, ← Nat.even_add_one] at hm
    dsimp [term]
    rw [Even.neg_pow hm, neg_one_mul, neg_add_cancel]

private def abelP (r x : ℝ) : ℝ := 1 + 2 * r * Real.cos (2 * x) + r ^ 2

private def abelM (r x : ℝ) : ℝ := 1 - 2 * r * Real.cos (2 * x) + r ^ 2

private def abelA (r x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * (Real.log (abelP r x) - Real.log (abelM r x))

private lemma aux_abelW_re (r x : ℝ) :
    (abelW r x).re = r * Real.cos (2 * x) := by
  have h := aux_abelW_pow_re r x 0
  simp only [mul_zero, zero_add, pow_one] at h
  have hcos : (((4 * 0 + 2 : ℕ) : ℝ) * x) = 2 * x := by
    norm_num
  rwa [hcos] at h

private lemma aux_abelW_im (r x : ℝ) :
    (abelW r x).im = r * Real.sin (2 * x) := by
  unfold abelW
  rw [Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  rw [Complex.exp_im]
  have hre : ((((2 * x : ℝ)) : ℂ) * Complex.I).re = 0 := by simp
  have him : ((((2 * x : ℝ)) : ℂ) * Complex.I).im = 2 * x := by simp
  rw [hre, him, Real.exp_zero, one_mul]

private lemma aux_P_eq_normSq (r x : ℝ) :
    abelP r x = ‖(1 : ℂ) + abelW r x‖ ^ 2 := by
  unfold abelP
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((1 : ℂ) + abelW r x).re = 1 + r * Real.cos (2 * x) := by
    rw [Complex.add_re, Complex.one_re, aux_abelW_re]
  have him : ((1 : ℂ) + abelW r x).im = r * Real.sin (2 * x) := by
    rw [Complex.add_im, Complex.one_im, aux_abelW_im, zero_add]
  rw [hre, him]
  have h := Real.sin_sq_add_cos_sq (2 * x)
  nlinarith [h]

private lemma aux_M_eq_normSq (r x : ℝ) :
    abelM r x = ‖(1 : ℂ) - abelW r x‖ ^ 2 := by
  unfold abelM
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((1 : ℂ) - abelW r x).re = 1 - r * Real.cos (2 * x) := by
    rw [Complex.sub_re, Complex.one_re, aux_abelW_re]
  have him : ((1 : ℂ) - abelW r x).im = -(r * Real.sin (2 * x)) := by
    rw [Complex.sub_im, Complex.one_im, aux_abelW_im, zero_sub]
  rw [hre, him]
  have h := Real.sin_sq_add_cos_sq (2 * x)
  nlinarith [h]

private lemma aux_P_pos (r x : ℝ) (hr : |r| < 1) : 0 < abelP r x := by
  rw [aux_P_eq_normSq]
  have hw : ‖abelW r x‖ < 1 := by
    rw [aux_abelW_norm]
    exact hr
  have htri : (1 : ℝ) - ‖abelW r x‖ ≤ ‖(1 : ℂ) + abelW r x‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (-abelW r x)
    rwa [sub_neg_eq_add, norm_neg, norm_one] at h
  have hpos : (0 : ℝ) < ‖(1 : ℂ) + abelW r x‖ := by linarith
  exact pow_pos hpos 2

private lemma aux_M_pos (r x : ℝ) (hr : |r| < 1) : 0 < abelM r x := by
  rw [aux_M_eq_normSq]
  have hw : ‖abelW r x‖ < 1 := by
    rw [aux_abelW_norm]
    exact hr
  have htri : (1 : ℝ) - ‖abelW r x‖ ≤ ‖(1 : ℂ) - abelW r x‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (abelW r x)
    rwa [norm_one] at h
  have hpos : (0 : ℝ) < ‖(1 : ℂ) - abelW r x‖ := by linarith
  exact pow_pos hpos 2

private lemma aux_logterm_re (r x : ℝ) (k : ℕ) :
    ((2 : ℂ) * (abelW r x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ))).re =
      2 * ArTerm r x k := by
  have hD : (((2 * k + 1 : ℕ)) : ℂ) = ((((2 * k + 1 : ℕ) : ℝ)) : ℂ) := by
    norm_cast
  have h2 : (2 : ℂ) = (((2 : ℝ)) : ℂ) := by norm_cast
  rw [hD, h2, Complex.re_ofReal_mul, Complex.div_ofReal_re,
    aux_abelW_pow_re]
  unfold ArTerm
  ring

private lemma aux_Ar_eq_closed (r x : ℝ) (hr : |r| < 1) :
    (∑' j, ArTerm r x j) = abelA r x := by
  have hHas := aux_log_sub_hasSum r x hr
  have hHas_re := Complex.hasSum_re hHas
  have hcongr : (fun k : ℕ =>
        ((2 : ℂ) * (abelW r x ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ))).re) =
      (fun k : ℕ => 2 * ArTerm r x k) :=
    funext (fun k => aux_logterm_re r x k)
  rw [hcongr] at hHas_re
  have htsum : (∑' k, 2 * ArTerm r x k) =
      (Complex.log (1 + abelW r x) - Complex.log (1 - abelW r x)).re :=
    hHas_re.tsum_eq
  rw [tsum_mul_left] at htsum
  have hw : ‖abelW r x‖ < 1 := by
    rw [aux_abelW_norm]
    exact hr
  have hpos1 : (0 : ℝ) < ‖(1 : ℂ) + abelW r x‖ := by
    have htri : (1 : ℝ) - ‖abelW r x‖ ≤ ‖(1 : ℂ) + abelW r x‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (-abelW r x)
      rwa [sub_neg_eq_add, norm_neg, norm_one] at h
    linarith
  have hpos2 : (0 : ℝ) < ‖(1 : ℂ) - abelW r x‖ := by
    have htri : (1 : ℝ) - ‖abelW r x‖ ≤ ‖(1 : ℂ) - abelW r x‖ := by
      have h := norm_sub_norm_le (1 : ℂ) (abelW r x)
      rwa [norm_one] at h
    linarith
  have hre : (Complex.log (1 + abelW r x) - Complex.log (1 - abelW r x)).re =
      Real.log ‖(1 : ℂ) + abelW r x‖ - Real.log ‖(1 : ℂ) - abelW r x‖ := by
    rw [Complex.sub_re, Complex.log_re, Complex.log_re]
  have hlogP : Real.log (abelP r x) = 2 * Real.log ‖(1 : ℂ) + abelW r x‖ := by
    rw [aux_P_eq_normSq, Real.log_pow]
    norm_num
  have hlogM : Real.log (abelM r x) = 2 * Real.log ‖(1 : ℂ) - abelW r x‖ := by
    rw [aux_M_eq_normSq, Real.log_pow]
    norm_num
  have hAv : abelA r x =
      (1 / 2 : ℝ) *
        (Real.log ‖(1 : ℂ) + abelW r x‖ - Real.log ‖(1 : ℂ) - abelW r x‖) := by
    unfold abelA
    rw [hlogP, hlogM]
    ring
  have hsum : (∑' j, ArTerm r x j) =
      (1 / 2 : ℝ) *
        (Real.log ‖(1 : ℂ) + abelW r x‖ - Real.log ‖(1 : ℂ) - abelW r x‖) := by
    have h2 : (2 : ℝ) * (∑' j, ArTerm r x j) =
        Real.log ‖(1 : ℂ) + abelW r x‖ - Real.log ‖(1 : ℂ) - abelW r x‖ := by
      rw [htsum, hre]
    linarith
  rw [hsum, hAv]

private lemma aux_SrTerm_hasDerivAt (r x : ℝ) (j : ℕ) :
    HasDerivAt (fun y => SrTerm r y j) (2 * ArTerm r x j) x := by
  have hinner : HasDerivAt (fun y : ℝ => (((4 * j + 2 : ℕ) : ℝ)) * y)
      ((((4 * j + 2 : ℕ) : ℝ))) x := by
    simpa using (hasDerivAt_id x).const_mul (((4 * j + 2 : ℕ) : ℝ))
  have hsin := hinner.sin
  have hK : HasDerivAt
      (fun y => (r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 2)) *
        Real.sin (((4 * j + 2 : ℕ) : ℝ) * y))
      ((r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 2)) *
        (Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) * (((4 * j + 2 : ℕ) : ℝ)))) x :=
    hsin.const_mul _
  have hfun : (fun y => SrTerm r y j) =
      (fun y => (r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 2)) *
        Real.sin (((4 * j + 2 : ℕ) : ℝ) * y)) := by
    funext y
    unfold SrTerm
    ring
  have hval : (r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 2)) *
        (Real.cos (((4 * j + 2 : ℕ) : ℝ) * x) * (((4 * j + 2 : ℕ) : ℝ))) =
      2 * ArTerm r x j := by
    unfold ArTerm
    have h4 : (((4 * j + 2 : ℕ) : ℝ)) = 2 * (((2 * j + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    have hD : (((2 * j + 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.ne_zero_of_lt (by omega : 0 < 2 * j + 1)
    rw [h4]
    field_simp
  rw [hfun]
  rwa [hval] at hK

private lemma aux_CrTerm_hasDerivAt (r x : ℝ) (j : ℕ) :
    HasDerivAt (fun y => CrTerm r y j) (-2 * SrTerm r x j) x := by
  have hinner : HasDerivAt (fun y : ℝ => (((4 * j + 2 : ℕ) : ℝ)) * y)
      ((((4 * j + 2 : ℕ) : ℝ))) x := by
    simpa using (hasDerivAt_id x).const_mul (((4 * j + 2 : ℕ) : ℝ))
  have hcos := hinner.cos
  have hK : HasDerivAt
      (fun y => (r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 3)) *
        Real.cos (((4 * j + 2 : ℕ) : ℝ) * y))
      ((r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 3)) *
        (-Real.sin (((4 * j + 2 : ℕ) : ℝ) * x) * (((4 * j + 2 : ℕ) : ℝ)))) x :=
    hcos.const_mul _
  have hfun : (fun y => CrTerm r y j) =
      (fun y => (r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 3)) *
        Real.cos (((4 * j + 2 : ℕ) : ℝ) * y)) := by
    funext y
    unfold CrTerm
    ring
  have hval : (r ^ (2 * j + 1) / (((2 * j + 1 : ℕ) : ℝ) ^ 3)) *
        (-Real.sin (((4 * j + 2 : ℕ) : ℝ) * x) * (((4 * j + 2 : ℕ) : ℝ))) =
      -2 * SrTerm r x j := by
    unfold SrTerm
    have h4 : (((4 * j + 2 : ℕ) : ℝ)) = 2 * (((2 * j + 1 : ℕ) : ℝ)) := by
      push_cast
      ring
    have hD : (((2 * j + 1 : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast Nat.ne_zero_of_lt (by omega : 0 < 2 * j + 1)
    rw [h4]
    field_simp
  rw [hfun]
  rwa [hval] at hK

private lemma aux_geom2_summable (r : ℝ) (hr : |r| < 1) :
    Summable (fun j : ℕ => 2 * |r| ^ (2 * j + 1)) := by
  have hgeom := aux_rpow_geom_summable r hr
  have hcongr : (fun j : ℕ => 2 * |r| ^ (2 * j + 1)) =
      (fun j : ℕ => (2 : ℝ) * (|r| * (|r| ^ 2) ^ j)) := by
    funext j
    rw [aux_abs_pow_split]
  rw [hcongr]
  exact hgeom.mul_left _

private lemma aux_Sr_hasDerivAt_tsum (r x : ℝ) (hr : |r| < 1) :
    HasDerivAt (fun y => ∑' j, SrTerm r y j) (∑' j, 2 * ArTerm r x j) x := by
  have hu := aux_geom2_summable r hr
  have hg : ∀ n y, HasDerivAt (fun z => SrTerm r z n) (2 * ArTerm r y n) y :=
    fun n y => aux_SrTerm_hasDerivAt r y n
  have hg' : ∀ n y, ‖2 * ArTerm r y n‖ ≤ 2 * |r| ^ (2 * n + 1) := by
    intro n y
    have hnorm2 : ‖(2 : ℝ)‖ = 2 := by
      rw [Real.norm_eq_abs, abs_two]
    calc ‖2 * ArTerm r y n‖ = ‖(2 : ℝ)‖ * ‖ArTerm r y n‖ := norm_mul _ _
      _ = 2 * ‖ArTerm r y n‖ := by rw [hnorm2]
      _ ≤ 2 * |r| ^ (2 * n + 1) :=
          mul_le_mul_of_nonneg_left (aux_ArTerm_norm_le r y n) (by norm_num)
  have hg0 : Summable (fun n => SrTerm r 0 n) := aux_Sr_summable r 0 hr
  exact hasDerivAt_tsum hu hg hg' hg0 x

private lemma aux_Sr_hasDerivAt (r x : ℝ) (hr : |r| < 1) :
    HasDerivAt (fun y => ∑' j, SrTerm r y j) (2 * (∑' j, ArTerm r x j)) x := by
  have h := aux_Sr_hasDerivAt_tsum r x hr
  rwa [tsum_mul_left] at h

private lemma aux_Cr_hasDerivAt_tsum (r x : ℝ) (hr : |r| < 1) :
    HasDerivAt (fun y => ∑' j, CrTerm r y j) (∑' j, -2 * SrTerm r x j) x := by
  have hu := aux_geom2_summable r hr
  have hg : ∀ n y, HasDerivAt (fun z => CrTerm r z n) (-2 * SrTerm r y n) y :=
    fun n y => aux_CrTerm_hasDerivAt r y n
  have hg' : ∀ n y, ‖-2 * SrTerm r y n‖ ≤ 2 * |r| ^ (2 * n + 1) := by
    intro n y
    have hnorm2 : ‖(-2 : ℝ)‖ = 2 := by
      rw [Real.norm_eq_abs]
      norm_num
    calc ‖-2 * SrTerm r y n‖ = ‖(-2 : ℝ)‖ * ‖SrTerm r y n‖ := norm_mul _ _
      _ = 2 * ‖SrTerm r y n‖ := by rw [hnorm2]
      _ ≤ 2 * |r| ^ (2 * n + 1) :=
          mul_le_mul_of_nonneg_left (aux_SrTerm_norm_le r y n) (by norm_num)
  have hg0 : Summable (fun n => CrTerm r 0 n) := aux_Cr_summable r 0 hr
  exact hasDerivAt_tsum hu hg hg' hg0 x

private lemma aux_Cr_hasDerivAt (r x : ℝ) (hr : |r| < 1) :
    HasDerivAt (fun y => ∑' j, CrTerm r y j) (-2 * (∑' j, SrTerm r x j)) x := by
  have h := aux_Cr_hasDerivAt_tsum r x hr
  rwa [tsum_mul_left] at h

private def abelQ (r x : ℝ) : ℝ :=
  2 * r * (1 + r ^ 2) * Real.sin (2 * x) /
    ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * x) ^ 2)

private lemma aux_cos2x_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y => Real.cos (2 * y)) (-Real.sin (2 * x) * 2) x := by
  have hinner : HasDerivAt (fun y : ℝ => (2 : ℝ) * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  exact hinner.cos

private lemma aux_P_hasDerivAt (r x : ℝ) :
    HasDerivAt (fun y => abelP r y) (-4 * r * Real.sin (2 * x)) x := by
  have hcos := aux_cos2x_hasDerivAt x
  have hmul : HasDerivAt (fun y => (2 * r) * Real.cos (2 * y))
      ((2 * r) * (-Real.sin (2 * x) * 2)) x :=
    hcos.const_mul _
  have hfun : (fun y => abelP r y) =
      (fun y => (1 + r ^ 2) + (2 * r) * Real.cos (2 * y)) := by
    funext y
    unfold abelP
    ring
  have hval : (2 * r) * (-Real.sin (2 * x) * 2) = -4 * r * Real.sin (2 * x) := by
    ring
  have hadd : HasDerivAt (fun y => (1 + r ^ 2) + (2 * r) * Real.cos (2 * y))
      ((2 * r) * (-Real.sin (2 * x) * 2)) x :=
    hmul.const_add _
  rw [← hfun, hval] at hadd
  exact hadd

private lemma aux_M_hasDerivAt (r x : ℝ) :
    HasDerivAt (fun y => abelM r y) (4 * r * Real.sin (2 * x)) x := by
  have hcos := aux_cos2x_hasDerivAt x
  have hmul : HasDerivAt (fun y => (-(2 * r)) * Real.cos (2 * y))
      ((-(2 * r)) * (-Real.sin (2 * x) * 2)) x :=
    hcos.const_mul _
  have hfun : (fun y => abelM r y) =
      (fun y => (1 + r ^ 2) + (-(2 * r)) * Real.cos (2 * y)) := by
    funext y
    unfold abelM
    ring
  have hval : (-(2 * r)) * (-Real.sin (2 * x) * 2) =
      4 * r * Real.sin (2 * x) := by
    ring
  have hadd : HasDerivAt (fun y => (1 + r ^ 2) + (-(2 * r)) * Real.cos (2 * y))
      ((-(2 * r)) * (-Real.sin (2 * x) * 2)) x :=
    hmul.const_add _
  rw [← hfun, hval] at hadd
  exact hadd

private lemma aux_PM_eq (r x : ℝ) :
    abelP r x * abelM r x =
      (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * x) ^ 2 := by
  unfold abelP abelM
  have h := Real.sin_sq_add_cos_sq (2 * x)
  nlinarith [h]

private lemma aux_PpM_eq (r x : ℝ) :
    abelP r x + abelM r x = 2 * (1 + r ^ 2) := by
  unfold abelP abelM
  ring

private lemma aux_A_hasDerivAt (r x : ℝ) (hr : |r| < 1) :
    HasDerivAt (fun y => abelA r y) (-abelQ r x) x := by
  have hPpos := aux_P_pos r x hr
  have hMpos := aux_M_pos r x hr
  have hPne : abelP r x ≠ 0 := ne_of_gt hPpos
  have hMne : abelM r x ≠ 0 := ne_of_gt hMpos
  have hP := aux_P_hasDerivAt r x
  have hM := aux_M_hasDerivAt r x
  have hlogP := hP.log hPne
  have hlogM := hM.log hMne
  have hsub := hlogP.sub hlogM
  have hmul := hsub.const_mul (1 / 4 : ℝ)
  simp only [Pi.sub_apply] at hmul
  have hfun : (fun y => abelA r y) =
      (fun y => (1 / 4 : ℝ) * (Real.log (abelP r y) - Real.log (abelM r y))) := by
    funext y
    unfold abelA
    ring
  have hPM := aux_PM_eq r x
  have hPpM := aux_PpM_eq r x
  have hsum : (-4 * r * Real.sin (2 * x) / abelP r x) -
      (4 * r * Real.sin (2 * x) / abelM r x) =
      -4 * r * Real.sin (2 * x) * (abelP r x + abelM r x) /
        (abelP r x * abelM r x) := by
    field_simp
    ring
  have hval : (1 / 4 : ℝ) *
      ((-4 * r * Real.sin (2 * x) / abelP r x) -
        (4 * r * Real.sin (2 * x) / abelM r x)) = -abelQ r x := by
    rw [hsum, hPpM, hPM]
    unfold abelQ
    ring
  rw [← hfun] at hmul
  rwa [hval] at hmul

private def abelFr (r x : ℝ) : ℝ :=
  (-(x ^ 2)) * abelA r x + x * (∑' j, SrTerm r x j) +
    (1 / 2 : ℝ) * ((∑' j, CrTerm r x j) - (∑' j, CrTerm r 0 j))

private def abelGr (r t : ℝ) : ℝ := t ^ 2 * abelQ r t

private lemma aux_Sr_sum_closed (r x : ℝ) (hr : |r| < 1) :
    HasDerivAt (fun y => ∑' j, SrTerm r y j) (2 * abelA r x) x := by
  have h := aux_Sr_hasDerivAt r x hr
  rwa [aux_Ar_eq_closed r x hr] at h

private lemma aux_Fr_hasDerivAt (r x : ℝ) (hr : |r| < 1) :
    HasDerivAt (fun y => abelFr r y) (x ^ 2 * abelQ r x) x := by
  have hA := aux_A_hasDerivAt r x hr
  have hS := aux_Sr_sum_closed r x hr
  have hC := aux_Cr_hasDerivAt r x hr
  have hpow : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hneg : HasDerivAt (fun y : ℝ => -(y ^ 2)) (-(2 * x)) x := hpow.neg
  have h1 : HasDerivAt (fun y : ℝ => (-(y ^ 2)) * abelA r y)
      ((-(2 * x)) * abelA r x + (-(x ^ 2)) * (-abelQ r x)) x :=
    hneg.mul hA
  have hid : HasDerivAt (fun y : ℝ => y) (1 : ℝ) x := hasDerivAt_id' x
  have h2 : HasDerivAt (fun y : ℝ => y * (∑' j, SrTerm r y j))
      (1 * (∑' j, SrTerm r x j) + x * (2 * abelA r x)) x :=
    hid.mul hS
  have hconst : HasDerivAt (fun _ : ℝ => (∑' j, CrTerm r 0 j)) (0 : ℝ) x :=
    hasDerivAt_const x _
  have hsub : HasDerivAt (fun y : ℝ => (∑' j, CrTerm r y j) - (∑' j, CrTerm r 0 j))
      ((-2 * (∑' j, SrTerm r x j)) - 0) x :=
    hC.sub hconst
  have h3 : HasDerivAt
      (fun y : ℝ => (1 / 2 : ℝ) * ((∑' j, CrTerm r y j) - (∑' j, CrTerm r 0 j)))
      ((1 / 2 : ℝ) * ((-2 * (∑' j, SrTerm r x j)) - 0)) x :=
    hsub.const_mul (1 / 2 : ℝ)
  have h12 : HasDerivAt
      (fun y : ℝ => (-(y ^ 2)) * abelA r y + y * (∑' j, SrTerm r y j))
      ((-(2 * x)) * abelA r x + (-(x ^ 2)) * (-abelQ r x) +
        (1 * (∑' j, SrTerm r x j) + x * (2 * abelA r x))) x :=
    h1.add h2
  have h123 : HasDerivAt
      (fun y : ℝ => (-(y ^ 2)) * abelA r y + y * (∑' j, SrTerm r y j) +
        (1 / 2 : ℝ) * ((∑' j, CrTerm r y j) - (∑' j, CrTerm r 0 j)))
      ((-(2 * x)) * abelA r x + (-(x ^ 2)) * (-abelQ r x) +
        (1 * (∑' j, SrTerm r x j) + x * (2 * abelA r x)) +
        ((1 / 2 : ℝ) * ((-2 * (∑' j, SrTerm r x j)) - 0))) x :=
    h12.add h3
  have hfun : (fun y => abelFr r y) =
      (fun y : ℝ => (-(y ^ 2)) * abelA r y + y * (∑' j, SrTerm r y j) +
        (1 / 2 : ℝ) * ((∑' j, CrTerm r y j) - (∑' j, CrTerm r 0 j))) := by
    funext y
    unfold abelFr
    ring
  have hval : (-(2 * x)) * abelA r x + (-(x ^ 2)) * (-abelQ r x) +
      (1 * (∑' j, SrTerm r x j) + x * (2 * abelA r x)) +
      ((1 / 2 : ℝ) * ((-2 * (∑' j, SrTerm r x j)) - 0)) =
      x ^ 2 * abelQ r x := by
    ring
  rw [← hfun, hval] at h123
  exact h123

private lemma aux_Fr_zero (r : ℝ) : abelFr r 0 = 0 := by
  unfold abelFr
  simp

private lemma aux_Qdenom_pos (r x : ℝ) (hr : |r| < 1) :
    0 < (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * x) ^ 2 := by
  have hr2 : r ^ 2 < 1 := by
    have h1 : |r| ^ 2 < 1 ^ 2 := by
      apply pow_lt_pow_left₀ hr (abs_nonneg r) (by norm_num)
    rwa [sq_abs, one_pow] at h1
  have hpos : (0 : ℝ) < (1 - r ^ 2) ^ 2 := by
    apply pow_pos
    linarith
  have hnn : (0 : ℝ) ≤ 4 * r ^ 2 * Real.sin (2 * x) ^ 2 := by positivity
  linarith

private lemma aux_Q_continuous (r : ℝ) (hr : |r| < 1) :
    Continuous (fun x => abelQ r x) := by
  unfold abelQ
  apply Continuous.div
  · fun_prop
  · fun_prop
  · intro x
    exact ne_of_gt (aux_Qdenom_pos r x hr)

private lemma aux_Gr_continuous (r : ℝ) (hr : |r| < 1) :
    Continuous (fun t => abelGr r t) := by
  unfold abelGr
  exact (continuous_pow 2).mul (aux_Q_continuous r hr)

private lemma aux_Fr_eq_integral (r x : ℝ) (hr : |r| < 1) :
    abelFr r x = ∫ u in (0 : ℝ)..x, abelGr r u := by
  have hderiv : ∀ y ∈ Set.uIcc 0 x,
      HasDerivAt (fun z => abelFr r z) (abelGr r y) y := by
    intro y _
    have h := aux_Fr_hasDerivAt r y hr
    rwa [show y ^ 2 * abelQ r y = abelGr r y from rfl] at h
  have hint : IntervalIntegrable (fun u => abelGr r u) MeasureTheory.volume 0 x :=
    (aux_Gr_continuous r hr).intervalIntegrable 0 x
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [aux_Fr_zero] at hftc
  simp only [sub_zero] at hftc
  exact hftc.symm

private lemma aux_SrTerm_contOn_r (x : ℝ) (j : ℕ) :
    ContinuousOn (fun r : ℝ => SrTerm r x j) (Set.Icc 0 1) := by
  unfold SrTerm
  exact ((continuous_id.pow _).mul continuous_const).div_const _ |>.continuousOn

private lemma aux_CrTerm_contOn_r (x : ℝ) (j : ℕ) :
    ContinuousOn (fun r : ℝ => CrTerm r x j) (Set.Icc 0 1) := by
  unfold CrTerm
  exact ((continuous_id.pow _).mul continuous_const).div_const _ |>.continuousOn

private lemma aux_SrTerm_norm_le_r (x : ℝ) (j : ℕ) (r : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ‖SrTerm r x j‖ ≤ 1 / (((j : ℝ) + 1) ^ 2) := by
  have hr0 : (0 : ℝ) ≤ r := hr.1
  have hr1 : r ≤ 1 := hr.2
  have habs : |r| ≤ 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hpow : |r| ^ (2 * j + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
  have hDpos : (0 : ℝ) < ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 :=
    pow_pos (Nat.cast_pos.mpr (by omega)) 2
  have hnorm : ‖SrTerm r x j‖ =
      |r| ^ (2 * j + 1) * |Real.sin ((((4 * j + 2 : ℕ)) : ℝ) * x)| /
        ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 := by
    unfold SrTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hDpos]
  have hnum : |r| ^ (2 * j + 1) * |Real.sin ((((4 * j + 2 : ℕ)) : ℝ) * x)| ≤ 1 :=
    (mul_le_of_le_one_left (abs_nonneg _) hpow).trans (Real.abs_sin_le_one _)
  have hle1 : |r| ^ (2 * j + 1) * |Real.sin ((((4 * j + 2 : ℕ)) : ℝ) * x)| /
      ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 ≤ 1 / ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right hnum (le_of_lt hDpos)
  have hle2 : (1 : ℝ) / ((((2 * j + 1 : ℕ))) : ℝ) ^ 2 ≤ 1 / (((j : ℝ) + 1) ^ 2) :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity) (aux_base_le j) 2)
  rw [hnorm]
  exact le_trans hle1 hle2

private lemma aux_CrTerm_norm_le_r (x : ℝ) (j : ℕ) (r : ℝ)
    (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ‖CrTerm r x j‖ ≤ 1 / (((j : ℝ) + 1) ^ 3) := by
  have hr0 : (0 : ℝ) ≤ r := hr.1
  have hr1 : r ≤ 1 := hr.2
  have habs : |r| ≤ 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hpow : |r| ^ (2 * j + 1) ≤ 1 := pow_le_one₀ (abs_nonneg _) habs
  have hDpos : (0 : ℝ) < ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 :=
    pow_pos (Nat.cast_pos.mpr (by omega)) 3
  have hnorm : ‖CrTerm r x j‖ =
      |r| ^ (2 * j + 1) * |Real.cos ((((4 * j + 2 : ℕ)) : ℝ) * x)| /
        ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 := by
    unfold CrTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_pos hDpos]
  have hnum : |r| ^ (2 * j + 1) * |Real.cos ((((4 * j + 2 : ℕ)) : ℝ) * x)| ≤ 1 :=
    (mul_le_of_le_one_left (abs_nonneg _) hpow).trans (Real.abs_cos_le_one _)
  have hle1 : |r| ^ (2 * j + 1) * |Real.cos ((((4 * j + 2 : ℕ)) : ℝ) * x)| /
      ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 ≤ 1 / ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right hnum (le_of_lt hDpos)
  have hle2 : (1 : ℝ) / ((((2 * j + 1 : ℕ))) : ℝ) ^ 3 ≤ 1 / (((j : ℝ) + 1) ^ 3) :=
    one_div_le_one_div_of_le (by positivity)
      (pow_le_pow_left₀ (by positivity) (aux_base_le j) 3)
  rw [hnorm]
  exact le_trans hle1 hle2

private lemma aux_Sr_contOn_r (x : ℝ) :
    ContinuousOn (fun r : ℝ => ∑' j, SrTerm r x j) (Set.Icc 0 1) :=
  continuousOn_tsum (fun j => aux_SrTerm_contOn_r x j) aux_summable_shift_two
    (fun j r hr => aux_SrTerm_norm_le_r x j r hr)

private lemma aux_Cr_contOn_r (x : ℝ) :
    ContinuousOn (fun r : ℝ => ∑' j, CrTerm r x j) (Set.Icc 0 1) :=
  continuousOn_tsum (fun j => aux_CrTerm_contOn_r x j) aux_summable_shift_three
    (fun j r hr => aux_CrTerm_norm_le_r x j r hr)

private lemma aux_SrTerm_one (x : ℝ) (j : ℕ) :
    SrTerm 1 x j = chapter9Entry21SineTerm x j := by
  unfold SrTerm chapter9Entry21SineTerm
  simp only [one_pow, one_mul]

private lemma aux_CrTerm_one (x : ℝ) (j : ℕ) :
    CrTerm 1 x j = chapter9Entry21CosineTerm x j := by
  unfold CrTerm chapter9Entry21CosineTerm
  simp only [one_pow, one_mul]

private lemma aux_CrTerm_one_zero (j : ℕ) :
    CrTerm 1 0 j = chapter9Chi3Term j := by
  unfold CrTerm chapter9Chi3Term
  simp only [one_pow, mul_zero, Real.cos_zero, one_mul]

private lemma aux_id_tendsto_Icc :
    Tendsto id (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhdsWithin 1 (Set.Icc 0 1)) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨tendsto_id.mono_right nhdsWithin_le_nhds, ?_⟩
  have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Set.Iio 1),
    mem_nhdsWithin_of_mem_nhds hIoo] with r hrIio hrIoo
  simp only [id_eq]
  exact ⟨le_of_lt hrIoo.1, le_of_lt hrIio⟩

private lemma aux_Sr_tendsto (x : ℝ) :
    Tendsto (fun r : ℝ => ∑' j, SrTerm r x j) (nhdsWithin 1 (Set.Iio 1))
      (nhds (∑' j, chapter9Entry21SineTerm x j)) := by
  have hmem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have htend : Tendsto (fun r : ℝ => ∑' j, SrTerm r x j)
      (nhdsWithin 1 (Set.Icc 0 1)) (nhds (∑' j, SrTerm 1 x j)) :=
    ((aux_Sr_contOn_r x).continuousWithinAt hmem).tendsto
  have heq : (∑' j, SrTerm 1 x j) = ∑' j, chapter9Entry21SineTerm x j :=
    tsum_congr (fun j => aux_SrTerm_one x j)
  rw [heq] at htend
  exact htend.comp aux_id_tendsto_Icc

private lemma aux_Cr_tendsto (x : ℝ) :
    Tendsto (fun r : ℝ => ∑' j, CrTerm r x j) (nhdsWithin 1 (Set.Iio 1))
      (nhds (∑' j, chapter9Entry21CosineTerm x j)) := by
  have hmem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have htend : Tendsto (fun r : ℝ => ∑' j, CrTerm r x j)
      (nhdsWithin 1 (Set.Icc 0 1)) (nhds (∑' j, CrTerm 1 x j)) :=
    ((aux_Cr_contOn_r x).continuousWithinAt hmem).tendsto
  have heq : (∑' j, CrTerm 1 x j) = ∑' j, chapter9Entry21CosineTerm x j :=
    tsum_congr (fun j => aux_CrTerm_one x j)
  rw [heq] at htend
  exact htend.comp aux_id_tendsto_Icc

private lemma aux_Cr0_tendsto :
    Tendsto (fun r : ℝ => ∑' j, CrTerm r 0 j) (nhdsWithin 1 (Set.Iio 1))
      (nhds chapter9Chi3AtOne) := by
  have hmem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have htend : Tendsto (fun r : ℝ => ∑' j, CrTerm r 0 j)
      (nhdsWithin 1 (Set.Icc 0 1)) (nhds (∑' j, CrTerm 1 0 j)) :=
    ((aux_Cr_contOn_r 0).continuousWithinAt hmem).tendsto
  have heq : (∑' j, CrTerm 1 0 j) = chapter9Chi3AtOne :=
    tsum_congr (fun j => aux_CrTerm_one_zero j)
  rw [heq] at htend
  exact htend.comp aux_id_tendsto_Icc

private lemma aux_abelP_cont (x : ℝ) : Continuous (fun r : ℝ => abelP r x) := by
  unfold abelP
  fun_prop

private lemma aux_abelM_cont (x : ℝ) : Continuous (fun r : ℝ => abelM r x) := by
  unfold abelM
  fun_prop

private lemma aux_abelP_one (x : ℝ) : abelP 1 x = 4 * Real.cos x ^ 2 := by
  have hcos := Real.cos_two_mul x
  unfold abelP
  simp only [one_pow, mul_one]
  linarith

private lemma aux_abelM_one (x : ℝ) : abelM 1 x = 4 * Real.sin x ^ 2 := by
  have hcos := Real.cos_two_mul x
  have hpy := Real.sin_sq_add_cos_sq x
  unfold abelM
  simp only [one_pow, mul_one]
  linarith

private lemma aux_abelP_one_pos (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    0 < abelP 1 x := by
  rw [aux_abelP_one]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have habs := abs_le.mp hx
    constructor <;> linarith
  have hc := Real.cos_pos_of_mem_Ioo hmem
  exact mul_pos (by norm_num) (pow_pos hc 2)

private lemma aux_abelM_one_pos (x : ℝ) (hx : |x| ≤ Real.pi / 4) (hx0 : x ≠ 0) :
    0 < abelM 1 x := by
  rw [aux_abelM_one]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlt : |x| < Real.pi := lt_of_le_of_lt hx (by linarith)
  have hsne : Real.sin x ≠ 0 := aux_sin_ne_zero x hx0 hlt
  have hs2 : (0 : ℝ) < Real.sin x ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hsne) 2
  exact mul_pos (by norm_num) hs2

private lemma aux_abelP_tendsto (x : ℝ) :
    Tendsto (fun r : ℝ => abelP r x) (nhdsWithin 1 (Set.Iio 1))
      (nhds (abelP 1 x)) :=
  ((aux_abelP_cont x).tendsto 1).mono_left nhdsWithin_le_nhds

private lemma aux_abelM_tendsto (x : ℝ) :
    Tendsto (fun r : ℝ => abelM r x) (nhdsWithin 1 (Set.Iio 1))
      (nhds (abelM 1 x)) :=
  ((aux_abelM_cont x).tendsto 1).mono_left nhdsWithin_le_nhds

private lemma aux_logP_tendsto (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Tendsto (fun r : ℝ => Real.log (abelP r x)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (Real.log (abelP 1 x))) :=
  (Real.continuousAt_log (ne_of_gt (aux_abelP_one_pos x hx))).tendsto.comp
    (aux_abelP_tendsto x)

private lemma aux_logM_tendsto (x : ℝ) (hx : |x| ≤ Real.pi / 4) (hx0 : x ≠ 0) :
    Tendsto (fun r : ℝ => Real.log (abelM r x)) (nhdsWithin 1 (Set.Iio 1))
      (nhds (Real.log (abelM 1 x))) :=
  (Real.continuousAt_log (ne_of_gt (aux_abelM_one_pos x hx hx0))).tendsto.comp
    (aux_abelM_tendsto x)

private lemma aux_negSqA_one_eq (x : ℝ) (hx : |x| ≤ Real.pi / 4) (hx0 : x ≠ 0) :
    (-(x ^ 2)) * abelA 1 x = chapter9TanLogTerm x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have habs := abs_le.mp hx
    constructor <;> linarith
  have hcpos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo hmem
  have hlt : |x| < Real.pi := lt_of_le_of_lt hx (by linarith)
  have hsne : Real.sin x ≠ 0 := aux_sin_ne_zero x hx0 hlt
  have hcne : Real.cos x ≠ 0 := ne_of_gt hcpos
  have htan_ne : Real.tan x ≠ 0 := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_ne_zero hsne hcne
  have hc2pos : (0 : ℝ) < Real.cos x ^ 2 := pow_pos hcpos 2
  have hs2pos : (0 : ℝ) < Real.sin x ^ 2 := by
    rw [← sq_abs]
    exact pow_pos (abs_pos.mpr hsne) 2
  have hlogP : Real.log (abelP 1 x)
      = Real.log 4 + 2 * Real.log (Real.cos x) := by
    rw [aux_abelP_one, Real.log_mul (by norm_num) (ne_of_gt hc2pos),
      Real.log_pow]
    norm_num
  have hlogM : Real.log (abelM 1 x)
      = Real.log 4 + 2 * Real.log |Real.sin x| := by
    rw [aux_abelM_one, Real.log_mul (by norm_num) (ne_of_gt hs2pos),
      ← sq_abs, Real.log_pow]
    norm_num
  have htan_abs : |Real.tan x| = |Real.sin x| / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos, abs_div, abs_of_pos hcpos]
  have hdiff : Real.log (abelP 1 x) - Real.log (abelM 1 x)
      = -2 * Real.log |Real.tan x| := by
    rw [hlogP, hlogM, htan_abs,
      Real.log_div (ne_of_gt (abs_pos.mpr hsne)) (ne_of_gt hcpos)]
    ring
  have hT : chapter9TanLogTerm x = x ^ 2 / 2 * Real.log |Real.tan x| := by
    unfold chapter9TanLogTerm
    simp only [hx0, ite_false]
  rw [hT]
  unfold abelA
  rw [hdiff]
  ring

private lemma aux_A_tendsto (x : ℝ) (hx : |x| ≤ Real.pi / 4) (hx0 : x ≠ 0) :
    Tendsto (fun r : ℝ => abelA r x) (nhdsWithin 1 (Set.Iio 1))
      (nhds (abelA 1 x)) := by
  have hP := aux_logP_tendsto x hx
  have hM := aux_logM_tendsto x hx hx0
  have hsub := hP.sub hM
  have hmul : Tendsto
      (fun r : ℝ => (1 / 4 : ℝ) * (Real.log (abelP r x) - Real.log (abelM r x)))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 / 4 : ℝ) * (Real.log (abelP 1 x) - Real.log (abelM 1 x)))) :=
    tendsto_const_nhds.mul hsub
  exact hmul

private lemma aux_negSqA_tendsto (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Tendsto (fun r : ℝ => (-(x ^ 2)) * abelA r x) (nhdsWithin 1 (Set.Iio 1))
      (nhds (chapter9TanLogTerm x)) := by
  by_cases hx0 : x = 0
  · subst hx0
    have hfun : (fun r : ℝ => (-((0 : ℝ) ^ 2)) * abelA r 0) = fun _ => (0 : ℝ) := by
      funext r
      simp
    have hT : chapter9TanLogTerm (0 : ℝ) = 0 := by
      unfold chapter9TanLogTerm
      simp
    rw [hfun, hT]
    exact tendsto_const_nhds
  · have hA := aux_A_tendsto x hx hx0
    have hmul : Tendsto (fun r : ℝ => (-(x ^ 2)) * abelA r x)
        (nhdsWithin 1 (Set.Iio 1)) (nhds ((-(x ^ 2)) * abelA 1 x)) :=
      tendsto_const_nhds.mul hA
    have heq : (-(x ^ 2)) * abelA 1 x = chapter9TanLogTerm x :=
      aux_negSqA_one_eq x hx hx0
    rw [heq] at hmul
    exact hmul

private lemma aux_Gr_tendsto_zero :
    Tendsto (fun r : ℝ => abelGr r 0) (nhdsWithin 1 (Set.Iio 1))
      (nhds (chapF 0)) := by
  have hfun : (fun r : ℝ => abelGr r 0) = fun _ => (0 : ℝ) := by
    funext r
    unfold abelGr
    simp
  rw [hfun, aux_chapF_zero]
  exact tendsto_const_nhds

private lemma aux_Gr_tendsto_ne (u : ℝ) (hu : |u| ≤ Real.pi / 4)
    (hu0 : u ≠ 0) :
    Tendsto (fun r : ℝ => abelGr r u) (nhdsWithin 1 (Set.Iio 1))
      (nhds (chapF u)) := by
  have h2ne : (2 : ℝ) * u ≠ 0 := mul_ne_zero (by norm_num) hu0
  have h2lt : |2 * u| < Real.pi := by
    rw [abs_mul, abs_two]
    calc 2 * |u| ≤ 2 * (Real.pi / 4) :=
          mul_le_mul_of_nonneg_left hu (by norm_num)
      _ = Real.pi / 2 := by ring
      _ < Real.pi := by linarith [Real.pi_pos]
  have hsne : Real.sin (2 * u) ≠ 0 := aux_sin_ne_zero (2 * u) h2ne h2lt
  have hNcont : Continuous
      (fun r : ℝ => 2 * r * (1 + r ^ 2) * Real.sin (2 * u)) := by
    fun_prop
  have hDcont : Continuous
      (fun r : ℝ => (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * u) ^ 2) := by
    fun_prop
  have hN : Tendsto (fun r : ℝ => 2 * r * (1 + r ^ 2) * Real.sin (2 * u))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (2 * 1 * (1 + 1 ^ 2) * Real.sin (2 * u))) :=
    (hNcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hD : Tendsto
      (fun r : ℝ => (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * u) ^ 2)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 - 1 ^ 2) ^ 2 + 4 * 1 ^ 2 * Real.sin (2 * u) ^ 2)) :=
    (hDcont.tendsto 1).mono_left nhdsWithin_le_nhds
  have hs2ne : (4 : ℝ) * Real.sin (2 * u) ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hsne)
  have hD1 : (1 - (1 : ℝ) ^ 2) ^ 2 + 4 * (1 : ℝ) ^ 2 * Real.sin (2 * u) ^ 2
      = 4 * Real.sin (2 * u) ^ 2 := by
    ring
  have hDne : (1 - (1 : ℝ) ^ 2) ^ 2 + 4 * (1 : ℝ) ^ 2 * Real.sin (2 * u) ^ 2
      ≠ 0 := by
    rw [hD1]
    exact hs2ne
  have hQ := hN.div hD hDne
  have hN1 : 2 * (1 : ℝ) * (1 + 1 ^ 2) * Real.sin (2 * u)
      = 4 * Real.sin (2 * u) := by
    ring
  rw [hN1, hD1] at hQ
  have hlim : (4 * Real.sin (2 * u)) / (4 * Real.sin (2 * u) ^ 2)
      = 1 / Real.sin (2 * u) := by
    rw [div_eq_div_iff hs2ne hsne]
    ring
  rw [hlim] at hQ
  have hchap : u ^ 2 * (1 / Real.sin (2 * u)) = chapF u := by
    unfold chapF
    exact (div_eq_mul_one_div _ _).symm
  have hGr : Tendsto
      (fun r : ℝ => u ^ 2 * (2 * r * (1 + r ^ 2) * Real.sin (2 * u) /
        ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * u) ^ 2)))
      (nhdsWithin 1 (Set.Iio 1)) (nhds (u ^ 2 * (1 / Real.sin (2 * u)))) :=
    tendsto_const_nhds.mul hQ
  rw [hchap] at hGr
  exact hGr

private lemma aux_Gr_tendsto (u : ℝ) (hu : |u| ≤ Real.pi / 4) :
    Tendsto (fun r : ℝ => abelGr r u) (nhdsWithin 1 (Set.Iio 1))
      (nhds (chapF u)) := by
  by_cases hu0 : u = 0
  · subst hu0
    exact aux_Gr_tendsto_zero
  · exact aux_Gr_tendsto_ne u hu hu0

private lemma aux_sin_sq_le_one (u : ℝ) : Real.sin (2 * u) ^ 2 ≤ 1 := by
  have h := Real.abs_sin_le_one (2 * u)
  calc Real.sin (2 * u) ^ 2 = |Real.sin (2 * u)| ^ 2 := (sq_abs _).symm
    _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = 1 := one_pow 2

private lemma aux_Qkey (r u : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1) :
    2 * r * (1 + r ^ 2) * Real.sin (2 * u) ^ 2
      ≤ (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * u) ^ 2 := by
  have hrpos : 0 < r := hr.1
  have hsq := aux_sin_sq_le_one u
  have h2r : (0 : ℝ) ≤ 2 * r := by linarith
  have hle : 2 * r * Real.sin (2 * u) ^ 2 ≤ 2 * r * 1 :=
    mul_le_mul_of_nonneg_left hsq h2r
  have h1 : (0 : ℝ) ≤ (1 + r) ^ 2 - 2 * r * Real.sin (2 * u) ^ 2 := by
    have hring : (1 + r) ^ 2 - 2 * r * 1 = 1 + r ^ 2 := by ring
    have hsq2 : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
    linarith
  have hfactor : (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * u) ^ 2
        - 2 * r * (1 + r ^ 2) * Real.sin (2 * u) ^ 2
      = (1 - r) ^ 2 * ((1 + r) ^ 2 - 2 * r * Real.sin (2 * u) ^ 2) := by
    ring
  have hnn : (0 : ℝ) ≤ (1 - r) ^ 2 * ((1 + r) ^ 2 - 2 * r * Real.sin (2 * u) ^ 2) :=
    mul_nonneg (sq_nonneg _) h1
  linarith

private lemma aux_Q_abs_le (r u : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hu : |u| ≤ Real.pi / 4) (hu0 : u ≠ 0) :
    |abelQ r u| ≤ 1 / |Real.sin (2 * u)| := by
  have hrpos : 0 < r := hr.1
  have hr1 : r < 1 := hr.2
  have hrabs : |r| < 1 := by
    rw [abs_of_nonneg (le_of_lt hrpos)]
    exact hr1
  have hDpos : (0 : ℝ) < (1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * u) ^ 2 :=
    aux_Qdenom_pos r u hrabs
  have h2ne : (2 : ℝ) * u ≠ 0 := mul_ne_zero (by norm_num) hu0
  have h2lt : |2 * u| < Real.pi := by
    rw [abs_mul, abs_two]
    calc 2 * |u| ≤ 2 * (Real.pi / 4) :=
          mul_le_mul_of_nonneg_left hu (by norm_num)
      _ = Real.pi / 2 := by ring
      _ < Real.pi := by linarith [Real.pi_pos]
  have hsne : Real.sin (2 * u) ≠ 0 := aux_sin_ne_zero (2 * u) h2ne h2lt
  have hsabspos : 0 < |Real.sin (2 * u)| := abs_pos.mpr hsne
  have hCoeff : (0 : ℝ) ≤ 2 * r * (1 + r ^ 2) := by positivity
  have hNabs : |2 * r * (1 + r ^ 2) * Real.sin (2 * u)|
      = 2 * r * (1 + r ^ 2) * |Real.sin (2 * u)| := by
    rw [abs_mul, abs_of_nonneg hCoeff]
  have hQnorm : |abelQ r u| = 2 * r * (1 + r ^ 2) * |Real.sin (2 * u)| /
      ((1 - r ^ 2) ^ 2 + 4 * r ^ 2 * Real.sin (2 * u) ^ 2) := by
    unfold abelQ
    rw [abs_div, hNabs, abs_of_pos hDpos]
  have hkey := aux_Qkey r u hr
  have hsq2 : |Real.sin (2 * u)| * |Real.sin (2 * u)|
      = Real.sin (2 * u) ^ 2 :=
    (pow_two _).symm.trans (sq_abs _)
  rw [hQnorm, div_le_div_iff₀ hDpos hsabspos, one_mul]
  have heq : 2 * r * (1 + r ^ 2) * |Real.sin (2 * u)| * |Real.sin (2 * u)|
      = 2 * r * (1 + r ^ 2) * Real.sin (2 * u) ^ 2 := by
    rw [← hsq2]
    ring
  rwa [heq]

private lemma aux_Gr_norm_le (r u : ℝ) (hr : r ∈ Set.Ioo (0 : ℝ) 1)
    (hu : |u| ≤ Real.pi / 4) :
    ‖abelGr r u‖ ≤ ‖chapF u‖ := by
  by_cases hu0 : u = 0
  · subst hu0
    have hGr0 : abelGr r 0 = 0 := by
      unfold abelGr
      simp
    rw [hGr0, aux_chapF_zero]
  · have hQle := aux_Q_abs_le r u hr hu hu0
    have hGrnorm : ‖abelGr r u‖ = u ^ 2 * |abelQ r u| := by
      unfold abelGr
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg u)]
    have hFnorm : ‖chapF u‖ = u ^ 2 * (1 / |Real.sin (2 * u)|) := by
      unfold chapF
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (sq_nonneg u),
        mul_one_div]
    rw [hGrnorm, hFnorm]
    exact mul_le_mul_of_nonneg_left hQle (sq_nonneg u)

private lemma aux_Ioo01_eventually :
    ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1), r ∈ Set.Ioo (0 : ℝ) 1 := by
  have hIoo : Set.Ioo (0 : ℝ) 2 ∈ nhds (1 : ℝ) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  filter_upwards [self_mem_nhdsWithin (a := (1 : ℝ)) (s := Set.Iio 1),
    mem_nhdsWithin_of_mem_nhds hIoo] with r hrIio hrIoo
  exact ⟨hrIoo.1, hrIio⟩

private lemma aux_integral_tendsto (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Tendsto (fun r : ℝ => ∫ u in (0 : ℝ)..x, abelGr r u)
      (nhdsWithin 1 (Set.Iio 1)) (nhds (∫ u in (0 : ℝ)..x, chapF u)) := by
  have hev := aux_Ioo01_eventually
  have hF_meas : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1),
      AEStronglyMeasurable (fun u => abelGr r u)
        (MeasureTheory.volume.restrict (Set.uIoc 0 x)) := by
    refine hev.mono fun r hr => ?_
    have hrabs : |r| < 1 := by
      rw [abs_of_nonneg (le_of_lt hr.1)]
      exact hr.2
    exact (aux_Gr_continuous r hrabs).aestronglyMeasurable
  have h_bound : ∀ᶠ r in nhdsWithin (1 : ℝ) (Set.Iio 1),
      ∀ᵐ u ∂MeasureTheory.volume, u ∈ Set.uIoc 0 x →
        ‖abelGr r u‖ ≤ ‖chapF u‖ := by
    refine hev.mono fun r hr => ?_
    refine Filter.Eventually.of_forall fun u hu => ?_
    have huIcc : u ∈ Set.uIcc 0 x := Set.uIoc_subset_uIcc hu
    have hu4 : |u| ≤ Real.pi / 4 :=
      le_trans (aux_mem_uIcc_abs_le x u huIcc) hx
    exact aux_Gr_norm_le r u hr hu4
  have h_int : IntervalIntegrable (fun u => ‖chapF u‖)
      MeasureTheory.volume 0 x := by
    have hx2 : |x| < Real.pi / 2 :=
      lt_of_le_of_lt hx (by linarith [Real.pi_pos])
    have hcontF : ContinuousOn chapF (Set.uIcc 0 x) := by
      apply aux_chapF_continuousOn.mono
      intro u hu
      have hlt : |u| < Real.pi / 2 :=
        lt_of_le_of_lt (aux_mem_uIcc_abs_le x u hu) hx2
      exact abs_lt.mp hlt
    exact hcontF.norm.intervalIntegrable
  have h_lim : ∀ᵐ u ∂MeasureTheory.volume, u ∈ Set.uIoc 0 x →
      Tendsto (fun r => abelGr r u) (nhdsWithin 1 (Set.Iio 1))
        (nhds (chapF u)) := by
    refine Filter.Eventually.of_forall fun u hu => ?_
    have huIcc : u ∈ Set.uIcc 0 x := Set.uIoc_subset_uIcc hu
    have hu4 : |u| ≤ Real.pi / 4 :=
      le_trans (aux_mem_uIcc_abs_le x u huIcc) hx
    exact aux_Gr_tendsto u hu4
  exact intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun u => ‖chapF u‖) hF_meas h_bound h_int h_lim

private lemma aux_Fr_tendsto_RHS (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Tendsto (fun r : ℝ => abelFr r x) (nhdsWithin 1 (Set.Iio 1))
      (nhds (chapter9TanLogTerm x + x * ∑' j, chapter9Entry21SineTerm x j +
        (1 / 2 : ℝ) * ∑' j, chapter9Entry21CosineTerm x j -
        (1 / 2 : ℝ) * chapter9Chi3AtOne)) := by
  have hA := aux_negSqA_tendsto x hx
  have hSr := aux_Sr_tendsto x
  have hB : Tendsto (fun r : ℝ => x * ∑' j, SrTerm r x j)
      (nhdsWithin 1 (Set.Iio 1))
      (nhds (x * ∑' j, chapter9Entry21SineTerm x j)) :=
    tendsto_const_nhds.mul hSr
  have hCr := aux_Cr_tendsto x
  have hC0 := aux_Cr0_tendsto
  have hsub := hCr.sub hC0
  have hC : Tendsto
      (fun r : ℝ => (1 / 2 : ℝ) * ((∑' j, CrTerm r x j) - (∑' j, CrTerm r 0 j)))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((1 / 2 : ℝ) * ((∑' j, chapter9Entry21CosineTerm x j) -
        chapter9Chi3AtOne))) :=
    tendsto_const_nhds.mul hsub
  have hAB := hA.add hB
  have hABC := hAB.add hC
  have heq : (chapter9TanLogTerm x + x * ∑' j, chapter9Entry21SineTerm x j) +
        (1 / 2 : ℝ) * ((∑' j, chapter9Entry21CosineTerm x j) - chapter9Chi3AtOne)
      = chapter9TanLogTerm x + x * ∑' j, chapter9Entry21SineTerm x j +
        (1 / 2 : ℝ) * ∑' j, chapter9Entry21CosineTerm x j -
        (1 / 2 : ℝ) * chapter9Chi3AtOne := by
    ring
  rw [heq] at hABC
  exact hABC

private lemma aux_Fr_tendsto_integral (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Tendsto (fun r : ℝ => abelFr r x) (nhdsWithin 1 (Set.Iio 1))
      (nhds (∫ u in (0 : ℝ)..x, chapF u)) := by
  have hev := aux_Ioo01_eventually
  have heq : (fun r : ℝ => ∫ u in (0 : ℝ)..x, abelGr r u)
        =ᶠ[nhdsWithin 1 (Set.Iio 1)] (fun r : ℝ => abelFr r x) := by
    refine hev.mono fun r hr => ?_
    have hrabs : |r| < 1 := by
      rw [abs_of_nonneg (le_of_lt hr.1)]
      exact hr.2
    exact (aux_Fr_eq_integral r x hrabs).symm
  exact Tendsto.congr' heq (aux_integral_tendsto x hx)

private lemma aux_RHS_eq_integral (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    chapter9TanLogTerm x + x * ∑' j, chapter9Entry21SineTerm x j +
        (1 / 2 : ℝ) * ∑' j, chapter9Entry21CosineTerm x j -
        (1 / 2 : ℝ) * chapter9Chi3AtOne
      = ∫ u in (0 : ℝ)..x, chapF u := by
  have hne := nhdsWithin_Iio_neBot (a := (1 : ℝ)) (b := (1 : ℝ)) (le_refl 1)
  exact tendsto_nhds_unique' hne (aux_Fr_tendsto_RHS x hx)
    (aux_Fr_tendsto_integral x hx)

/-- **A series in even powers of $\tan x$ with odd harmonic numbers.** Let $x$ be a real number
with $|x| \le \pi/4$. Let $h_k = \sum_{j=0}^{k-1} \frac{1}{2j+1}$, let
$N(x) = \frac{x^2}{2} \log|\tan x|$ for $x \ne 0$ and $N(0) = 0$, and let
$\lambda(3) = \sum_{j=0}^{\infty} (2j+1)^{-3}$. Then the series $\sum_{j=0}^{\infty} (2j+1)^{-3}$,
$A(x) = \sum_{k=1}^{\infty} (-1)^{k-1} \frac{h_k \tan^{2k} x}{(2k)^2}$,
$B(x) = \sum_{j=0}^{\infty} \frac{\sin((4j+2)x)}{(2j+1)^2}$ and
$E(x) = \sum_{j=0}^{\infty} \frac{\cos((4j+2)x)}{(2j+1)^3}$ are all summable, and
$A(x) = N(x) + x B(x) + \frac{1}{2} E(x) - \frac{1}{2} \lambda(3)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry21_piseries2 (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Summable chapter9Chi3Term ∧
      Summable (chapter9Entry21LeftTerm x) ∧
      Summable (chapter9Entry21SineTerm x) ∧
      Summable (chapter9Entry21CosineTerm x) ∧
      (∑' j : ℕ, chapter9Entry21LeftTerm x j) =
        chapter9TanLogTerm x +
          x * ∑' j : ℕ, chapter9Entry21SineTerm x j +
          (1 / 2 : ℝ) * ∑' j : ℕ, chapter9Entry21CosineTerm x j -
          (1 / 2 : ℝ) * chapter9Chi3AtOne := by
  refine ⟨summable_chi3, summable_left x hx, summable_sine x, summable_cosine x, ?_⟩
  have hL := aux_left_eq_integral_closed x hx
  have hR := aux_RHS_eq_integral x hx
  rw [hL, hR]

end
end Entry21Piseries2
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
