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
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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

namespace Entry32Lambertdivisor

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9Entry19TanTerm (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1) /
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)

def chapter9Entry32LeftTerm (x : ℝ) (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * (k.factorial : ℝ) ^ 2 *
      Real.sin (2 * x) ^ (2 * k + 1) /
    (((2 * k).factorial : ℝ) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

-- Helper: central coefficient b k = 4^k (k!)^2 / (2k)!
private noncomputable def bCoeff32 (k : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k) * ((k.factorial : ℝ) ^ 2) / (((2 * k).factorial : ℝ))

private lemma bCoeff32_pos (k : ℕ) : 0 < bCoeff32 k := by
  unfold bCoeff32
  positivity

private lemma bCoeff32_succ (k : ℕ) :
    bCoeff32 (k + 1) = bCoeff32 k * (2 * ((k : ℝ) + 1) / (2 * (k : ℝ) + 1)) := by
  unfold bCoeff32
  have h1 : (((k + 1).factorial : ℕ) : ℝ) = ((k : ℝ) + 1) * ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  have h2 : ((((2 * (k + 1)).factorial : ℕ)) : ℝ)
      = (2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1) * ((((2 * k).factorial : ℕ)) : ℝ) := by
    have e1 : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    have e2 : 2 * k + 1 = (2 * k) + 1 := by omega
    conv_lhs => rw [e1]
    rw [Nat.factorial_succ]
    conv_lhs => rw [e2]
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [h1, h2]
  have hpow : (2 : ℝ) ^ (2 * (k + 1)) = 4 * (2 : ℝ) ^ (2 * k) := by
    rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add]
    ring
  rw [hpow]
  field_simp
  ring

private lemma bCoeff32_one : bCoeff32 1 = 2 := by norm_num [bCoeff32, Nat.factorial]

private lemma poly32_step (k : ℕ) (hk : 1 ≤ k) :
    16 * ((k : ℝ) + 1) ^ 7 ≤ (2 * (k : ℝ) + 1) ^ 4 * ((k : ℝ) + 2) ^ 3 := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [sq_nonneg ((k : ℝ)), sq_nonneg ((k : ℝ) ^ 2), sq_nonneg ((k : ℝ) ^ 3),
    mul_nonneg (show (0:ℝ) ≤ (k:ℝ) - 1 by linarith) (show (0:ℝ) ≤ (k:ℝ)^2 by positivity)]

private lemma bCoeff32_pow4_le (k : ℕ) : (bCoeff32 k) ^ 4 ≤ 2 * ((k : ℝ) + 1) ^ 3 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => norm_num [bCoeff32]
    | 1 => rw [bCoeff32_one]; norm_num
    | (k + 2) =>
      have hk1 : 1 ≤ k + 1 := Nat.le_add_left 1 k
      have ih1 := ih (k + 1) (by omega)
      rw [bCoeff32_succ]
      have hstep : ((2 * (((k+1 : ℕ) : ℝ)+1) / (2*(((k+1 : ℕ) : ℝ))+1)) ^ 4)
          * (2 * ((((k+1 : ℕ) : ℝ))+1)^3) ≤ 2 * ((((k+1 : ℕ) : ℝ))+1+1)^3 := by
        have hpos4 : (0:ℝ) < (2*((((k+1:ℕ)):ℝ))+1)^4 := by positivity
        rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ hpos4]
        have hpoly := poly32_step (k + 1) hk1
        have heq : ((((k+1 : ℕ)) : ℝ)+1+1) = ((((k+1 : ℕ)) : ℝ))+2 := by ring
        rw [heq]
        nlinarith [hpoly]
      calc (bCoeff32 (k + 1) * (2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1))) ^ 4
          = (bCoeff32 (k + 1)) ^ 4 * (2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1)) ^ 4 := by ring
        _ ≤ (2 * (↑(k + 1) + 1) ^ 3) * (2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1)) ^ 4 := by
            apply mul_le_mul_of_nonneg_right ih1 (by positivity)
        _ = ((2 * (↑(k + 1) + 1) / (2 * ↑(k + 1) + 1)) ^ 4) * (2 * (↑(k + 1) + 1) ^ 3) := by ring
        _ ≤ 2 * (↑(k + 1) + 1 + 1) ^ 3 := hstep
        _ = 2 * ((((k + 2 : ℕ)) : ℝ) + 1) ^ 3 := by push_cast; ring

private lemma rpow32_fourth (k : ℕ) :
    ((2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ)))) ^ 4
      = 2 * ((k : ℝ) + 1) ^ 3 := by
  rw [mul_pow]
  have h1 : ((2 : ℝ) ^ ((1/4 : ℝ))) ^ (4:ℕ) = 2 := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by norm_num)]
    have he : (1/4 : ℝ) * ((4:ℕ) : ℝ) = 1 := by norm_num
    rw [he, Real.rpow_one]
  have h2 : ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) ^ (4:ℕ)) = ((k : ℝ) + 1) ^ (3:ℕ) := by
    rw [← Real.rpow_natCast _ 4, ← Real.rpow_mul (by positivity)]
    have he : (3/4 : ℝ) * ((4:ℕ) : ℝ) = ((3:ℕ) : ℝ) := by norm_num
    rw [he, Real.rpow_natCast]
  rw [h1, h2]

private lemma bCoeff32_le_rpow (k : ℕ) :
    bCoeff32 k ≤ (2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := by
  have h4 := bCoeff32_pow4_le k
  have hC4 := rpow32_fourth k
  have hle : (bCoeff32 k) ^ 4
      ≤ ((2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ)))) ^ 4 := by
    rw [hC4]; exact h4
  have h0 : (0:ℝ) ≤ bCoeff32 k := le_of_lt (bCoeff32_pos k)
  have h1 : (0:ℝ) ≤ (2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := by positivity
  exact (pow_le_pow_iff_left₀ h0 h1 (by norm_num)).mp hle

private lemma summable32_maj54 :
    Summable (fun k : ℕ => ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) := by
  have hbase : Summable (fun n : ℕ => ((((n : ℝ)) ^ ((5/4 : ℝ)))⁻¹)) :=
    (Real.summable_nat_rpow_inv).mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => ((((k + 1 : ℕ) : ℝ) ^ ((5/4 : ℝ)))⁻¹)) :=
    (summable_nat_add_iff (G := ℝ) 1).mpr hbase
  have heq : (fun k : ℕ => ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) =
      (fun k : ℕ => ((((k + 1 : ℕ) : ℝ) ^ ((5/4 : ℝ)))⁻¹)) := by
    funext k
    push_cast
    ring_nf
  rw [heq]
  exact hshift

private lemma rpow32_div_eq (k : ℕ) :
    (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ))
      = ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹) := by
  have hpos : (0:ℝ) < (k : ℝ) + 1 := by positivity
  rw [← Real.rpow_natCast _ 2, div_eq_mul_inv,
    ← Real.rpow_neg (le_of_lt hpos), ← Real.rpow_add hpos,
    show (3/4 : ℝ) + (-((2:ℕ) : ℝ)) = -((5/4) : ℝ) by norm_num,
    Real.rpow_neg (le_of_lt hpos)]

private lemma cos32_pos (x : ℝ) (hx : |x| ≤ Real.pi / 4) : 0 < Real.cos x := by
  have hmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    have hneg : -(Real.pi / 4) ≤ x := neg_le_of_abs_le hx
    have hle : x ≤ Real.pi / 4 := le_of_abs_le hx
    have := Real.pi_pos
    constructor <;> linarith
  exact Real.cos_pos_of_mem_Ioo hmem

private lemma tan32_abs_le (x : ℝ) (hx : |x| ≤ Real.pi / 4) : |Real.tan x| ≤ 1 := by
  have h1 : -(Real.pi / 4) ≤ x := neg_le_of_abs_le hx
  have h2 : x ≤ Real.pi / 4 := le_of_abs_le hx
  have hmem1 : (-(Real.pi / 4)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmemx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmem2 : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmono := Real.strictMonoOn_tan.monotoneOn
  have hle1 : Real.tan (-(Real.pi / 4)) ≤ Real.tan x :=
    hmono hmem1 hmemx (by simpa using h1)
  have hle2 : Real.tan x ≤ Real.tan (Real.pi / 4) :=
    hmono hmemx hmem2 (by simpa using h2)
  rw [Real.tan_pi_div_four] at hle2
  have hneg : Real.tan (-(Real.pi / 4)) = -1 := by
    rw [Real.tan_neg, Real.tan_pi_div_four]
  rw [hneg] at hle1
  rw [abs_le]
  constructor <;> linarith

private lemma summable32_maj2 :
    Summable (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) := by
  have h2 : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hshift : Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) :=
    (summable_nat_add_iff (G := ℝ) 1).mpr h2
  have heq : (fun k : ℕ => (1 : ℝ) / (((k : ℝ) + 1) ^ 2)) =
      (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext k
    push_cast
    ring_nf
  rw [heq]
  exact hshift

private lemma summable32_tan (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Summable (chapter9Entry19TanTerm x) := by
  have htan : |Real.tan x| ≤ 1 := tan32_abs_le x hx
  have hmaj := summable32_maj2
  have habs : Summable (fun k : ℕ => |chapter9Entry19TanTerm x k|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmaj
    unfold chapter9Entry19TanTerm
    rw [abs_div]
    have hpow : |(-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1)| ≤ 1 := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact pow_le_one₀ (abs_nonneg _) htan
    calc |(-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1)| / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)|
        ≤ 1 / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)| :=
          div_le_div_of_nonneg_right hpow (by positivity)
      _ = 1 / ((((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [abs_of_nonneg (by positivity)]
      _ ≤ 1 / (((k : ℝ) + 1) ^ 2) := by
          apply one_div_le_one_div_of_le (by positivity)
          have hle : ((k : ℝ) + 1) ≤ (((2 * k + 1 : ℕ)) : ℝ) := by
            have hkn : k + 1 ≤ 2 * k + 1 := by omega
            have h := Nat.cast_le (α := ℝ) |>.mpr hkn
            push_cast at h ⊢
            linarith
          calc ((k : ℝ) + 1) ^ 2 ≤ ((((2 * k + 1 : ℕ)) : ℝ)) ^ 2 :=
                pow_le_pow_left₀ (by positivity) hle 2
            _ = ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by ring
  exact (summable_abs_iff).mp habs

private lemma summable32_left (x : ℝ) : Summable (chapter9Entry32LeftTerm x) := by
  have hs : |Real.sin (2 * x)| ≤ 1 := Real.abs_sin_le_one _
  have hCnn : (0:ℝ) ≤ (2 : ℝ) ^ ((1/4 : ℝ)) := by positivity
  have hMnn : ∀ k : ℕ, (0:ℝ) ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := fun k => by positivity
  have hmaj : Summable
      (fun k : ℕ => (2 : ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) :=
    summable32_maj54.mul_left _
  have habs : Summable (fun k : ℕ => |chapter9Entry32LeftTerm x k|) := by
    apply Summable.of_nonneg_of_le (fun k => abs_nonneg _) (fun k => ?_) hmaj
    have h1 : |bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1)| ≤ bCoeff32 k := by
      rw [abs_mul]
      have hpow : |Real.sin (2 * x) ^ (2 * k + 1)| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) hs
      calc |bCoeff32 k| * |Real.sin (2 * x) ^ (2 * k + 1)|
          = bCoeff32 k * |Real.sin (2 * x) ^ (2 * k + 1)| := by
            rw [abs_of_nonneg (le_of_lt (bCoeff32_pos k))]
        _ ≤ bCoeff32 k * 1 :=
            mul_le_mul_of_nonneg_left hpow (le_of_lt (bCoeff32_pos k))
        _ = bCoeff32 k := mul_one _
    have hD2pos : (0:ℝ) < (((k : ℝ) + 1) ^ (2:ℕ)) := by positivity
    have hDle : (((k : ℝ) + 1) ^ (2:ℕ)) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ)) := by
      apply pow_le_pow_left₀ (by positivity) _ 2
      have hkn : k + 1 ≤ 2 * k + 1 := by omega
      have h := Nat.cast_le (α := ℝ) |>.mpr hkn
      push_cast at h ⊢
      linarith
    have hMdiv : (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ))
        ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ)) :=
      div_le_div_of_nonneg_left (hMnn k) hD2pos hDle
    have heq : chapter9Entry32LeftTerm x k
        = bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      unfold chapter9Entry32LeftTerm bCoeff32
      field_simp
    rw [heq, abs_div]
    calc |bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1)| / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)|
        ≤ bCoeff32 k / |(((2 * k + 1 : ℕ) : ℝ) ^ 2)| :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ = bCoeff32 k / ((((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [abs_of_nonneg (by positivity)]
      _ ≤ ((2 : ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ)))) / ((((2 * k + 1 : ℕ) : ℝ) ^ 2)) :=
          div_le_div_of_nonneg_right (bCoeff32_le_rpow k) (by positivity)
      _ = (2 : ℝ) ^ ((1/4 : ℝ)) *
          ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) / ((((2 * k + 1 : ℕ) : ℝ) ^ 2))) := by
          rw [mul_div_assoc]
      _ ≤ (2 : ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ))) := by
          apply mul_le_mul_of_nonneg_left hMdiv hCnn
      _ = (2 : ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹) := by
          rw [rpow32_div_eq]
  exact (summable_abs_iff).mp habs

private lemma bCoeff32_zero : bCoeff32 0 = 1 := by
  norm_num [bCoeff32]

private lemma bCoeff32_le_two_succ (k : ℕ) :
    bCoeff32 k ≤ 2 * ((k : ℝ) + 1) := by
  have h4 := bCoeff32_pow4_le k
  have hle : 2 * ((k : ℝ) + 1) ^ 3 ≤ (2 * ((k : ℝ) + 1)) ^ 4 := by
    have hk1 : (1:ℝ) ≤ (k : ℝ) + 1 := by
      have hkn : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      linarith
    have h8 : (1:ℝ) ≤ 8 * ((k : ℝ) + 1) := by linarith
    have hpos : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) ^ 3 := by positivity
    calc 2 * ((k : ℝ) + 1) ^ 3
        = 1 * (2 * ((k : ℝ) + 1) ^ 3) := by ring
      _ ≤ (8 * ((k : ℝ) + 1)) * (2 * ((k : ℝ) + 1) ^ 3) :=
          mul_le_mul_of_nonneg_right h8 hpos
      _ = (2 * ((k : ℝ) + 1)) ^ 4 := by ring
  have hB : (bCoeff32 k) ^ 4 ≤ (2 * ((k : ℝ) + 1)) ^ 4 := by
    linarith [h4, hle]
  have h0 : (0:ℝ) ≤ bCoeff32 k := le_of_lt (bCoeff32_pos k)
  have h1 : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
  exact (pow_le_pow_iff_left₀ h0 h1 (by norm_num)).mp hB

private noncomputable def aCoeff32 (k : ℕ) : ℝ :=
  bCoeff32 k / (((2 * k + 1 : ℕ)) : ℝ)

private lemma aCoeff32_nonneg (k : ℕ) : 0 ≤ aCoeff32 k := by
  unfold aCoeff32
  exact div_nonneg (le_of_lt (bCoeff32_pos k)) (Nat.cast_nonneg _)

private lemma aCoeff32_zero : aCoeff32 0 = 1 := by
  unfold aCoeff32
  rw [bCoeff32_zero]
  norm_num

private lemma aCoeff32_le (k : ℕ) :
    aCoeff32 k ≤ 2 * ((k : ℝ) + 1) := by
  unfold aCoeff32
  have hD : (1:ℝ) ≤ (((2 * k + 1 : ℕ)) : ℝ) := by
    have hle : 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast hle
  have hDpos : (0:ℝ) < (((2 * k + 1 : ℕ)) : ℝ) := by positivity
  have hb := bCoeff32_le_two_succ k
  have hCnn : (0:ℝ) ≤ 2 * ((k : ℝ) + 1) := by positivity
  calc bCoeff32 k / (((2 * k + 1 : ℕ)) : ℝ)
      ≤ (2 * ((k : ℝ) + 1)) / (((2 * k + 1 : ℕ)) : ℝ) :=
        div_le_div_of_nonneg_right hb (le_of_lt hDpos)
    _ ≤ (2 * ((k : ℝ) + 1)) / 1 :=
        div_le_div_of_nonneg_left hCnn (by norm_num) hD
    _ = 2 * ((k : ℝ) + 1) := by ring

private lemma aCoeff32_rec (k : ℕ) :
    (2 * (k : ℝ) + 3) * aCoeff32 (k + 1)
      = 2 * ((k : ℝ) + 1) * aCoeff32 k := by
  unfold aCoeff32
  rw [bCoeff32_succ]
  have hD1 : ((((2 * (k + 1) + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 3 := by
    push_cast
    ring
  have hD0 : ((((2 * k + 1 : ℕ))) : ℝ) = 2 * (k : ℝ) + 1 := by
    push_cast
    ring
  rw [hD1, hD0]
  field_simp

private noncomputable def S32 (z : ℝ) : ℝ :=
  ∑' k : ℕ, aCoeff32 k * z ^ k

private noncomputable def F32 (s : ℝ) : ℝ :=
  ∑' k : ℕ, bCoeff32 k * s ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

private noncomputable def G32 (t : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

private lemma leftTerm_eq_F32term (x : ℝ) (k : ℕ) :
    chapter9Entry32LeftTerm x k
      = bCoeff32 k * Real.sin (2 * x) ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold chapter9Entry32LeftTerm bCoeff32
  field_simp

private lemma tsum_left_eq_F32 (x : ℝ) :
    (∑' k : ℕ, chapter9Entry32LeftTerm x k) = F32 (Real.sin (2 * x)) := by
  unfold F32
  apply tsum_congr
  intro k
  exact leftTerm_eq_F32term x k

private lemma tanTerm_eq_G32term (x : ℝ) (k : ℕ) :
    chapter9Entry19TanTerm x k
      = (-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold chapter9Entry19TanTerm
  ring

private lemma tsum_tan_eq_G32 (x : ℝ) :
    (∑' k : ℕ, chapter9Entry19TanTerm x k) = G32 (Real.tan x) := by
  unfold G32
  apply tsum_congr
  intro k
  exact tanTerm_eq_G32term x k

private lemma summable_succ_mul_pow32 {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * r ^ n) := by
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have heq : (fun n : ℕ => ((n : ℝ) + 1) * r ^ n)
      = fun n : ℕ => (n : ℝ) * r ^ n + r ^ n := by
    funext n
    ring
  rw [heq]
  exact h1.add h0

private lemma summable_sq_mul_pow32 {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ 2 * r ^ n) := by
  simpa [Nat.cast_pow] using
    summable_pow_mul_geometric_of_norm_lt_one 2 hr

private lemma summable_succ_mul_succ_pow32 {r : ℝ} (hr : ‖r‖ < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * r ^ n) := by
  have h2 := summable_sq_mul_pow32 hr
  have h1 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) := by
    simpa [pow_one] using
      summable_pow_mul_geometric_of_norm_lt_one 1 hr
  have h0 : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_norm_lt_one hr
  have heq : (fun n : ℕ => ((n : ℝ) + 1) * ((n : ℝ) + 2) * r ^ n)
      = fun n : ℕ => (n : ℝ) ^ 2 * r ^ n + 3 * ((n : ℝ) * r ^ n)
        + 2 * r ^ n := by
    funext n
    ring
  rw [heq]
  exact (h2.add (h1.mul_left 3)).add (h0.mul_left 2)

private lemma summable_S32_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => aCoeff32 k * z ^ k) := by
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hz
  have hbase := summable_succ_mul_pow32 (r := ‖z‖) hr
  have hsum : Summable (fun k : ℕ => 2 * (((k : ℝ) + 1) * ‖z‖ ^ k)) :=
    hbase.mul_left 2
  apply Summable.of_norm_bounded hsum
  intro k
  rw [norm_mul, norm_pow]
  have ha : ‖aCoeff32 k‖ ≤ 2 * ((k : ℝ) + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff32_nonneg k)]
    exact aCoeff32_le k
  calc ‖aCoeff32 k‖ * ‖z‖ ^ k
      ≤ (2 * ((k : ℝ) + 1)) * ‖z‖ ^ k :=
        mul_le_mul_of_nonneg_right ha (pow_nonneg (norm_nonneg _) _)
    _ = 2 * (((k : ℝ) + 1) * ‖z‖ ^ k) := by ring

private lemma S32_zero : S32 0 = 1 := by
  unfold S32
  have hsingle : HasSum (fun k : ℕ => aCoeff32 k * (0 : ℝ) ^ k) 1 := by
    have h0 : aCoeff32 0 * (0 : ℝ) ^ (0 : ℕ) = 1 := by
      rw [aCoeff32_zero]
      norm_num
    have h00 : ∀ b : ℕ, b ≠ 0 → aCoeff32 b * (0 : ℝ) ^ b = 0 := by
      intro b hb
      rw [zero_pow hb]
      ring
    have hS := hasSum_single (0 : ℕ) h00
    rw [h0] at hS
    exact hS
  exact hsingle.tsum_eq

private lemma F32_zero : F32 0 = 0 := by
  unfold F32
  have hzero : (fun k : ℕ => bCoeff32 k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => 0 := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

private lemma G32_zero : G32 0 = 0 := by
  unfold G32
  have hzero : (fun k : ℕ => (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => 0 := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

private lemma summable_F32_zero :
    Summable (fun k : ℕ => bCoeff32 k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have hzero : (fun k : ℕ => bCoeff32 k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => (0 : ℝ) := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero]
  exact summable_zero

private lemma summable_G32_zero :
    Summable (fun k : ℕ => (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have hzero : (fun k : ℕ => (-1 : ℝ) ^ k * (0 : ℝ) ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => (0 : ℝ) := by
    funext k
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero]
  exact summable_zero

private lemma S32_term_hasDerivAt (k : ℕ) (y : ℝ) :
    HasDerivAt (fun z : ℝ => aCoeff32 k * z ^ k)
      (aCoeff32 k * (k : ℝ) * y ^ (k - 1)) y := by
  have hpow : HasDerivAt (fun z : ℝ => z ^ k)
      ((k : ℝ) * y ^ (k - 1)) y :=
    hasDerivAt_pow k y
  have hmul := hpow.const_mul (aCoeff32 k)
  have heq : aCoeff32 k * ((k : ℝ) * y ^ (k - 1))
      = aCoeff32 k * (k : ℝ) * y ^ (k - 1) := by ring
  rw [heq] at hmul
  exact hmul

private lemma S32_majorant {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
    ‖aCoeff32 k * (k : ℝ) * y ^ (k - 1)‖
      ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    have hmem := Set.mem_Ioo.mp hy
    rw [abs_lt]
    constructor <;> linarith [hmem.1, hmem.2]
  have hyrle : ‖y‖ ≤ r := le_of_lt hyr
  have ha : ‖aCoeff32 k‖ ≤ 2 * ((k : ℝ) + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff32_nonneg k)]
    exact aCoeff32_le k
  have hk : ‖(k : ℝ)‖ ≤ (k : ℝ) + 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    have hkn : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
    linarith
  have hpow : ‖y‖ ^ (k - 1) ≤ r ^ (k - 1) :=
    pow_le_pow_left₀ (norm_nonneg _) hyrle _
  have hmain : ‖aCoeff32 k‖ * ‖(k : ℝ)‖ * ‖y‖ ^ (k - 1)
      ≤ (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) * r ^ (k - 1) := by
    have h1 : ‖aCoeff32 k‖ * ‖(k : ℝ)‖
        ≤ (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) :=
      mul_le_mul ha hk (by positivity) (by positivity)
    exact mul_le_mul h1 hpow (by positivity) (by positivity)
  have hkk : ((k : ℝ) + 1) ≤ (k : ℝ) + 2 := by linarith
  have hkk2 : ((k : ℝ) + 1) * ((k : ℝ) + 1)
      ≤ ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
    apply mul_le_mul_of_nonneg_left hkk (by positivity)
  have hrpow : r ^ (k - 1) ≤ r ^ k / r := by
    match k with
    | 0 =>
      simp only [Nat.zero_sub, pow_zero]
      have hrle : r ≤ 1 := le_of_lt hr1
      have h1r : (1:ℝ) ≤ 1 / r := by
        rw [le_div_iff₀ hr0]
        simp [hrle]
      simpa using h1r
    | (j + 1) =>
      have hsub : (j + 1 - 1) = j := by omega
      rw [hsub]
      have hpow : r ^ (j + 1) = r ^ j * r := pow_succ r j
      rw [hpow, mul_div_cancel_right₀ _ (ne_of_gt hr0)]
  have h2 : (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) * r ^ (k - 1)
      ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) := by
    have hA : (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1)
        ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      have := mul_le_mul_of_nonneg_left hkk2 (show (0:ℝ) ≤ 2 by norm_num)
      linarith [this]
    have hB : (0:ℝ) ≤ r ^ (k - 1) := pow_nonneg hr0.le _
    have hC : (0:ℝ) ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by
      positivity
    calc (2 * ((k : ℝ) + 1)) * ((k : ℝ) + 1) * r ^ (k - 1)
        ≤ (2 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) * r ^ (k - 1) :=
          mul_le_mul_of_nonneg_right hA hB
      _ ≤ (2 * (((k : ℝ) + 1) * ((k : ℝ) + 2))) * (r ^ k / r) :=
          mul_le_mul_of_nonneg_left hrpow hC
      _ = 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) := by ring
  rw [norm_mul, norm_mul, norm_pow]
  linarith [hmain, h2]

private lemma S32_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt S32 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * y ^ (k - 1)) y := by
  have hrN : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hbase := summable_succ_mul_succ_pow32 (r := r) hrN
  have hu : Summable
      (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r)) := by
    have heq : (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r))
        = fun k : ℕ => (2 / r)
          * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k) := by
      funext k
      field_simp
    rw [heq]
    exact hbase.mul_left (2 / r)
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt (fun w : ℝ => aCoeff32 k * w ^ k)
        (aCoeff32 k * (k : ℝ) * z ^ (k - 1)) z :=
    fun k z _ => S32_term_hasDerivAt k z
  have hbound : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖aCoeff32 k * (k : ℝ) * z ^ (k - 1)‖
        ≤ 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r) :=
    fun k z hz => S32_majorant hr0 hr1 k z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by
    simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun k : ℕ => aCoeff32 k * (0 : ℝ) ^ k) := by
    have h0 : ‖(0 : ℝ)‖ < 1 := by norm_num
    exact summable_S32_of_norm_lt_one h0
  have hmain := hasDerivAt_tsum_of_isPreconnected hu hopen hpre
    hderiv hbound hy0 hsum0 hy
  have efun : (fun z : ℝ => ∑' k : ℕ, aCoeff32 k * z ^ k) = S32 := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

private lemma F32_term_hasDerivAt (k : ℕ) (y : ℝ) :
    HasDerivAt
      (fun s : ℝ => bCoeff32 k * s ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
      (aCoeff32 k * y ^ (2 * k)) y := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * k + 1))
      ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k)) y := by
    have h := hasDerivAt_pow (2 * k + 1) y
    have heq : (2 * k + 1) - 1 = 2 * k := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul (bCoeff32 k)
  have hD : ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := by positivity
  have hdiv := hmul.div_const ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
  have hsimp : bCoeff32 k * ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k))
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
      = aCoeff32 k * y ^ (2 * k) := by
    unfold aCoeff32
    field_simp
  rw [hsimp] at hdiv
  exact hdiv

private lemma F32_majorant {r : ℝ}
    (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
    ‖aCoeff32 k * y ^ (2 * k)‖ ≤ 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k) := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    have hmem := Set.mem_Ioo.mp hy
    rw [abs_lt]
    constructor <;> linarith [hmem.1, hmem.2]
  have ha : ‖aCoeff32 k‖ ≤ 2 * ((k : ℝ) + 1) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (aCoeff32_nonneg k)]
    exact aCoeff32_le k
  have hpow : ‖y‖ ^ (2 * k) ≤ (r ^ 2) ^ k := by
    have h2 : ‖y‖ ^ (2 * k) = (‖y‖ ^ 2) ^ k := by
      rw [← pow_mul]
    have hle : ‖y‖ ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) 2
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) hle _
  rw [norm_mul, norm_pow]
  calc ‖aCoeff32 k‖ * ‖y‖ ^ (2 * k)
      ≤ (2 * ((k : ℝ) + 1)) * (r ^ 2) ^ k :=
        mul_le_mul ha hpow (by positivity) (by positivity)
    _ = 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k) := by ring

private lemma F32_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt F32 (∑' k : ℕ, aCoeff32 k * y ^ (2 * k)) y := by
  have hr2 : ‖(r ^ 2 : ℝ)‖ < 1 := by
    have hnn : (0:ℝ) ≤ r ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    nlinarith [hr0, hr1]
  have hbase := summable_succ_mul_pow32 (r := r ^ 2) hr2
  have hu : Summable
      (fun k : ℕ => 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k)) :=
    hbase.mul_left 2
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt
        (fun s : ℝ => bCoeff32 k * s ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
        (aCoeff32 k * z ^ (2 * k)) z :=
    fun k z _ => F32_term_hasDerivAt k z
  have hbound : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖aCoeff32 k * z ^ (2 * k)‖
        ≤ 2 * (((k : ℝ) + 1) * (r ^ 2) ^ k) :=
    fun k z hz => F32_majorant k z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by
    simp [Set.mem_Ioo, hr0]
  have hmain := hasDerivAt_tsum_of_isPreconnected hu hopen hpre
    hderiv hbound hy0 summable_F32_zero hy
  have efun : (fun s : ℝ => ∑' k : ℕ, bCoeff32 k * s ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = F32 := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

private lemma G32_term_hasDerivAt (k : ℕ) (y : ℝ) :
    HasDerivAt
      (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k + 1)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
      ((-1 : ℝ) ^ k * y ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)) y := by
  have hpow : HasDerivAt (fun t : ℝ => t ^ (2 * k + 1))
      ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k)) y := by
    have h := hasDerivAt_pow (2 * k + 1) y
    have heq : (2 * k + 1) - 1 = 2 * k := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul ((-1 : ℝ) ^ k)
  have hdiv := hmul.div_const ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
  have hsimp : (-1 : ℝ) ^ k * ((((2 * k + 1 : ℕ)) : ℝ) * y ^ (2 * k))
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
      = (-1 : ℝ) ^ k * y ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ) := by
    field_simp
  rw [hsimp] at hdiv
  exact hdiv

private lemma G32_majorant {r : ℝ}
    (k : ℕ) (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
    ‖(-1 : ℝ) ^ k * y ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)‖
      ≤ (r ^ 2) ^ k := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs]
    have hmem := Set.mem_Ioo.mp hy
    rw [abs_lt]
    constructor <;> linarith [hmem.1, hmem.2]
  have hpow : ‖y‖ ^ (2 * k) ≤ (r ^ 2) ^ k := by
    have h2 : ‖y‖ ^ (2 * k) = (‖y‖ ^ 2) ^ k := by
      rw [← pow_mul]
    have hle : ‖y‖ ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) 2
    rw [h2]
    exact pow_le_pow_left₀ (by positivity) hle _
  have hD : (1:ℝ) ≤ (((2 * k + 1 : ℕ)) : ℝ) := by
    have hle : 1 ≤ 2 * k + 1 := by omega
    exact_mod_cast hle
  simp only [norm_div, norm_mul, norm_pow]
  have h1 : ‖(-1 : ℝ)‖ ^ k = 1 := by simp
  have hDnn : ‖((((2 * k + 1 : ℕ)) : ℝ))‖ = (((2 * k + 1 : ℕ)) : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [h1, hDnn, one_mul]
  calc ‖y‖ ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)
      ≤ (r ^ 2) ^ k / (((2 * k + 1 : ℕ)) : ℝ) :=
        div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ (r ^ 2) ^ k / 1 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num) hD
    _ = (r ^ 2) ^ k := by ring

private lemma G32_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt G32
      (∑' k : ℕ, (-1 : ℝ) ^ k * y ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) y := by
  have hr2 : ‖(r ^ 2 : ℝ)‖ < 1 := by
    have hnn : (0:ℝ) ≤ r ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    nlinarith [hr0, hr1]
  have hu : Summable (fun k : ℕ => (r ^ 2) ^ k) :=
    summable_geometric_of_norm_lt_one hr2
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt
        (fun t : ℝ => (-1 : ℝ) ^ k * t ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
        ((-1 : ℝ) ^ k * z ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)) z :=
    fun k z _ => G32_term_hasDerivAt k z
  have hbound : ∀ k : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖(-1 : ℝ) ^ k * z ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)‖
        ≤ (r ^ 2) ^ k :=
    fun k z hz => G32_majorant k z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by
    simp [Set.mem_Ioo, hr0]
  have hmain := hasDerivAt_tsum_of_isPreconnected hu hopen hpre
    hderiv hbound hy0 summable_G32_zero hy
  have efun : (fun t : ℝ => ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k + 1)
      / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = G32 := by
    funext z
    rfl
  rw [efun] at hmain
  exact hmain

private noncomputable def S32partial (N : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, aCoeff32 k * z ^ k

private noncomputable def S32partialDeriv (N : ℕ) (z : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, aCoeff32 k * (k : ℝ) * z ^ (k - 1)

private lemma finite_ode_S32 (N : ℕ) (z : ℝ) :
    2 * z * (1 - z) * S32partialDeriv (N + 1) z
        + (1 - 2 * z) * S32partial (N + 1) z
      = 1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1) := by
  induction N with
  | zero =>
    have hS : S32partial 1 z = 1 := by
      unfold S32partial
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      simp [aCoeff32_zero]
    have hD : S32partialDeriv 1 z = 0 := by
      unfold S32partialDeriv
      rw [Finset.sum_range_succ, Finset.sum_range_zero]
      simp
    rw [hS, hD]
    have ha0 : aCoeff32 0 = 1 := aCoeff32_zero
    rw [ha0]
    push_cast
    ring
  | succ n ih =>
    have hS : S32partial (n + 1 + 1) z
        = S32partial (n + 1) z + aCoeff32 (n + 1) * z ^ (n + 1) := by
      unfold S32partial
      rw [Finset.sum_range_succ]
    have hD : S32partialDeriv (n + 1 + 1) z
        = S32partialDeriv (n + 1) z
          + aCoeff32 (n + 1) * ((n + 1 : ℕ) : ℝ) * z ^ (n + 1 - 1) := by
      unfold S32partialDeriv
      rw [Finset.sum_range_succ]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub] at hD
    have hpow1 : z ^ (n + 1 + 1) = z ^ (n + 1) * z := pow_succ z (n + 1)
    have hpow2 : z * z ^ n = z ^ (n + 1) := by
      rw [← pow_succ']
    have hrec := aCoeff32_rec n
    have hcast : (((n + 1 : ℕ)) : ℝ) = (n : ℝ) + 1 := by
      push_cast
      ring
    rw [hcast] at hD
    push_cast at ⊢
    rw [hS, hD, hpow1, ← hpow2]
    linear_combination ih + (z * z ^ n) * hrec

private lemma err32_tendsto_zero {z : ℝ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1))
      atTop (𝓝 0) := by
  have hr : ‖(‖z‖ : ℝ)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hz
  have hbase := summable_succ_mul_succ_pow32 (r := ‖z‖) hr
  have hsum : Summable
      (fun N : ℕ => 4 * ‖z‖ * (((N : ℝ) + 1) * ((N : ℝ) + 2) * ‖z‖ ^ N)) :=
    hbase.mul_left (4 * ‖z‖)
  have htend := hsum.tendsto_atTop_zero
  refine squeeze_zero_norm ?_ htend
  intro N
  have ha := aCoeff32_le N
  have han := aCoeff32_nonneg N
  have hN1 : (0:ℝ) ≤ (N : ℝ) + 1 := by positivity
  have hN2 : (0:ℝ) ≤ (N : ℝ) + 2 := by positivity
  have hle1 : ((N : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + 1) * ((N : ℝ) + 2) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_left (by linarith) hN1
  have hnorm : ‖2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1)‖
      = 2 * ((N : ℝ) + 1) * aCoeff32 N * ‖z‖ ^ (N + 1) := by
    have hnn : (0:ℝ) ≤ 2 * ((N : ℝ) + 1) * aCoeff32 N := by positivity
    rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hnn]
  rw [hnorm]
  have hpow : ‖z‖ ^ (N + 1) = ‖z‖ * ‖z‖ ^ N := pow_succ' ‖z‖ N
  rw [hpow]
  calc 2 * ((N : ℝ) + 1) * aCoeff32 N * (‖z‖ * ‖z‖ ^ N)
      ≤ 2 * ((N : ℝ) + 1) * (2 * ((N : ℝ) + 1)) * (‖z‖ * ‖z‖ ^ N) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left ha (by positivity)
    _ = 4 * ‖z‖ * (((N : ℝ) + 1) ^ 2 * ‖z‖ ^ N) := by ring
    _ ≤ 4 * ‖z‖ * (((N : ℝ) + 1) * ((N : ℝ) + 2) * ‖z‖ ^ N) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hle1 (by positivity)

private lemma mem_Ioo_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ z ∈ Set.Ioo (-r) r := by
  refine ⟨(‖z‖ + 1) / 2, by positivity, by linarith [hz], ?_⟩
  have habs : |z| < (‖z‖ + 1) / 2 := by
    rw [← Real.norm_eq_abs]
    linarith [hz]
  rw [abs_lt] at habs
  rw [Set.mem_Ioo]
  constructor <;> linarith [habs.1, habs.2]

private lemma S32_hasDerivAt_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    HasDerivAt S32 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1)) z := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one hz
  exact S32_hasDerivAt_of_mem hr0 hr1 hy

private lemma F32_hasDerivAt_of_norm_lt_one {s : ℝ} (hs : ‖s‖ < 1) :
    HasDerivAt F32 (∑' k : ℕ, aCoeff32 k * s ^ (2 * k)) s := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one hs
  exact F32_hasDerivAt_of_mem hr0 hr1 hy

private lemma G32_hasDerivAt_of_norm_lt_one {t : ℝ} (ht : ‖t‖ < 1) :
    HasDerivAt G32
      (∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) t := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one ht
  exact G32_hasDerivAt_of_mem hr0 hr1 hy

private lemma summable_S32deriv_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    Summable (fun k : ℕ => aCoeff32 k * (k : ℝ) * z ^ (k - 1)) := by
  obtain ⟨r, hr0, hr1, hy⟩ := mem_Ioo_of_norm_lt_one hz
  have hrN : ‖r‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hr0]
    exact hr1
  have hbase := summable_succ_mul_succ_pow32 (r := r) hrN
  have hu : Summable
      (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r)) := by
    have heq : (fun k : ℕ => 2 * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k / r))
        = fun k : ℕ => (2 / r)
          * (((k : ℝ) + 1) * ((k : ℝ) + 2) * r ^ k) := by
      funext k
      field_simp
    rw [heq]
    exact hbase.mul_left (2 / r)
  apply Summable.of_norm_bounded hu
  intro k
  exact S32_majorant hr0 hr1 k z hy

private lemma ode_S32_of_norm_lt_one {z : ℝ} (hz : ‖z‖ < 1) :
    2 * z * (1 - z) * deriv S32 z + (1 - 2 * z) * S32 z = 1 := by
  have hSsum := summable_S32_of_norm_lt_one hz
  have hDsum := summable_S32deriv_of_norm_lt_one hz
  have hHas := S32_hasDerivAt_of_norm_lt_one hz
  have hDeriv : deriv S32 z
      = ∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1) :=
    hHas.deriv
  have hS_tend : Tendsto (fun M : ℕ => S32partial M z) atTop (𝓝 (S32 z)) := by
    have h := hSsum.hasSum.tendsto_sum_nat
    have e1 : (fun M : ℕ => ∑ k ∈ Finset.range M, aCoeff32 k * z ^ k)
        = fun M : ℕ => S32partial M z := by
      funext M
      rfl
    have e2 : (∑' k : ℕ, aCoeff32 k * z ^ k) = S32 z := rfl
    rw [e1, e2] at h
    exact h
  have hD_tend : Tendsto (fun M : ℕ => S32partialDeriv M z) atTop
      (𝓝 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))) := by
    have h := hDsum.hasSum.tendsto_sum_nat
    have e1 : (fun M : ℕ => ∑ k ∈ Finset.range M,
          aCoeff32 k * (k : ℝ) * z ^ (k - 1))
        = fun M : ℕ => S32partialDeriv M z := by
      funext M
      rfl
    rw [e1] at h
    exact h
  have hSucc : Tendsto (fun N : ℕ => N + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hS_succ : Tendsto (fun N : ℕ => S32partial (N + 1) z) atTop
      (𝓝 (S32 z)) :=
    hS_tend.comp hSucc
  have hD_succ : Tendsto (fun N : ℕ => S32partialDeriv (N + 1) z) atTop
      (𝓝 (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))) :=
    hD_tend.comp hSucc
  rw [← hDeriv] at hD_succ
  have hLHS : Tendsto
      (fun N : ℕ => 2 * z * (1 - z) * S32partialDeriv (N + 1) z
        + (1 - 2 * z) * S32partial (N + 1) z)
      atTop (𝓝 (2 * z * (1 - z) * deriv S32 z + (1 - 2 * z) * S32 z)) := by
    apply Tendsto.add
    · exact tendsto_const_nhds.mul hD_succ
    · exact tendsto_const_nhds.mul hS_succ
  have herr := err32_tendsto_zero hz
  have hRHS : Tendsto
      (fun N : ℕ => 1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun _ : ℕ => (1:ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have h := h1.sub herr
    simpa [sub_zero] using h
  have hEq : ∀ N : ℕ,
      (2 * z * (1 - z) * S32partialDeriv (N + 1) z
        + (1 - 2 * z) * S32partial (N + 1) z)
        = (1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1)) :=
    fun N => finite_ode_S32 N z
  have hLHS2 : Tendsto
      (fun N : ℕ => 1 - 2 * ((N : ℝ) + 1) * aCoeff32 N * z ^ (N + 1))
      atTop (𝓝 (2 * z * (1 - z) * deriv S32 z + (1 - 2 * z) * S32 z)) :=
    Tendsto.congr hEq hLHS
  exact tendsto_nhds_unique hLHS2 hRHS

private noncomputable def mu32 (z : ℝ) : ℝ := √(z * (1 - z))

private noncomputable def A32 (z : ℝ) : ℝ := Real.arcsin (√z)

private lemma mu32_pos {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    0 < mu32 z := by
  unfold mu32
  apply Real.sqrt_pos.mpr
  have h1 : (0:ℝ) < 1 - z := by linarith
  exact mul_pos hz0 h1

private lemma mu32_ne_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    mu32 z ≠ 0 :=
  ne_of_gt (mu32_pos hz0 hz1)

private lemma mu32_sq {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    mu32 z ^ 2 = z * (1 - z) := by
  unfold mu32
  have hnn : (0:ℝ) ≤ z * (1 - z) := by
    have h1 : (0:ℝ) ≤ 1 - z := by linarith
    exact mul_nonneg hz0 h1
  rw [Real.sq_sqrt hnn]

private lemma mu32_zero : mu32 0 = 0 := by
  unfold mu32
  simp

private lemma A32_zero : A32 0 = 0 := by
  unfold A32
  simp [Real.arcsin_zero]

private lemma hasDerivAt_mu32 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt mu32 ((1 - 2 * z) / (2 * mu32 z)) z := by
  have hg : HasDerivAt (fun w : ℝ => w * (1 - w)) (1 - 2 * z) z := by
    have h1 : HasDerivAt (fun w : ℝ => w) 1 z := hasDerivAt_id' z
    have h2 : HasDerivAt (fun w : ℝ => (1:ℝ) - w) (-1) z :=
      HasDerivAt.const_sub 1 (hasDerivAt_id' z)
    have hmul := h1.mul h2
    have hval : (1:ℝ) * (1 - z) + z * (-1) = 1 - 2 * z := by ring
    rw [hval] at hmul
    exact hmul
  have hne : z * (1 - z) ≠ 0 := by
    have h1 : (0:ℝ) < 1 - z := by linarith
    exact ne_of_gt (mul_pos hz0 h1)
  have hsqrt := hg.sqrt hne
  have e1 : (fun y : ℝ => √(y * (1 - y))) = mu32 := by
    funext y
    rfl
  have e2 : (1 - 2 * z) / (2 * √(z * (1 - z)))
      = (1 - 2 * z) / (2 * mu32 z) := by
    rfl
  rw [e1, e2] at hsqrt
  exact hsqrt

private lemma hasDerivAt_A32 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt A32 (1 / (2 * mu32 z)) z := by
  have hzN : z ≠ 0 := ne_of_gt hz0
  have hsqrt : HasDerivAt (fun w : ℝ => √(w)) (1 / (2 * √z)) z :=
    Real.hasDerivAt_sqrt hzN
  have hsz0 : (0:ℝ) < √z := Real.sqrt_pos.mpr hz0
  have hsz1 : √z < 1 := by
    have h : √z < √(1:ℝ) :=
      (Real.sqrt_lt_sqrt_iff hz0.le).mpr hz1
    rwa [Real.sqrt_one] at h
  have h1 : √z ≠ -1 := by
    have := ne_of_gt hsz0
    linarith [this]
  have h2 : √z ≠ 1 := ne_of_lt hsz1
  have harcsin : HasDerivAt Real.arcsin (1 / √(1 - (√z) ^ 2)) (√z) :=
    Real.hasDerivAt_arcsin h1 h2
  have hcomp := harcsin.comp z hsqrt
  have e1 : (Real.arcsin ∘ Real.sqrt) = A32 := by
    funext y
    rfl
  rw [e1] at hcomp
  have hsq : (√z) ^ 2 = z := Real.sq_sqrt hz0.le
  have hmu : mu32 z = √z * √(1 - z) := by
    unfold mu32
    rw [Real.sqrt_mul hz0.le]
  have hval : (1 / √(1 - (√z) ^ 2)) * (1 / (2 * √z))
      = 1 / (2 * mu32 z) := by
    rw [hsq, hmu]
    have hz1pos : (0:ℝ) < 1 - z := by linarith
    have hszne : √z ≠ 0 := ne_of_gt hsz0
    have h1zne : √(1 - z) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hz1pos)
    field_simp
  rw [hval] at hcomp
  exact hcomp

private noncomputable def H32 (z : ℝ) : ℝ := mu32 z * S32 z

private lemma hasDerivAt_H32 {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt H32 (1 / (2 * mu32 z)) z := by
  have hzN : ‖z‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hz0]
    exact hz1
  have hS := S32_hasDerivAt_of_norm_lt_one hzN
  have hMu := hasDerivAt_mu32 hz0 hz1
  have hH := hMu.mul hS
  have hDeriv : deriv S32 z
      = ∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1) :=
    hS.deriv
  have hODE := ode_S32_of_norm_lt_one hzN
  have hmu2 := mu32_sq hz0.le hz1.le
  have hmuN := mu32_ne_zero hz0 hz1
  have hEq : ((1 - 2 * z) / (2 * mu32 z)) * S32 z
        + mu32 z * (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))
      = 1 / (2 * mu32 z) := by
    rw [← hDeriv]
    field_simp
    rw [hmu2]
    linear_combination hODE
  have e1 : (mu32 * S32) = H32 := by
    funext y
    rfl
  rw [e1] at hH
  have e2 : ((1 - 2 * z) / (2 * mu32 z)) * S32 z
        + mu32 z * (∑' k : ℕ, aCoeff32 k * (k : ℝ) * z ^ (k - 1))
      = 1 / (2 * mu32 z) :=
    hEq
  rw [e2] at hH
  exact hH

private lemma continuous_mu32 : Continuous mu32 := by
  have hinner : Continuous (fun z : ℝ => z * (1 - z)) := by continuity
  have hcomp : Continuous (Real.sqrt ∘ (fun z : ℝ => z * (1 - z))) :=
    Real.continuous_sqrt.comp hinner
  have e : (Real.sqrt ∘ (fun z : ℝ => z * (1 - z))) = mu32 := by
    funext z
    rfl
  rw [e] at hcomp
  exact hcomp

private lemma continuous_A32 : Continuous A32 := by
  have hcomp : Continuous (Real.arcsin ∘ Real.sqrt) :=
    Real.continuous_arcsin.comp Real.continuous_sqrt
  have e : (Real.arcsin ∘ Real.sqrt) = A32 := by
    funext z
    rfl
  rw [e] at hcomp
  exact hcomp

private lemma continuousAt_S32_zero : ContinuousAt S32 0 := by
  have h0 : ‖(0:ℝ)‖ < 1 := by norm_num
  exact (S32_hasDerivAt_of_norm_lt_one h0).continuousAt

private lemma H32_zero : H32 0 = 0 := by
  unfold H32
  rw [mu32_zero, S32_zero]
  ring

private noncomputable def D32 (z : ℝ) : ℝ := H32 z - A32 z

private lemma D32_zero : D32 0 = 0 := by
  unfold D32
  rw [H32_zero, A32_zero]
  ring

private lemma continuousAt_D32_zero : ContinuousAt D32 0 := by
  have hH : ContinuousAt H32 0 := by
    have hmu : ContinuousAt mu32 0 := continuous_mu32.continuousAt
    have hS := continuousAt_S32_zero
    have hmul := hmu.mul hS
    have e : (mu32 * S32) = H32 := by
      funext z
      rfl
    rw [e] at hmul
    exact hmul
  have hA : ContinuousAt A32 0 := continuous_A32.continuousAt
  have hsub := hH.sub hA
  have e : (H32 - A32) = D32 := by
    funext z
    rfl
  rw [e] at hsub
  exact hsub

private lemma hasDerivAt_D32_zero {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt D32 0 z := by
  have hH := hasDerivAt_H32 hz0 hz1
  have hA := hasDerivAt_A32 hz0 hz1
  have hsub := hH.sub hA
  have e1 : (H32 - A32) = D32 := by
    funext y
    rfl
  rw [e1] at hsub
  have e2 : (1 / (2 * mu32 z)) - (1 / (2 * mu32 z)) = (0:ℝ) := by ring
  rw [e2] at hsub
  exact hsub

private lemma S32_eq_of_mem {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    S32 z = A32 z / mu32 z := by
  have hopen : IsOpen (Set.Ioo (0:ℝ) 1) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (0:ℝ) 1) := isPreconnected_Ioo
  have hdiff : DifferentiableOn ℝ D32 (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := (Set.mem_Ioo.mp hx).1
    have hx1 : x < 1 := (Set.mem_Ioo.mp hx).2
    have hHas := hasDerivAt_D32_zero hx0 hx1
    exact hHas.differentiableAt.differentiableWithinAt
  have hderiv : Set.EqOn (deriv D32) 0 (Set.Ioo 0 1) := by
    intro x hx
    have hx0 : (0:ℝ) < x := (Set.mem_Ioo.mp hx).1
    have hx1 : x < 1 := (Set.mem_Ioo.mp hx).2
    have hHas := hasDerivAt_D32_zero hx0 hx1
    rw [hHas.deriv]
    rfl
  obtain ⟨C, hC⟩ :=
    hopen.exists_is_const_of_deriv_eq_zero hpre hdiff hderiv
  have hseq_mem : ∀ n : ℕ, (1:ℝ) / ((n : ℝ) + 2) ∈ Set.Ioo 0 1 := by
    intro n
    have hN : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    constructor
    · positivity
    · have h2 : (2:ℝ) ≤ (n : ℝ) + 2 := by linarith
      have hpos : (0:ℝ) < (n : ℝ) + 2 := by linarith
      calc (1:ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
            apply one_div_le_one_div_of_le (by norm_num) h2
        _ < 1 := by norm_num
  have hseq_lim : Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
      tendsto_add_atTop_nat 1
    have hcomp := h1.comp hsucc
    have e : (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) ∘ (fun n : ℕ => n + 1)
        = fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2) := by
      funext n
      simp only [Function.comp_apply]
      push_cast
      ring
    rw [e] at hcomp
    exact hcomp
  have hDseq : ∀ n : ℕ, D32 ((1:ℝ) / ((n : ℝ) + 2)) = C := by
    intro n
    exact hC _ (hseq_mem n)
  have hcont := continuousAt_D32_zero
  have hlim : Tendsto (fun n : ℕ => D32 ((1:ℝ) / ((n : ℝ) + 2))) atTop
      (𝓝 (D32 0)) :=
    hcont.tendsto.comp hseq_lim
  rw [D32_zero] at hlim
  have hconst : Tendsto (fun _ : ℕ => C) atTop (𝓝 C) := tendsto_const_nhds
  have hEq : (fun n : ℕ => D32 ((1:ℝ) / ((n : ℝ) + 2)))
      = fun _ : ℕ => C := by
    funext n
    exact hDseq n
  rw [hEq] at hlim
  have hC0 : C = 0 := tendsto_nhds_unique hconst hlim
  have hDz : D32 z = C := hC z (Set.mem_Ioo.mpr ⟨hz0, hz1⟩)
  rw [hC0] at hDz
  have hHA : H32 z = A32 z := by
    unfold D32 at hDz
    linarith [hDz]
  unfold H32 at hHA
  have hmuN := mu32_ne_zero hz0 hz1
  have hEq2 : S32 z = A32 z / mu32 z := by
    rw [eq_div_iff hmuN]
    linear_combination hHA
  exact hEq2

private lemma S32_sq_eq {s : ℝ} (hs : ‖s‖ < 1) (hs0 : s ≠ 0) :
    S32 (s ^ 2) = Real.arcsin s / (s * √(1 - s ^ 2)) := by
  have hs0' : (0:ℝ) < s ^ 2 := sq_pos_of_ne_zero hs0
  have hs1 : s ^ 2 < 1 := by
    have habs : |s| < 1 := by
      rw [← Real.norm_eq_abs]
      exact hs
    have hmem := abs_lt.mp habs
    have hsq : s ^ 2 < 1 ^ 2 := sq_lt_sq' hmem.1 hmem.2
    simpa using hsq
  have hEq := S32_eq_of_mem hs0' hs1
  have hA : A32 (s ^ 2) = Real.arcsin |s| := by
    unfold A32
    rw [Real.sqrt_sq_eq_abs]
  have hmu : mu32 (s ^ 2) = |s| * √(1 - s ^ 2) := by
    unfold mu32
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]
  rw [hEq, hA, hmu]
  have hsqrtN : √(1 - s ^ 2) ≠ 0 := by
    have hpos : (0:ℝ) < 1 - s ^ 2 := by linarith [hs1]
    exact ne_of_gt (Real.sqrt_pos.mpr hpos)
  have habsN : |s| ≠ 0 := abs_ne_zero.mpr hs0
  by_cases hsN : 0 ≤ s
  · have habs : |s| = s := abs_of_nonneg hsN
    rw [habs]
  · have hsneg : s < 0 := lt_of_not_ge hsN
    have habs : |s| = -s := abs_of_neg hsneg
    rw [habs, Real.arcsin_neg]
    field_simp

private lemma deriv_F32_eq_S32 {s : ℝ} (hs : ‖s‖ < 1) :
    deriv F32 s = S32 (s ^ 2) := by
  have hHas := F32_hasDerivAt_of_norm_lt_one hs
  have hDeriv : deriv F32 s
      = ∑' k : ℕ, aCoeff32 k * s ^ (2 * k) :=
    hHas.deriv
  rw [hDeriv]
  have e : (fun k : ℕ => aCoeff32 k * s ^ (2 * k))
      = fun k : ℕ => aCoeff32 k * (s ^ 2) ^ k := by
    funext k
    rw [← pow_mul]
  rw [e]
  rfl

private lemma G32_deriv_zero : (∑' k : ℕ, (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
    / (((2 * k + 1 : ℕ)) : ℝ)) = 1 := by
  have hsingle : HasSum
      (fun k : ℕ => (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) 1 := by
    have h0 : (-1 : ℝ) ^ (0:ℕ) * (0:ℝ) ^ (2 * 0)
        / (((2 * 0 + 1 : ℕ)) : ℝ) = 1 := by norm_num
    have h00 : ∀ b : ℕ, b ≠ 0 →
        (-1 : ℝ) ^ b * (0:ℝ) ^ (2 * b) / (((2 * b + 1 : ℕ)) : ℝ) = 0 := by
      intro b hb
      have hz : (0:ℝ) ^ (2 * b) = 0 := zero_pow (by omega)
      rw [hz]
      simp
    have hS := hasSum_single (0 : ℕ) h00
    rw [h0] at hS
    exact hS
  exact hsingle.tsum_eq

private lemma G32_deriv_eq_arctan_div {t : ℝ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    (∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ))
      = Real.arctan t / t := by
  have hArctan := Real.hasSum_arctan ht
  have hDiv := hArctan.div_const t
  have hEq : (fun k : ℕ => (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ))
      = fun k : ℕ => ((-1 : ℝ) ^ k * t ^ (2 * k + 1)
        / (((2 * k + 1 : ℕ)) : ℝ)) / t := by
    funext k
    have hpow : t ^ (2 * k + 1) = t ^ (2 * k) * t := pow_succ t (2 * k)
    rw [hpow]
    field_simp
  rw [hEq]
  exact hDiv.tsum_eq

private lemma deriv_G32_eq {t : ℝ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    deriv G32 t = Real.arctan t / t := by
  have hHas := G32_hasDerivAt_of_norm_lt_one ht
  have hDeriv : deriv G32 t
      = ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ) :=
    hHas.deriv
  rw [hDeriv]
  exact G32_deriv_eq_arctan_div ht ht0

private lemma deriv_G32_zero : deriv G32 0 = 1 := by
  have h0 : ‖(0:ℝ)‖ < 1 := by norm_num
  have hHas := G32_hasDerivAt_of_norm_lt_one h0
  have hDeriv : deriv G32 0
      = ∑' k : ℕ, (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ) :=
    hHas.deriv
  rw [hDeriv]
  exact G32_deriv_zero

private noncomputable def s32_of_t (t : ℝ) : ℝ := 2 * t / (1 + t ^ 2)

private lemma s32_of_t_zero : s32_of_t 0 = 0 := by
  unfold s32_of_t
  norm_num

private lemma abs_s32_of_t_lt_one {t : ℝ} (ht : ‖t‖ < 1) :
    ‖s32_of_t t‖ < 1 := by
  have habs : |t| < 1 := by
    rw [← Real.norm_eq_abs]
    exact ht
  have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hSq : t ^ 2 = |t| ^ 2 := (sq_abs t).symm
  have h1 : 2 * |t| < 1 + t ^ 2 := by
    have hsq : (0:ℝ) < (1 - |t|) ^ 2 := by
      have hpos : (0:ℝ) < 1 - |t| := by linarith [habs]
      exact sq_pos_of_ne_zero (ne_of_gt hpos)
    have hexpand : (1 - |t|) ^ 2 = 1 - 2 * |t| + |t| ^ 2 := by ring
    rw [hexpand] at hsq
    rw [← hSq] at hsq
    linarith [hsq]
  have hAbs : |s32_of_t t| = 2 * |t| / (1 + t ^ 2) := by
    unfold s32_of_t
    rw [abs_div, abs_of_pos hDpos]
    congr 1
    rw [abs_mul]
    norm_num
  rw [Real.norm_eq_abs, hAbs]
  rw [div_lt_one hDpos]
  exact h1

private lemma hasDerivAt_s32_of_t (t : ℝ) :
    HasDerivAt s32_of_t (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2) t := by
  have h1 : HasDerivAt (fun w : ℝ => 2 * w) 2 t := by
    have h := hasDerivAt_id' t
    have h2 := h.const_mul (2:ℝ)
    simpa using h2
  have h2 : HasDerivAt (fun w : ℝ => (1:ℝ) + w ^ 2) (2 * t) t := by
    have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * t) t := by
      have h := hasDerivAt_pow 2 t
      simpa using h
    have hc := hp.const_add (1:ℝ)
    simpa [add_comm] using hc
  have hDne : (1:ℝ) + t ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hdiv := h1.div h2 hDne
  have hval : (2 * (1 + t ^ 2) - 2 * t * (2 * t)) / (1 + t ^ 2) ^ 2
      = 2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2 := by ring
  rw [hval] at hdiv
  exact hdiv

private lemma sqrt_one_sub_s32_sq {t : ℝ} (ht : ‖t‖ < 1) :
    √(1 - (s32_of_t t) ^ 2) = (1 - t ^ 2) / (1 + t ^ 2) := by
  have habs : |t| < 1 := by
    rw [← Real.norm_eq_abs]
    exact ht
  have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hNpos : (0:ℝ) < 1 - t ^ 2 := by
    have hsq : t ^ 2 < 1 := by
      have hmem := abs_lt.mp habs
      have hsq2 : t ^ 2 < 1 ^ 2 := sq_lt_sq' hmem.1 hmem.2
      simpa using hsq2
    linarith [hsq]
  have hEq : 1 - (s32_of_t t) ^ 2
      = ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 := by
    unfold s32_of_t
    field_simp
    ring
  rw [hEq, Real.sqrt_sq (by positivity)]

private lemma arcsin_s32_eq {t : ℝ} (ht : ‖t‖ < 1) :
    Real.arcsin (s32_of_t t) = 2 * Real.arctan t := by
  have habs : |t| < 1 := by
    rw [← Real.norm_eq_abs]
    exact ht
  have hmem := abs_lt.mp habs
  have h1 : Real.arctan (-1) < Real.arctan t := by
    rw [Real.arctan_lt_arctan_iff]
    exact hmem.1
  have h2 : Real.arctan t < Real.arctan 1 := by
    rw [Real.arctan_lt_arctan_iff]
    exact hmem.2
  have ha1 : Real.arctan (1:ℝ) = Real.pi / 4 := Real.arctan_one
  have haN1 : Real.arctan (-1 : ℝ) = -(Real.pi / 4) := by
    rw [Real.arctan_neg, ha1]
  rw [haN1] at h1
  rw [ha1] at h2
  have hy1 : -(Real.pi / 2) ≤ 2 * Real.arctan t := by linarith [h1]
  have hy2 : 2 * Real.arctan t ≤ Real.pi / 2 := by linarith [h2]
  have hsin : Real.sin (2 * Real.arctan t) = s32_of_t t := by
    have h2mul := Real.sin_two_mul (Real.arctan t)
    have hs := Real.sin_arctan t
    have hc := Real.cos_arctan t
    have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
    have hsq : √(1 + t ^ 2) * √(1 + t ^ 2) = 1 + t ^ 2 :=
      Real.mul_self_sqrt hDpos.le
    have hne : √(1 + t ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hDpos)
    calc Real.sin (2 * Real.arctan t)
        = 2 * (t / √(1 + t ^ 2)) * (1 / √(1 + t ^ 2)) := by
          rw [h2mul, hs, hc]
      _ = 2 * t / (√(1 + t ^ 2) * √(1 + t ^ 2)) := by field_simp
      _ = 2 * t / (1 + t ^ 2) := by rw [hsq]
      _ = s32_of_t t := by unfold s32_of_t; ring
  have hEq : Real.arcsin (Real.sin (2 * Real.arctan t))
      = 2 * Real.arctan t :=
    Real.arcsin_sin hy1 hy2
  rw [hsin] at hEq
  exact hEq

private noncomputable def Phi32 (t : ℝ) : ℝ :=
  F32 (s32_of_t t) - 2 * G32 t

private lemma Phi32_zero : Phi32 0 = 0 := by
  unfold Phi32
  rw [s32_of_t_zero, F32_zero, G32_zero]
  ring

private lemma hasDerivAt_Phi32_of_ne {t : ℝ} (ht : ‖t‖ < 1) (ht0 : t ≠ 0) :
    HasDerivAt Phi32 0 t := by
  have hs : ‖s32_of_t t‖ < 1 := abs_s32_of_t_lt_one ht
  have hDpos : (0:ℝ) < 1 + t ^ 2 := by positivity
  have hDne : (1:ℝ) + t ^ 2 ≠ 0 := ne_of_gt hDpos
  have hs0 : s32_of_t t ≠ 0 := by
    unfold s32_of_t
    apply div_ne_zero _ hDne
    exact mul_ne_zero (by norm_num) ht0
  have hFtsum := F32_hasDerivAt_of_norm_lt_one hs
  have eF : (∑' k : ℕ, aCoeff32 k * (s32_of_t t) ^ (2 * k))
      = S32 ((s32_of_t t) ^ 2) := by
    have e : (fun k : ℕ => aCoeff32 k * (s32_of_t t) ^ (2 * k))
        = fun k : ℕ => aCoeff32 k * ((s32_of_t t) ^ 2) ^ k := by
      funext k
      rw [← pow_mul]
    rw [e]
    rfl
  rw [eF] at hFtsum
  have hGtsum := G32_hasDerivAt_of_norm_lt_one ht
  have eG : (∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ))
      = Real.arctan t / t :=
    G32_deriv_eq_arctan_div ht ht0
  rw [eG] at hGtsum
  have hsDeriv := hasDerivAt_s32_of_t t
  have hComp := hFtsum.comp t hsDeriv
  have h2G := hGtsum.const_mul (2:ℝ)
  have hSub := hComp.sub h2G
  have ePhi : ((F32 ∘ s32_of_t) - (fun w : ℝ => 2 * G32 w)) = Phi32 := by
    funext w
    unfold Phi32
    rfl
  rw [ePhi] at hSub
  have hSval := S32_sq_eq hs hs0
  have hArcsin := arcsin_s32_eq ht
  have hSqrt := sqrt_one_sub_s32_sq ht
  have hsDef : s32_of_t t = 2 * t / (1 + t ^ 2) := rfl
  have hNpos : (0:ℝ) < 1 - t ^ 2 := by
    have habs : |t| < 1 := by
      rw [← Real.norm_eq_abs]
      exact ht
    have hmem := abs_lt.mp habs
    have hsq : t ^ 2 < 1 := by
      have hsq2 : t ^ 2 < 1 ^ 2 := sq_lt_sq' hmem.1 hmem.2
      simpa using hsq2
    linarith [hsq]
  have hNne : (1:ℝ) - t ^ 2 ≠ 0 := ne_of_gt hNpos
  have hEq : S32 ((s32_of_t t) ^ 2)
        * (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2)
        - 2 * (Real.arctan t / t) = 0 := by
    rw [hSval, hArcsin, hSqrt, hsDef]
    field_simp
    ring
  have eDeriv : S32 ((s32_of_t t) ^ 2)
        * (2 * (1 - t ^ 2) / (1 + t ^ 2) ^ 2)
        - 2 * (Real.arctan t / t) = 0 :=
    hEq
  rw [eDeriv] at hSub
  exact hSub

private lemma hasDerivAt_Phi32_zero' : HasDerivAt Phi32 0 0 := by
  have ht : ‖(0:ℝ)‖ < 1 := by norm_num
  have hs : ‖s32_of_t 0‖ < 1 := by
    rw [s32_of_t_zero]
    exact ht
  have hFtsum := F32_hasDerivAt_of_norm_lt_one hs
  have eF : (∑' k : ℕ, aCoeff32 k * (s32_of_t 0) ^ (2 * k)) = 1 := by
    rw [s32_of_t_zero]
    have hsingle : HasSum (fun k : ℕ => aCoeff32 k * (0:ℝ) ^ (2 * k)) 1 := by
      have h0 : aCoeff32 0 * (0:ℝ) ^ (2 * 0) = 1 := by
        rw [aCoeff32_zero]
        norm_num
      have h00 : ∀ b : ℕ, b ≠ 0 → aCoeff32 b * (0:ℝ) ^ (2 * b) = 0 := by
        intro b hb
        have hz : (0:ℝ) ^ (2 * b) = 0 := zero_pow (by omega)
        rw [hz]
        ring
      have hS := hasSum_single (0 : ℕ) h00
      rw [h0] at hS
      exact hS
    exact hsingle.tsum_eq
  rw [eF] at hFtsum
  have hGtsum := G32_hasDerivAt_of_norm_lt_one ht
  have eG : (∑' k : ℕ, (-1 : ℝ) ^ k * (0:ℝ) ^ (2 * k)
        / (((2 * k + 1 : ℕ)) : ℝ)) = 1 :=
    G32_deriv_zero
  rw [eG] at hGtsum
  have hsDeriv := hasDerivAt_s32_of_t 0
  have hsVal : (2:ℝ) * (1 - (0:ℝ) ^ 2) / (1 + (0:ℝ) ^ 2) ^ 2 = 2 := by
    norm_num
  rw [hsVal] at hsDeriv
  have hComp := hFtsum.comp 0 hsDeriv
  have h2G := hGtsum.const_mul (2:ℝ)
  have hSub := hComp.sub h2G
  have ePhi : ((F32 ∘ s32_of_t) - (fun w : ℝ => 2 * G32 w)) = Phi32 := by
    funext w
    unfold Phi32
    rfl
  rw [ePhi] at hSub
  have eDeriv : (1:ℝ) * 2 - 2 * (1:ℝ) = (0:ℝ) := by ring
  have hEq : (1:ℝ) * 2 - 2 * (1:ℝ) = (0:ℝ) := eDeriv
  rw [hEq] at hSub
  exact hSub

private lemma hasDerivAt_Phi32 {t : ℝ} (ht : ‖t‖ < 1) :
    HasDerivAt Phi32 0 t := by
  by_cases ht0 : t = 0
  · subst ht0
    exact hasDerivAt_Phi32_zero'
  · exact hasDerivAt_Phi32_of_ne ht ht0

private lemma Phi32_eq_zero_of_mem {t : ℝ} (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
    Phi32 t = 0 := by
  have hopen : IsOpen (Set.Ioo (-1 : ℝ) 1) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-1 : ℝ) 1) := isPreconnected_Ioo
  have hf : DifferentiableOn ℝ Phi32 (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have habs : ‖x‖ < 1 := by
      have hmem := Set.mem_Ioo.mp hx
      rw [Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hmem.1, hmem.2]
    have hHas := hasDerivAt_Phi32 habs
    exact hHas.differentiableAt.differentiableWithinAt
  have hg : DifferentiableOn ℝ (fun _ : ℝ => (0:ℝ)) (Set.Ioo (-1 : ℝ) 1) :=
    (differentiable_const (0:ℝ)).differentiableOn
  have hf' : Set.EqOn (deriv Phi32) (deriv (fun _ : ℝ => (0:ℝ)))
      (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    have habs : ‖x‖ < 1 := by
      have hmem := Set.mem_Ioo.mp hx
      rw [Real.norm_eq_abs, abs_lt]
      constructor <;> linarith [hmem.1, hmem.2]
    have hHas := hasDerivAt_Phi32 habs
    rw [hHas.deriv]
    simp
  have hx0 : (0:ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have hfgx : Phi32 0 = (fun _ : ℝ => (0:ℝ)) 0 := Phi32_zero
  have hEq := hopen.eqOn_of_deriv_eq hpre hf hg hf' hx0 hfgx
  have h := hEq ht
  simpa using h

private lemma F32_s32_eq {t : ℝ} (ht : ‖t‖ < 1) :
    F32 (s32_of_t t) = 2 * G32 t := by
  have hmem : t ∈ Set.Ioo (-1 : ℝ) 1 := by
    have habs : |t| < 1 := by
      rw [← Real.norm_eq_abs]
      exact ht
    rw [abs_lt] at habs
    rw [Set.mem_Ioo]
    constructor <;> linarith [habs.1, habs.2]
  have hPhi := Phi32_eq_zero_of_mem hmem
  unfold Phi32 at hPhi
  linarith [hPhi]

private lemma tan_abs_lt_one_of_abs_lt {x : ℝ} (hx : |x| < Real.pi / 4) :
    ‖Real.tan x‖ < 1 := by
  have h1 : -(Real.pi / 4) < x := by
    have := abs_lt.mp hx
    linarith [this.1]
  have h2 : x < Real.pi / 4 := (abs_lt.mp hx).2
  have hmem1 : (-(Real.pi / 4)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmemx : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith [h1, h2])
  have hmem2 : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> (have := Real.pi_pos; linarith)
  have hmono := Real.strictMonoOn_tan
  have hlt1 : Real.tan (-(Real.pi / 4)) < Real.tan x :=
    hmono hmem1 hmemx h1
  have hlt2 : Real.tan x < Real.tan (Real.pi / 4) :=
    hmono hmemx hmem2 h2
  rw [Real.tan_pi_div_four] at hlt2
  have hneg : Real.tan (-(Real.pi / 4)) = -1 := by
    rw [Real.tan_neg, Real.tan_pi_div_four]
  rw [hneg] at hlt1
  rw [Real.norm_eq_abs, abs_lt]
  constructor <;> linarith [hlt1, hlt2]

private lemma sin_two_eq_s32_of_tan {x : ℝ} (hx : |x| ≤ Real.pi / 4) :
    Real.sin (2 * x) = s32_of_t (Real.tan x) := by
  have hcos : Real.cos x ≠ 0 := ne_of_gt (cos32_pos x hx)
  have htan : Real.tan x = Real.sin x / Real.cos x :=
    Real.tan_eq_sin_div_cos x
  have hsin2 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
    have h := Real.sin_two_mul x
    linarith [h]
  have hsq : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
    Real.sin_sq_add_cos_sq x
  calc Real.sin (2 * x)
      = 2 * Real.sin x * Real.cos x := hsin2
    _ = 2 * Real.sin x * Real.cos x
        / (Real.sin x ^ 2 + Real.cos x ^ 2) := by
          rw [hsq]
          ring
    _ = 2 * (Real.sin x / Real.cos x)
        / (1 + (Real.sin x / Real.cos x) ^ 2) := by
          field_simp
          ring
    _ = s32_of_t (Real.sin x / Real.cos x) := by
          unfold s32_of_t
          ring
    _ = s32_of_t (Real.tan x) := by rw [← htan]

private lemma eq_of_abs_lt {x : ℝ} (hx : |x| < Real.pi / 4) :
    (∑' k : ℕ, chapter9Entry32LeftTerm x k)
      = 2 * ∑' k : ℕ, chapter9Entry19TanTerm x k := by
  have hx_le : |x| ≤ Real.pi / 4 := le_of_lt hx
  have ht : ‖Real.tan x‖ < 1 := tan_abs_lt_one_of_abs_lt hx
  have hsin := sin_two_eq_s32_of_tan hx_le
  have hF := F32_s32_eq ht
  rw [tsum_left_eq_F32, tsum_tan_eq_G32, hsin]
  exact hF

private lemma continuousOn_F32_Icc :
    ContinuousOn F32 (Set.Icc (-1 : ℝ) 1) := by
  have hu : Summable
      (fun k : ℕ => (2:ℝ) ^ ((1/4 : ℝ))
        * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹)) :=
    summable32_maj54.mul_left _
  apply continuousOn_tsum (fun k => ?_) hu (fun k s hs => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * k + 1)).continuousOn
  · have hs1 : |s| ≤ 1 := by
      have hmem := Set.mem_Icc.mp hs
      rw [abs_le]
      constructor <;> linarith [hmem.1, hmem.2]
    have hpow : |s| ^ (2 * k + 1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hs1
    have hCnn : (0:ℝ) ≤ (2:ℝ) ^ ((1/4 : ℝ)) := by positivity
    have hMnn : (0:ℝ) ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) := by positivity
    have hD2pos : (0:ℝ) < (((k : ℝ) + 1) ^ (2:ℕ)) := by positivity
    have hDle : (((k : ℝ) + 1) ^ (2:ℕ))
        ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ)) := by
      apply pow_le_pow_left₀ (by positivity) _ 2
      have hkn : k + 1 ≤ 2 * k + 1 := by omega
      have h := Nat.cast_le (α := ℝ) |>.mpr hkn
      push_cast at h ⊢
      linarith
    have hMdiv : (((k : ℝ) + 1) ^ ((3/4 : ℝ)))
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ (2:ℕ))
        ≤ (((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ)) :=
      div_le_div_of_nonneg_left hMnn hD2pos hDle
    have hB : bCoeff32 k * |s| ^ (2 * k + 1) ≤ bCoeff32 k := by
      have hle : |s| ^ (2 * k + 1) ≤ 1 := hpow
      calc bCoeff32 k * |s| ^ (2 * k + 1)
          ≤ bCoeff32 k * 1 :=
            mul_le_mul_of_nonneg_left hle (le_of_lt (bCoeff32_pos k))
        _ = bCoeff32 k := mul_one _
    have hnorm : ‖bCoeff32 k * s ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)‖
        = bCoeff32 k * |s| ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      simp only [norm_div, norm_mul, norm_pow, Real.norm_eq_abs]
      rw [abs_of_nonneg (le_of_lt (bCoeff32_pos k)),
        abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n := 2 * k + 1))]
    rw [hnorm]
    calc bCoeff32 k * |s| ^ (2 * k + 1) / ((((2*k+1:ℕ)):ℝ) ^ 2)
        ≤ bCoeff32 k / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hB (by positivity)
      _ ≤ ((2:ℝ) ^ ((1/4 : ℝ)) * (((k : ℝ) + 1) ^ ((3/4 : ℝ))))
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right (bCoeff32_le_rpow k) (by positivity)
      _ = (2:ℝ) ^ ((1/4 : ℝ))
          * ((((k : ℝ) + 1) ^ ((3/4 : ℝ)))
            / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
          rw [mul_div_assoc]
      _ ≤ (2:ℝ) ^ ((1/4 : ℝ))
          * ((((k : ℝ) + 1) ^ ((3/4 : ℝ))) / (((k : ℝ) + 1) ^ (2:ℕ))) := by
          apply mul_le_mul_of_nonneg_left hMdiv hCnn
      _ = (2:ℝ) ^ ((1/4 : ℝ)) * ((((k : ℝ) + 1) ^ ((5/4 : ℝ)))⁻¹) := by
          rw [rpow32_div_eq]

private lemma continuousOn_G32_Icc :
    ContinuousOn G32 (Set.Icc (-1 : ℝ) 1) := by
  apply continuousOn_tsum (fun k => ?_) summable32_maj2
    (fun k t ht => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * k + 1)).continuousOn
  · have ht1 : |t| ≤ 1 := by
      have hmem := Set.mem_Icc.mp ht
      rw [abs_le]
      constructor <;> linarith [hmem.1, hmem.2]
    have hpow : |(-1 : ℝ) ^ k * t ^ (2 * k + 1)| ≤ 1 := by
      simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
      exact pow_le_one₀ (abs_nonneg _) ht1
    have hDle : (((k : ℝ) + 1) ^ 2)
        ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      have hkn : k + 1 ≤ 2 * k + 1 := by omega
      have h := Nat.cast_le (α := ℝ) |>.mpr hkn
      have heq : ((((2 * k + 1 : ℕ)) : ℝ)) = 2 * (k : ℝ) + 1 := by
        push_cast
        ring
      rw [heq]
      have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg _
      nlinarith [hk]
    have hqpos : (0:ℝ) < (((k : ℝ) + 1) ^ 2) := by positivity
    have hnorm : ‖(-1 : ℝ) ^ k * t ^ (2 * k + 1)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)‖
        = |(-1 : ℝ) ^ k * t ^ (2 * k + 1)|
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      simp only [norm_div, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ((((2*k+1:ℕ)):ℝ)^2))]
    rw [hnorm]
    calc |(-1 : ℝ) ^ k * t ^ (2 * k + 1)|
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
        ≤ 1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
          div_le_div_of_nonneg_right hpow (by positivity)
      _ ≤ 1 / (((k : ℝ) + 1) ^ 2) :=
          one_div_le_one_div_of_le hqpos hDle

private lemma continuousOn_LHS32 :
    ContinuousOn (fun x : ℝ => F32 (Real.sin (2 * x)))
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  have hsin : Continuous (fun x : ℝ => Real.sin (2 * x)) := by continuity
  have hmem : ∀ x ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4),
      Real.sin (2 * x) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x _
    have h1 : |Real.sin (2 * x)| ≤ 1 := Real.abs_sin_le_one _
    rw [abs_le] at h1
    rw [Set.mem_Icc]
    constructor <;> linarith [h1.1, h1.2]
  have hcomp := continuousOn_F32_Icc.comp hsin.continuousOn hmem
  have e : (F32 ∘ (fun x : ℝ => Real.sin (2 * x)))
      = fun x : ℝ => F32 (Real.sin (2 * x)) := by
    funext x
    rfl
  rw [e] at hcomp
  exact hcomp

private lemma continuousOn_RHS32 :
    ContinuousOn (fun x : ℝ => G32 (Real.tan x))
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
  have htan : ContinuousOn Real.tan (Set.Icc (-Real.pi / 4) (Real.pi / 4)) := by
    have hsub : Set.Icc (-Real.pi / 4) (Real.pi / 4)
        ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro x hx
      have hmem := Set.mem_Icc.mp hx
      rw [Set.mem_Ioo]
      constructor <;> (have := Real.pi_pos; linarith [hmem.1, hmem.2])
    exact Real.continuousOn_tan_Ioo.mono hsub
  have hmem : ∀ x ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4),
      Real.tan x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x hx
    have hmemIcc := Set.mem_Icc.mp hx
    have habs : |x| ≤ Real.pi / 4 := by
      rw [abs_le]
      constructor <;> linarith [hmemIcc.1, hmemIcc.2]
    have htan := tan32_abs_le x habs
    rw [abs_le] at htan
    rw [Set.mem_Icc]
    constructor <;> linarith [htan.1, htan.2]
  have hcomp := continuousOn_G32_Icc.comp htan hmem
  have e : (G32 ∘ Real.tan) = fun x : ℝ => G32 (Real.tan x) := by
    funext x
    rfl
  rw [e] at hcomp
  exact hcomp

private lemma continuousOn_RHS32mul :
    ContinuousOn (fun x : ℝ => 2 * G32 (Real.tan x))
      (Set.Icc (-Real.pi / 4) (Real.pi / 4)) :=
  continuousOn_RHS32.const_mul 2

private lemma tendsto_one_div_succ :
    Tendsto (fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsucc : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    tendsto_add_atTop_nat 1
  have hcomp := h1.comp hsucc
  have e : (fun k : ℕ => (1:ℝ) / ((k : ℝ) + 1)) ∘ (fun n : ℕ => n + 1)
      = fun n : ℕ => (1:ℝ) / ((n : ℝ) + 2) := by
    funext n
    simp only [Function.comp_apply]
    push_cast
    ring
  rw [e] at hcomp
  exact hcomp

private lemma eq_at_pi_div_four :
    (∑' k : ℕ, chapter9Entry32LeftTerm (Real.pi / 4) k)
      = 2 * ∑' k : ℕ, chapter9Entry19TanTerm (Real.pi / 4) k := by
  have hIcc : (Real.pi / 4) ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    rw [Set.mem_Icc]
    constructor
    · have := Real.pi_pos
      linarith
    · linarith
  have useq : ∀ n : ℕ, Real.pi / 4 - 1 / ((n : ℝ) + 2)
      ∈ Set.Ioo (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    have hN : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hle : (1:ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) _
      linarith [hN]
    have hpi : (1:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
    constructor
    · linarith [hpos, hle, hpi]
    · linarith [hpos]
  have useq_Icc : ∀ n : ℕ, Real.pi / 4 - 1 / ((n : ℝ) + 2)
      ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    exact Set.Ioo_subset_Icc_self (useq n)
  have hlim : Tendsto (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2))
      atTop (𝓝 (Real.pi / 4)) := by
    have h1 : Tendsto (fun _ : ℕ => (Real.pi / 4 : ℝ)) atTop
        (𝓝 (Real.pi / 4)) :=
      tendsto_const_nhds
    have h := h1.sub tendsto_one_div_succ
    simpa [sub_zero] using h
  have hwithin : Tendsto (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2))
      atTop (𝓝[Set.Icc (-Real.pi / 4) (Real.pi / 4)] (Real.pi / 4)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hlim (Filter.Eventually.of_forall useq_Icc)
  have hLHScont := continuousOn_LHS32.continuousWithinAt hIcc
  have hRHScont := continuousOn_RHS32mul.continuousWithinAt hIcc
  have hLHSlim : Tendsto
      ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (F32 (Real.sin (2 * (Real.pi / 4))))) :=
    hLHScont.tendsto.comp hwithin
  have hRHSlim : Tendsto
      ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (2 * G32 (Real.tan (Real.pi / 4)))) :=
    hRHScont.tendsto.comp hwithin
  have hEq : ∀ n : ℕ, F32 (Real.sin (2 * (Real.pi / 4 - 1 / ((n : ℝ) + 2))))
      = 2 * G32 (Real.tan (Real.pi / 4 - 1 / ((n : ℝ) + 2))) := by
    intro n
    have hmem := useq n
    have habs : |Real.pi / 4 - 1 / ((n : ℝ) + 2)| < Real.pi / 4 := by
      have hmemIoo := Set.mem_Ioo.mp hmem
      rw [abs_lt]
      constructor <;> linarith [hmemIoo.1, hmemIoo.2]
    have heq := eq_of_abs_lt habs
    rw [tsum_left_eq_F32, tsum_tan_eq_G32] at heq
    exact heq
  have hEqFun : ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2)))
      = ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => Real.pi / 4 - 1 / ((n : ℝ) + 2))) := by
    funext n
    simp only [Function.comp_apply]
    exact hEq n
  rw [hEqFun] at hLHSlim
  have hUnique : F32 (Real.sin (2 * (Real.pi / 4)))
      = 2 * G32 (Real.tan (Real.pi / 4)) :=
    tendsto_nhds_unique hLHSlim hRHSlim
  rw [tsum_left_eq_F32, tsum_tan_eq_G32]
  exact hUnique

private lemma eq_at_neg_pi_div_four :
    (∑' k : ℕ, chapter9Entry32LeftTerm (-Real.pi / 4) k)
      = 2 * ∑' k : ℕ, chapter9Entry19TanTerm (-Real.pi / 4) k := by
  have hIcc : (-Real.pi / 4) ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    rw [Set.mem_Icc]
    constructor
    · linarith
    · have := Real.pi_pos
      linarith
  have vseq : ∀ n : ℕ, -Real.pi / 4 + 1 / ((n : ℝ) + 2)
      ∈ Set.Ioo (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    have hN : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have hpos : (0:ℝ) < 1 / ((n : ℝ) + 2) := by positivity
    have hle : (1:ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num) _
      linarith [hN]
    have hpi : (1:ℝ) < Real.pi := by linarith [Real.pi_gt_d2]
    constructor
    · linarith [hpos]
    · linarith [hpos, hle, hpi]
  have vseq_Icc : ∀ n : ℕ, -Real.pi / 4 + 1 / ((n : ℝ) + 2)
      ∈ Set.Icc (-Real.pi / 4) (Real.pi / 4) := by
    intro n
    exact Set.Ioo_subset_Icc_self (vseq n)
  have hlim : Tendsto (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2))
      atTop (𝓝 (-Real.pi / 4)) := by
    have h1 : Tendsto (fun _ : ℕ => (-Real.pi / 4 : ℝ)) atTop
        (𝓝 (-Real.pi / 4)) :=
      tendsto_const_nhds
    have h := h1.add tendsto_one_div_succ
    simpa [add_zero] using h
  have hwithin : Tendsto (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2))
      atTop (𝓝[Set.Icc (-Real.pi / 4) (Real.pi / 4)] (-Real.pi / 4)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      hlim (Filter.Eventually.of_forall vseq_Icc)
  have hLHScont := continuousOn_LHS32.continuousWithinAt hIcc
  have hRHScont := continuousOn_RHS32mul.continuousWithinAt hIcc
  have hLHSlim : Tendsto
      ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (F32 (Real.sin (2 * (-Real.pi / 4))))) :=
    hLHScont.tendsto.comp hwithin
  have hRHSlim : Tendsto
      ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2)))
      atTop (𝓝 (2 * G32 (Real.tan (-Real.pi / 4)))) :=
    hRHScont.tendsto.comp hwithin
  have hEq : ∀ n : ℕ, F32 (Real.sin (2 * (-Real.pi / 4 + 1 / ((n : ℝ) + 2))))
      = 2 * G32 (Real.tan (-Real.pi / 4 + 1 / ((n : ℝ) + 2))) := by
    intro n
    have hmem := vseq n
    have habs : |-Real.pi / 4 + 1 / ((n : ℝ) + 2)| < Real.pi / 4 := by
      have hmemIoo := Set.mem_Ioo.mp hmem
      rw [abs_lt]
      constructor <;> linarith [hmemIoo.1, hmemIoo.2]
    have heq := eq_of_abs_lt habs
    rw [tsum_left_eq_F32, tsum_tan_eq_G32] at heq
    exact heq
  have hEqFun : ((fun x : ℝ => F32 (Real.sin (2 * x))) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2)))
      = ((fun x : ℝ => 2 * G32 (Real.tan x)) ∘
        (fun n : ℕ => -Real.pi / 4 + 1 / ((n : ℝ) + 2))) := by
    funext n
    simp only [Function.comp_apply]
    exact hEq n
  rw [hEqFun] at hLHSlim
  have hUnique : F32 (Real.sin (2 * (-Real.pi / 4)))
      = 2 * G32 (Real.tan (-Real.pi / 4)) :=
    tendsto_nhds_unique hLHSlim hRHSlim
  rw [tsum_left_eq_F32, tsum_tan_eq_G32]
  exact hUnique

/-- **Ramanujan's sine series in odd powers of the tangent (Entry 32).** Let $x$ be real with
$|x| \le \pi/4$. Then $\cos x > 0$, the series
$\sum_{k \ge 0} \frac{2^{2k} (k!)^2}{(2k)!\,(2k+1)^2} \sin^{2k+1}(2x)$ and
$\sum_{k \ge 0} \frac{(-1)^k \tan^{2k+1} x}{(2k+1)^2}$ converge absolutely, and the first sum
equals twice the second.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry32_lambertdivisor (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    0 < Real.cos x ∧
      Summable (chapter9Entry32LeftTerm x) ∧
      Summable (chapter9Entry19TanTerm x) ∧
      (∑' k : ℕ, chapter9Entry32LeftTerm x k) =
        2 * ∑' k : ℕ, chapter9Entry19TanTerm x k := by
  refine ⟨cos32_pos x hx, summable32_left x, summable32_tan x hx, ?_⟩
  by_cases hlt : |x| < Real.pi / 4
  · exact eq_of_abs_lt hlt
  · have hEq : |x| = Real.pi / 4 := le_antisymm hx (le_of_not_gt hlt)
    by_cases hx0 : 0 ≤ x
    · have hxAbs : |x| = x := abs_of_nonneg hx0
      have hxPi : x = Real.pi / 4 := by linarith [hEq, hxAbs]
      rw [hxPi]
      exact eq_at_pi_div_four
    · have hxNeg : x < 0 := lt_of_not_ge hx0
      have hxAbs : |x| = -x := abs_of_neg hxNeg
      have hxPi : x = -Real.pi / 4 := by linarith [hEq, hxAbs]
      rw [hxPi]
      exact eq_at_neg_pi_div_four

end
end Entry32Lambertdivisor
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
