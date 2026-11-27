/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Integrals.Log
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.Order.Filter.Basic
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Basic

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry19Catalangf

open scoped Topology
open Filter

noncomputable section

def chapter9Entry19CentralTerm (x : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) *
      (Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
    ((2 : ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

def chapter9Entry19TanTerm (x : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * Real.tan x ^ (2 * k + 1) /
    (((2 * k + 1 : ℕ) : ℝ) ^ 2)

private theorem cos_pos_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < Real.cos x := by
  apply Real.cos_pos_of_mem_Ioo
  have hpi : 0 < Real.pi := Real.pi_pos
  constructor <;> linarith

private theorem sin_nonneg_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 ≤ Real.sin x := by
  apply Real.sin_nonneg_of_nonneg_of_le_pi hx0
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

private theorem tan_nonneg_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 ≤ Real.tan x := by
  apply Real.tan_nonneg_of_nonneg_of_le_pi_div_two hx0
  have hpi : 0 < Real.pi := Real.pi_pos
  linarith

private theorem tan_le_one_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.tan x ≤ 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hx_mem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hpi4_mem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have h := Real.strictMonoOn_tan.monotoneOn hx_mem hpi4_mem hx
  rwa [Real.tan_pi_div_four] at h

private theorem summable_two_div_succ_sq :
    Summable (fun k : ℕ => (2 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) :=
    (Real.summable_one_div_nat_pow).mpr one_lt_two
  have h2 : Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2)) := by
    have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ) ^ 2)) 1).mpr h
    exact hshift
  have h3 := h2.mul_left (2 : ℝ)
  simpa [div_eq_mul_inv, Nat.cast_add, Nat.cast_one] using h3

private theorem sq_succ_le_aux (k : ℕ) :
    ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤ ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  have hk : k + 1 ≤ 2 * k + 1 := by omega
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hk) 2

private theorem Dpos_aux (k : ℕ) : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  apply pow_pos
  apply Nat.cast_pos.mpr
  omega

private theorem summable_central_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Summable (chapter9Entry19CentralTerm x) := by
  have hcos := cos_pos_aux hx0 hx
  have hsin_nn := sin_nonneg_aux hx0 hx
  have hcos_le : Real.cos x ≤ 1 := Real.cos_le_one x
  have hsin_le : Real.sin x ≤ 1 := Real.sin_le_one x
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_two_div_succ_sq
  · unfold chapter9Entry19CentralTerm
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply add_nonneg <;> apply pow_nonneg
      · exact le_of_lt hcos
      · exact hsin_nn
    · apply mul_nonneg
      · apply pow_nonneg; norm_num
      · apply pow_nonneg; exact Nat.cast_nonneg _
  · have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      have h := Nat.choose_le_two_pow (2 * k) k
      have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
        Nat.cast_le.mpr h
      rwa [Nat.cast_pow, Nat.cast_two] at h2
    have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    have hD := Dpos_aux k
    have hcP : ((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 :=
      div_le_one_of_le₀ hchoose (le_of_lt hP)
    have hS2 : Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1) ≤ 2 := by
      have c1 : Real.cos x ^ (2 * k + 1) ≤ 1 :=
        pow_le_one₀ (le_of_lt hcos) hcos_le
      have c2 : Real.sin x ^ (2 * k + 1) ≤ 1 :=
        pow_le_one₀ hsin_nn hsin_le
      linarith
    have hSD : (Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
        ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤ 2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have he := sq_succ_le_aux k
      have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        apply pow_pos
        apply Nat.cast_pos.mpr
        omega
      have step1 : (Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
          ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤ 2 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hS2 (le_of_lt hD)
      have step2 : (2 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hepos he
      exact le_trans step1 step2
    have hSDnn : (0 : ℝ) ≤ (Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
        ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply div_nonneg _ (le_of_lt hD)
      apply add_nonneg <;> apply pow_nonneg
      · exact le_of_lt hcos
      · exact hsin_nn
    have hmul : (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
        ((Real.cos x ^ (2 * k + 1) + Real.sin x ^ (2 * k + 1)) /
          ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) ≤ 2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have h := mul_le_mul hcP hSD hSDnn zero_le_one
      rwa [one_mul] at h
    unfold chapter9Entry19CentralTerm
    rw [← div_mul_div_comm]
    exact hmul

private theorem summable_tan_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Summable (chapter9Entry19TanTerm x) := by
  have htan_nn := tan_nonneg_aux hx0 hx
  have htan_le := tan_le_one_aux hx0 hx
  refine Summable.of_norm_bounded summable_two_div_succ_sq (fun k => ?_)
  have habs : |Real.tan x| ≤ 1 := by rwa [abs_of_nonneg htan_nn]
  have hD := Dpos_aux k
  have he := sq_succ_le_aux k
  have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
    apply pow_pos
    apply Nat.cast_pos.mpr
    omega
  have hpow : |Real.tan x| ^ (2 * k + 1) ≤ 1 :=
    pow_le_one₀ (abs_nonneg (Real.tan x)) habs
  have hle : |Real.tan x| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
      2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
    have step1 : |Real.tan x| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right hpow (le_of_lt hD)
    have hinv : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
      one_div_le_one_div_of_le hepos he
    have h12 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hepos)
    exact le_trans step1 (le_trans hinv h12)
  have hnorm : ‖chapter9Entry19TanTerm x k‖ =
      |Real.tan x| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
    unfold chapter9Entry19TanTerm
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos hD]
  rw [hnorm]
  exact hle

/-- The auxiliary series `S(u) = Σ_k c_k u^{2k+1} / (2k+1)²` with `c_k = C(2k,k)/4^k`. -/
private def chap9S (u : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) * u ^ (2 * k + 1) /
    ((2 : ℝ) ^ (2 * k) * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

/-- The auxiliary series `T(v) = Σ_k (-1)^k v^{2k+1} / (2k+1)²`. -/
private def chap9T (v : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * v ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

private theorem central_split_aux (x : ℝ) (k : ℕ) : chapter9Entry19CentralTerm x k =
    chap9S (Real.cos x) k + chap9S (Real.sin x) k := by
  unfold chapter9Entry19CentralTerm chap9S
  rw [mul_add, add_div]

private theorem summable_chap9S_aux {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (chap9S u) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) summable_two_div_succ_sq
  · unfold chap9S
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      exact pow_nonneg hu0 _
    · apply mul_nonneg
      · apply pow_nonneg; norm_num
      · apply pow_nonneg; exact Nat.cast_nonneg _
  · have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      have h := Nat.choose_le_two_pow (2 * k) k
      have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
        Nat.cast_le.mpr h
      rwa [Nat.cast_pow, Nat.cast_two] at h2
    have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    have hD := Dpos_aux k
    have hcP : ((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 :=
      div_le_one_of_le₀ hchoose (le_of_lt hP)
    have hS2 : u ^ (2 * k + 1) ≤ 2 := by
      have h1 : u ^ (2 * k + 1) ≤ 1 := pow_le_one₀ hu0 hu1
      linarith
    have hSD : u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have he := sq_succ_le_aux k
      have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        apply pow_pos
        apply Nat.cast_pos.mpr
        omega
      have step1 : u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hS2 (le_of_lt hD)
      have step2 : (2 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hepos he
      exact le_trans step1 step2
    have hSDnn : (0 : ℝ) ≤ u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_nonneg (pow_nonneg hu0 _) (le_of_lt hD)
    have hmul : (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
        (u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have h := mul_le_mul hcP hSD hSDnn zero_le_one
      rwa [one_mul] at h
    unfold chap9S
    rw [← div_mul_div_comm]
    exact hmul

private theorem tsum_central_split_aux {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    (∑' k : ℕ, chapter9Entry19CentralTerm x k) =
      (∑' k : ℕ, chap9S (Real.cos x) k) + ∑' k : ℕ, chap9S (Real.sin x) k := by
  have hcos := cos_pos_aux hx0 hx
  have hsin_nn := sin_nonneg_aux hx0 hx
  have h1 := summable_chap9S_aux (le_of_lt hcos) (Real.cos_le_one x)
  have h2 := summable_chap9S_aux hsin_nn (Real.sin_le_one x)
  simp only [central_split_aux]
  exact Summable.tsum_add h1 h2

private theorem chap9S_zero_aux : (∑' k : ℕ, chap9S 0 k) = 0 := by
  have h : (fun k : ℕ => chap9S 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chap9S
    rw [zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

private theorem chap9T_zero_aux : (∑' k : ℕ, chap9T 0 k) = 0 := by
  have h : (fun k : ℕ => chap9T 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chap9T
    rw [zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

private theorem continuousOn_chap9S_tsum_aux :
    ContinuousOn (fun u : ℝ => ∑' k : ℕ, chap9S u k) (Set.Icc (-1) 1) := by
  refine continuousOn_tsum (fun k => ?_) summable_two_div_succ_sq (fun k u hu => ?_)
  · unfold chap9S
    apply ContinuousOn.div
    · exact ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
    · exact continuousOn_const
    · intro v _
      apply ne_of_gt
      apply mul_pos (by positivity)
      exact Dpos_aux k
  · rw [Set.mem_Icc] at hu
    have habs : |u| ≤ 1 := abs_le.mpr hu
    have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
      have h := Nat.choose_le_two_pow (2 * k) k
      have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
        Nat.cast_le.mpr h
      rwa [Nat.cast_pow, Nat.cast_two] at h2
    have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
    have hD := Dpos_aux k
    have hPDnn : (0 : ℝ) ≤ (2 : ℝ) ^ (2 * k) * ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      mul_nonneg (le_of_lt hP) (le_of_lt hD)
    have hcP : ((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k) ≤ 1 :=
      div_le_one_of_le₀ hchoose (le_of_lt hP)
    have he := sq_succ_le_aux k
    have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      apply Nat.cast_pos.mpr
      omega
    have hpow : |u| ^ (2 * k + 1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg u) habs
    have hSD : |u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have step1 : |u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hpow (le_of_lt hD)
      have hinv : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        one_div_le_one_div_of_le hepos he
      have h12 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hepos)
      exact le_trans step1 (le_trans hinv h12)
    have hSDnn : (0 : ℝ) ≤ |u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
      div_nonneg (pow_nonneg (abs_nonneg u) _) (le_of_lt hD)
    have hmul : (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
        (|u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have h := mul_le_mul hcP hSD hSDnn zero_le_one
      rwa [one_mul] at h
    have hnorm : ‖chap9S u k‖ =
        (((Nat.choose (2 * k) k : ℕ) : ℝ) / (2 : ℝ) ^ (2 * k)) *
          (|u| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
      unfold chap9S
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow,
        abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg hPDnn,
        ← div_mul_div_comm]
    rw [hnorm]
    exact hmul

private theorem continuousOn_chap9T_tsum_aux :
    ContinuousOn (fun v : ℝ => ∑' k : ℕ, chap9T v k) (Set.Icc (-1) 1) := by
  refine continuousOn_tsum (fun k => ?_) summable_two_div_succ_sq (fun k v hv => ?_)
  · unfold chap9T
    apply ContinuousOn.div
    · exact ContinuousOn.mul continuousOn_const (ContinuousOn.pow continuousOn_id _)
    · exact continuousOn_const
    · intro w _
      apply ne_of_gt
      exact Dpos_aux k
  · rw [Set.mem_Icc] at hv
    have habs : |v| ≤ 1 := abs_le.mpr hv
    have hD := Dpos_aux k
    have he := sq_succ_le_aux k
    have hepos : (0 : ℝ) < ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      apply pow_pos
      apply Nat.cast_pos.mpr
      omega
    have hpow : |v| ^ (2 * k + 1) ≤ 1 :=
      pow_le_one₀ (abs_nonneg v) habs
    have hle : |v| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
        2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) := by
      have step1 : |v| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hpow (le_of_lt hD)
      have hinv : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≤
          1 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        one_div_le_one_div_of_le hepos he
      have h12 : (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ) ^ 2) ≤
          2 / ((((k + 1 : ℕ)) : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 2) (le_of_lt hepos)
      exact le_trans step1 (le_trans hinv h12)
    have hnorm : ‖chap9T v k‖ =
        |v| ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
      unfold chap9T
      rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs]
      rw [abs_mul, abs_pow, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos hD]
    rw [hnorm]
    exact hle

private theorem tan_at_zero_aux : (∑' k : ℕ, chapter9Entry19TanTerm 0 k) = 0 := by
  have h : (fun k : ℕ => chapter9Entry19TanTerm 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chapter9Entry19TanTerm
    rw [Real.tan_zero, zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

private theorem log_two_cos_zero_aux : Real.log (2 * Real.cos 0) = Real.log 2 := by
  rw [Real.cos_zero, mul_one]

/-- Central coefficient `c_k = C(2k,k)/4^k`. -/
private def chap9c (k : ℕ) : ℝ :=
  (Nat.choose (2 * k) k : ℝ) / (2 : ℝ) ^ (2 * k)

/-- `A` series term `c_k u^{2k+1}/(2k+1)`. -/
private def chap9A (u : ℝ) (k : ℕ) : ℝ :=
  chap9c k * u ^ (2 * k + 1) / (((2 * k + 1 : ℕ)) : ℝ)

/-- `B` series term `c_k u^{2k}`. -/
private def chap9B (u : ℝ) (k : ℕ) : ℝ :=
  chap9c k * u ^ (2 * k)

/-- Derivative of `S` term: `c_k u^{2k}/(2k+1)`. -/
private def chap9Sderiv (u : ℝ) (k : ℕ) : ℝ :=
  chap9c k * u ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)

/-- Derivative of `T` term: `(-1)^k v^{2k}/(2k+1)`. -/
private def chap9Tderiv (v : ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * v ^ (2 * k) / (((2 * k + 1 : ℕ)) : ℝ)

private theorem chap9c_nonneg (k : ℕ) : 0 ≤ chap9c k := by
  unfold chap9c
  apply div_nonneg (Nat.cast_nonneg _)
  apply pow_nonneg
  norm_num

private theorem chap9c_le_one (k : ℕ) : chap9c k ≤ 1 := by
  unfold chap9c
  have hchoose : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * k) := by
    have h := Nat.choose_le_two_pow (2 * k) k
    have h2 : ((Nat.choose (2 * k) k : ℕ) : ℝ) ≤ ((((2 ^ (2 * k) : ℕ))) : ℝ) :=
      Nat.cast_le.mpr h
    rwa [Nat.cast_pow, Nat.cast_two] at h2
  have hP : (0 : ℝ) < (2 : ℝ) ^ (2 * k) := by positivity
  exact div_le_one_of_le₀ hchoose (le_of_lt hP)

private theorem Dpos1_aux (k : ℕ) : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ)) := by
  apply Nat.cast_pos.mpr
  omega

private theorem inv_D_le_one_aux (k : ℕ) : (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ)) ≤ 1 := by
  rw [div_le_one (Dpos1_aux k)]
  have h : (1 : ℕ) ≤ 2 * k + 1 := by omega
  exact_mod_cast h

private theorem chap9S_eq_aux (u : ℝ) (k : ℕ) :
    chap9S u k = chap9c k * u ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold chap9S chap9c
  have hP : (2 : ℝ) ^ (2 * k) ≠ 0 := by positivity
  have hD : ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt (Dpos_aux k)
  field_simp

private theorem chap9c_zero_eq : chap9c 0 = 1 := by
  unfold chap9c
  simp

private theorem chap9c_succ (n : ℕ) :
    chap9c (n + 1) = chap9c n * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) := by
  have hcb := Nat.succ_mul_centralBinom_succ n
  have hcbR : (((n : ℝ) + 1)) * ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * ((Nat.centralBinom n : ℕ) : ℝ) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) hcb
    push_cast at h
    linarith [h]
  have hcb_eq : ∀ m : ℕ, ((Nat.choose (2 * m) m : ℕ) : ℝ)
      = ((Nat.centralBinom m : ℕ) : ℝ) := by
    intro m
    rw [Nat.centralBinom_eq_two_mul_choose]
  have hpow : (2 : ℝ) ^ (2 * (n + 1)) = 4 * (2 : ℝ) ^ (2 * n) := by
    have : 2 * (n + 1) = 2 * n + 2 := by omega
    rw [this, pow_add]
    norm_num [pow_two]
    ring
  have hn1 : ((((n + 1 : ℕ)) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have h2n2 : ((((2 * n + 2 : ℕ)) : ℝ)) ≠ 0 := by
    have : (0 : ℕ) < 2 * n + 2 := by omega
    exact_mod_cast ne_of_gt this
  have hP : (2 : ℝ) ^ (2 * n) ≠ 0 := by positivity
  unfold chap9c
  rw [hcb_eq (n + 1), hcb_eq n, hpow]
  have hcast1 : ((((n + 1 : ℕ)) : ℝ)) = (n : ℝ) + 1 := by
    push_cast
    ring
  have hcast2 : ((((2 * n + 1 : ℕ)) : ℝ)) = 2 * (n : ℝ) + 1 := by
    push_cast
    ring
  have hcbR' : ((Nat.centralBinom (n + 1) : ℕ) : ℝ)
      = 2 * (((2 * n + 1 : ℕ)) : ℝ) * ((Nat.centralBinom n : ℕ) : ℝ)
        / ((((n + 1 : ℕ)) : ℝ)) := by
    rw [eq_div_iff hn1, hcast1, hcast2]
    linarith [hcbR]
  rw [hcbR']
  have hcast : ((((2 * n + 2 : ℕ)) : ℝ)) = 2 * ((((n + 1 : ℕ)) : ℝ)) := by
    push_cast
    ring
  rw [hcast]
  field_simp
  ring

private theorem multichoose_half_succ (n : ℕ) :
    Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = Ring.multichoose (1 / 2 : ℝ) n
        * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) := by
  have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) (n + 1)
  have h0 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 / 2 : ℝ) n
  rw [nsmul_eq_mul] at h1 h0
  have e1 := Polynomial.ascPochhammer_smeval_eq_eval (1 / 2 : ℝ) (n + 1)
  have e0 := Polynomial.ascPochhammer_smeval_eq_eval (1 / 2 : ℝ) n
  rw [e1] at h1
  rw [e0] at h0
  have hsucc : (ascPochhammer ℝ (n + 1)).eval (1 / 2 : ℝ)
      = (ascPochhammer ℝ n).eval (1 / 2 : ℝ) * ((1 / 2 : ℝ) + (n : ℝ)) :=
    ascPochhammer_succ_eval n (1 / 2 : ℝ)
  have hfact1 : ((((n + 1).factorial : ℕ)) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (n + 1)
  have hfact0 : ((((n.factorial : ℕ))) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : ((((n + 1 : ℕ)) : ℝ)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hfact_succ : ((((n + 1).factorial : ℕ)) : ℝ)
      = ((((n + 1 : ℕ)) : ℝ)) * ((((n.factorial : ℕ))) : ℝ) := by
    have h : (n + 1).factorial = (n + 1) * n.factorial := Nat.factorial_succ n
    have hc := congrArg (Nat.cast : ℕ → ℝ) h
    push_cast at hc
    push_cast
    linarith [hc]
  have hcast1 : ((((n + 1 : ℕ)) : ℝ)) = (n : ℝ) + 1 := by
    push_cast
    ring
  have hcast2 : ((((2 * n + 1 : ℕ)) : ℝ)) = 2 * (n : ℝ) + 1 := by
    push_cast
    ring
  have hcast3 : ((((2 * n + 2 : ℕ)) : ℝ)) = 2 * ((n : ℝ) + 1) := by
    push_cast
    ring
  have hmn : Ring.multichoose (1 / 2 : ℝ) n
      = (ascPochhammer ℝ n).eval (1 / 2 : ℝ) / ((((n.factorial : ℕ))) : ℝ) := by
    rw [eq_div_iff hfact0]
    linarith [h0]
  have hmn1 : Ring.multichoose (1 / 2 : ℝ) (n + 1)
      = (ascPochhammer ℝ (n + 1)).eval (1 / 2 : ℝ)
        / ((((n + 1).factorial : ℕ)) : ℝ) := by
    rw [eq_div_iff hfact1]
    linarith [h1]
  rw [hmn1, hmn, hsucc, hfact_succ, hcast1, hcast2, hcast3]
  field_simp
  ring

private theorem ring_choose_half_eq_chap9c (n : ℕ) :
    Ring.choose ((1 / 2 : ℝ) + (n : ℝ) - 1) n = chap9c n := by
  induction n with
  | zero =>
    have hz : Ring.choose ((1 / 2 : ℝ) + ((0 : ℕ) : ℝ) - 1) 0 = 1 :=
      Ring.choose_zero_right _
    rw [hz]
    exact chap9c_zero_eq.symm
  | succ n ih =>
    have hmulti : Ring.choose ((1 / 2 : ℝ) + (((n + 1 : ℕ)) : ℝ) - 1) (n + 1)
        = Ring.multichoose (1 / 2 : ℝ) (n + 1) := by
      have h := Ring.multichoose_eq (1 / 2 : ℝ) (n + 1)
      exact h.symm ▸ rfl
    have hmulti0 : Ring.choose ((1 / 2 : ℝ) + (n : ℝ) - 1) n
        = Ring.multichoose (1 / 2 : ℝ) n := by
      have h := Ring.multichoose_eq (1 / 2 : ℝ) n
      exact h.symm ▸ rfl
    calc Ring.choose ((1 / 2 : ℝ) + (((n + 1 : ℕ)) : ℝ) - 1) (n + 1)
        = Ring.multichoose (1 / 2 : ℝ) (n + 1) := hmulti
      _ = Ring.multichoose (1 / 2 : ℝ) n
            * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) :=
          multichoose_half_succ n
      _ = chap9c n * (((2 * n + 1 : ℕ) : ℝ) / (((2 * n + 2 : ℕ)) : ℝ)) := by
          rw [← hmulti0, ih]
      _ = chap9c (n + 1) := (chap9c_succ n).symm

private theorem abs_sq_lt_one_of_abs_lt_one {u : ℝ} (hu : |u| < 1) :
    |u ^ 2| < 1 := by
  rw [abs_pow]
  have h0 : 0 ≤ |u| := abs_nonneg u
  have h2 : |u| ^ 2 < 1 := by
    have h := pow_lt_one₀ h0 hu (by norm_num : 2 ≠ 0)
    exact h
  exact h2

private theorem chap9B_hasSum {u : ℝ} (hu : |u| < 1) :
    HasSum (chap9B u) (1 / Real.sqrt (1 - u ^ 2)) := by
  have hY : |u ^ 2| < 1 := abs_sq_lt_one_of_abs_lt_one hu
  have hmem : (u ^ 2) ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_dist, dist_zero_right]
    simp only [Real.norm_eq_abs]
    exact ENNReal.ofReal_lt_one.mpr hY
  have hPS := Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero (1 / 2 : ℝ)
  have hHas := hPS.hasSum hmem
  simp only [zero_add, FormalMultilinearSeries.ofScalars_apply_eq,
    smul_eq_mul] at hHas
  have hterm : (fun n : ℕ => Ring.choose ((1 / 2 : ℝ) + (n : ℝ) - 1) n
      * (u ^ 2) ^ n) = chap9B u := by
    funext n
    unfold chap9B
    rw [ring_choose_half_eq_chap9c n]
    congr 1
    rw [← pow_mul]
  rw [hterm] at hHas
  have hsqrt : Real.sqrt (1 - u ^ 2) = (1 - u ^ 2) ^ ((1 / 2 : ℝ)) :=
    Real.sqrt_eq_rpow (1 - u ^ 2)
  rw [hsqrt]
  exact hHas

private theorem chap9B_tsum {u : ℝ} (hu : |u| < 1) :
    (∑' k : ℕ, chap9B u k) = 1 / Real.sqrt (1 - u ^ 2) :=
  (chap9B_hasSum hu).tsum_eq

private theorem hasDerivAt_chap9A_term (n : ℕ) (y : ℝ) :
    HasDerivAt (fun u => chap9A u n) (chap9B y n) y := by
  have hD : ((((2 * n + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (Dpos1_aux n)
  have hsub : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel _ _
  have hpow : HasDerivAt (fun u : ℝ => u ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * y ^ (2 * n)) y := by
    have h := hasDerivAt_pow (2 * n + 1) y
    rw [hsub] at h
    exact h
  have hcm := hpow.const_mul (chap9c n)
  have hdiv := hcm.div_const ((((2 * n + 1 : ℕ)) : ℝ))
  have hEq : (fun u => chap9A u n)
      = (fun u => chap9c n * u ^ (2 * n + 1) / ((((2 * n + 1 : ℕ)) : ℝ))) := by
    funext u
    rfl
  rw [hEq]
  have hval : chap9c n * ((((2 * n + 1 : ℕ)) : ℝ) * y ^ (2 * n))
      / ((((2 * n + 1 : ℕ)) : ℝ)) = chap9B y n := by
    unfold chap9B
    field_simp
  rw [hval] at hdiv
  exact hdiv

private theorem hasDerivAt_chap9S_term (n : ℕ) (y : ℝ) :
    HasDerivAt (fun u => chap9S u n) (chap9Sderiv y n) y := by
  have hD : ((((2 * n + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (Dpos1_aux n)
  have hD2 : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt (Dpos_aux n)
  have hsub : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel _ _
  have hpow : HasDerivAt (fun u : ℝ => u ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * y ^ (2 * n)) y := by
    have h := hasDerivAt_pow (2 * n + 1) y
    rw [hsub] at h
    exact h
  have hcm := hpow.const_mul (chap9c n)
  have hdiv := hcm.div_const ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
  have hEq : (fun u => chap9S u n)
      = (fun u => chap9c n * u ^ (2 * n + 1) / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext u
    exact chap9S_eq_aux u n
  rw [hEq]
  have hval : chap9c n * ((((2 * n + 1 : ℕ)) : ℝ) * y ^ (2 * n))
      / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) = chap9Sderiv y n := by
    unfold chap9Sderiv
    have hsq : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
        = ((((2 * n + 1 : ℕ)) : ℝ)) * ((((2 * n + 1 : ℕ)) : ℝ)) := by
      rw [pow_two]
    rw [hsq]
    field_simp
  rw [hval] at hdiv
  exact hdiv

private theorem hasDerivAt_chap9T_term (n : ℕ) (y : ℝ) :
    HasDerivAt (fun v => chap9T v n) (chap9Tderiv y n) y := by
  have hD2 : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) ≠ 0 := ne_of_gt (Dpos_aux n)
  have hsub : 2 * n + 1 - 1 = 2 * n := Nat.add_sub_cancel _ _
  have hpow : HasDerivAt (fun v : ℝ => v ^ (2 * n + 1))
      (((2 * n + 1 : ℕ) : ℝ) * y ^ (2 * n)) y := by
    have h := hasDerivAt_pow (2 * n + 1) y
    rw [hsub] at h
    exact h
  have hcm := hpow.const_mul ((-1 : ℝ) ^ n)
  have hdiv := hcm.div_const ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
  have hEq : (fun v => chap9T v n)
      = (fun v => (-1 : ℝ) ^ n * v ^ (2 * n + 1)
        / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
    funext v
    rfl
  rw [hEq]
  have hval : (-1 : ℝ) ^ n * ((((2 * n + 1 : ℕ)) : ℝ) * y ^ (2 * n))
      / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2) = chap9Tderiv y n := by
    unfold chap9Tderiv
    have hD : ((((2 * n + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (Dpos1_aux n)
    have hsq : ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
        = ((((2 * n + 1 : ℕ)) : ℝ)) * ((((2 * n + 1 : ℕ)) : ℝ)) := by
      rw [pow_two]
    rw [hsq]
    field_simp
  rw [hval] at hdiv
  exact hdiv

private theorem abs_pow_two_mul_le {y ρ : ℝ} (hy : |y| < ρ) (_hρ0 : 0 ≤ ρ) (n : ℕ) :
    |y| ^ (2 * n) ≤ (ρ ^ 2) ^ n := by
  have hle : |y| ≤ ρ := le_of_lt hy
  have h1 : |y| ^ (2 * n) ≤ ρ ^ (2 * n) :=
    pow_le_pow_left₀ (abs_nonneg y) hle (2 * n)
  have h2 : ρ ^ (2 * n) = (ρ ^ 2) ^ n := by
    rw [← pow_mul]
  rw [h2] at h1
  exact h1

private theorem norm_chap9B_le {ρ y : ℝ} (hρ0 : 0 ≤ ρ) (hy : y ∈ Set.Ioo (-ρ) ρ)
    (n : ℕ) : ‖chap9B y n‖ ≤ (ρ ^ 2) ^ n := by
  have habs : |y| < ρ := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hpow := abs_pow_two_mul_le habs hρ0 n
  have hc0 : 0 ≤ chap9c n := chap9c_nonneg n
  have hc1 : chap9c n ≤ 1 := chap9c_le_one n
  unfold chap9B
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hc0]
  calc chap9c n * |y| ^ (2 * n)
      ≤ 1 * (ρ ^ 2) ^ n := by
        apply mul_le_mul hc1 hpow (by positivity) zero_le_one
    _ = (ρ ^ 2) ^ n := one_mul _

private theorem norm_chap9Sderiv_le {ρ y : ℝ} (hρ0 : 0 ≤ ρ)
    (hy : y ∈ Set.Ioo (-ρ) ρ) (n : ℕ) :
    ‖chap9Sderiv y n‖ ≤ (ρ ^ 2) ^ n := by
  have habs : |y| < ρ := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hpow := abs_pow_two_mul_le habs hρ0 n
  have hc0 : 0 ≤ chap9c n := chap9c_nonneg n
  have hc1 : chap9c n ≤ 1 := chap9c_le_one n
  have hD := Dpos1_aux n
  have hDnn : (0 : ℝ) ≤ ((((2 * n + 1 : ℕ)) : ℝ)) := le_of_lt hD
  unfold chap9Sderiv
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_nonneg hc0,
    abs_of_nonneg hDnn]
  have h1 : chap9c n * |y| ^ (2 * n) ≤ (ρ ^ 2) ^ n := by
    calc chap9c n * |y| ^ (2 * n)
        ≤ 1 * (ρ ^ 2) ^ n := mul_le_mul hc1 hpow (by positivity) zero_le_one
      _ = (ρ ^ 2) ^ n := one_mul _
  have h2 : (1 : ℝ) / ((((2 * n + 1 : ℕ)) : ℝ)) ≤ 1 := inv_D_le_one_aux n
  have h2nn : (0 : ℝ) ≤ 1 / ((((2 * n + 1 : ℕ)) : ℝ)) := by positivity
  have hnn : (0 : ℝ) ≤ (ρ ^ 2) ^ n := by positivity
  calc chap9c n * |y| ^ (2 * n) / ((((2 * n + 1 : ℕ)) : ℝ))
      = (chap9c n * |y| ^ (2 * n)) * (1 / ((((2 * n + 1 : ℕ)) : ℝ))) := by
        rw [div_eq_mul_one_div]
    _ ≤ (ρ ^ 2) ^ n * 1 := mul_le_mul h1 h2 h2nn hnn
    _ = (ρ ^ 2) ^ n := mul_one _

private theorem norm_chap9Tderiv_le {ρ y : ℝ} (_hρ0 : 0 ≤ ρ)
    (hy : y ∈ Set.Ioo (-ρ) ρ) (n : ℕ) :
    ‖chap9Tderiv y n‖ ≤ (ρ ^ 2) ^ n := by
  have habs : |y| < ρ := abs_lt.mpr (Set.mem_Ioo.mp hy)
  have hρ0 : 0 ≤ ρ := _hρ0
  have hpow := abs_pow_two_mul_le habs hρ0 n
  have hD := Dpos1_aux n
  have hDnn : (0 : ℝ) ≤ ((((2 * n + 1 : ℕ)) : ℝ)) := le_of_lt hD
  unfold chap9Tderiv
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg hDnn]
  have h1 : |y| ^ (2 * n) ≤ (ρ ^ 2) ^ n := hpow
  have h2 : (1 : ℝ) / ((((2 * n + 1 : ℕ)) : ℝ)) ≤ 1 := inv_D_le_one_aux n
  have h2nn : (0 : ℝ) ≤ 1 / ((((2 * n + 1 : ℕ)) : ℝ)) := by positivity
  have hnn : (0 : ℝ) ≤ (ρ ^ 2) ^ n := by positivity
  calc |y| ^ (2 * n) / ((((2 * n + 1 : ℕ)) : ℝ))
      = (|y| ^ (2 * n)) * (1 / ((((2 * n + 1 : ℕ)) : ℝ))) := by
        rw [div_eq_mul_one_div]
    _ ≤ (ρ ^ 2) ^ n * 1 := mul_le_mul h1 h2 h2nn hnn
    _ = (ρ ^ 2) ^ n := mul_one _

private theorem summable_rho_sq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    Summable (fun n : ℕ => (ρ ^ 2) ^ n) := by
  have h0 : (0 : ℝ) ≤ ρ ^ 2 := by positivity
  have h1 : ρ ^ 2 < 1 := by nlinarith [hρ0, hρ1, sq_nonneg ρ]
  exact summable_geometric_of_lt_one h0 h1

private theorem summable_chap9A_zero : Summable (fun n : ℕ => chap9A 0 n) := by
  have h0 : (fun n : ℕ => chap9A 0 n) = fun _ => (0 : ℝ) := by
    funext n
    unfold chap9A
    rw [zero_pow (by omega : 2 * n + 1 ≠ 0), mul_zero, zero_div]
  rw [h0]
  exact hasSum_zero.summable

private theorem summable_chap9S_zero : Summable (fun n : ℕ => chap9S 0 n) := by
  have h0 : (fun n : ℕ => chap9S 0 n) = fun _ => (0 : ℝ) := by
    funext n
    unfold chap9S
    rw [zero_pow (by omega : 2 * n + 1 ≠ 0), mul_zero, zero_div]
  rw [h0]
  exact hasSum_zero.summable

private theorem summable_chap9T_zero : Summable (fun n : ℕ => chap9T 0 n) := by
  have h0 : (fun n : ℕ => chap9T 0 n) = fun _ => (0 : ℝ) := by
    funext n
    unfold chap9T
    rw [zero_pow (by omega : 2 * n + 1 ≠ 0), mul_zero, zero_div]
  rw [h0]
  exact hasSum_zero.summable

private theorem hasDerivAt_chap9A_tsum_on_Ioo {ρ y : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hy : y ∈ Set.Ioo (-ρ) ρ) :
    HasDerivAt (fun u => ∑' k : ℕ, chap9A u k) (∑' k : ℕ, chap9B y k) y := by
  have hu := summable_rho_sq (le_of_lt hρ0) hρ1
  have ht : IsOpen (Set.Ioo (-ρ) ρ) := isOpen_Ioo
  have hpc : IsPreconnected (Set.Ioo (-ρ) ρ) :=
    (convex_Ioo (-ρ) ρ).isPreconnected
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected hu ht hpc
    (fun n y _ => hasDerivAt_chap9A_term n y)
    (fun n y hy => norm_chap9B_le (le_of_lt hρ0) hy n)
    hy0 summable_chap9A_zero hy

private theorem hasDerivAt_chap9S_tsum_on_Ioo {ρ y : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hy : y ∈ Set.Ioo (-ρ) ρ) :
    HasDerivAt (fun u => ∑' k : ℕ, chap9S u k) (∑' k : ℕ, chap9Sderiv y k) y := by
  have hu := summable_rho_sq (le_of_lt hρ0) hρ1
  have ht : IsOpen (Set.Ioo (-ρ) ρ) := isOpen_Ioo
  have hpc : IsPreconnected (Set.Ioo (-ρ) ρ) :=
    (convex_Ioo (-ρ) ρ).isPreconnected
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected hu ht hpc
    (fun n y _ => hasDerivAt_chap9S_term n y)
    (fun n y hy => norm_chap9Sderiv_le (le_of_lt hρ0) hy n)
    hy0 summable_chap9S_zero hy

private theorem hasDerivAt_chap9T_tsum_on_Ioo {ρ y : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ < 1) (hy : y ∈ Set.Ioo (-ρ) ρ) :
    HasDerivAt (fun v => ∑' k : ℕ, chap9T v k) (∑' k : ℕ, chap9Tderiv y k) y := by
  have hu := summable_rho_sq (le_of_lt hρ0) hρ1
  have ht : IsOpen (Set.Ioo (-ρ) ρ) := isOpen_Ioo
  have hpc : IsPreconnected (Set.Ioo (-ρ) ρ) :=
    (convex_Ioo (-ρ) ρ).isPreconnected
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, by linarith⟩
  exact hasDerivAt_tsum_of_isPreconnected hu ht hpc
    (fun n y _ => hasDerivAt_chap9T_term n y)
    (fun n y hy => norm_chap9Tderiv_le (le_of_lt hρ0) hy n)
    hy0 summable_chap9T_zero hy

private theorem exists_rho_between {u : ℝ} (hu : |u| < 1) :
    ∃ ρ : ℝ, |u| < ρ ∧ ρ < 1 ∧ 0 < ρ ∧ u ∈ Set.Ioo (-ρ) ρ := by
  obtain ⟨ρ, h1, h2⟩ := exists_between hu
  have hρ0 : 0 < ρ := lt_of_le_of_lt (abs_nonneg u) h1
  have hmem : u ∈ Set.Ioo (-ρ) ρ := Set.mem_Ioo.mpr (abs_lt.mp h1)
  exact ⟨ρ, h1, h2, hρ0, hmem⟩

private theorem hasDerivAt_chap9A {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (fun w => ∑' k : ℕ, chap9A w k) (∑' k : ℕ, chap9B u k) u := by
  obtain ⟨ρ, _, hρ1, hρ0, hmem⟩ := exists_rho_between hu
  exact hasDerivAt_chap9A_tsum_on_Ioo hρ0 hρ1 hmem

private theorem hasDerivAt_chap9S {u : ℝ} (hu : |u| < 1) :
    HasDerivAt (fun w => ∑' k : ℕ, chap9S w k) (∑' k : ℕ, chap9Sderiv u k) u := by
  obtain ⟨ρ, _, hρ1, hρ0, hmem⟩ := exists_rho_between hu
  exact hasDerivAt_chap9S_tsum_on_Ioo hρ0 hρ1 hmem

private theorem hasDerivAt_chap9T {v : ℝ} (hv : |v| < 1) :
    HasDerivAt (fun w => ∑' k : ℕ, chap9T w k) (∑' k : ℕ, chap9Tderiv v k) v := by
  obtain ⟨ρ, _, hρ1, hρ0, hmem⟩ := exists_rho_between hv
  exact hasDerivAt_chap9T_tsum_on_Ioo hρ0 hρ1 hmem

private theorem chap9A_zero_tsum : (∑' k : ℕ, chap9A 0 k) = 0 := by
  have h : (fun k : ℕ => chap9A 0 k) = fun _ => (0 : ℝ) := by
    funext k
    unfold chap9A
    rw [zero_pow (by omega : 2 * k + 1 ≠ 0), mul_zero, zero_div]
  rw [h]
  exact tsum_zero

private theorem chap9A_eq_arcsin {u : ℝ} (hu : |u| < 1) :
    (∑' k : ℕ, chap9A u k) = Real.arcsin u := by
  have huIoo : u ∈ Set.Ioo (-1 : ℝ) 1 := Set.mem_Ioo.mpr (abs_lt.mp hu)
  have h0Ioo : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by norm_num
  have h1ne : ∀ v : ℝ, v ∈ Set.Ioo (-1 : ℝ) 1 → v ≠ -1 ∧ v ≠ 1 := by
    intro v hv
    have h := Set.mem_Ioo.mp hv
    constructor <;> linarith
  have hderiv : ∀ v ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun w => (∑' k : ℕ, chap9A w k) - Real.arcsin w) 0 v := by
    intro v hv
    have habs : |v| < 1 := abs_lt.mpr (Set.mem_Ioo.mp hv)
    have hA := hasDerivAt_chap9A habs
    rw [chap9B_tsum habs] at hA
    have hne := h1ne v hv
    have hArc := Real.hasDerivAt_arcsin hne.1 hne.2
    have hsub := hA.sub hArc
    rwa [sub_self] at hsub
  have hdiff : DifferentiableOn ℝ
      (fun w => (∑' k : ℕ, chap9A w k) - Real.arcsin w) (Set.Ioo (-1) 1) := by
    intro x hx
    exact (hderiv x hx).differentiableAt.differentiableWithinAt
  have hEq : Set.EqOn (deriv (fun w => (∑' k : ℕ, chap9A w k) - Real.arcsin w))
      0 (Set.Ioo (-1 : ℝ) 1) := by
    intro x hx
    simp only [Pi.zero_apply]
    exact (hderiv x hx).deriv
  have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo hdiff hEq
    huIoo h0Ioo
  have hf0 : (∑' k : ℕ, chap9A (0 : ℝ) k) - Real.arcsin 0 = 0 := by
    rw [chap9A_zero_tsum, Real.arcsin_zero, sub_self]
  have hfu : (∑' k : ℕ, chap9A u k) - Real.arcsin u
      = (∑' k : ℕ, chap9A (0 : ℝ) k) - Real.arcsin 0 := hconst
  linarith [hf0, hfu]

private theorem summable_chap9Sderiv {u : ℝ} (hu : |u| < 1) :
    Summable (chap9Sderiv u) := by
  obtain ⟨ρ, h1, h2, hρ0, hmem⟩ := exists_rho_between hu
  exact Summable.of_norm_bounded (summable_rho_sq (le_of_lt hρ0) h2)
    (fun n => norm_chap9Sderiv_le (le_of_lt hρ0) hmem n)

private theorem summable_chap9Tderiv {v : ℝ} (hv : |v| < 1) :
    Summable (chap9Tderiv v) := by
  obtain ⟨ρ, h1, h2, hρ0, hmem⟩ := exists_rho_between hv
  exact Summable.of_norm_bounded (summable_rho_sq (le_of_lt hρ0) h2)
    (fun n => norm_chap9Tderiv_le (le_of_lt hρ0) hmem n)

private theorem mul_Sderiv_eq_A (u : ℝ) (k : ℕ) :
    u * chap9Sderiv u k = chap9A u k := by
  unfold chap9Sderiv chap9A
  have hpow : u ^ (2 * k + 1) = u ^ (2 * k) * u := by
    rw [pow_succ]
  rw [hpow]
  ring

private theorem mul_Tderiv_eq_arctan_term (v : ℝ) (k : ℕ) :
    v * chap9Tderiv v k = (-1 : ℝ) ^ k * v ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ)) := by
  unfold chap9Tderiv
  have hpow : v ^ (2 * k + 1) = v ^ (2 * k) * v := by
    rw [pow_succ]
  rw [hpow]
  ring

private theorem mul_tsum_Sderiv_eq_arcsin {u : ℝ} (hu : |u| < 1) :
    u * (∑' k : ℕ, chap9Sderiv u k) = Real.arcsin u := by
  have hsumm := summable_chap9Sderiv hu
  have hmul := hsumm.tsum_mul_left u
  have hEq : (fun k : ℕ => u * chap9Sderiv u k) = chap9A u := by
    funext k
    exact mul_Sderiv_eq_A u k
  have hA := chap9A_eq_arcsin hu
  calc u * (∑' k : ℕ, chap9Sderiv u k)
      = ∑' k : ℕ, u * chap9Sderiv u k := hmul.symm
    _ = ∑' k : ℕ, chap9A u k := by rw [hEq]
    _ = Real.arcsin u := hA

private theorem mul_tsum_Tderiv_eq_arctan {v : ℝ} (hv : |v| < 1) :
    v * (∑' k : ℕ, chap9Tderiv v k) = Real.arctan v := by
  have hsumm := summable_chap9Tderiv hv
  have hmul := hsumm.tsum_mul_left v
  have hArc := Real.hasSum_arctan (x := v) (by rwa [Real.norm_eq_abs])
  have hEq : (fun k : ℕ => v * chap9Tderiv v k)
      = (fun n : ℕ => (-1 : ℝ) ^ n * v ^ (2 * n + 1) / (↑(2 * n + 1))) := by
    funext k
    exact mul_Tderiv_eq_arctan_term v k
  calc v * (∑' k : ℕ, chap9Tderiv v k)
      = ∑' k : ℕ, v * chap9Tderiv v k := hmul.symm
    _ = ∑' n : ℕ, (-1 : ℝ) ^ n * v ^ (2 * n + 1) / (↑(2 * n + 1)) := by rw [hEq]
    _ = Real.arctan v := hArc.tsum_eq

private theorem cos_mem_Ioo_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.cos x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_pos : 0 < Real.cos x := cos_pos_aux (le_of_lt hx0) (le_of_lt hx)
  have hcos_lt : Real.cos x < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl (0 : ℝ))
      (le_of_lt (by linarith : x < Real.pi)) hx0
    rwa [Real.cos_zero] at h
  exact ⟨hcos_pos, hcos_lt⟩

private theorem sin_mem_Ioo_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.sin x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsin_pos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx0 (by linarith)
  have hsin_lt : Real.sin x < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith : -(Real.pi / 2) ≤ x)
      (le_refl (Real.pi / 2)) (by linarith : x < Real.pi / 2)
    rwa [Real.sin_pi_div_two] at h
  exact ⟨hsin_pos, hsin_lt⟩

private theorem tan_mem_Ioo_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.tan x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_pos := (cos_mem_Ioo_of_mem hx0 hx).1
  have hsin_pos := (sin_mem_Ioo_of_mem hx0 hx).1
  have htan_pos : 0 < Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin_pos hcos_pos
  have hx_mem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hpi4_mem : Real.pi / 4 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hlt : Real.tan x < Real.tan (Real.pi / 4) :=
    Real.strictMonoOn_tan hx_mem hpi4_mem hx
  rw [Real.tan_pi_div_four] at hlt
  exact ⟨htan_pos, hlt⟩

private theorem abs_cos_lt_one_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    |Real.cos x| < 1 := by
  have h := cos_mem_Ioo_of_mem hx0 hx
  rw [abs_of_pos h.1]
  exact h.2

private theorem abs_sin_lt_one_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    |Real.sin x| < 1 := by
  have h := sin_mem_Ioo_of_mem hx0 hx
  rw [abs_of_pos h.1]
  exact h.2

private theorem abs_tan_lt_one_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    |Real.tan x| < 1 := by
  have h := tan_mem_Ioo_of_mem hx0 hx
  rw [abs_of_pos h.1]
  exact h.2

/-- Difference `D(x) = S(cos x)+S(sin x) - ((π/2)log(2cos x)+T(tan x))`. -/
private def chap9D (x : ℝ) : ℝ :=
  ((∑' k : ℕ, chap9S (Real.cos x) k) + (∑' k : ℕ, chap9S (Real.sin x) k))
    - (Real.pi / 2 * Real.log (2 * Real.cos x) + (∑' k : ℕ, chap9T (Real.tan x) k))

private theorem tanTerm_eq_chap9T (x : ℝ) (k : ℕ) :
    chapter9Entry19TanTerm x k = chap9T (Real.tan x) k := by
  rfl

private theorem tsum_tan_eq_chap9T (x : ℝ) :
    (∑' k : ℕ, chapter9Entry19TanTerm x k) = ∑' k : ℕ, chap9T (Real.tan x) k :=
  rfl

private theorem chap9D_eq_central {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    chap9D x = (∑' k : ℕ, chapter9Entry19CentralTerm x k)
      - (Real.pi / 2 * Real.log (2 * Real.cos x)
        + (∑' k : ℕ, chapter9Entry19TanTerm x k)) := by
  unfold chap9D
  rw [tsum_central_split_aux hx0 hx, tsum_tan_eq_chap9T]

private theorem cos_mem_Icc_neg_one_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.cos x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hcos_pos := le_of_lt (cos_pos_aux hx0 hx)
  have hcos_le := Real.cos_le_one x
  constructor <;> linarith

private theorem sin_mem_Icc_neg_one_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.sin x ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsin_nn := sin_nonneg_aux hx0 hx
  have hsin_le := Real.sin_le_one x
  constructor <;> linarith

private theorem tan_mem_Icc_neg_one_one {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    Real.tan x ∈ Set.Icc (-1 : ℝ) 1 := by
  have htan_nn := tan_nonneg_aux hx0 hx
  have htan_le := tan_le_one_aux hx0 hx
  constructor <;> linarith

private theorem continuousOn_S_cos :
    ContinuousOn (fun x : ℝ => ∑' k : ℕ, chap9S (Real.cos x) k)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hcomp := continuousOn_chap9S_tsum_aux.comp Real.continuous_cos.continuousOn
    (fun x hx => cos_mem_Icc_neg_one_one (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  have hEq : (fun u : ℝ => ∑' k : ℕ, chap9S u k) ∘ Real.cos
      = (fun x : ℝ => ∑' k : ℕ, chap9S (Real.cos x) k) := rfl
  rwa [hEq] at hcomp

private theorem continuousOn_S_sin :
    ContinuousOn (fun x : ℝ => ∑' k : ℕ, chap9S (Real.sin x) k)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hcomp := continuousOn_chap9S_tsum_aux.comp Real.continuous_sin.continuousOn
    (fun x hx => sin_mem_Icc_neg_one_one (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  have hEq : (fun u : ℝ => ∑' k : ℕ, chap9S u k) ∘ Real.sin
      = (fun x : ℝ => ∑' k : ℕ, chap9S (Real.sin x) k) := rfl
  rwa [hEq] at hcomp

private theorem continuousOn_T_tan :
    ContinuousOn (fun x : ℝ => ∑' k : ℕ, chap9T (Real.tan x) k)
      (Set.Icc 0 (Real.pi / 4)) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 4) ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro x hx
    have h := Set.mem_Icc.mp hx
    constructor <;> linarith
  have htan_cont : ContinuousOn Real.tan (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuousOn_tan_Ioo.mono hsub
  have hcomp := continuousOn_chap9T_tsum_aux.comp htan_cont
    (fun x hx => tan_mem_Icc_neg_one_one (Set.mem_Icc.mp hx).1 (Set.mem_Icc.mp hx).2)
  have hEq : (fun v : ℝ => ∑' k : ℕ, chap9T v k) ∘ Real.tan
      = (fun x : ℝ => ∑' k : ℕ, chap9T (Real.tan x) k) := rfl
  rwa [hEq] at hcomp

private theorem continuousOn_log_two_cos :
    ContinuousOn (fun x : ℝ => Real.log (2 * Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) := by
  have hcos_cont : ContinuousOn (fun x : ℝ => 2 * Real.cos x)
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_const.mul Real.continuous_cos.continuousOn
  have hcomp := Real.continuousOn_log.comp hcos_cont (fun x hx => by
    have h := Set.mem_Icc.mp hx
    have hcos := cos_pos_aux h.1 h.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith)
  have hEq : Real.log ∘ (fun x : ℝ => 2 * Real.cos x)
      = (fun x : ℝ => Real.log (2 * Real.cos x)) := rfl
  rwa [hEq] at hcomp

private theorem continuousOn_chap9D :
    ContinuousOn chap9D (Set.Icc 0 (Real.pi / 4)) := by
  unfold chap9D
  exact ((continuousOn_S_cos.add continuousOn_S_sin).sub
    ((continuousOn_const.mul continuousOn_log_two_cos).add continuousOn_T_tan))

private theorem arcsin_sin_eq_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.arcsin (Real.sin x) = x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  exact Real.arcsin_sin (by linarith) (by linarith)

private theorem arcsin_cos_eq_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.arcsin (Real.cos x) = Real.pi / 2 - x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have harccos : Real.arccos (Real.cos x) = x :=
    Real.arccos_cos (le_of_lt hx0) (by linarith)
  have h := Real.arcsin_eq_pi_div_two_sub_arccos (Real.cos x)
  rw [harccos] at h
  exact h

private theorem arctan_tan_eq_of_mem {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    Real.arctan (Real.tan x) = x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  exact Real.arctan_tan (by linarith) (by linarith)

private theorem hasDerivAt_chap9D {x : ℝ} (hx0 : 0 < x) (hx : x < Real.pi / 4) :
    HasDerivAt chap9D 0 x := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcos_mem := cos_mem_Ioo_of_mem hx0 hx
  have hsin_mem := sin_mem_Ioo_of_mem hx0 hx
  have htan_mem := tan_mem_Ioo_of_mem hx0 hx
  have hcos_pos : 0 < Real.cos x := hcos_mem.1
  have hsin_pos : 0 < Real.sin x := hsin_mem.1
  have htan_pos : 0 < Real.tan x := htan_mem.1
  have hcos_ne : Real.cos x ≠ 0 := ne_of_gt hcos_pos
  have hsin_ne : Real.sin x ≠ 0 := ne_of_gt hsin_pos
  have htan_ne : Real.tan x ≠ 0 := ne_of_gt htan_pos
  have hcos_abs := abs_cos_lt_one_of_mem hx0 hx
  have hsin_abs := abs_sin_lt_one_of_mem hx0 hx
  have htan_abs := abs_tan_lt_one_of_mem hx0 hx
  have h_arcsin_sin := arcsin_sin_eq_of_mem hx0 hx
  have h_arcsin_cos := arcsin_cos_eq_of_mem hx0 hx
  have h_arctan_tan := arctan_tan_eq_of_mem hx0 hx
  have hS1 : Real.cos x * (∑' k : ℕ, chap9Sderiv (Real.cos x) k)
      = Real.pi / 2 - x := by
    have h := mul_tsum_Sderiv_eq_arcsin hcos_abs
    rwa [h_arcsin_cos] at h
  have hS2 : Real.sin x * (∑' k : ℕ, chap9Sderiv (Real.sin x) k) = x := by
    have h := mul_tsum_Sderiv_eq_arcsin hsin_abs
    rwa [h_arcsin_sin] at h
  have hT : Real.tan x * (∑' k : ℕ, chap9Tderiv (Real.tan x) k) = x := by
    have h := mul_tsum_Tderiv_eq_arctan htan_abs
    rwa [h_arctan_tan] at h
  have hS_cos_has : HasDerivAt (fun u : ℝ => ∑' k : ℕ, chap9S u k)
      (∑' k : ℕ, chap9Sderiv (Real.cos x) k) (Real.cos x) :=
    hasDerivAt_chap9S hcos_abs
  have hS_sin_has : HasDerivAt (fun u : ℝ => ∑' k : ℕ, chap9S u k)
      (∑' k : ℕ, chap9Sderiv (Real.sin x) k) (Real.sin x) :=
    hasDerivAt_chap9S hsin_abs
  have hT_has : HasDerivAt (fun v : ℝ => ∑' k : ℕ, chap9T v k)
      (∑' k : ℕ, chap9Tderiv (Real.tan x) k) (Real.tan x) :=
    hasDerivAt_chap9T htan_abs
  have hcos_deriv := Real.hasDerivAt_cos x
  have hsin_deriv := Real.hasDerivAt_sin x
  have htan_deriv := Real.hasDerivAt_tan hcos_ne
  have hS_cos_comp : HasDerivAt (fun x : ℝ => ∑' k : ℕ, chap9S (Real.cos x) k)
      ((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x)) x :=
    hS_cos_has.comp x hcos_deriv
  have hS_sin_comp : HasDerivAt (fun x : ℝ => ∑' k : ℕ, chap9S (Real.sin x) k)
      ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x)) x :=
    hS_sin_has.comp x hsin_deriv
  have hT_comp : HasDerivAt (fun x : ℝ => ∑' k : ℕ, chap9T (Real.tan x) k)
      ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2)) x :=
    hT_has.comp x htan_deriv
  have h2cos_deriv : HasDerivAt (fun x : ℝ => 2 * Real.cos x) (2 * (-Real.sin x)) x :=
    hcos_deriv.const_mul 2
  have h2cos_ne : (2 : ℝ) * Real.cos x ≠ 0 := by
    positivity
  have hlog_deriv : HasDerivAt (fun x : ℝ => Real.log (2 * Real.cos x))
      ((2 * (-Real.sin x)) / (2 * Real.cos x)) x :=
    h2cos_deriv.log h2cos_ne
  have hlog_const : HasDerivAt (fun x : ℝ => Real.pi / 2 * Real.log (2 * Real.cos x))
      ((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x))) x :=
    hlog_deriv.const_mul (Real.pi / 2)
  have hLHS : HasDerivAt
      (fun x : ℝ => (∑' k : ℕ, chap9S (Real.cos x) k)
        + (∑' k : ℕ, chap9S (Real.sin x) k))
      (((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x))
        + ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x))) x :=
    hS_cos_comp.add hS_sin_comp
  have hRHS : HasDerivAt
      (fun x : ℝ => (Real.pi / 2 * Real.log (2 * Real.cos x))
        + (∑' k : ℕ, chap9T (Real.tan x) k))
      (((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x)))
        + ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2))) x :=
    hlog_const.add hT_comp
  have hDfun : HasDerivAt
      (fun x : ℝ => ((∑' k : ℕ, chap9S (Real.cos x) k)
        + (∑' k : ℕ, chap9S (Real.sin x) k))
        - (Real.pi / 2 * Real.log (2 * Real.cos x)
          + (∑' k : ℕ, chap9T (Real.tan x) k)))
      ((((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x))
        + ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x)))
        - (((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x)))
          + ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2)))) x :=
    hLHS.sub hRHS
  have hDeriv_zero : ((((∑' k : ℕ, chap9Sderiv (Real.cos x) k) * (-Real.sin x))
      + ((∑' k : ℕ, chap9Sderiv (Real.sin x) k) * (Real.cos x)))
      - (((Real.pi / 2) * ((2 * (-Real.sin x)) / (2 * Real.cos x)))
        + ((∑' k : ℕ, chap9Tderiv (Real.tan x) k) * (1 / Real.cos x ^ 2)))) = 0 := by
    have hS1' : (∑' k : ℕ, chap9Sderiv (Real.cos x) k)
        = (Real.pi / 2 - x) / Real.cos x := by
      rw [eq_div_iff hcos_ne]
      linarith [hS1]
    have hS2' : (∑' k : ℕ, chap9Sderiv (Real.sin x) k) = x / Real.sin x := by
      rw [eq_div_iff hsin_ne]
      linarith [hS2]
    have hT' : (∑' k : ℕ, chap9Tderiv (Real.tan x) k) = x / Real.tan x := by
      rw [eq_div_iff htan_ne]
      linarith [hT]
    have htan_eq : Real.tan x = Real.sin x / Real.cos x :=
      Real.tan_eq_sin_div_cos x
    have hsq : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq x
    have hsc_ne : Real.sin x / Real.cos x ≠ 0 :=
      div_ne_zero hsin_ne hcos_ne
    have h2c_ne : (2 : ℝ) * Real.cos x ≠ 0 :=
      mul_ne_zero (by norm_num) hcos_ne
    rw [hS1', hS2', hT', htan_eq]
    field_simp
    have h2 : x * (Real.sin x ^ 2 + Real.cos x ^ 2) = x := by
      rw [hsq, mul_one]
    nlinarith [h2, hsq]
  rw [hDeriv_zero] at hDfun
  exact hDfun

/-- The continuous extension of `Real.arcsin t / t` to `t = 0`. -/
private def chap9G (t : ℝ) : ℝ :=
  if t = 0 then 1 else Real.arcsin t / t

private theorem chap9G_zero : chap9G 0 = 1 := by
  simp [chap9G]

private theorem chap9G_of_ne {t : ℝ} (ht : t ≠ 0) : chap9G t = Real.arcsin t / t := by
  simp [chap9G, ht]

private theorem tendsto_arcsin_div_self_nhdsNE :
    Filter.Tendsto (fun t : ℝ => Real.arcsin t / t) (𝓝[≠] 0) (𝓝 1) := by
  have hderiv : HasDerivAt Real.arcsin 1 (0 : ℝ) := by
    have h := Real.hasDerivAt_arcsin (x := (0 : ℝ)) (by norm_num) (by norm_num)
    have h1 : (1 : ℝ) / Real.sqrt (1 - (0 : ℝ) ^ 2) = 1 := by
      rw [show (1 : ℝ) - (0 : ℝ) ^ 2 = 1 by norm_num, Real.sqrt_one, div_one]
    rwa [h1] at h
  have hslope := hderiv.tendsto_slope
  have hEq : (fun t : ℝ => Real.arcsin t / t) =ᶠ[𝓝[≠] (0 : ℝ)] slope Real.arcsin 0 :=
    Filter.Eventually.of_forall
      (fun t => by simp only [slope_def_field, Real.arcsin_zero, sub_zero])
  exact Filter.Tendsto.congr' hEq.symm hslope

private theorem continuousAt_chap9G_zero : ContinuousAt chap9G 0 := by
  have hpunc : Filter.Tendsto chap9G (𝓝[≠] (0 : ℝ)) (𝓝 1) := by
    have hEq : chap9G =ᶠ[𝓝[≠] (0 : ℝ)] (fun t : ℝ => Real.arcsin t / t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht
      exact chap9G_of_ne ht
    exact Filter.Tendsto.congr' hEq.symm tendsto_arcsin_div_self_nhdsNE
  rw [Metric.continuousAt_iff]
  intro ε hε
  rw [Metric.tendsto_nhdsWithin_nhds] at hpunc
  obtain ⟨δ, hδ, hball⟩ := hpunc ε hε
  refine ⟨δ, hδ, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · rw [hx0, chap9G_zero, dist_self]
    exact hε
  · have hxmem : x ∈ ({0} : Set ℝ)ᶜ := by simpa using hx0
    rw [chap9G_zero]
    exact hball hxmem hx

private theorem continuous_chap9G : Continuous chap9G := by
  rw [continuous_iff_continuousAt]
  intro t
  by_cases ht : t = 0
  · rw [ht]
    exact continuousAt_chap9G_zero
  · have hdiv : ContinuousAt (fun t : ℝ => Real.arcsin t / t) t :=
      Real.continuous_arcsin.continuousAt.div continuousAt_id ht
    have hEq : chap9G =ᶠ[𝓝 t] (fun t : ℝ => Real.arcsin t / t) := by
      filter_upwards [eventually_ne_nhds ht] with s hs
      exact chap9G_of_ne hs
    exact ContinuousAt.congr_of_eventuallyEq hdiv hEq

private theorem chap9S_eq_integral_chap9G {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    (∑' k : ℕ, chap9S u k) = ∫ t in (0 : ℝ)..u, chap9G t := by
  have hcont : ContinuousOn (fun w : ℝ => ∑' k : ℕ, chap9S w k) (Set.Icc 0 u) := by
    apply continuousOn_chap9S_tsum_aux.mono
    intro t ht
    rw [Set.mem_Icc] at ht ⊢
    constructor <;> linarith [ht.1, ht.2, hu1]
  have hderiv : ∀ t ∈ Set.Ioo 0 u,
      HasDerivAt (fun w : ℝ => ∑' k : ℕ, chap9S w k) (chap9G t) t := by
    intro t ht
    rw [Set.mem_Ioo] at ht
    have habs : |t| < 1 := by
      rw [abs_of_pos ht.1]
      linarith [ht.2, hu1]
    have hS := hasDerivAt_chap9S habs
    have hmul := mul_tsum_Sderiv_eq_arcsin habs
    have htne : t ≠ 0 := ne_of_gt ht.1
    have hval : (∑' k : ℕ, chap9Sderiv t k) = chap9G t := by
      rw [chap9G_of_ne htne, eq_div_iff htne]
      linarith [hmul]
    rwa [hval] at hS
  have hint : IntervalIntegrable chap9G MeasureTheory.volume 0 u :=
    continuous_chap9G.intervalIntegrable 0 u
  have hFTC : (∫ t in (0 : ℝ)..u, chap9G t)
      = (∑' k : ℕ, chap9S u k) - (∑' k : ℕ, chap9S 0 k) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hu0 hcont hderiv hint
  rw [chap9S_zero_aux, sub_zero] at hFTC
  exact hFTC.symm

private theorem chap9S_one_eq_integral :
    (∑' k : ℕ, chap9S 1 k) = ∫ t in (0 : ℝ)..1, chap9G t :=
  chap9S_eq_integral_chap9G zero_le_one le_rfl

private theorem integral_chap9G_eq_integral_h :
    (∫ t in (0 : ℝ)..1, chap9G t)
      = ∫ s in (0 : ℝ)..(Real.pi / 2), chap9G (Real.sin s) * Real.cos s := by
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) (Real.pi / 2),
      HasDerivAt Real.sin (Real.cos x) x := fun x _ => Real.hasDerivAt_sin x
  have hcont : ContinuousOn Real.cos (Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_cos.continuousOn
  have hg : ContinuousOn chap9G (Real.sin '' Set.uIcc (0 : ℝ) (Real.pi / 2)) :=
    continuous_chap9G.continuousOn
  have hsub : (∫ x in (0 : ℝ)..(Real.pi / 2), (chap9G ∘ Real.sin) x * Real.cos x)
      = ∫ x in Real.sin 0..Real.sin (Real.pi / 2), chap9G x :=
    intervalIntegral.integral_comp_mul_deriv' hderiv hcont hg
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  simp only [Function.comp_apply]

private theorem sin_mem_Ioo_pi_half {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    Real.sin θ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpos : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith)
  have hlt : Real.sin θ < 1 := by
    have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith : -(Real.pi / 2) ≤ θ)
      (le_refl (Real.pi / 2)) h1
    rwa [Real.sin_pi_div_two] at h
  exact ⟨hpos, hlt⟩

private theorem abs_sin_lt_one_pi_half {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    |Real.sin θ| < 1 := by
  have h := sin_mem_Ioo_pi_half h0 h1
  rw [abs_of_pos h.1]
  exact h.2

private theorem arcsin_sin_eq_pi_half {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    Real.arcsin (Real.sin θ) = θ := by
  have hpi : 0 < Real.pi := Real.pi_pos
  exact Real.arcsin_sin (by linarith) (by linarith)

/-- `E(θ) = S(sin θ)` on `[0, π/2]`. -/
private def chap9E (θ : ℝ) : ℝ :=
  ∑' k : ℕ, chap9S (Real.sin θ) k

private theorem hasDerivAt_chap9E {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt chap9E (θ * Real.cos θ / Real.sin θ) θ := by
  have habs := abs_sin_lt_one_pi_half h0 h1
  have hsin_pos : 0 < Real.sin θ := (sin_mem_Ioo_pi_half h0 h1).1
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt hsin_pos
  have hS := hasDerivAt_chap9S habs
  have hcomp : HasDerivAt (fun θ : ℝ => ∑' k : ℕ, chap9S (Real.sin θ) k)
      ((∑' k : ℕ, chap9Sderiv (Real.sin θ) k) * Real.cos θ) θ :=
    hS.comp θ (Real.hasDerivAt_sin θ)
  have hmul := mul_tsum_Sderiv_eq_arcsin habs
  rw [arcsin_sin_eq_pi_half h0 h1] at hmul
  have hSderiv : (∑' k : ℕ, chap9Sderiv (Real.sin θ) k)
      = θ / Real.sin θ := by
    rw [eq_div_iff hsin_ne]
    linarith [hmul]
  rw [hSderiv] at hcomp
  have hval : θ / Real.sin θ * Real.cos θ = θ * Real.cos θ / Real.sin θ := by
    ring
  rw [hval] at hcomp
  exact hcomp

/-- `f(θ) = E(θ) - θ * log (sin θ)`. -/
private def chap9f (θ : ℝ) : ℝ :=
  chap9E θ - θ * Real.log (Real.sin θ)

private theorem hasDerivAt_chap9f {θ : ℝ} (h0 : 0 < θ) (h1 : θ < Real.pi / 2) :
    HasDerivAt chap9f (-Real.log (Real.sin θ)) θ := by
  have hsin_ne : Real.sin θ ≠ 0 := ne_of_gt (sin_mem_Ioo_pi_half h0 h1).1
  have hE := hasDerivAt_chap9E h0 h1
  have hlog : HasDerivAt (fun θ : ℝ => Real.log (Real.sin θ))
      (Real.cos θ / Real.sin θ) θ :=
    (Real.hasDerivAt_sin θ).log hsin_ne
  have hid : HasDerivAt (fun θ : ℝ => θ) 1 θ := hasDerivAt_id' θ
  have hmul : HasDerivAt (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (1 * Real.log (Real.sin θ) + θ * (Real.cos θ / Real.sin θ)) θ :=
    hid.mul hlog
  have hsub := hE.sub hmul
  have hval : θ * Real.cos θ / Real.sin θ
      - (1 * Real.log (Real.sin θ) + θ * (Real.cos θ / Real.sin θ))
      = -Real.log (Real.sin θ) := by
    ring
  rw [hval] at hsub
  exact hsub

private theorem sin_mem_Icc_pi_half {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    Real.sin θ ∈ Set.Icc (-1 : ℝ) 1 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hnn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
  have hle : Real.sin θ ≤ 1 := Real.sin_le_one θ
  constructor <;> linarith

private theorem continuousOn_chap9E :
    ContinuousOn chap9E (Set.Icc 0 (Real.pi / 2)) := by
  have hcomp := continuousOn_chap9S_tsum_aux.comp Real.continuous_sin.continuousOn
    (fun θ hθ => sin_mem_Icc_pi_half (Set.mem_Icc.mp hθ).1 (Set.mem_Icc.mp hθ).2)
  have hEq : (fun u : ℝ => ∑' k : ℕ, chap9S u k) ∘ Real.sin = chap9E := rfl
  rwa [hEq] at hcomp

private theorem tendsto_lower_zero :
    Tendsto (fun θ : ℝ => -(θ * Real.log (2 / Real.pi * θ)))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hphi : Tendsto (fun θ : ℝ => 2 / Real.pi * θ)
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
    have hcont : Continuous (fun θ : ℝ => 2 / Real.pi * θ) :=
      continuous_const.mul continuous_id
    have h := hcont.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hbase : Tendsto (fun x : ℝ => x * Real.log x)
      (nhds 0) (nhds 0) := by
    simpa using Real.continuous_mul_log.tendsto 0
  have hcomp : Tendsto (fun θ : ℝ => (2 / Real.pi * θ) * Real.log (2 / Real.pi * θ))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) :=
    hbase.comp hphi
  have hEq : (fun θ : ℝ => -(θ * Real.log (2 / Real.pi * θ)))
      = (fun θ : ℝ => (-(Real.pi / 2)) * ((2 / Real.pi * θ) * Real.log (2 / Real.pi * θ))) := by
    funext θ
    field_simp
  rw [hEq]
  have hmul := hcomp.const_mul (-(Real.pi / 2))
  simpa using hmul

private theorem tendsto_neg_mul_log_sin_zero :
    Tendsto (fun θ : ℝ => -(θ * Real.log (Real.sin θ)))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
  refine squeeze_zero' ?_ ?_ tendsto_lower_zero
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    have h0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
    have h1 : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
    have hpi : 0 < Real.pi := Real.pi_pos
    have hsin_nn : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith)
    have hsin_le : Real.sin θ ≤ 1 := Real.sin_le_one θ
    have hlog : Real.log (Real.sin θ) ≤ 0 := Real.log_nonpos hsin_nn hsin_le
    have hmul : θ * Real.log (Real.sin θ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h0 hlog
    linarith
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    have h0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
    have h1 : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
    have hpi : 0 < Real.pi := Real.pi_pos
    by_cases hθ0 : θ = 0
    · rw [hθ0]
      simp
    · have hpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ0)
      have hlow_pos : 0 < 2 / Real.pi * θ := by positivity
      have hle : 2 / Real.pi * θ ≤ Real.sin θ := Real.mul_le_sin h0 h1
      have hlog_le : Real.log (2 / Real.pi * θ) ≤ Real.log (Real.sin θ) :=
        Real.log_le_log hlow_pos hle
      have hmul_le : θ * Real.log (2 / Real.pi * θ) ≤ θ * Real.log (Real.sin θ) :=
        mul_le_mul_of_nonneg_left hlog_le (le_of_lt hpos)
      linarith

private theorem tendsto_mul_log_sin_zero :
    Tendsto (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (nhdsWithin 0 (Set.Icc 0 (Real.pi / 2))) (nhds 0) := by
  simpa using tendsto_neg_mul_log_sin_zero.neg

private theorem continuousOn_mul_log_sin :
    ContinuousOn (fun θ : ℝ => θ * Real.log (Real.sin θ))
      (Set.Icc 0 (Real.pi / 2)) := by
  intro θ hθ
  by_cases hθ0 : θ = 0
  · rw [hθ0]
    have hval : (0 : ℝ) * Real.log (Real.sin 0) = 0 := by simp
    rw [ContinuousWithinAt, hval]
    exact tendsto_mul_log_sin_zero
  · have h0 : 0 ≤ θ := (Set.mem_Icc.mp hθ).1
    have h1 : θ ≤ Real.pi / 2 := (Set.mem_Icc.mp hθ).2
    have hpi : 0 < Real.pi := Real.pi_pos
    have hpos : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ0)
    have hsin_ne : Real.sin θ ≠ 0 :=
      ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos (by linarith))
    have hlog : ContinuousAt (fun θ : ℝ => Real.log (Real.sin θ)) θ :=
      (Real.continuousAt_log hsin_ne).comp Real.continuous_sin.continuousAt
    have hmul : ContinuousAt (fun θ : ℝ => θ * Real.log (Real.sin θ)) θ :=
      continuous_id.continuousAt.mul hlog
    exact hmul.continuousWithinAt

private theorem continuousOn_chap9f :
    ContinuousOn chap9f (Set.Icc 0 (Real.pi / 2)) :=
  continuousOn_chap9E.sub continuousOn_mul_log_sin

private theorem intervalIntegrable_neg_log_sin :
    IntervalIntegrable (fun θ : ℝ => -Real.log (Real.sin θ))
      MeasureTheory.volume 0 (Real.pi / 2) := by
  have hbase : IntervalIntegrable (Real.log ∘ Real.sin)
      MeasureTheory.volume 0 (Real.pi / 2) :=
    intervalIntegrable_log_sin
  have hEq : (Real.log ∘ Real.sin) = (fun θ : ℝ => Real.log (Real.sin θ)) := rfl
  rw [hEq] at hbase
  have hneg := hbase.neg
  exact hneg

private theorem chap9S_one_eq_pi_half_mul_log_two :
    (∑' k : ℕ, chap9S 1 k) = Real.pi / 2 * Real.log 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hab : (0 : ℝ) ≤ Real.pi / 2 := by linarith
  have hderiv : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivAt chap9f (-Real.log (Real.sin x)) x := by
    intro x hx
    have h0 : 0 < x := (Set.mem_Ioo.mp hx).1
    have h1 : x < Real.pi / 2 := (Set.mem_Ioo.mp hx).2
    exact hasDerivAt_chap9f h0 h1
  have hFTC : (∫ θ in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin θ))
      = chap9f (Real.pi / 2) - chap9f 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab
      continuousOn_chap9f hderiv intervalIntegrable_neg_log_sin
  have hintegral : (∫ θ in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin θ))
      = Real.pi / 2 * Real.log 2 := by
    have hbase := integral_log_sin_zero_pi_div_two
    have hEq : (∫ θ in (0 : ℝ)..(Real.pi / 2), -Real.log (Real.sin θ))
        = -(∫ x in (0 : ℝ)..(Real.pi / 2), Real.log (Real.sin x)) :=
      intervalIntegral.integral_neg
    rw [hEq, hbase]
    ring
  have hf0 : chap9f 0 = 0 := by
    unfold chap9f chap9E
    rw [Real.sin_zero, chap9S_zero_aux]
    simp
  have hfpi : chap9f (Real.pi / 2) = ∑' k : ℕ, chap9S 1 k := by
    unfold chap9f chap9E
    rw [Real.sin_pi_div_two, Real.log_one, mul_zero, sub_zero]
  rw [hintegral, hfpi, hf0, sub_zero] at hFTC
  exact hFTC.symm

private theorem chap9D_zero : chap9D 0 = 0 := by
  have hS1 := chap9S_one_eq_pi_half_mul_log_two
  unfold chap9D
  rw [log_two_cos_zero_aux, Real.cos_zero, Real.sin_zero, Real.tan_zero,
    chap9S_zero_aux, chap9T_zero_aux, hS1]
  ring

private theorem chap9D_eq_zero {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    chap9D x = 0 := by
  by_cases hx0' : x = 0
  · rw [hx0']
    exact chap9D_zero
  · have hpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx0')
    have hpi : 0 < Real.pi := Real.pi_pos
    have hcont : ContinuousOn chap9D (Set.Icc 0 x) :=
      continuousOn_chap9D.mono (Set.Icc_subset_Icc le_rfl hx)
    have hderiv : ∀ c ∈ Set.Ioo 0 x, HasDerivAt chap9D 0 c := by
      intro c hc
      have hc0 : 0 < c := (Set.mem_Ioo.mp hc).1
      have hcx : c < x := (Set.mem_Ioo.mp hc).2
      exact hasDerivAt_chap9D hc0 (lt_of_lt_of_le hcx hx)
    obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope (f := chap9D)
      (f' := fun _ => (0 : ℝ)) hpos hcont hderiv
    have hne : x - 0 ≠ 0 := sub_ne_zero.mpr hx0'
    have hdiv : (chap9D x - chap9D 0) / (x - 0) = 0 := hc.symm
    have hor := (div_eq_zero_iff.mp hdiv)
    cases hor with
    | inl hnum =>
      have h0 := chap9D_zero
      linarith [hnum, h0]
    | inr hden =>
      exact absurd hden hne

/-- **The central binomial series in $\cos x$ plus that in $\sin x$.** Let $x$ be a real number
with $0 \le x \le \pi/4$. Then $2\cos x > 0$, the series
$C(x) = \sum_{k=0}^{\infty} \binom{2k}{k} \frac{\cos^{2k+1} x + \sin^{2k+1} x}
{2^{2k} (2k+1)^2}$ and $T(x) = \sum_{k=0}^{\infty} (-1)^k \frac{\tan^{2k+1} x}{(2k+1)^2}$ are
both summable, and $C(x) = \frac{\pi}{2} \log(2\cos x) + T(x)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry19_catalangf (x : ℝ)
    (hx0 : 0 ≤ x) (hx : x ≤ Real.pi / 4) :
    0 < 2 * Real.cos x ∧
      Summable (chapter9Entry19CentralTerm x) ∧
      Summable (chapter9Entry19TanTerm x) ∧
      (∑' k : ℕ, chapter9Entry19CentralTerm x k) =
        Real.pi / 2 * Real.log (2 * Real.cos x) +
          ∑' k : ℕ, chapter9Entry19TanTerm x k := by
  refine ⟨?_, summable_central_aux hx0 hx, summable_tan_aux hx0 hx, ?_⟩
  · have h := cos_pos_aux hx0 hx
    linarith
  · have hEq := chap9D_eq_central hx0 hx
    have hD := chap9D_eq_zero hx0 hx
    rw [hD] at hEq
    exact sub_eq_zero.mp hEq.symm

end
end Entry19Catalangf
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
