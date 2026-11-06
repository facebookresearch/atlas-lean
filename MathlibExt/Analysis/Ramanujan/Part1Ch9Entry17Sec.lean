/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Basic
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry21Piseries2
public import MathlibExt.Analysis.Ramanujan.Part1Ch9Entry32Lambertdivisor

@[expose] public section

section
/-!
# Ramanujan's Notebooks, Part I, Chapter 9

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch9

namespace Entry17Sec

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter9XLogAbsTan (x : ℝ) : ℝ :=
  if x = 0 then 0 else x * Real.log |Real.tan x|

private lemma entry17_cos_ne_zero (x : ℝ) (hx : |x| ≤ Real.pi / 4) : Real.cos x ≠ 0 := by
  have hxmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have h1 : -(Real.pi / 2) < -(Real.pi / 4) := by linarith [Real.pi_pos]
      have h2 : -(Real.pi / 4) ≤ x := by
        have := neg_le_of_abs_le hx
        linarith
      linarith
    · have h1 : (Real.pi / 4) < (Real.pi / 2) := by linarith [Real.pi_pos]
      have h2 : x ≤ Real.pi / 4 := le_of_abs_le hx
      linarith
  exact ne_of_gt (Real.cos_pos_of_mem_Ioo hxmem)

private lemma entry17_tan_abs_le_one (x : ℝ) (hx : |x| ≤ Real.pi / 4) : |Real.tan x| ≤ 1 := by
  have hmem : ∀ y : ℝ, |y| ≤ Real.pi / 4 → y ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro y hy
    have h1 := neg_le_of_abs_le hy
    have h2 := le_of_abs_le hy
    constructor <;> linarith [Real.pi_pos]
  have hmono := Real.strictMonoOn_tan
  have hxmem := hmem x hx
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have h4mem : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  have hn4mem : (-(Real.pi / 4)) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [Real.pi_pos]
  rcases le_total 0 x with hx0 | hx0
  · have hx4 : x ≤ Real.pi / 4 := le_of_abs_le hx
    have h1 : (0 : ℝ) ≤ Real.tan x := by
      have h := hmono.monotoneOn h0mem hxmem hx0
      rwa [Real.tan_zero] at h
    have h2 : Real.tan x ≤ 1 := by
      have h := hmono.monotoneOn hxmem h4mem hx4
      rwa [Real.tan_pi_div_four] at h
    rw [abs_of_nonneg h1]
    exact h2
  · have hx4 : -(Real.pi / 4) ≤ x := neg_le_of_abs_le hx
    have h1 : (-1 : ℝ) ≤ Real.tan x := by
      have h := hmono.monotoneOn hn4mem hxmem hx4
      have htan4 : Real.tan (-(Real.pi / 4)) = -1 := by
        rw [Real.tan_neg, Real.tan_pi_div_four]
      rwa [htan4] at h
    have h2 : Real.tan x ≤ (0 : ℝ) := by
      have h := hmono.monotoneOn hxmem h0mem hx0
      rwa [Real.tan_zero] at h
    rw [abs_of_nonpos h2]
    linarith

private lemma entry17_base_summable :
    Summable (fun k : ℕ => (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  have h := (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  exact h.comp_injective (by intro a b h2; dsimp only at h2; omega)

private def entry17Ti2 (t : ℝ) : ℝ :=
  ∑' k : ℕ, (-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

private lemma entry17Ti2_norm_le (t : ℝ) (ht : ‖t‖ ≤ 1) (k : ℕ) :
    ‖(-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)‖ ≤
      (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  have hDpos : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hDpos]
  have ht1 : |t| ≤ 1 := by rwa [Real.norm_eq_abs] at ht
  have hpow : |t| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg t) ht1
  have hnum : |(-1 : ℝ) ^ k * t ^ (2 * k + 1)| ≤ 1 := by
    have heq : |(-1 : ℝ) ^ k * t ^ (2 * k + 1)|
        = |(-1 : ℝ)| ^ k * |t| ^ (2 * k + 1) := by
      rw [abs_mul, abs_pow, abs_pow]
    have hneg : |(-1 : ℝ)| ^ k = 1 := by simp
    rw [heq, hneg, one_mul]
    exact hpow
  exact div_le_div_of_nonneg_right hnum (le_of_lt hDpos)

private lemma entry17Ti2_summable (t : ℝ) (ht : ‖t‖ ≤ 1) :
    Summable (fun k : ℕ =>
      (-1 : ℝ) ^ k * t ^ (2 * k + 1) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => entry17Ti2_norm_le t ht k) entry17_base_summable

private lemma entry17Ti2_continuousOn :
    ContinuousOn entry17Ti2 (Set.Icc (-1 : ℝ) 1) := by
  apply continuousOn_tsum (fun n => ?_) entry17_base_summable (fun n x hx => ?_)
  · apply ContinuousOn.div_const
    apply ContinuousOn.mul continuousOn_const
    exact (continuous_pow (2 * n + 1)).continuousOn
  · have ht : ‖x‖ ≤ 1 := by
      rw [Set.mem_Icc] at hx
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hx.1, hx.2]
    exact entry17Ti2_norm_le x ht n

private lemma entry17Ti2_term_hasDerivAt (n : ℕ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ => (-1 : ℝ) ^ n * s ^ (2 * n + 1) / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2))
      ((-1 : ℝ) ^ n * t ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ)) t := by
  have hpow : HasDerivAt (fun s : ℝ => s ^ (2 * n + 1))
      ((((2 * n + 1 : ℕ)) : ℝ) * t ^ (2 * n)) t := by
    have h := hasDerivAt_pow (2 * n + 1) t
    have heq : (2 * n + 1) - 1 = 2 * n := by omega
    rwa [heq] at h
  have hmul := hpow.const_mul ((-1 : ℝ) ^ n)
  have hdiv := hmul.div_const ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
  have hsimp : (-1 : ℝ) ^ n * ((((2 * n + 1 : ℕ)) : ℝ) * t ^ (2 * n)) /
        ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)
      = (-1 : ℝ) ^ n * t ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma entry17Ti2_majorant (r : ℝ) (_hr0 : 0 < r) (_hr1 : r < 1) (n : ℕ)
    (y : ℝ) (hy : y ∈ Set.Ioo (-r) r) :
    ‖(-1 : ℝ) ^ n * y ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ)‖ ≤ (r ^ 2) ^ n := by
  have hyr : ‖y‖ < r := by
    rw [Real.norm_eq_abs, abs_lt]
    rw [Set.mem_Ioo] at hy
    constructor <;> linarith [hy.1, hy.2]
  have hneg : ‖(-1 : ℝ) ^ n‖ = 1 := by simp
  have hDpos : (0 : ℝ) < ((((2 * n + 1 : ℕ)) : ℝ)) := by positivity
  have hD : ‖((((2 * n + 1 : ℕ)) : ℝ))‖ = ((((2 * n + 1 : ℕ)) : ℝ)) :=
    abs_of_nonneg (le_of_lt hDpos)
  rw [norm_div, norm_mul, hneg, norm_pow, hD, one_mul]
  have hpow_le : ‖y‖ ^ (2 * n) ≤ r ^ (2 * n) :=
    pow_le_pow_left₀ (norm_nonneg _) (le_of_lt hyr) _
  have hD1 : (1 : ℝ) ≤ ((((2 * n + 1 : ℕ)) : ℝ)) := by
    have hle : 1 ≤ 2 * n + 1 := by omega
    exact_mod_cast hle
  calc ‖y‖ ^ (2 * n) / ((((2 * n + 1 : ℕ)) : ℝ))
      ≤ r ^ (2 * n) / ((((2 * n + 1 : ℕ)) : ℝ)) :=
        div_le_div_of_nonneg_right hpow_le (le_of_lt hDpos)
    _ ≤ r ^ (2 * n) := div_le_self (by positivity) hD1
    _ = (r ^ 2) ^ n := by rw [pow_mul]

private lemma entry17Ti2_hasDerivAt_of_mem {r y : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hy : y ∈ Set.Ioo (-r) r) :
    HasDerivAt entry17Ti2
      (∑' n : ℕ, (-1 : ℝ) ^ n * y ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ)) y := by
  have hu : Summable (fun n : ℕ => (r ^ 2) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [hr0, hr1]
  have hopen : IsOpen (Set.Ioo (-r : ℝ) r) := isOpen_Ioo
  have hpre : IsPreconnected (Set.Ioo (-r : ℝ) r) := isPreconnected_Ioo
  have hderiv : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      HasDerivAt
        (fun s : ℝ =>
          (-1 : ℝ) ^ n * s ^ (2 * n + 1) / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2))
        ((-1 : ℝ) ^ n * z ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ)) z :=
    fun n z _ => entry17Ti2_term_hasDerivAt n z
  have hbound : ∀ n : ℕ, ∀ z ∈ Set.Ioo (-r : ℝ) r,
      ‖(-1 : ℝ) ^ n * z ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ)‖ ≤ (r ^ 2) ^ n :=
    fun n z hz => entry17Ti2_majorant r hr0 hr1 n z hz
  have hy0 : (0 : ℝ) ∈ Set.Ioo (-r : ℝ) r := by simp [Set.mem_Ioo, hr0]
  have hsum0 : Summable (fun n : ℕ => (-1 : ℝ) ^ n * (0 : ℝ) ^ (2 * n + 1) /
      ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
    have h0 : ‖(0 : ℝ)‖ ≤ 1 := by simp
    exact entry17Ti2_summable 0 h0
  exact hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound hy0 hsum0 hy

private lemma entry17Ti2_hasDerivAt_arctan_div {y : ℝ} (hy : ‖y‖ < 1)
    (hy0 : y ≠ 0) :
    HasDerivAt entry17Ti2 (Real.arctan y / y) y := by
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
  have hF := entry17Ti2_hasDerivAt_of_mem hr0 hr1 hymem
  have harctan := Real.hasSum_arctan (x := y) hy
  have hterm : (fun n : ℕ => (-1 : ℝ) ^ n * y ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ))
      = (fun n : ℕ => ((-1 : ℝ) ^ n * y ^ (2 * n + 1) /
        (((2 * n + 1 : ℕ)) : ℝ)) * y⁻¹) := by
    funext n
    have hne : ((((2 * n + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (by positivity)
    have hpow : y ^ (2 * n + 1) = y ^ (2 * n) * y := by
      rw [show 2 * n + 1 = (2 * n) + 1 by ring, pow_succ]
    rw [hpow]
    field_simp
  have hsum_eq : (∑' n : ℕ, (-1 : ℝ) ^ n * y ^ (2 * n) / (((2 * n + 1 : ℕ)) : ℝ))
      = (∑' n : ℕ, (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
        (((2 * n + 1 : ℕ)) : ℝ)) / y := by
    rw [hterm, harctan.summable.tsum_mul_right, div_eq_mul_inv]
  have hGval : (∑' n : ℕ, (-1 : ℝ) ^ n * y ^ (2 * n + 1) /
      (((2 * n + 1 : ℕ)) : ℝ)) = Real.arctan y := harctan.tsum_eq
  rw [hsum_eq, hGval] at hF
  exact hF

private lemma entry17_left_eq_Ti2 (x : ℝ) :
    (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm x k) = entry17Ti2 (Real.tan x) := by
  unfold entry17Ti2 Entry32Lambertdivisor.chapter9Entry19TanTerm
  rfl

private lemma entry17_tan_mem_Ioo_pos {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    Real.tan x ∈ Set.Ioo 0 1 := by
  have hmono := Real.strictMonoOn_tan
  have hpi := Real.pi_pos
  rw [Set.mem_Ioo] at hx
  have hxmem : x ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have h0mem : (0 : ℝ) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hpi]
  have h4mem : (Real.pi / 4) ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hpi]
  have h1 : (0 : ℝ) < Real.tan x := by
    have h := hmono h0mem hxmem hx.1
    rwa [Real.tan_zero] at h
  have h2 : Real.tan x < 1 := by
    have h := hmono hxmem h4mem hx.2
    rwa [Real.tan_pi_div_four] at h
  exact ⟨h1, h2⟩

private lemma entry17_L_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt (fun y : ℝ => entry17Ti2 (Real.tan y))
      (x / (Real.sin x * Real.cos x)) x := by
  have hpi := Real.pi_pos
  have hmem := hx
  rw [Set.mem_Ioo] at hx
  have htan := entry17_tan_mem_Ioo_pos hmem
  rw [Set.mem_Ioo] at htan
  have hnorm : ‖Real.tan x‖ < 1 := by
    rw [Real.norm_eq_abs, abs_lt]
    constructor <;> linarith [htan.1, htan.2]
  have htan0 : Real.tan x ≠ 0 := ne_of_gt htan.1
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  have houter := entry17Ti2_hasDerivAt_arctan_div hnorm htan0
  have hinner := Real.hasDerivAt_tan hcos
  have hcomp := houter.comp x hinner
  have harctan : Real.arctan (Real.tan x) = x :=
    Real.arctan_tan (by linarith) (by linarith)
  rw [harctan] at hcomp
  have htan_eq : Real.tan x = Real.sin x / Real.cos x :=
    Real.tan_eq_sin_div_cos x
  have hsin0 : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith))
  have hsimp : (x / Real.tan x) * (1 / Real.cos x ^ 2)
      = x / (Real.sin x * Real.cos x) := by
    rw [htan_eq]
    field_simp
  rw [hsimp] at hcomp
  exact hcomp

private lemma entry17_tan_continuousOn_Icc :
    ContinuousOn Real.tan (Set.Icc 0 (Real.pi / 4)) := by
  have hsub : Set.Icc (0 : ℝ) (Real.pi / 4)
      ⊆ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    intro y hy
    rw [Set.mem_Icc] at hy
    rw [Set.mem_Ioo]
    constructor <;> linarith [Real.pi_pos, hy.1, hy.2]
  exact Real.continuousOn_tan_Ioo.mono hsub

private lemma entry17_L_continuousOn :
    ContinuousOn (fun y : ℝ => entry17Ti2 (Real.tan y))
      (Set.Icc 0 (Real.pi / 4)) := by
  apply entry17Ti2_continuousOn.comp entry17_tan_continuousOn_Icc
  intro y hy
  rw [Set.mem_Icc] at hy
  have habs : |y| ≤ Real.pi / 4 := by
    rw [abs_of_nonneg hy.1]
    exact hy.2
  have htan := entry17_tan_abs_le_one y habs
  rw [Set.mem_Icc]
  exact abs_le.mp htan

private lemma entry17_L_zero : entry17Ti2 (Real.tan 0) = 0 := by
  rw [Real.tan_zero]
  unfold entry17Ti2
  have hzero : (fun n : ℕ => (-1 : ℝ) ^ n * (0 : ℝ) ^ (2 * n + 1) /
      ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => 0 := by
    funext n
    have hz : (0 : ℝ) ^ (2 * n + 1) = 0 := zero_pow (by omega)
    rw [hz]
    simp
  rw [hzero, tsum_zero]

private lemma entry17_sinc_pos_of_mem_Icc {θ : ℝ}
    (hθ : θ ∈ Set.Icc 0 (Real.pi / 4)) : 0 < Real.sinc θ := by
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

private lemma entry17_sin_eq_mul_sinc (θ : ℝ) :
    Real.sin θ = θ * Real.sinc θ := by
  by_cases h0 : θ = 0
  · subst h0
    simp only [Real.sin_zero, Real.sinc_zero, zero_mul]
  · rw [Real.sinc_of_ne_zero h0]
    field_simp

private def entry17XG (x : ℝ) : ℝ :=
  x * Real.log x + x * Real.log (Real.sinc x) - x * Real.log (Real.cos x)

private lemma entry17XG_continuousOn :
    ContinuousOn entry17XG (Set.Icc 0 (Real.pi / 4)) := by
  have hA : ContinuousOn (fun x : ℝ => x * Real.log x)
      (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuous_mul_log.continuousOn
  have hsinc_on : ContinuousOn Real.sinc (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuous_sinc.continuousOn
  have hlog_sinc_on : ContinuousOn (fun x : ℝ => Real.log (Real.sinc x))
      (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuousOn_log.comp hsinc_on (fun x hx => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_gt (entry17_sinc_pos_of_mem_Icc hx))
  have hB : ContinuousOn (fun x : ℝ => x * Real.log (Real.sinc x))
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_id.mul hlog_sinc_on
  have hcos_on : ContinuousOn Real.cos (Set.Icc 0 (Real.pi / 4)) :=
    Real.continuous_cos.continuousOn
  have hlog_cos_on : ContinuousOn (fun x : ℝ => Real.log (Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) := by
    apply Real.continuousOn_log.comp hcos_on
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    rw [Set.mem_Icc] at hx
    have habs : |x| ≤ Real.pi / 4 := by
      rw [abs_of_nonneg hx.1]
      exact hx.2
    exact entry17_cos_ne_zero x habs
  have hC : ContinuousOn (fun x : ℝ => x * Real.log (Real.cos x))
      (Set.Icc 0 (Real.pi / 4)) :=
    continuousOn_id.mul hlog_cos_on
  unfold entry17XG
  exact (hA.add hB).sub hC

private lemma entry17_X_eq_XG_on (x : ℝ) (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    chapter9XLogAbsTan x = entry17XG x := by
  rw [Set.mem_Icc] at hx
  by_cases h0 : x = 0
  · subst h0
    unfold chapter9XLogAbsTan entry17XG
    simp
  · have hpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h0)
    have hpi := Real.pi_pos
    have hsin : 0 < Real.sin x :=
      Real.sin_pos_of_pos_of_lt_pi hpos (by linarith)
    have hcos : 0 < Real.cos x :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
    have htan : 0 < Real.tan x := by
      rw [Real.tan_eq_sin_div_cos]
      exact div_pos hsin hcos
    have hsinc : 0 < Real.sinc x := entry17_sinc_pos_of_mem_Icc ⟨hx.1, hx.2⟩
    unfold chapter9XLogAbsTan entry17XG
    simp only [h0, ite_false]
    rw [abs_of_pos htan]
    have hsin_eq := entry17_sin_eq_mul_sinc x
    have hlogsin : Real.log (Real.sin x)
        = Real.log x + Real.log (Real.sinc x) := by
      rw [hsin_eq, Real.log_mul h0 (ne_of_gt hsinc)]
    have hlogtan : Real.log (Real.tan x)
        = Real.log (Real.sin x) - Real.log (Real.cos x) := by
      rw [Real.tan_eq_sin_div_cos,
        Real.log_div (ne_of_gt hsin) (ne_of_gt hcos)]
    rw [hlogtan, hlogsin]
    ring

private lemma entry17_X_continuousOn :
    ContinuousOn chapter9XLogAbsTan (Set.Icc 0 (Real.pi / 4)) :=
  entry17XG_continuousOn.congr entry17_X_eq_XG_on

private lemma entry17_X_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt chapter9XLogAbsTan
      (Real.log (Real.tan x) + x / (Real.sin x * Real.cos x)) x := by
  have hpi := Real.pi_pos
  have hmem := hx
  rw [Set.mem_Ioo] at hx
  have htanmem := entry17_tan_mem_Ioo_pos hmem
  rw [Set.mem_Ioo] at htanmem
  have htan0 : Real.tan x ≠ 0 := ne_of_gt htanmem.1
  have hcos : Real.cos x ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩)
  have hsin0 : Real.sin x ≠ 0 :=
    ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hx.1 (by linarith))
  have hEq : chapter9XLogAbsTan =ᶠ[𝓝 x]
      (fun y : ℝ => y * Real.log (Real.tan y)) := by
    have hnhds : Set.Ioo (0 : ℝ) (Real.pi / 4) ∈ 𝓝 x :=
      isOpen_Ioo.mem_nhds hmem
    filter_upwards [hnhds] with y hymem
    have htanmem_y := entry17_tan_mem_Ioo_pos hymem
    rw [Set.mem_Ioo] at htanmem_y
    unfold chapter9XLogAbsTan
    have hy0 : y ≠ 0 := ne_of_gt (Set.mem_Ioo.mp hymem).1
    simp only [hy0, ite_false, abs_of_pos htanmem_y.1]
  have htan : HasDerivAt Real.tan (1 / Real.cos x ^ 2) x :=
    Real.hasDerivAt_tan hcos
  have hlogtan : HasDerivAt (fun y : ℝ => Real.log (Real.tan y))
      ((Real.tan x)⁻¹ * (1 / Real.cos x ^ 2)) x :=
    (Real.hasDerivAt_log htan0).comp x htan
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id' x
  have hprod := hid.mul hlogtan
  have hsimp : 1 * Real.log (Real.tan x)
        + x * ((Real.tan x)⁻¹ * (1 / Real.cos x ^ 2))
      = Real.log (Real.tan x) + x / (Real.sin x * Real.cos x) := by
    have htan_eq : Real.tan x = Real.sin x / Real.cos x :=
      Real.tan_eq_sin_div_cos x
    rw [htan_eq]
    field_simp
  rw [hsimp] at hprod
  exact hprod.congr_of_eventuallyEq hEq

private def entry17K (x : ℝ) : ℝ :=
  entry17Ti2 (Real.tan x) - chapter9XLogAbsTan x

private lemma entry17_K_continuousOn :
    ContinuousOn entry17K (Set.Icc 0 (Real.pi / 4)) :=
  entry17_L_continuousOn.sub entry17_X_continuousOn

private lemma entry17_K_hasDerivAt {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 4)) :
    HasDerivAt entry17K (-Real.log (Real.tan x)) x := by
  have h := (entry17_L_hasDerivAt hx).sub (entry17_X_hasDerivAt hx)
  have hsimp : x / (Real.sin x * Real.cos x)
        - (Real.log (Real.tan x) + x / (Real.sin x * Real.cos x))
      = -Real.log (Real.tan x) := by ring
  rw [hsimp] at h
  exact h

private lemma entry17_K_zero : entry17K 0 = 0 := by
  have hX : chapter9XLogAbsTan 0 = 0 := by
    unfold chapter9XLogAbsTan
    simp
  unfold entry17K
  rw [entry17_L_zero, hX, sub_zero]

private lemma entry17_odd_hasSum {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ))
      ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2) := by
  have h1 := Complex.hasSum_taylorSeries_neg_log (z := z) hz
  have hzneg : ‖-z‖ < 1 := by rwa [norm_neg]
  have h2 := Complex.hasSum_taylorSeries_neg_log (z := -z) hzneg
  have heq1 : (1 : ℂ) - (-z) = 1 + z := by ring
  rw [heq1] at h2
  have hdiv := (h1.sub h2).div_const (2 : ℂ)
  have hval : (-Complex.log (1 - z) - -Complex.log (1 + z)) / 2
      = (-Complex.log (1 - z) + Complex.log (1 + z)) / 2 := by
    congr 1
    ring
  rw [hval] at hdiv
  replace := (Nat.divModEquiv 2).symm.hasSum_iff.mpr hdiv
  simp only [Function.comp_def, Nat.divModEquiv_symm_apply] at this
  simp_rw [← mul_comm 2 _] at this
  refine this.prod_fiberwise fun k => ?_
  dsimp only
  convert! hasSum_fintype (_ : Fin 2 → ℂ) using 1
  rw [Fin.sum_univ_two, Fin.val_zero, Fin.val_one]
  have heven : Even (2 * k + 0) := ⟨k, by ring⟩
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  rw [heven.neg_pow, hodd.neg_pow]
  simp only [sub_self, zero_div, zero_add]
  rw [neg_div, sub_neg_eq_add, add_self_div_two]

private lemma entry17_polar_pow (r θ : ℝ) (n : ℕ) :
    ((((r * Real.cos θ : ℝ)) : ℂ)
        + (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I) ^ n
      = ((((r ^ n * Real.cos ((n : ℝ) * θ) : ℝ)) : ℂ)
        + (((r ^ n * Real.sin ((n : ℝ) * θ) : ℝ)) : ℂ) * Complex.I) := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    have hcast : (((n + 1 : ℕ)) : ℝ) * θ = θ + (n : ℝ) * θ := by
      push_cast
      ring
    have hrpow : r ^ (n + 1) = r * r ^ n := pow_succ' r n
    rw [pow_succ, ih]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      rw [hcast, hrpow, Real.cos_add]
      ring
    · simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
        mul_zero, mul_one, sub_zero, add_zero]
      rw [hcast, hrpow, Real.sin_add]
      ring

private lemma entry17_polar_norm (r θ : ℝ) (hr0 : 0 ≤ r) :
    ‖((((r * Real.cos θ : ℝ)) : ℂ)
        + (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I)‖ = r := by
  have hnsq : Complex.normSq ((((r * Real.cos θ : ℝ)) : ℂ)
        + (((r * Real.sin θ : ℝ)) : ℂ) * Complex.I) = r ^ 2 := by
    rw [Complex.normSq_add_mul_I]
    have hcs := Real.cos_sq_add_sin_sq θ
    have hexpand : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2
        = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    rw [hexpand, hcs, mul_one]
  rw [Complex.norm_def, hnsq, Real.sqrt_sq hr0]

private lemma entry17_Dr_closed (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' k : ℕ, r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
        / (((2 * k + 1 : ℕ)) : ℝ))
      = Real.log ((1 + 2 * r * Real.cos (2 * x) + r ^ 2)
        / (1 - 2 * r * Real.cos (2 * x) + r ^ 2)) / 2 := by
  set θ : ℝ := 2 * x with hθ
  set z : ℂ := ((((r * Real.cos θ : ℝ))) : ℂ)
    + ((((r * Real.sin θ : ℝ))) : ℂ) * Complex.I with hzdef
  have hnorm : ‖z‖ < 1 := by
    rw [hzdef, entry17_polar_norm r θ hr0]
    exact hr1
  have hod := entry17_odd_hasSum hnorm
  have hre := Complex.hasSum_re hod
  have hterm (k : ℕ) : (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re
      = r ^ (2 * k + 1) * Real.cos (((2 * k + 1 : ℕ) : ℝ) * θ)
        / (((2 * k + 1 : ℕ)) : ℝ) := by
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, hzdef,
      entry17_polar_pow]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      mul_one, sub_zero, add_zero]
  have hDr : (fun k : ℕ => r ^ (2 * k + 1) * 2
        * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x) / (((2 * k + 1 : ℕ)) : ℝ))
      = (fun k : ℕ =>
        2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re) := by
    funext k
    rw [hterm k]
    have harg : ((2 * k + 1 : ℕ) : ℝ) * θ
        = 2 * ((2 * k + 1 : ℕ) : ℝ) * x := by
      rw [hθ]
      ring
    rw [harg]
    ring
  have htsum : (∑' k : ℕ,
        2 * (z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℂ)).re)
      = 2 * ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2).re :=
    (hre.mul_left 2).tsum_eq
  rw [hDr, htsum]
  have hz1 : z ≠ 1 := by
    intro hcon
    rw [hcon, norm_one] at hnorm
    exact lt_irrefl 1 hnorm
  have hzm1 : z ≠ -1 := by
    intro hcon
    rw [hcon] at hnorm
    simp only [norm_neg, norm_one, lt_self_iff_false] at hnorm
  have h1mz0 : (1 : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz1)
  have h1pz0 : (1 : ℂ) + z ≠ 0 := by
    intro hcon
    apply hzm1
    linear_combination hcon
  have h1pz : (1 : ℂ) + z
      = ((((1 + r * Real.cos θ : ℝ))) : ℂ)
        + ((((r * Real.sin θ : ℝ))) : ℂ) * Complex.I := by
    rw [hzdef, Complex.ofReal_add, Complex.ofReal_one]
    ring
  have h1mz : (1 : ℂ) - z
      = ((((1 - r * Real.cos θ : ℝ))) : ℂ)
        + ((((-(r * Real.sin θ) : ℝ))) : ℂ) * Complex.I := by
    rw [hzdef, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_neg]
    ring
  have hN1 : Complex.normSq (1 + z)
      = 1 + 2 * r * Real.cos θ + r ^ 2 := by
    rw [h1pz, Complex.normSq_add_mul_I]
    have hcs := Real.sin_sq_add_cos_sq θ
    have hexpand : (1 + r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2
        = 1 + 2 * r * Real.cos θ
          + r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    rw [hexpand, hcs, mul_one]
  have hN0 : Complex.normSq (1 - z)
      = 1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [h1mz, Complex.normSq_add_mul_I]
    have hcs := Real.sin_sq_add_cos_sq θ
    have hexpand : (1 - r * Real.cos θ) ^ 2 + (-(r * Real.sin θ)) ^ 2
        = 1 - 2 * r * Real.cos θ
          + r ^ 2 * (Real.sin θ ^ 2 + Real.cos θ ^ 2) := by ring
    rw [hexpand, hcs, mul_one]
  have hN1pos : 0 < 1 + 2 * r * Real.cos θ + r ^ 2 := by
    rw [← hN1]
    exact Complex.normSq_pos.mpr h1pz0
  have hN0pos : 0 < 1 - 2 * r * Real.cos θ + r ^ 2 := by
    rw [← hN0]
    exact Complex.normSq_pos.mpr h1mz0
  have hVre : ((-Complex.log (1 - z) + Complex.log (1 + z)) / 2).re
      = (-Real.log ‖1 - z‖ + Real.log ‖1 + z‖) / 2 := by
    have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by simp
    rw [h2, Complex.div_ofReal_re, Complex.add_re, Complex.neg_re,
      Complex.log_re, Complex.log_re]
  rw [hVre]
  have e1 : Real.log ‖1 + z‖
      = Real.log (1 + 2 * r * Real.cos θ + r ^ 2) / 2 := by
    rw [Complex.norm_def, hN1, Real.log_sqrt (le_of_lt hN1pos)]
  have e0 : Real.log ‖1 - z‖
      = Real.log (1 - 2 * r * Real.cos θ + r ^ 2) / 2 := by
    rw [Complex.norm_def, hN0, Real.log_sqrt (le_of_lt hN0pos)]
  rw [e1, e0, Real.log_div (ne_of_gt hN1pos) (ne_of_gt hN0pos)]
  ring

private def entry17Sr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
    / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)

private def entry17Dr (r x : ℝ) : ℝ :=
  ∑' k : ℕ, r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
    / (((2 * k + 1 : ℕ)) : ℝ)

private lemma entry17Sr_norm_le (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (k : ℕ) :
    ‖r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)‖ ≤
      (1 : ℝ) / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  have hDpos : (0 : ℝ) < ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by positivity
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hDpos]
  have hr1' : |r| ≤ 1 := by
    rw [abs_of_nonneg hr0]
    exact hr1
  have hpow : |r| ^ (2 * k + 1) ≤ 1 := pow_le_one₀ (abs_nonneg r) hr1'
  have hsin := Real.abs_sin_le_one (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
  have hnum : |r ^ (2 * k + 1) * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)|
      ≤ 1 := by
    rw [abs_mul, abs_pow]
    calc |r| ^ (2 * k + 1) * |Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)|
        ≤ 1 * 1 := mul_le_mul hpow hsin (abs_nonneg _) zero_le_one
      _ = 1 := mul_one 1
  exact div_le_div_of_nonneg_right hnum (le_of_lt hDpos)

private lemma entry17Sr_summable (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Summable (fun k : ℕ => r ^ (2 * k + 1)
      * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
        / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le (fun k => norm_nonneg _)
    (fun k => entry17Sr_norm_le r x hr0 hr1 k) entry17_base_summable

private lemma entry17Sr_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    Continuous (entry17Sr r) := by
  apply continuous_tsum (fun n => ?_) entry17_base_summable
    (fun n x => entry17Sr_norm_le r x hr0 hr1 n)
  have hlin : Continuous
      (fun x : ℝ => 2 * ((((2 * n + 1 : ℕ)) : ℝ)) * x) := by fun_prop
  apply Continuous.div_const
  refine Continuous.mul continuous_const ?_
  exact Real.continuous_sin.comp hlin

private lemma entry17Dr_norm_le (r z : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (n : ℕ) :
    ‖r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)
        / (((2 * n + 1 : ℕ)) : ℝ)‖ ≤ 2 * (r ^ 2) ^ n := by
  have hD1 : (1 : ℝ) ≤ ((((2 * n + 1 : ℕ)) : ℝ)) := by
    have hle : 1 ≤ 2 * n + 1 := by omega
    exact_mod_cast hle
  have hDpos : (0 : ℝ) < ((((2 * n + 1 : ℕ)) : ℝ)) := by linarith [hD1]
  have hrpow : r ^ (2 * n + 1) ≤ (r ^ 2) ^ n := by
    have hexp : r ^ (2 * n + 1) = r * (r ^ 2) ^ n := by
      rw [pow_succ', pow_mul]
    rw [hexp]
    calc r * (r ^ 2) ^ n ≤ 1 * (r ^ 2) ^ n :=
          mul_le_mul_of_nonneg_right (le_of_lt hr1) (by positivity)
      _ = (r ^ 2) ^ n := one_mul _
  have hcos := Real.abs_cos_le_one (2 * ((2 * n + 1 : ℕ) : ℝ) * z)
  have habs : |r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)|
      ≤ 2 * (r ^ 2) ^ n := by
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hr0 _),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc r ^ (2 * n + 1) * 2 * |Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)|
        ≤ (r ^ 2) ^ n * 2 * 1 := by
          apply mul_le_mul _ hcos (abs_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_right hrpow (by norm_num)
      _ = 2 * (r ^ 2) ^ n := by ring
  rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hDpos]
  calc |r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)|
        / ((((2 * n + 1 : ℕ)) : ℝ))
      ≤ (2 * (r ^ 2) ^ n) / ((((2 * n + 1 : ℕ)) : ℝ)) :=
        div_le_div_of_nonneg_right habs (le_of_lt hDpos)
    _ ≤ 2 * (r ^ 2) ^ n := div_le_self (by positivity) hD1

private lemma entry17Sr_term_hasDerivAt (r x : ℝ) (k : ℕ) :
    HasDerivAt
      (fun y : ℝ => r ^ (2 * k + 1)
        * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * y)
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2))
      (r ^ (2 * k + 1) * 2 * Real.cos (2 * ((2 * k + 1 : ℕ) : ℝ) * x)
        / (((2 * k + 1 : ℕ)) : ℝ)) x := by
  have hlin : HasDerivAt (fun y : ℝ => 2 * ((((2 * k + 1 : ℕ)) : ℝ)) * y)
      (2 * ((((2 * k + 1 : ℕ)) : ℝ))) x := by
    simpa using (hasDerivAt_id' x).const_mul (2 * ((((2 * k + 1 : ℕ)) : ℝ)))
  have hsin := (Real.hasDerivAt_sin
    (2 * ((((2 * k + 1 : ℕ)) : ℝ)) * x)).comp x hlin
  have hmul := hsin.const_mul (r ^ (2 * k + 1))
  have hdiv := hmul.div_const ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
  have hD0 : ((((2 * k + 1 : ℕ)) : ℝ)) ≠ 0 := ne_of_gt (by positivity)
  have hsimp : r ^ (2 * k + 1)
          * (Real.cos (2 * ((((2 * k + 1 : ℕ)) : ℝ)) * x)
            * (2 * ((((2 * k + 1 : ℕ)) : ℝ))))
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)
        = r ^ (2 * k + 1) * 2
          * Real.cos (2 * ((((2 * k + 1 : ℕ)) : ℝ)) * x)
          / ((((2 * k + 1 : ℕ)) : ℝ)) := by
    field_simp
  rwa [hsimp] at hdiv

private lemma entry17Sr_hasDerivAt (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    HasDerivAt (entry17Sr r) (entry17Dr r x) x := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hr2nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hu : Summable (fun n : ℕ => 2 * (r ^ 2) ^ n) := by
    have hgeom : Summable (fun n : ℕ => (r ^ 2) ^ n) :=
      summable_geometric_of_lt_one hr2nn hr2
    exact hgeom.mul_left 2
  have hopen : IsOpen (Set.univ : Set ℝ) := isOpen_univ
  have hpre : IsPreconnected (Set.univ : Set ℝ) := isPreconnected_univ
  have hderiv : ∀ n : ℕ, ∀ z ∈ (Set.univ : Set ℝ),
      HasDerivAt
        (fun y : ℝ => r ^ (2 * n + 1)
          * Real.sin (2 * ((2 * n + 1 : ℕ) : ℝ) * y)
            / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2))
        (r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)
          / (((2 * n + 1 : ℕ)) : ℝ)) z :=
    fun n z _ => entry17Sr_term_hasDerivAt r z n
  have hbound : ∀ n : ℕ, ∀ z ∈ (Set.univ : Set ℝ),
      ‖r ^ (2 * n + 1) * 2 * Real.cos (2 * ((2 * n + 1 : ℕ) : ℝ) * z)
          / (((2 * n + 1 : ℕ)) : ℝ)‖ ≤ 2 * (r ^ 2) ^ n :=
    fun n z _ => entry17Dr_norm_le r z hr0 hr1 n
  have hy0 : (0 : ℝ) ∈ (Set.univ : Set ℝ) := Set.mem_univ 0
  have hsum0 : Summable (fun n : ℕ => r ^ (2 * n + 1)
      * Real.sin (2 * ((2 * n + 1 : ℕ) : ℝ) * 0)
        / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) := by
    have hzero : (fun n : ℕ => r ^ (2 * n + 1)
          * Real.sin (2 * ((2 * n + 1 : ℕ) : ℝ) * (0 : ℝ))
            / ((((2 * n + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => 0 := by
      funext n
      simp
    rw [hzero]
    exact summable_zero
  have h := hasDerivAt_tsum_of_isPreconnected hu hopen hpre hderiv hbound
    hy0 hsum0 (Set.mem_univ x)
  unfold entry17Sr entry17Dr at ⊢
  exact h

private lemma entry17Dr_continuous (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Continuous (entry17Dr r) := by
  have hr2 : r ^ 2 < 1 := pow_lt_one₀ hr0 hr1 (by norm_num)
  have hr2nn : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
  have hu : Summable (fun n : ℕ => 2 * (r ^ 2) ^ n) := by
    have hgeom : Summable (fun n : ℕ => (r ^ 2) ^ n) :=
      summable_geometric_of_lt_one hr2nn hr2
    exact hgeom.mul_left 2
  apply continuous_tsum (fun n => ?_) hu
    (fun n x => entry17Dr_norm_le r x hr0 hr1 n)
  have hlin : Continuous
      (fun x : ℝ => 2 * ((((2 * n + 1 : ℕ)) : ℝ)) * x) := by fun_prop
  apply Continuous.div_const
  refine Continuous.mul continuous_const ?_
  exact Real.continuous_cos.comp hlin

private def entry17DrClosed (r t : ℝ) : ℝ :=
  Real.log ((1 + 2 * r * Real.cos (2 * t) + r ^ 2)
    / (1 - 2 * r * Real.cos (2 * t) + r ^ 2)) / 2

private lemma entry17Dr_eq_closed (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    entry17Dr r x = entry17DrClosed r x := by
  unfold entry17Dr entry17DrClosed
  exact entry17_Dr_closed r x hr0 hr1

private lemma entry17Sr_zero (r : ℝ) : entry17Sr r 0 = 0 := by
  unfold entry17Sr
  have hzero : (fun k : ℕ => r ^ (2 * k + 1)
        * Real.sin (2 * ((2 * k + 1 : ℕ) : ℝ) * (0 : ℝ))
          / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) = fun _ => 0 := by
    funext k
    simp
  rw [hzero, tsum_zero]

private lemma entry17_S_eq_Sr_one (x : ℝ) :
    (∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k) = entry17Sr 1 x := by
  unfold entry17Sr Entry21Piseries2.chapter9Entry21SineTerm
  apply tsum_congr
  intro k
  have hcast : ((((4 * k + 2 : ℕ))) : ℝ)
      = 2 * ((((2 * k + 1 : ℕ))) : ℝ) := by
    push_cast
    ring
  rw [hcast]
  simp

private lemma entry17Sr_eq_integral (r x : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx0 : 0 ≤ x) :
    entry17Sr r x = ∫ t in (0 : ℝ)..x, entry17DrClosed r t := by
  have hSrC : ContinuousOn (entry17Sr r) (Set.Icc 0 x) :=
    (entry17Sr_continuous r hr0 (le_of_lt hr1)).continuousOn.mono
      (Set.subset_univ _)
  have hFTC : (∫ t in (0 : ℝ)..x, entry17Dr r t)
      = entry17Sr r x - entry17Sr r 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx0 hSrC
      (fun t _ => entry17Sr_hasDerivAt r t hr0 hr1)
      (((entry17Dr_continuous r hr0 hr1).continuousOn.mono
        (Set.subset_univ _)).intervalIntegrable_of_Icc hx0)
  rw [entry17Sr_zero] at hFTC
  have hint : (∫ t in (0 : ℝ)..x, entry17Dr r t)
      = ∫ t in (0 : ℝ)..x, entry17DrClosed r t := by
    apply intervalIntegral.integral_congr
    intro t _
    exact entry17Dr_eq_closed r t hr0 hr1
  rw [hint, sub_zero] at hFTC
  exact hFTC.symm

private def entry17rho (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 1)

private lemma entry17rho_nonneg (n : ℕ) : 0 ≤ entry17rho n := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 := by
    calc 1 / ((n : ℝ) + 1) ≤ 1 / 1 :=
          one_div_le_one_div_of_le zero_lt_one h1
      _ = 1 := one_div_one
  unfold entry17rho
  linarith

private lemma entry17rho_lt_one (n : ℕ) : entry17rho n < 1 := by
  unfold entry17rho
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  linarith

private lemma entry17rho_tendsto : Tendsto entry17rho atTop (𝓝 1) := by
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto entry17rho atTop (𝓝 (1 - 0)) := tendsto_const_nhds.sub h0
  simpa using h1

private lemma entry17rho_eventually_ge :
    ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) ≤ entry17rho n := by
  have h := entry17rho_tendsto.eventually
    (eventually_gt_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  filter_upwards [h] with n hn
  exact le_of_lt hn

private lemma entry17Sr_continuous_r (x : ℝ) :
    ContinuousOn (fun r : ℝ => entry17Sr r x) (Set.Icc 0 1) := by
  apply continuousOn_tsum (fun n => ?_) entry17_base_summable
    (fun n r hr => ?_)
  · apply ContinuousOn.div_const
    refine ContinuousOn.mul ?_ continuousOn_const
    exact (continuous_pow (2 * n + 1)).continuousOn
  · rw [Set.mem_Icc] at hr
    exact entry17Sr_norm_le r x hr.1 hr.2 n

private lemma entry17Sr_tendsto_S (x : ℝ) :
    Tendsto (fun n : ℕ => entry17Sr (entry17rho n) x) atTop
      (𝓝 (∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k)) := by
  have hcont := entry17Sr_continuous_r x
  have hmem : (1 : ℝ) ∈ Set.Icc 0 1 := ⟨by norm_num, by norm_num⟩
  have hev : ∀ᶠ n : ℕ in atTop, entry17rho n ∈ Set.Icc 0 1 := by
    filter_upwards with n
    exact ⟨entry17rho_nonneg n, le_of_lt (entry17rho_lt_one n)⟩
  have hρw : Tendsto entry17rho atTop (𝓝[Set.Icc 0 1] 1) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨entry17rho_tendsto, hev⟩
  have hlim : Tendsto (fun n : ℕ => entry17Sr (entry17rho n) x) atTop
      (𝓝 (entry17Sr 1 x)) :=
    Tendsto.comp (hcont 1 hmem) hρw
  rwa [← entry17_S_eq_Sr_one x] at hlim

private lemma entry17DrClosed_tendsto (t : ℝ)
    (ht : t ∈ Set.Ioc 0 (Real.pi / 4)) :
    Tendsto (fun n : ℕ => entry17DrClosed (entry17rho n) t) atTop
      (𝓝 (-Real.log (Real.tan t))) := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioc] at ht
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith)
  have hcos : 0 < Real.cos t :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have htan : 0 < Real.tan t := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsin hcos
  have hN : (1 : ℝ) + 2 * 1 * Real.cos (2 * t) + 1 ^ 2
      = 4 * Real.cos t ^ 2 := by
    rw [Real.cos_two_mul]
    ring
  have hM : (1 : ℝ) - 2 * 1 * Real.cos (2 * t) + 1 ^ 2
      = 4 * Real.sin t ^ 2 := by
    rw [Real.cos_two_mul_eq_one_sub]
    ring
  have hval : entry17DrClosed 1 t = -Real.log (Real.tan t) := by
    unfold entry17DrClosed
    rw [hN, hM]
    have hc0 : (0 : ℝ) < Real.cos t ^ 2 := pow_pos hcos 2
    have hs0 : (0 : ℝ) < Real.sin t ^ 2 := pow_pos hsin 2
    have h14 : (0 : ℝ) < 4 * Real.cos t ^ 2 := mul_pos (by norm_num) hc0
    have h24 : (0 : ℝ) < 4 * Real.sin t ^ 2 := mul_pos (by norm_num) hs0
    rw [Real.log_div (ne_of_gt h14) (ne_of_gt h24),
      Real.log_mul (by norm_num) (ne_of_gt hc0),
      Real.log_mul (by norm_num) (ne_of_gt hs0),
      Real.log_pow, Real.log_pow]
    have htan_eq : Real.log (Real.tan t)
        = Real.log (Real.sin t) - Real.log (Real.cos t) := by
      rw [Real.tan_eq_sin_div_cos,
        Real.log_div (ne_of_gt hsin) (ne_of_gt hcos)]
    rw [htan_eq]
    ring
  have hcont : ContinuousAt (fun r : ℝ => entry17DrClosed r t) 1 := by
    unfold entry17DrClosed
    have hNf : ContinuousAt
        (fun r : ℝ => 1 + 2 * r * Real.cos (2 * t) + r ^ 2) 1 := by
      fun_prop
    have hMf : ContinuousAt
        (fun r : ℝ => 1 - 2 * r * Real.cos (2 * t) + r ^ 2) 1 := by
      fun_prop
    have hMpos : (0 : ℝ) < 1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2 := by
      rw [hM]
      exact mul_pos (by norm_num) (pow_pos hsin 2)
    have hdiv : ContinuousAt
        (fun r : ℝ => (1 + 2 * r * Real.cos (2 * t) + r ^ 2)
          / (1 - 2 * r * Real.cos (2 * t) + r ^ 2)) 1 :=
      hNf.div hMf (ne_of_gt hMpos)
    have hNpos : (0 : ℝ) < 1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2 := by
      rw [hN]
      exact mul_pos (by norm_num) (pow_pos hcos 2)
    have hratio : (1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2)
        / (1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2) ≠ 0 :=
      div_ne_zero (ne_of_gt hNpos) (ne_of_gt hMpos)
    have hlog : Tendsto
        (fun r : ℝ => Real.log ((1 + 2 * r * Real.cos (2 * t) + r ^ 2)
          / (1 - 2 * r * Real.cos (2 * t) + r ^ 2)))
        (𝓝 1)
        (𝓝 (Real.log ((1 + 2 * 1 * Real.cos (2 * t) + 1 ^ 2)
          / (1 - 2 * 1 * Real.cos (2 * t) + 1 ^ 2)))) :=
      (Real.continuousAt_log hratio).tendsto.comp hdiv.tendsto
    exact hlog.div_const 2
  have hcomp : Tendsto (fun n : ℕ => entry17DrClosed (entry17rho n) t) atTop
      (𝓝 (entry17DrClosed 1 t)) :=
    hcont.tendsto.comp entry17rho_tendsto
  rwa [hval] at hcomp

private lemma entry17DrClosed_bound (r t : ℝ) (hr0 : (1 / 2 : ℝ) ≤ r)
    (hr1 : r ≤ 1) (ht : t ∈ Set.Ioc 0 (Real.pi / 4)) :
    ‖entry17DrClosed r t‖ ≤ Real.log 2 - Real.log (Real.sin t) := by
  have hpi := Real.pi_pos
  rw [Set.mem_Ioc] at ht
  have hsin : 0 < Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith)
  have hsin1 : Real.sin t ≤ 1 := Real.sin_le_one t
  have hcos2 : Real.cos (2 * t) ≤ 1 := Real.cos_le_one _
  have hcos2nn : 0 ≤ Real.cos (2 * t) := by
    have hmem : 2 * t ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      constructor <;> linarith [ht.1, ht.2]
    exact Real.cos_nonneg_of_mem_Icc hmem
  unfold entry17DrClosed
  set C : ℝ := Real.cos (2 * t) with hCdef
  set N : ℝ := 1 + 2 * r * C + r ^ 2 with hNdef
  set M : ℝ := 1 - 2 * r * C + r ^ 2 with hMdef
  have hr0' : (0 : ℝ) ≤ r := by linarith [hr0]
  have hr2 : r ^ 2 ≤ 1 := pow_le_one₀ hr0' hr1
  have h2rC : (0 : ℝ) ≤ 2 * r * C := by positivity
  have hNlo : (1 : ℝ) ≤ N := by
    rw [hNdef]
    have hsq : (0 : ℝ) ≤ r ^ 2 := sq_nonneg r
    linarith [h2rC, hsq]
  have hNhi : N ≤ 4 := by
    rw [hNdef]
    have h1 : 2 * r * C ≤ 2 := by
      have e1 : 2 * r ≤ 2 * 1 := mul_le_mul_of_nonneg_left hr1 (by norm_num)
      have e2 : (2 * r) * C ≤ (2 * 1) * C :=
        mul_le_mul_of_nonneg_right e1 hcos2nn
      have e3 : (2 * 1) * C ≤ (2 * 1) * 1 :=
        mul_le_mul_of_nonneg_left hcos2 (by norm_num)
      calc (2 * r) * C ≤ (2 * 1) * C := e2
        _ ≤ (2 * 1) * 1 := e3
        _ = 2 := by norm_num
    linarith [h1, hr2]
  have hC2 : C = 1 - 2 * Real.sin t ^ 2 := by
    rw [hCdef, Real.cos_two_mul_eq_one_sub]
  have hMlo : 2 * Real.sin t ^ 2 ≤ M := by
    have hsq : (0 : ℝ) ≤ (1 - r) ^ 2 := sq_nonneg _
    have h2r : (0 : ℝ) ≤ (2 * r - 1) * (2 * Real.sin t ^ 2) :=
      mul_nonneg (by linarith [hr0]) (by positivity)
    have hexpand : M - 2 * Real.sin t ^ 2
        = (1 - r) ^ 2 + (2 * r - 1) * (2 * Real.sin t ^ 2) := by
      rw [hMdef, hC2]
      ring
    linarith [hexpand, hsq, h2r]
  have hMpos : (0 : ℝ) < M := by
    have h2s : (0 : ℝ) < 2 * Real.sin t ^ 2 :=
      mul_pos (by norm_num) (pow_pos hsin 2)
    linarith [hMlo, h2s]
  have hMhi : M ≤ 2 := by
    rw [hMdef]
    linarith [h2rC, hr2]
  have hNpos : (0 : ℝ) < N := by linarith [hNlo]
  have hM2sin : (0 : ℝ) < 2 * Real.sin t ^ 2 :=
    mul_pos (by norm_num) (pow_pos hsin 2)
  have hratio_le : N / M ≤ 2 / Real.sin t ^ 2 := by
    have h1 : N / M ≤ 4 / M :=
      div_le_div_of_nonneg_right hNhi (le_of_lt hMpos)
    have h2 : (4 : ℝ) / M ≤ 4 / (2 * Real.sin t ^ 2) := by
      rw [div_le_div_iff_of_pos_left (by norm_num) hMpos hM2sin]
      exact hMlo
    have h3 : (4 : ℝ) / (2 * Real.sin t ^ 2) = 2 / Real.sin t ^ 2 := by
      have hs0 : Real.sin t ^ 2 ≠ 0 := ne_of_gt (pow_pos hsin 2)
      have h2s0 : 2 * Real.sin t ^ 2 ≠ 0 := ne_of_gt hM2sin
      field_simp
      ring
    rw [h3] at h2
    exact le_trans h1 h2
  have hratio_ge : (1 / 2 : ℝ) ≤ N / M := by
    have h1 : (1 : ℝ) / M ≤ N / M :=
      div_le_div_of_nonneg_right hNlo (le_of_lt hMpos)
    have h2 : (1 / 2 : ℝ) ≤ 1 / M := one_div_le_one_div_of_le hMpos hMhi
    exact le_trans h2 h1
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogsin_nn : Real.log (Real.sin t) ≤ 0 :=
    Real.log_nonpos (le_of_lt hsin) hsin1
  have hDle : Real.log (N / M) / 2 ≤ Real.log 2 - Real.log (Real.sin t) := by
    have hlog : Real.log (N / M) ≤ Real.log (2 / Real.sin t ^ 2) :=
      Real.log_le_log (div_pos hNpos hMpos) hratio_le
    have hexpand : Real.log (2 / Real.sin t ^ 2)
        = Real.log 2 - 2 * Real.log (Real.sin t) := by
      rw [Real.log_div (by norm_num) (ne_of_gt (pow_pos hsin 2)),
        Real.log_pow]
      ring
    rw [hexpand] at hlog
    linarith [hlog, hlog2pos]
  have hDge : -(Real.log 2 - Real.log (Real.sin t))
      ≤ Real.log (N / M) / 2 := by
    have hlog : Real.log (1 / 2) ≤ Real.log (N / M) :=
      Real.log_le_log (by norm_num) hratio_ge
    have hexpand : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one, zero_sub]
    rw [hexpand] at hlog
    linarith [hlog, hlogsin_nn, hlog2pos]
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨hDge, hDle⟩

private lemma entry17_zero_eq :
    (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm 0 k) =
      chapter9XLogAbsTan 0 + ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm 0 k := by
  have hL : ∀ k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm 0 k = 0 := by
    intro k
    unfold Entry32Lambertdivisor.chapter9Entry19TanTerm
    rw [Real.tan_zero]
    have hz : (0 : ℝ) ^ (2 * k + 1) = 0 := zero_pow (by omega)
    rw [hz, mul_zero, zero_div]
  have hR : ∀ k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm 0 k = 0 := by
    intro k
    unfold Entry21Piseries2.chapter9Entry21SineTerm
    rw [mul_zero, Real.sin_zero, zero_div]
  have hX : chapter9XLogAbsTan 0 = 0 := by unfold chapter9XLogAbsTan; simp
  simp only [hL, hR, tsum_zero, hX, zero_add]

private lemma entry17_sin_odd_pi_div_two (k : ℕ) :
    Real.sin ((((4 * k + 2 : ℕ)) : ℝ) * (Real.pi / 4)) = (-1 : ℝ) ^ k := by
  have hcast : ((((4 * k + 2 : ℕ)) : ℝ)) = 4 * (k : ℝ) + 2 := by push_cast; ring
  have heq : (4 * (k : ℝ) + 2) * (Real.pi / 4) = Real.pi / 2 + (k : ℝ) * Real.pi := by
    ring
  rw [hcast, heq, Real.sin_add_nat_mul_pi, Real.sin_pi_div_two, mul_one]

private lemma entry17_left_pi_eq (k : ℕ) :
    Entry32Lambertdivisor.chapter9Entry19TanTerm (Real.pi / 4) k =
      (-1 : ℝ) ^ k / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold Entry32Lambertdivisor.chapter9Entry19TanTerm
  rw [Real.tan_pi_div_four, one_pow, mul_one]

private lemma entry17_right_pi_eq (k : ℕ) :
    Entry21Piseries2.chapter9Entry21SineTerm (Real.pi / 4) k =
      (-1 : ℝ) ^ k / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2) := by
  unfold Entry21Piseries2.chapter9Entry21SineTerm
  rw [entry17_sin_odd_pi_div_two k]

private lemma entry17_pi_div_four_eq :
    (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm (Real.pi / 4) k) =
      chapter9XLogAbsTan (Real.pi / 4) +
        ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm (Real.pi / 4) k := by
  have hne : Real.pi / 4 ≠ 0 := ne_of_gt (by linarith [Real.pi_pos])
  have hX : chapter9XLogAbsTan (Real.pi / 4) = 0 := by
    unfold chapter9XLogAbsTan
    simp only [hne, ite_false]
    rw [Real.tan_pi_div_four, abs_one, Real.log_one, mul_zero]
  rw [hX, zero_add]
  exact tsum_congr (fun k => by rw [entry17_left_pi_eq k, entry17_right_pi_eq k])

private lemma entry17_sin_neg_odd (k : ℕ) :
    Real.sin ((((4 * k + 2 : ℕ)) : ℝ) * (-(Real.pi / 4))) = -((-1 : ℝ) ^ k) := by
  have hneg : ((((4 * k + 2 : ℕ)) : ℝ)) * (-(Real.pi / 4)) =
      -((((4 * k + 2 : ℕ)) : ℝ) * (Real.pi / 4)) := by ring
  rw [hneg, Real.sin_neg, entry17_sin_odd_pi_div_two k]

private lemma entry17_left_neg_pi_eq (k : ℕ) :
    Entry32Lambertdivisor.chapter9Entry19TanTerm (-(Real.pi / 4)) k =
      -((-1 : ℝ) ^ k / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold Entry32Lambertdivisor.chapter9Entry19TanTerm
  have htan : Real.tan (-(Real.pi / 4)) = -1 := by
    rw [Real.tan_neg, Real.tan_pi_div_four]
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := hodd.neg_one_pow
  rw [htan, hpow]
  ring

private lemma entry17_right_neg_pi_eq (k : ℕ) :
    Entry21Piseries2.chapter9Entry21SineTerm (-(Real.pi / 4)) k =
      -((-1 : ℝ) ^ k / ((((2 * k + 1 : ℕ)) : ℝ) ^ 2)) := by
  unfold Entry21Piseries2.chapter9Entry21SineTerm
  rw [entry17_sin_neg_odd k]
  ring

private lemma entry17_neg_pi_div_four_eq :
    (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm (-(Real.pi / 4)) k) =
      chapter9XLogAbsTan (-(Real.pi / 4)) +
        ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm (-(Real.pi / 4)) k := by
  have hne : -(Real.pi / 4) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (by linarith [Real.pi_pos]))
  have hX : chapter9XLogAbsTan (-(Real.pi / 4)) = 0 := by
    unfold chapter9XLogAbsTan
    simp only [hne, ite_false]
    rw [Real.tan_neg, Real.tan_pi_div_four, abs_neg, abs_one, Real.log_one, mul_zero]
  rw [hX, zero_add]
  exact tsum_congr (fun k => by rw [entry17_left_neg_pi_eq k, entry17_right_neg_pi_eq k])

private lemma entry17_left_odd (x : ℝ) (k : ℕ) :
    Entry32Lambertdivisor.chapter9Entry19TanTerm (-x) k = -Entry32Lambertdivisor.chapter9Entry19TanTerm x k := by
  unfold Entry32Lambertdivisor.chapter9Entry19TanTerm
  rw [Real.tan_neg]
  have hodd : Odd (2 * k + 1) := ⟨k, rfl⟩
  rw [hodd.neg_pow, mul_neg, neg_div]

private lemma entry17_right_odd (x : ℝ) (k : ℕ) :
    Entry21Piseries2.chapter9Entry21SineTerm (-x) k = -Entry21Piseries2.chapter9Entry21SineTerm x k := by
  unfold Entry21Piseries2.chapter9Entry21SineTerm
  have harg : ((((4 * k + 2 : ℕ)) : ℝ)) * (-x) =
      -((((4 * k + 2 : ℕ)) : ℝ) * x) := by ring
  rw [harg, Real.sin_neg, neg_div]

private lemma entry17_X_odd (x : ℝ) :
    chapter9XLogAbsTan (-x) = -chapter9XLogAbsTan x := by
  by_cases hx0 : x = 0
  · subst hx0
    simp only [neg_zero, chapter9XLogAbsTan, ite_true, neg_zero]
  · have hnx0 : -x ≠ 0 := neg_ne_zero.mpr hx0
    unfold chapter9XLogAbsTan
    simp only [hnx0, hx0, ite_false]
    rw [Real.tan_neg, abs_neg]
    ring

private lemma entry17_tsum_left_odd (x : ℝ) :
    (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm (-x) k) =
      -(∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm x k) := by
  have h : (fun k : ℕ => Entry32Lambertdivisor.chapter9Entry19TanTerm (-x) k) =
      (fun k : ℕ => -Entry32Lambertdivisor.chapter9Entry19TanTerm x k) :=
    funext (fun k => entry17_left_odd x k)
  rw [h, tsum_neg]

private lemma entry17_tsum_right_odd (x : ℝ) :
    (∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm (-x) k) =
      -(∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k) := by
  have h : (fun k : ℕ => Entry21Piseries2.chapter9Entry21SineTerm (-x) k) =
      (fun k : ℕ => -Entry21Piseries2.chapter9Entry21SineTerm x k) :=
    funext (fun k => entry17_right_odd x k)
  rw [h, tsum_neg]

private lemma entry17_DrClosed_continuous (r : ℝ) (hr0 : 0 ≤ r)
    (hr1 : r < 1) :
    Continuous (fun t : ℝ => entry17DrClosed r t) := by
  have h : (fun t : ℝ => entry17DrClosed r t) = entry17Dr r := by
    funext t
    exact (entry17Dr_eq_closed r t hr0 hr1).symm
  rw [h]
  exact entry17Dr_continuous r hr0 hr1

private lemma entry17_bound_intervalIntegrable (a b : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log 2 - Real.log (Real.sin t))
      volume a b := by
  have hsin : IntervalIntegrable (Real.log ∘ Real.sin) volume a b :=
    intervalIntegrable_log_sin
  have hconst : IntervalIntegrable (fun _ : ℝ => Real.log 2) volume a b :=
    intervalIntegrable_const
  have h := hconst.sub hsin
  simpa [Pi.sub_apply, Function.comp_apply] using h

private lemma entry17_neglogtan_intervalIntegrable {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    IntervalIntegrable (fun t : ℝ => -Real.log (Real.tan t)) volume 0 x := by
  rw [Set.mem_Icc] at hx
  have hcos : IntervalIntegrable (Real.log ∘ Real.cos) volume (0 : ℝ) x :=
    intervalIntegrable_log_cos
  have hsin : IntervalIntegrable (Real.log ∘ Real.sin) volume (0 : ℝ) x :=
    intervalIntegrable_log_sin
  have hsub := hcos.sub hsin
  have heq : Set.EqOn (Real.log ∘ Real.cos - Real.log ∘ Real.sin)
      (fun t : ℝ => -Real.log (Real.tan t)) (Set.uIoc 0 x) := by
    intro t ht
    rw [Set.uIoc_of_le hx.1] at ht
    rw [Set.mem_Ioc] at ht
    have hsin0 : Real.sin t ≠ 0 := ne_of_gt
      (Real.sin_pos_of_pos_of_lt_pi ht.1 (by linarith [Real.pi_pos, ht.2, hx.2]))
    have hcos0 : Real.cos t ≠ 0 := ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos, ht.1, ht.2, hx.2],
        by linarith [Real.pi_pos, ht.2, hx.2]⟩)
    simp only [Pi.sub_apply, Function.comp_apply]
    rw [Real.tan_eq_sin_div_cos, Real.log_div hsin0 hcos0]
    ring
  exact (intervalIntegrable_congr heq).mp hsub

private lemma entry17_S_eq_integral {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    (∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k) =
      ∫ t in (0 : ℝ)..x, -Real.log (Real.tan t) := by
  rw [Set.mem_Icc] at hx
  have hSr_lim := entry17Sr_tendsto_S x
  have hSeqEq : (fun n : ℕ => entry17Sr (entry17rho n) x) =
      (fun n : ℕ => ∫ t in (0 : ℝ)..x, entry17DrClosed (entry17rho n) t) := by
    funext n
    exact entry17Sr_eq_integral (entry17rho n) x (entry17rho_nonneg n)
      (entry17rho_lt_one n) hx.1
  rw [hSeqEq] at hSr_lim
  have hF_meas : ∀ᶠ n : ℕ in atTop, AEStronglyMeasurable
      (fun t : ℝ => entry17DrClosed (entry17rho n) t)
        (volume.restrict (Set.uIoc 0 x)) := by
    filter_upwards with n
    exact (entry17_DrClosed_continuous (entry17rho n) (entry17rho_nonneg n)
      (entry17rho_lt_one n)).aestronglyMeasurable
  have h_bound : ∀ᶠ n : ℕ in atTop, ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 x →
      ‖entry17DrClosed (entry17rho n) t‖ ≤
        Real.log 2 - Real.log (Real.sin t) := by
    filter_upwards [entry17rho_eventually_ge] with n hn
    filter_upwards with t
    intro ht
    have hr1 : entry17rho n ≤ 1 := le_of_lt (entry17rho_lt_one n)
    have htIoc : t ∈ Set.Ioc 0 (Real.pi / 4) := by
      rw [Set.uIoc_of_le hx.1] at ht
      rw [Set.mem_Ioc] at ht ⊢
      exact ⟨ht.1, le_trans ht.2 hx.2⟩
    exact entry17DrClosed_bound (entry17rho n) t hn hr1 htIoc
  have h_int : IntervalIntegrable
      (fun t : ℝ => Real.log 2 - Real.log (Real.sin t)) volume 0 x :=
    entry17_bound_intervalIntegrable 0 x
  have h_lim : ∀ᵐ t ∂volume, t ∈ Set.uIoc 0 x →
      Tendsto (fun n : ℕ => entry17DrClosed (entry17rho n) t) atTop
        (𝓝 (-Real.log (Real.tan t))) := by
    filter_upwards with t
    intro ht
    have htIoc : t ∈ Set.Ioc 0 (Real.pi / 4) := by
      rw [Set.uIoc_of_le hx.1] at ht
      rw [Set.mem_Ioc] at ht ⊢
      exact ⟨ht.1, le_trans ht.2 hx.2⟩
    exact entry17DrClosed_tendsto t htIoc
  have hDCT := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (bound := fun t : ℝ => Real.log 2 - Real.log (Real.sin t))
    hF_meas h_bound h_int h_lim
  exact tendsto_nhds_unique hSr_lim hDCT

private lemma entry17_K_eq_integral {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    entry17K x = ∫ t in (0 : ℝ)..x, -Real.log (Real.tan t) := by
  rw [Set.mem_Icc] at hx
  have hcont : ContinuousOn entry17K (Set.Icc 0 x) := by
    apply entry17_K_continuousOn.mono
    exact Set.Icc_subset_Icc le_rfl hx.2
  have hderiv : ∀ t ∈ Set.Ioo 0 x,
      HasDerivAt entry17K (-Real.log (Real.tan t)) t := by
    intro t ht
    have ht' : t ∈ Set.Ioo 0 (Real.pi / 4) :=
      Set.Ioo_subset_Ioo le_rfl hx.2 ht
    exact entry17_K_hasDerivAt ht'
  have hint : IntervalIntegrable (fun t : ℝ => -Real.log (Real.tan t))
      volume 0 x :=
    entry17_neglogtan_intervalIntegrable ⟨hx.1, hx.2⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hcont
    hderiv hint
  rw [entry17_K_zero, sub_zero] at hFTC
  exact hFTC.symm

private lemma entry17_eq_of_nonneg {x : ℝ}
    (hx : x ∈ Set.Icc 0 (Real.pi / 4)) :
    (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm x k) =
      chapter9XLogAbsTan x + ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k := by
  have hS := entry17_S_eq_integral hx
  have hK := entry17_K_eq_integral hx
  have hKS : entry17K x = ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k := by
    rw [hK, hS]
  unfold entry17K at hKS
  have hL := entry17_left_eq_Ti2 x
  rw [hL]
  linarith [hKS]

/-- **The inverse tangent integral at $\tan x$.** Let $x$ be a real number with
$|x| \le \pi/4$, and let $P(x) = x \log|\tan x|$ for $x \ne 0$ and $P(0) = 0$. Then
$\cos x \ne 0$, the series
$T(x) = \sum_{k=0}^{\infty} (-1)^k \frac{\tan^{2k+1} x}{(2k+1)^2}$ (the inverse tangent integral
of $\tan x$) and $F(x) = \sum_{j=0}^{\infty} \frac{\sin((4j+2)x)}{(2j+1)^2}$ are both summable,
and $T(x) = P(x) + F(x)$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 9.
-/
theorem ramanujan_part1_ch9_entry17_sec (x : ℝ) (hx : |x| ≤ Real.pi / 4) :
    Real.cos x ≠ 0 ∧
      Summable (Entry32Lambertdivisor.chapter9Entry19TanTerm x) ∧
      Summable (Entry21Piseries2.chapter9Entry21SineTerm x) ∧
      (∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm x k) =
        chapter9XLogAbsTan x +
          ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k := by
  have h21 := Entry21Piseries2.ramanujan_part1_ch9_entry21_piseries2 x hx
  have h32 := Entry32Lambertdivisor.ramanujan_part1_ch9_entry32_lambertdivisor x hx
  have hSleft : Summable (Entry32Lambertdivisor.chapter9Entry19TanTerm x) := by
    exact h32.2.2.1
  have hSright : Summable (Entry21Piseries2.chapter9Entry21SineTerm x) := by
    exact h21.2.2.1
  refine ⟨entry17_cos_ne_zero x hx, hSleft, hSright, ?_⟩
  by_cases hx0 : x = 0
  · subst hx0
    exact entry17_zero_eq
  rcases le_total 0 x with hxnn | hxnn
  · have hxIcc : x ∈ Set.Icc 0 (Real.pi / 4) := ⟨hxnn, le_of_abs_le hx⟩
    exact entry17_eq_of_nonneg hxIcc
  · have hxpos : 0 ≤ -x := neg_nonneg.mpr hxnn
    have habs_neg : |-x| ≤ Real.pi / 4 := by rwa [abs_neg]
    have hxIcc : -x ∈ Set.Icc 0 (Real.pi / 4) :=
      ⟨hxpos, le_of_abs_le habs_neg⟩
    have hpos := entry17_eq_of_nonneg hxIcc
    rw [entry17_tsum_left_odd, entry17_X_odd,
      entry17_tsum_right_odd] at hpos
    have hneg : -(∑' k : ℕ, Entry32Lambertdivisor.chapter9Entry19TanTerm x k) =
        -((chapter9XLogAbsTan x) +
          ∑' k : ℕ, Entry21Piseries2.chapter9Entry21SineTerm x k) := by
      rw [hpos]
      ring
    exact neg_injective hneg

end
end Entry17Sec
end MathlibExt.Analysis.Ramanujan.Part1Ch9
end
