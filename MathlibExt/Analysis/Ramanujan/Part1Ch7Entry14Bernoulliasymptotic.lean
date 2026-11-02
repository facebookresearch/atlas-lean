/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeriesComplex

public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry13Bernoullipolyadd
import MathlibExt.Analysis.Ramanujan.Part1Ch7Entry13Bernoullirecurrence

@[expose] public section

section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry14Bernoulliasymptotic

open scoped Nat Real BigOperators Interval Polynomial ContDiff
open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry14Cor2LeftTerm (s : ℝ) (j : ℕ) : ℝ :=
  let k : ℝ := j + 2
  1 / (Real.rpow k (s + 1) * Real.log k)

def chapter7StieltjesA (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  (-1 : ℝ) ^ k * c k / (k.factorial : ℝ)

def chapter7Entry14Cor2ConstantTerm (c : ℕ → ℝ) (j : ℕ) : ℝ :=
  chapter7StieltjesA c (j + 1) / (j + 2)

def chapter7Entry14Cor2Constant (c : ℕ → ℝ) : ℝ :=
  (∑' j : ℕ, chapter7Entry14Cor2LeftTerm 1 j) - 1 +
    Real.eulerMascheroniConstant +
      ∑' j : ℕ, chapter7Entry14Cor2ConstantTerm c j

def chapter7Entry14Cor2PowerTerm (c : ℕ → ℝ) (s : ℝ) (j : ℕ) : ℝ :=
  chapter7StieltjesA c (j + 1) * s ^ (j + 2) / (j + 2)

def chapter7StieltjesApprox (k m : ℕ) : ℝ :=
  (∑ j ∈ Icc 1 m, Real.log (j : ℝ) ^ k / j) -
    Real.log (m : ℝ) ^ (k + 1) / (k + 1)

private theorem chapter7StieltjesApprox_eq_entry13 :
    chapter7StieltjesApprox =
      Entry13Bernoullipolyadd.chapter7StieltjesApprox := rfl

private theorem auxLaurent (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (s : ℂ) (hs : s ≠ 1) :
    HasSum (Entry13Bernoullirecurrence.chapter7StieltjesLaurentTerm c s)
      (riemannZeta s - 1 / (s - 1)) := by
  apply Entry13Bernoullirecurrence.ramanujan_part1_ch7_entry13_bernoullirecurrence c ?_ s hs
  simpa only [← chapter7StieltjesApprox_eq_entry13] using hc

private theorem chapter7Entry14Cor2LeftTerm_eq (s : ℝ) (j : ℕ) :
    chapter7Entry14Cor2LeftTerm s j =
      1 / (Real.rpow ((j : ℝ) + 2) (s + 1) * Real.log ((j : ℝ) + 2)) := rfl

private theorem chapter7Entry14Cor2LeftTerm_summable (s : ℝ) (hs : 0 < s) :
    Summable (chapter7Entry14Cor2LeftTerm s) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcomp : Summable (fun j : ℕ => (Real.log 2)⁻¹ * (Real.rpow ((j : ℝ) + 2) (s + 1))⁻¹) := by
    apply Summable.mul_left
    have h1 : (1 : ℝ) < s + 1 := by linarith
    have hps := (Real.summable_nat_rpow_inv (p := s + 1)).mpr h1
    have hshift :=
      (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ (s + 1))⁻¹) 2).mpr hps
    simpa using hshift
  refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hcomp
  · rw [chapter7Entry14Cor2LeftTerm_eq]
    apply le_of_lt
    apply one_div_pos.mpr
    apply mul_pos
    · exact Real.rpow_pos_of_pos (by positivity) (s + 1)
    · apply Real.log_pos
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
  · rw [chapter7Entry14Cor2LeftTerm_eq]
    have hA : 0 < Real.rpow ((j : ℝ) + 2) (s + 1) :=
      Real.rpow_pos_of_pos (by positivity) (s + 1)
    have hL0L : Real.log 2 ≤ Real.log ((j : ℝ) + 2) := by
      apply Real.log_le_log (by norm_num)
      have hj : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    have hle : Real.rpow ((j : ℝ) + 2) (s + 1) * Real.log 2 ≤
        Real.rpow ((j : ℝ) + 2) (s + 1) * Real.log ((j : ℝ) + 2) :=
      mul_le_mul_of_nonneg_left hL0L (le_of_lt hA)
    have h1 := one_div_le_one_div_of_le (mul_pos hA hlog2) hle
    have h2 : (1 : ℝ) / (Real.rpow ((j : ℝ) + 2) (s + 1) * Real.log 2) =
        (Real.log 2)⁻¹ * (Real.rpow ((j : ℝ) + 2) (s + 1))⁻¹ := by
      rw [one_div, mul_inv, mul_comm]
    rwa [h2] at h1

private theorem auxHarmonicIcc (m : ℕ) :
    (((harmonic m : ℚ)) : ℝ) = ∑ j ∈ Finset.Icc 1 m, (((j : ℝ))⁻¹) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h1 : harmonic (m + 1) = harmonic m + (((m + 1 : ℕ) : ℚ))⁻¹ :=
        harmonic_succ m
      have h2 : ((((harmonic (m + 1) : ℚ)) : ℝ)) =
          ((((harmonic m : ℚ)) : ℝ)) + ((((m + 1 : ℕ)) : ℝ))⁻¹ := by
        rw [h1]
        simp
      rw [h2, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1)]

private theorem auxApproxZero (m : ℕ) :
    chapter7StieltjesApprox 0 m = (((harmonic m : ℚ)) : ℝ) - Real.log (m : ℝ) := by
  have hsum : (∑ j ∈ Finset.Icc 1 m, Real.log (j : ℝ) ^ 0 / (j : ℝ)) =
      (((harmonic m : ℚ)) : ℝ) := by
    simp only [pow_zero, one_div]
    exact (auxHarmonicIcc m).symm
  unfold chapter7StieltjesApprox
  rw [hsum]
  congr 1
  simp

private theorem auxC0 (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
    c 0 = Real.eulerMascheroniConstant := by
  have hlim : Tendsto (chapter7StieltjesApprox 0) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [← auxApproxZero] using Real.tendsto_harmonic_sub_log
  exact tendsto_nhds_unique (hc 0) hlim

private theorem auxCoeffDecay (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (r : ℝ) (hr : 0 < r) :
    Summable (fun k : ℕ => |chapter7StieltjesA c k| * r ^ k) := by
  have hs1 : ((((1 + 2 * r : ℝ))) : ℂ) ≠ 1 := by
    intro h
    rw [← Complex.ofReal_one, Complex.ofReal_inj] at h
    linarith
  have hsum := (auxLaurent c hc _ hs1).summable
  have hsub : ((((1 + 2 * r : ℝ))) : ℂ) - 1 = ((((2 * r : ℝ))) : ℂ) := by
    push_cast
    ring
  have hterm : ∀ k : ℕ,
      Entry13Bernoullirecurrence.chapter7StieltjesLaurentTerm
        c ((((1 + 2 * r : ℝ))) : ℂ) k =
      (((chapter7StieltjesA c k : ℝ)) : ℂ) * ((((2 * r : ℝ))) : ℂ) ^ k := by
    intro k
    simp only [Entry13Bernoullirecurrence.chapter7StieltjesLaurentTerm, chapter7StieltjesA]
    rw [hsub]
    push_cast
    ring
  have hsumm : Summable
      (fun k : ℕ => (((chapter7StieltjesA c k : ℝ)) : ℂ) * ((((2 * r : ℝ))) : ℂ) ^ k) :=
    hsum.congr hterm
  have h0 : Tendsto
      (fun k : ℕ => (((chapter7StieltjesA c k : ℝ)) : ℂ) * ((((2 * r : ℝ))) : ℂ) ^ k)
      atTop (𝓝 0) :=
    hsumm.tendsto_atTop_zero
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ k : ℕ,
      ‖(((chapter7StieltjesA c k : ℝ)) : ℂ) * ((((2 * r : ℝ))) : ℂ) ^ k‖ ≤ M := by
    obtain ⟨R, hR⟩ := (Metric.isBounded_range_of_tendsto _ h0).subset_ball 0
    refine ⟨max R 0, fun k => ?_⟩
    have hmem : (((chapter7StieltjesA c k : ℝ)) : ℂ) * ((((2 * r : ℝ))) : ℂ) ^ k ∈
        Metric.ball (0 : ℂ) R :=
      hR (Set.mem_range_self k)
    rw [Metric.mem_ball, dist_zero_right] at hmem
    exact le_trans (le_of_lt hmem) (le_max_left _ _)
  have hnorm : ∀ k : ℕ,
      ‖(((chapter7StieltjesA c k : ℝ)) : ℂ) * ((((2 * r : ℝ))) : ℂ) ^ k‖ =
        |chapter7StieltjesA c k| * (2 * r) ^ k := by
    intro k
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (pow_pos (by linarith : (0 : ℝ) < 2 * r) k)]
  have hsplit : ∀ k : ℕ, |chapter7StieltjesA c k| * r ^ k =
      (|chapter7StieltjesA c k| * (2 * r) ^ k) * ((1 : ℝ) / 2) ^ k := by
    intro k
    have h2r : (2 * r) * ((1 : ℝ) / 2) = r := by ring
    calc |chapter7StieltjesA c k| * r ^ k
        = |chapter7StieltjesA c k| * ((2 * r) * ((1 : ℝ) / 2)) ^ k := by rw [h2r]
      _ = (|chapter7StieltjesA c k| * (2 * r) ^ k) * ((1 : ℝ) / 2) ^ k := by
          rw [mul_pow]
          ring
  have hgeo : Summable (fun k : ℕ => M * ((1 : ℝ) / 2) ^ k) :=
    summable_geometric_two.mul_left M
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt hr) _)) (fun k => ?_) hgeo
  rw [hsplit k]
  exact mul_le_mul_of_nonneg_right (by rw [← hnorm k]; exact hM k) (by positivity)

private theorem auxPowerSummable (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (s : ℝ) (hs : 0 < s) :
    Summable (chapter7Entry14Cor2PowerTerm c s) := by
  have hdecay := auxCoeffDecay c hc s hs
  have hshift : Summable (fun j : ℕ => |chapter7StieltjesA c (j + 1)| * s ^ (j + 1)) :=
    (summable_nat_add_iff
      (f := fun k : ℕ => |chapter7StieltjesA c k| * s ^ k) 1).mpr hdecay
  have hbound : Summable
      (fun j : ℕ => s * (|chapter7StieltjesA c (j + 1)| * s ^ (j + 1))) :=
    hshift.mul_left s
  refine Summable.of_norm_bounded hbound (fun j => ?_)
  have hjNN : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hj2 : (0 : ℝ) < ((j : ℝ) + 2) := by linarith
  have h2 : (1 : ℝ) ≤ ((j : ℝ) + 2) := by linarith
  have h1 : (0 : ℝ) ≤ |chapter7StieltjesA c (j + 1)| * s ^ (j + 2) :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (le_of_lt hs) _)
  unfold chapter7Entry14Cor2PowerTerm
  rw [Real.norm_eq_abs, abs_div,
    abs_mul, abs_of_pos (pow_pos hs _), abs_of_pos hj2]
  refine le_trans (div_le_self h1 h2) (le_of_eq ?_)
  have hexp : j + 2 = (j + 1) + 1 := by omega
  rw [hexp, pow_succ]
  ring

private theorem auxConstSummable (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
    Summable (chapter7Entry14Cor2ConstantTerm c) := by
  have h := auxPowerSummable c hc 1 one_pos
  apply h.congr
  intro j
  simp only [chapter7Entry14Cor2ConstantTerm, chapter7Entry14Cor2PowerTerm,
    one_pow, mul_one]

private theorem auxRealLaurent (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (hc0 : c 0 = Real.eulerMascheroniConstant)
    (x : ℝ) (hx : 0 < x) :
    HasSum (fun j : ℕ => chapter7StieltjesA c (j + 1) * x ^ (j + 1))
      ((riemannZeta ((((1 + x : ℝ))) : ℂ)).re - 1 / x -
        Real.eulerMascheroniConstant) := by
  have hs1 : ((((1 + x : ℝ))) : ℂ) ≠ 1 := by
    intro h
    rw [← Complex.ofReal_one, Complex.ofReal_inj] at h
    linarith
  have hsum := auxLaurent c hc _ hs1
  have hsub : ((((1 + x : ℝ))) : ℂ) - 1 = ((((x : ℝ))) : ℂ) := by
    push_cast
    ring
  have hterm : ∀ k : ℕ,
      Entry13Bernoullirecurrence.chapter7StieltjesLaurentTerm
        c ((((1 + x : ℝ))) : ℂ) k =
      (((chapter7StieltjesA c k * x ^ k : ℝ)) : ℂ) := by
    intro k
    simp only [Entry13Bernoullirecurrence.chapter7StieltjesLaurentTerm, chapter7StieltjesA]
    rw [hsub]
    push_cast
    ring
  have hfun : ∀ k : ℕ,
      (Entry13Bernoullirecurrence.chapter7StieltjesLaurentTerm
        c ((((1 + x : ℝ))) : ℂ) k).re =
        chapter7StieltjesA c k * x ^ k := by
    intro k
    rw [hterm k, Complex.ofReal_re]
  have hre : HasSum (fun k : ℕ => chapter7StieltjesA c k * x ^ k)
      (riemannZeta ((((1 + x : ℝ))) : ℂ) -
        1 / (((((1 + x : ℝ))) : ℂ) - 1)).re := by
    simpa only [hfun] using Complex.hasSum_re hsum
  have hone : ((1 : ℂ) / ((((x : ℝ))) : ℂ)).re = 1 / x := by
    have hcast : (1 : ℂ) / ((((x : ℝ))) : ℂ) = ((((1 / x : ℝ))) : ℂ) := by
      push_cast
      ring
    rw [hcast, Complex.ofReal_re]
  have hval : (riemannZeta ((((1 + x : ℝ))) : ℂ) -
      1 / (((((1 + x : ℝ))) : ℂ) - 1)).re =
      (riemannZeta ((((1 + x : ℝ))) : ℂ)).re - 1 / x := by
    rw [hsub, Complex.sub_re, hone]
  rw [hval] at hre
  have hsumm := hre.summable
  have hA0 : chapter7StieltjesA c 0 = c 0 := by
    simp [chapter7StieltjesA]
  have h0 : chapter7StieltjesA c 0 * x ^ 0 = Real.eulerMascheroniConstant := by
    rw [hA0, pow_zero, mul_one, hc0]
  have hshift_sum : Summable
      (fun j : ℕ => chapter7StieltjesA c (j + 1) * x ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hsumm
  rw [hshift_sum.hasSum_iff]
  have hts := hre.tsum_eq
  have hsp := Summable.tsum_eq_zero_add hsumm
  simp only [h0] at hsp
  linear_combination hts - hsp

private theorem auxLeftHasDerivAt (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => ∑' j : ℕ, chapter7Entry14Cor2LeftTerm x j)
      (-∑' j : ℕ, (((j : ℝ) + 2) ^ (-(s + 1)))) s := by
  have hcast : ∀ j : ℕ, ((((j + 2 : ℕ))) : ℝ) = ((j : ℝ) + 2) := by
    intro j
    push_cast
    ring
  have hexp1 : (1 : ℝ) < 1 + s / 2 := by linarith
  have hps := (Real.summable_nat_rpow_inv (p := 1 + s / 2)).mpr hexp1
  have hshift := (summable_nat_add_iff
    (f := fun n : ℕ => ((((n : ℝ) ^ (1 + s / 2)))⁻¹)) 2).mpr hps
  have hu : Summable (fun j : ℕ => (((j : ℝ) + 2) ^ (-(1 + s / 2)))) := by
    apply hshift.congr
    intro j
    have hjpos : (0 : ℝ) < ((j : ℝ) + 2) := by
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      linarith
    rw [hcast j, Real.rpow_neg (le_of_lt hjpos)]
  have hmem : s ∈ Set.Ioi (s / 2) :=
    Set.mem_Ioi.mpr (by linarith : s / 2 < s)
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun j : ℕ => (((j : ℝ) + 2) ^ (-(1 + s / 2))))
    (g := fun j : ℕ => fun x : ℝ => chapter7Entry14Cor2LeftTerm x j)
    (g' := fun j : ℕ => fun y : ℝ => -((((j : ℝ) + 2) ^ (-(y + 1)))))
    (t := Set.Ioi (s / 2)) (y₀ := s) (y := s)
    hu isOpen_Ioi isPreconnected_Ioi
    (fun j y hy => by
      have hkpos : (0 : ℝ) < ((j : ℝ) + 2) := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have hk1 : (1 : ℝ) < ((j : ℝ) + 2) := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have hklog : Real.log (((j : ℝ) + 2)) ≠ 0 :=
        ne_of_gt (Real.log_pos hk1)
      have hfeq : (fun x : ℝ => chapter7Entry14Cor2LeftTerm x j) =
          (fun x : ℝ => (Real.log (((j : ℝ) + 2)))⁻¹ *
            (((j : ℝ) + 2) ^ (-(x + 1)))) := by
        funext x
        rw [chapter7Entry14Cor2LeftTerm_eq, Real.rpow_neg (le_of_lt hkpos)]
        rw [one_div, mul_inv]
        exact mul_comm _ _
      have hinner : HasDerivAt (fun x : ℝ => -(x + 1)) (-1) y :=
        ((hasDerivAt_id y).add_const 1).neg
      have hpow := HasDerivAt.const_rpow hkpos hinner
      have hmul := hpow.const_mul ((Real.log (((j : ℝ) + 2)))⁻¹)
      have heq : (Real.log (((j : ℝ) + 2)))⁻¹ *
          (Real.log (((j : ℝ) + 2)) * -1 * (((j : ℝ) + 2) ^ (-(y + 1)))) =
          -((((j : ℝ) + 2) ^ (-(y + 1)))) := by
        calc (Real.log (((j : ℝ) + 2)))⁻¹ *
              (Real.log (((j : ℝ) + 2)) * -1 * (((j : ℝ) + 2) ^ (-(y + 1))))
            = ((Real.log (((j : ℝ) + 2)))⁻¹ * Real.log (((j : ℝ) + 2))) *
              (-1 * (((j : ℝ) + 2) ^ (-(y + 1)))) := by ring
          _ = -1 * (((j : ℝ) + 2) ^ (-(y + 1))) := by
              rw [inv_mul_cancel₀ hklog, one_mul]
          _ = -((((j : ℝ) + 2) ^ (-(y + 1)))) := by ring
      have hgoal : HasDerivAt (fun x : ℝ => chapter7Entry14Cor2LeftTerm x j)
          (-((((j : ℝ) + 2) ^ (-(y + 1))))) y := by
        rw [hfeq]
        rw [heq] at hmul
        exact hmul
      exact hgoal)
    (fun j y hy => by
      have hlt : s / 2 < y := hy
      have hk1 : (1 : ℝ) ≤ ((j : ℝ) + 2) := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have hexp : -(y + 1) ≤ -(1 + s / 2) := by linarith
      have hle : ‖-((((j : ℝ) + 2) ^ (-(y + 1))))‖ ≤
          (((j : ℝ) + 2) ^ (-(1 + s / 2))) := by
        rw [norm_neg, Real.norm_eq_abs,
          abs_of_pos (Real.rpow_pos_of_pos (by linarith : (0 : ℝ) < (j : ℝ) + 2) _)]
        exact Real.rpow_le_rpow_of_exponent_le hk1 hexp
      exact hle)
    hmem (chapter7Entry14Cor2LeftTerm_summable s hs) hmem
  simpa only [tsum_neg] using hmain

private theorem auxLeftDerivValue (s : ℝ) (hs : 0 < s) :
    (∑' j : ℕ, (((j : ℝ) + 2) ^ (-(s + 1)))) =
      (riemannZeta ((1 + s : ℝ) : ℂ)).re - 1 := by
  have hw : (1 : ℝ) < (((1 + s : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]
    linarith
  have hsumm : Summable
      (fun n : ℕ => (1 : ℂ) / ((n : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ)) :=
    (Complex.summable_one_div_nat_cpow).mpr hw
  have hzeta := zeta_eq_tsum_one_div_nat_cpow hw
  have hsummR : Summable
      (fun n : ℕ => ((1 : ℂ) / ((n : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ)).re) :=
    (Complex.hasSum_re hsumm.hasSum).summable
  have hval : (riemannZeta ((1 + s : ℝ) : ℂ)).re =
      ∑' n : ℕ, (((1 : ℂ) / ((n : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ))).re := by
    rw [hzeta]
    exact Complex.re_tsum hsumm
  have hw0 : ((1 + s : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by linarith : (0 : ℝ) < 1 + s))
  have hg0 : (((1 : ℂ) / ((0 : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ))).re = 0 := by
    rw [Nat.cast_zero, Complex.zero_cpow hw0, div_zero, Complex.zero_re]
  have hg1 : (((1 : ℂ) / ((1 : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ))).re = 1 := by
    rw [Nat.cast_one, Complex.one_cpow, div_one, Complex.one_re]
  have hsp1 := Summable.tsum_eq_zero_add hsummR
  simp only [hg0, zero_add] at hsp1
  have hsummR1 : Summable
      (fun b : ℕ => (((1 : ℂ) / ((b + 1 : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ))).re) :=
    (summable_nat_add_iff 1).mpr hsummR
  have hsp2 := Summable.tsum_eq_zero_add hsummR1
  simp only [hg1] at hsp2
  have hpos2 : ∀ b : ℕ, (0 : ℝ) ≤ ((b : ℝ) + 2) := by
    intro b
    have hj0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
    linarith
  have htail : ∀ b : ℕ, (((1 : ℂ) / ((b + 2 : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ))).re =
      (((b : ℝ) + 2) ^ (-(s + 1))) := by
    intro b
    have hcc : ((b + 2 : ℕ) : ℂ) = ((((b : ℝ) + 2) : ℝ) : ℂ) := by
      norm_cast
    have e1 : ((b + 2 : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ) =
        ((((b : ℝ) + 2) ^ (1 + s) : ℝ) : ℂ) := by
      rw [hcc, Complex.ofReal_cpow (hpos2 b) (1 + s)]
    have e2 : (1 : ℂ) / ((((b : ℝ) + 2) ^ (1 + s) : ℝ) : ℂ) =
        ((1 / (((b : ℝ) + 2) ^ (1 + s)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [e1, e2, Complex.ofReal_re, one_div, ← Real.rpow_neg (hpos2 b),
      add_comm (1 : ℝ) s]
  have htailEq : (∑' b : ℕ,
      (((1 : ℂ) / ((b + 2 : ℕ) : ℂ) ^ ((1 + s : ℝ) : ℂ))).re) =
      ∑' j : ℕ, (((j : ℝ) + 2) ^ (-(s + 1))) :=
    tsum_congr htail
  linear_combination -hval - hsp1 - hsp2 - htailEq

private theorem auxPowerHasDerivAt (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c x j)
      (∑' j : ℕ, chapter7StieltjesA c (j + 1) * s ^ (j + 1)) s := by
  have h2s : (0 : ℝ) < 2 * s := by linarith
  have hdecay := auxCoeffDecay c hc (2 * s) h2s
  have hshift : Summable
      (fun j : ℕ => |chapter7StieltjesA c (j + 1)| * (2 * s) ^ (j + 1)) :=
    (summable_nat_add_iff
      (f := fun k : ℕ => |chapter7StieltjesA c k| * (2 * s) ^ k) 1).mpr hdecay
  have hu : Summable
      (fun j : ℕ => |chapter7StieltjesA c (j + 1)| * (2 * s) ^ (j + 1)) := hshift
  have hmem : s ∈ Set.Ioo (-(2 * s)) (2 * s) :=
    Set.mem_Ioo.mpr ⟨by linarith, by linarith⟩
  have hmain := hasDerivAt_tsum_of_isPreconnected
    (u := fun j : ℕ => |chapter7StieltjesA c (j + 1)| * (2 * s) ^ (j + 1))
    (g := fun j : ℕ => fun x : ℝ => chapter7Entry14Cor2PowerTerm c x j)
    (g' := fun j : ℕ => fun y : ℝ => chapter7StieltjesA c (j + 1) * y ^ (j + 1))
    (t := Set.Ioo (-(2 * s)) (2 * s)) (y₀ := s) (y := s)
    hu isOpen_Ioo isPreconnected_Ioo
    (fun j y hy => by
      have hK : ((j : ℝ) + 2) ≠ 0 := by
        have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        have : (0 : ℝ) < ((j : ℝ) + 2) := by linarith
        exact ne_of_gt this
      have h1 := hasDerivAt_pow (j + 2) y
      have h2 := h1.const_mul (chapter7StieltjesA c (j + 1))
      have h3 := h2.div_const (((j : ℝ) + 2))
      have hval : chapter7StieltjesA c (j + 1) *
            ((((j + 2 : ℕ)) : ℝ) * y ^ (j + 2 - 1)) / ((j : ℝ) + 2) =
          chapter7StieltjesA c (j + 1) * y ^ (j + 1) := by
        have e1 : ((((j + 2 : ℕ))) : ℝ) = ((j : ℝ) + 2) := by
          push_cast
          ring
        have e2 : j + 2 - 1 = j + 1 := by omega
        rw [e1, e2, div_eq_iff hK]
        ring
      have hgoal : HasDerivAt
          (fun x : ℝ => chapter7Entry14Cor2PowerTerm c x j)
          (chapter7StieltjesA c (j + 1) * y ^ (j + 1)) y := by
        unfold chapter7Entry14Cor2PowerTerm
        rw [hval] at h3
        exact h3
      exact hgoal)
    (fun j y hy => by
      have hyI := Set.mem_Ioo.mp hy
      have habs : |y| < 2 * s := abs_lt.mpr ⟨by linarith [hyI.1], hyI.2⟩
      have hle : ‖chapter7StieltjesA c (j + 1) * y ^ (j + 1)‖ ≤
          |chapter7StieltjesA c (j + 1)| * (2 * s) ^ (j + 1) := by
        rw [norm_mul, Real.norm_eq_abs, norm_pow, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (abs_nonneg _) (le_of_lt habs) _)
          (abs_nonneg _)
      exact hle)
    hmem (auxPowerSummable c hc s hs) hmem
  exact hmain

private theorem auxRightHasDerivAt (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (s : ℝ) (hs : 0 < s) :
    HasDerivAt
      (fun x : ℝ => -Real.log x + chapter7Entry14Cor2Constant c +
        (1 - Real.eulerMascheroniConstant) * x -
          ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c x j)
      (-s⁻¹ + (1 - Real.eulerMascheroniConstant) -
        ∑' j : ℕ, chapter7StieltjesA c (j + 1) * s ^ (j + 1)) s := by
  have hP := auxPowerHasDerivAt c hc s hs
  have hlog : HasDerivAt (fun x : ℝ => -Real.log x) (-s⁻¹) s :=
    (Real.hasDerivAt_log (ne_of_gt hs)).neg
  have hC : HasDerivAt (fun _ : ℝ => chapter7Entry14Cor2Constant c) 0 s :=
    hasDerivAt_const s _
  have hlin : HasDerivAt (fun x : ℝ => (1 - Real.eulerMascheroniConstant) * x)
      (1 - Real.eulerMascheroniConstant) s := by
    simpa only [mul_one] using
      (hasDerivAt_id' s).const_mul (1 - Real.eulerMascheroniConstant)
  have h := ((hlog.add hC).add hlin).sub hP
  have hfun : (((fun x : ℝ => -Real.log x) + (fun _ : ℝ => chapter7Entry14Cor2Constant c)) +
      (fun x : ℝ => (1 - Real.eulerMascheroniConstant) * x)) -
      (fun x : ℝ => ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c x j) =
      (fun x : ℝ => -Real.log x + chapter7Entry14Cor2Constant c +
        (1 - Real.eulerMascheroniConstant) * x -
          ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c x j) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
  rw [hfun] at h
  simpa only [add_zero] using h

private theorem auxDerivAgree (c : ℕ → ℝ)
    (hc : ∀ k : ℕ, Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k)))
    (hc0 : c 0 = Real.eulerMascheroniConstant)
    (s : ℝ) (hs : 0 < s) :
    -(∑' j : ℕ, (((j : ℝ) + 2) ^ (-(s + 1)))) =
      -s⁻¹ + (1 - Real.eulerMascheroniConstant) -
        ∑' j : ℕ, chapter7StieltjesA c (j + 1) * s ^ (j + 1) := by
  have hN9 := auxLeftDerivValue s hs
  have hts := (auxRealLaurent c hc hc0 s hs).tsum_eq
  linear_combination -hN9 + hts

/-- **Expansion of $\sum 1/(n^{s+1} \log n)$ in the Stieltjes constants.** Let $(c_k)_{k \ge 0}$ be
real numbers such that, for every $k \ge 0$,
$\sum_{j=1}^{m} (\log j)^k / j - (\log m)^{k+1} / (k+1)$ tends to $c_k$ as $m \to \infty$, and put
$A_k = (-1)^k c_k / k!$. Then the series $\sum_{n \ge 2} \frac{1}{n^2 \log n}$ and
$\sum_{k \ge 1} \frac{A_k}{k+1}$ converge absolutely, and for every real $s > 0$ the series
$\sum_{n \ge 2} \frac{1}{n^{s+1} \log n}$ and $\sum_{k \ge 1} \frac{A_k s^{k+1}}{k+1}$ converge
absolutely and
$$\sum_{n=2}^{\infty} \frac{1}{n^{s+1} \log n} = -\log s + C + (1 - \gamma) s
  - \sum_{k=1}^{\infty} \frac{A_k s^{k+1}}{k+1},$$
where $\gamma$ is Euler's constant and
$C = \sum_{n \ge 2} \frac{1}{n^2 \log n} - 1 + \gamma + \sum_{k \ge 1} \frac{A_k}{k+1}$.

Proof outline: the limits $c_k$ are the Stieltjes constants, and
$\zeta(1+s) - 1/s = \sum_{k \ge 0} A_k s^k$. Both sides are differentiated termwise in $s$, their
derivatives agree on $s > 0$, and the two sides agree at $s = 1$.

Proves `Wanted` entry `ramanujan_part1_ch7_entry14_bernoulliasymptotic`.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7.
-/
theorem ramanujan_part1_ch7_entry14_bernoulliasymptotic
    (c : ℕ → ℝ)
    (hc : ∀ k : ℕ,
      Tendsto (chapter7StieltjesApprox k) atTop (𝓝 (c k))) :
    Summable (chapter7Entry14Cor2LeftTerm 1) ∧
      Summable (chapter7Entry14Cor2ConstantTerm c) ∧
      ∀ s : ℝ, 0 < s →
        Summable (chapter7Entry14Cor2LeftTerm s) ∧
          Summable (chapter7Entry14Cor2PowerTerm c s) ∧
          (∑' j : ℕ, chapter7Entry14Cor2LeftTerm s j) =
            -Real.log s + chapter7Entry14Cor2Constant c +
              (1 - Real.eulerMascheroniConstant) * s -
                ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c s j := by
  have hc0 : c 0 = Real.eulerMascheroniConstant := auxC0 c hc
  refine ⟨?_, auxConstSummable c hc, fun s hs => ⟨?_, ?_, ?_⟩⟩
  · exact chapter7Entry14Cor2LeftTerm_summable 1 one_pos
  · exact chapter7Entry14Cor2LeftTerm_summable s hs
  · exact auxPowerSummable c hc s hs
  · have hEq : Set.EqOn (fun x : ℝ => ∑' j : ℕ, chapter7Entry14Cor2LeftTerm x j)
        (fun x : ℝ => -Real.log x + chapter7Entry14Cor2Constant c +
          (1 - Real.eulerMascheroniConstant) * x -
            ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c x j) (Set.Ioi 0) := by
      refine IsOpen.eqOn_of_deriv_eq (s := Set.Ioi (0 : ℝ)) (x := 1)
        isOpen_Ioi isPreconnected_Ioi ?_ ?_ ?_ (Set.mem_Ioi.mpr one_pos) ?_
      · intro x hx
        exact ((auxLeftHasDerivAt x hx).differentiableAt).differentiableWithinAt
      · intro x hx
        exact ((auxRightHasDerivAt c hc x hx).differentiableAt).differentiableWithinAt
      · intro x hx
        rw [(auxLeftHasDerivAt x hx).deriv,
          (auxRightHasDerivAt c hc x hx).deriv]
        exact auxDerivAgree c hc hc0 x hx
      · have hPC : ∀ j : ℕ, chapter7Entry14Cor2PowerTerm c 1 j =
            chapter7Entry14Cor2ConstantTerm c j := by
          intro j
          simp only [chapter7Entry14Cor2ConstantTerm, chapter7Entry14Cor2PowerTerm,
            one_pow, mul_one]
        have h1 : (∑' j : ℕ, chapter7Entry14Cor2LeftTerm 1 j) =
            -Real.log 1 + chapter7Entry14Cor2Constant c +
              (1 - Real.eulerMascheroniConstant) * 1 -
                ∑' j : ℕ, chapter7Entry14Cor2PowerTerm c 1 j := by
          rw [Real.log_one]
          simp only [hPC]
          unfold chapter7Entry14Cor2Constant
          ring
        exact h1
    exact hEq (Set.mem_Ioi.mpr hs)

end
end Entry14Bernoulliasymptotic
end MathlibExt.Analysis.Ramanujan.Part1Ch7
end
