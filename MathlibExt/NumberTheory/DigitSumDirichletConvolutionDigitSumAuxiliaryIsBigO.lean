/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.DigitSumDirichletConvolution
public import MathlibExt.NumberTheory.Digits.TrollopeDelange
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Log
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Order.BooleanAlgebra.Set
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Size bounds for the Trollope–Delange auxiliary functions

For every base `q ≥ 2`, `digitSum_auxiliary_isBigO` bounds Delange's series, the
Trollope–Delange fluctuation, the remainder of the Trollope–Delange formula, and the four
auxiliary integrals built from the fluctuation and the remainder.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 3 (`integers-2026-A43-lem-3`).
-/

namespace MetaMathlibExt

@[expose] public section

open Filter Asymptotics Real

namespace digitSum_auxiliary_bounds

open MeasureTheory intervalIntegral

-- `digitSum_reciprocal_fluctuation_sum_le.series_bounded` with a nonnegative constant.
private lemma series_bounded {q : ℕ} (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |trollopeDelangeSeries q x| ≤ C := by
  obtain ⟨C, hC⟩ := digitSum_reciprocal_fluctuation_sum_le.series_bounded hq
  exact ⟨C, (abs_nonneg _).trans (hC 0), hC⟩

-- `digitSum_reciprocal_fluctuation_sum_le.fluctuation_bddAbove` as a nonnegative uniform bound.
private lemma fluctuation_bounded {q : ℕ} (hq : 2 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |trollopeDelangeFluctuation q x| ≤ C := by
  obtain ⟨C, hC⟩ := digitSum_reciprocal_fluctuation_sum_le.fluctuation_bddAbove hq
  exact ⟨C, (abs_nonneg _).trans (hC ⟨0, rfl⟩), fun x => hC ⟨x, rfl⟩⟩

private lemma digitSum_le {q n : ℕ} (hq : 2 ≤ q) (hn : n ≠ 0) :
    ((Nat.digits q n).sum : ℝ) ≤ ((q : ℝ) - 1) * ((Nat.log q n : ℝ) + 1) := by
  have hq1 : 1 < q := lt_of_lt_of_le one_lt_two hq
  have hlen : (Nat.digits q n).length = Nat.log q n + 1 := Nat.length_digits q n hq1 hn
  have hmem : ∀ d ∈ Nat.digits q n, d ≤ q - 1 := fun d hd => by
    have h := Nat.digits_lt_base hq1 hd
    omega
  have hsumN : (Nat.digits q n).sum ≤ (Nat.log q n + 1) * (q - 1) := by
    simpa [hlen, nsmul_eq_mul] using List.sum_le_length_nsmul (Nat.digits q n) (q - 1) hmem
  calc ((Nat.digits q n).sum : ℝ) ≤ (((Nat.log q n + 1) * (q - 1) : ℕ) : ℝ) := by
        exact_mod_cast hsumN
    _ = ((q : ℝ) - 1) * ((Nat.log q n : ℝ) + 1) := by
        rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub (show 1 ≤ q by omega),
          Nat.cast_one]
        ring

private lemma natLog_le_log_div {q n : ℕ} (hq : 2 ≤ q) (hn : n ≠ 0) {x : ℝ}
    (hle : (n : ℝ) ≤ x) (hx : 1 ≤ x) :
    (Nat.log q n : ℝ) ≤ Real.log x / Real.log q := by
  have hq1 : (1:ℝ) < q := by exact_mod_cast lt_of_lt_of_le one_lt_two hq
  have hlogq : (0:ℝ) < Real.log q := Real.log_pos hq1
  have hx0 : (0:ℝ) < x := by linarith
  have hpow : (q ^ Nat.log q n : ℕ) ≤ n := Nat.pow_log_le_self q hn
  have hpowR : (q:ℝ) ^ Nat.log q n ≤ x := by
    have h1 : ((q ^ Nat.log q n : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hpow
    push_cast at h1
    exact h1.trans hle
  have hlog : (Nat.log q n : ℝ) * Real.log q ≤ Real.log x := by
    have hqpow0 : (0:ℝ) < (q:ℝ) ^ Nat.log q n :=
      pow_pos (by exact_mod_cast (show 0 < q by omega)) _
    have h1 : Real.log ((q:ℝ) ^ Nat.log q n) ≤ Real.log x :=
      (Real.log_le_log_iff hqpow0 hx0).mpr hpowR
    rwa [Real.log_pow] at h1
  exact (le_div_iff₀ hlogq).mpr hlog

private noncomputable def remA (q : ℕ) (Ch : ℝ) : ℝ := ((q : ℝ) - 1) + Ch

private noncomputable def remB (q : ℕ) : ℝ := ((q : ℝ) - 1) / Real.log q

private lemma remA_nonneg {q : ℕ} {Ch : ℝ} (hq : 2 ≤ q) (hCh0 : 0 ≤ Ch) :
    0 ≤ remA q Ch := by
  unfold remA
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  linarith

private lemma remB_nonneg {q : ℕ} (hq : 2 ≤ q) : 0 ≤ remB q := by
  unfold remB
  have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
  have hlogq : (0:ℝ) < Real.log q :=
    Real.log_pos (by exact_mod_cast lt_of_lt_of_le one_lt_two hq)
  exact div_nonneg (by linarith) hlogq.le

private lemma abs_remainder_le {q : ℕ} {Ch : ℝ} (hq : 2 ≤ q)
    (hCh : ∀ x : ℝ, |trollopeDelangeSeries q x| ≤ Ch) :
    ∀ u : ℝ, 1 ≤ u → |digitSumRemainder q u| ≤ remA q Ch + remB q * Real.log u := by
  intro u hu
  have hu0 : (0:ℝ) < u := by linarith
  have hn0 : ⌊u⌋₊ ≠ 0 := ne_of_gt (Nat.floor_pos.mpr hu)
  have hfloor : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0.le
  have hfac0 : (0:ℝ) ≤ 1 + ⌊u⌋₊ - u := by
    have h := Nat.lt_floor_add_one u
    linarith
  have hfac1 : (1:ℝ) + ⌊u⌋₊ - u ≤ 1 := by linarith
  have hS0 : (0:ℝ) ≤ ((Nat.digits q ⌊u⌋₊).sum : ℝ) := Nat.cast_nonneg _
  have hS_sum : ((Nat.digits q ⌊u⌋₊).sum : ℝ) ≤ ((q:ℝ)-1) * ((Nat.log q ⌊u⌋₊ : ℝ) + 1) :=
    digitSum_le hq hn0
  have hlog_bound : (Nat.log q ⌊u⌋₊ : ℝ) ≤ Real.log u / Real.log q :=
    natLog_le_log_div hq hn0 hfloor hu
  have hq1 : (0:ℝ) ≤ (q:ℝ) - 1 := by
    have hq2 : (2:ℝ) ≤ q := by exact_mod_cast hq
    linarith
  have hSL : ((Nat.digits q ⌊u⌋₊).sum : ℝ) ≤ ((q:ℝ)-1) * (Real.log u / Real.log q + 1) := by
    have hmul : ((q:ℝ)-1) * ((Nat.log q ⌊u⌋₊ : ℝ) + 1)
        ≤ ((q:ℝ)-1) * (Real.log u / Real.log q + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hq1
    linarith
  have hSeq : ((q:ℝ)-1) * (Real.log u / Real.log q + 1)
      = ((q:ℝ)-1) + remB q * Real.log u := by
    unfold remB
    ring
  have hS_le : (1 + ⌊u⌋₊ - u) * ((Nat.digits q ⌊u⌋₊).sum : ℝ)
      ≤ ((q:ℝ)-1) + remB q * Real.log u := by
    calc (1 + ⌊u⌋₊ - u) * ((Nat.digits q ⌊u⌋₊).sum : ℝ)
          ≤ 1 * ((Nat.digits q ⌊u⌋₊).sum : ℝ) := mul_le_mul_of_nonneg_right hfac1 hS0
      _ = ((Nat.digits q ⌊u⌋₊).sum : ℝ) := one_mul _
      _ ≤ ((q:ℝ)-1) * (Real.log u / Real.log q + 1) := hSL
      _ = ((q:ℝ)-1) + remB q * Real.log u := hSeq
  have hJ : digitSumRemainder q u = (1 + ⌊u⌋₊ - u) * ((Nat.digits q ⌊u⌋₊).sum : ℝ)
      - trollopeDelangeSeries q u := rfl
  rw [hJ]
  calc |(1 + ⌊u⌋₊ - u) * ((Nat.digits q ⌊u⌋₊).sum : ℝ) - trollopeDelangeSeries q u|
        ≤ |(1 + ⌊u⌋₊ - u) * ((Nat.digits q ⌊u⌋₊).sum : ℝ)|
          + |trollopeDelangeSeries q u| := abs_sub _ _
    _ = (1 + ⌊u⌋₊ - u) * ((Nat.digits q ⌊u⌋₊).sum : ℝ)
          + |trollopeDelangeSeries q u| := by
        rw [abs_mul, abs_of_nonneg hfac0, abs_of_nonneg hS0]
    _ ≤ (((q:ℝ)-1) + remB q * Real.log u) + Ch := by linarith [hS_le, hCh u]
    _ = remA q Ch + remB q * Real.log u := by
        unfold remA
        ring

private lemma zero_notMem_uIcc {x : ℝ} (hx : 1 ≤ x) : (0:ℝ) ∉ Set.uIcc 1 x := by
  rw [Set.uIcc_of_le hx, Set.mem_Icc]
  intro h
  linarith [h.1]

private lemma intervalIntegrable_inv_one {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun u : ℝ => u⁻¹) volume (1:ℝ) x :=
  (continuousOn_inv₀.mono
    (Set.subset_compl_singleton_iff.mpr (zero_notMem_uIcc hx))).intervalIntegrable

private lemma abs_fluctuationIntegral_le {q : ℕ} {CF : ℝ}
    (hCF : ∀ x : ℝ, |trollopeDelangeFluctuation q x| ≤ CF) :
    ∀ x : ℝ, 1 ≤ x → |digitSumFluctuationIntegral q x| ≤ CF * Real.log x := by
  intro x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hae : ∀ᵐ u ∂volume, u ∈ Set.Ioc (1:ℝ) x →
      ‖trollopeDelangeFluctuation q (Real.log u / Real.log q) / u‖ ≤ CF * u⁻¹ := by
    refine Eventually.of_forall fun u hu => ?_
    rw [Set.mem_Ioc] at hu
    have hu0 : (0:ℝ) < u := by linarith [hu.1]
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hCF _) (inv_nonneg.mpr hu0.le)
  have hle : ‖∫ u in (1:ℝ)..x, trollopeDelangeFluctuation q (Real.log u / Real.log q) / u‖
      ≤ ∫ u in (1:ℝ)..x, CF * u⁻¹ :=
    intervalIntegral.norm_integral_le_of_norm_le hx (g := fun u => CF * u⁻¹) hae
      ((intervalIntegrable_inv_one hx).const_mul CF)
  have hint : ∫ u in (1:ℝ)..x, CF * u⁻¹ = CF * Real.log x := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one hx0, div_one]
  exact hle.trans_eq hint

private lemma log_le_two_rpow_half {u : ℝ} (hu : 1 ≤ u) : Real.log u ≤ 2 * u ^ (1/2 : ℝ) := by
  have h := Real.log_le_rpow_div (x := u) (ε := 1/2) (by linarith) (by norm_num)
  have h2 : u ^ (1/2 : ℝ) / (1/2) = 2 * u ^ (1/2 : ℝ) := by ring
  exact h.trans_eq h2

private lemma abs_fluctuationDoubleIntegral_le {q : ℕ} {CF : ℝ} (hCF0 : 0 ≤ CF)
    (hCF : ∀ x : ℝ, |trollopeDelangeFluctuation q x| ≤ CF) :
    ∀ x : ℝ, 1 ≤ x → |digitSumFluctuationDoubleIntegral q x| ≤ CF * Real.log x * Real.log x := by
  intro x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hG : ∀ u : ℝ, 1 ≤ u → |digitSumFluctuationIntegral q u| ≤ CF * Real.log u :=
    fun u hu => abs_fluctuationIntegral_le hCF u hu
  have hae : ∀ᵐ u ∂volume, u ∈ Set.Ioc (1:ℝ) x →
      ‖(∫ v in (1:ℝ)..u, trollopeDelangeFluctuation q (Real.log v / Real.log q) / v) / u‖
        ≤ (CF * Real.log x) * u⁻¹ := by
    refine Eventually.of_forall fun u hu => ?_
    rw [Set.mem_Ioc] at hu
    have hu0 : (0:ℝ) < u := by linarith [hu.1]
    have hu1 : (1:ℝ) ≤ u := le_of_lt hu.1
    have hGu : |digitSumFluctuationIntegral q u| ≤ CF * Real.log u := hG u hu1
    have hlog : Real.log u ≤ Real.log x := (Real.log_le_log_iff hu0 hx0).mpr hu.2
    have hCFlog : CF * Real.log u ≤ CF * Real.log x := mul_le_mul_of_nonneg_left hlog hCF0
    have hmain : |digitSumFluctuationIntegral q u| ≤ CF * Real.log x := hGu.trans hCFlog
    change ‖digitSumFluctuationIntegral q u / u‖ ≤ (CF * Real.log x) * u⁻¹
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hmain (inv_nonneg.mpr hu0.le)
  have hle : ‖∫ u in (1:ℝ)..x,
        (∫ v in (1:ℝ)..u, trollopeDelangeFluctuation q (Real.log v / Real.log q) / v) / u‖
      ≤ ∫ u in (1:ℝ)..x, (CF * Real.log x) * u⁻¹ :=
    intervalIntegral.norm_integral_le_of_norm_le hx (g := fun u => (CF * Real.log x) * u⁻¹)
      hae ((intervalIntegrable_inv_one hx).const_mul (CF * Real.log x))
  have hint : ∫ u in (1:ℝ)..x, (CF * Real.log x) * u⁻¹ = CF * Real.log x * Real.log x := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one hx0, div_one]
  exact hle.trans_eq hint

private lemma abs_remainderIntegral_le {q : ℕ} {Ch : ℝ} (hq : 2 ≤ q) (hCh0 : 0 ≤ Ch)
    (hCh : ∀ x : ℝ, |trollopeDelangeSeries q x| ≤ Ch) :
    ∀ x : ℝ, 1 ≤ x → |digitSumRemainderIntegral q x| ≤ 2 * (remA q Ch + 2 * remB q) := by
  intro x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hA0 : 0 ≤ remA q Ch := remA_nonneg hq hCh0
  have hB0 : 0 ≤ remB q := remB_nonneg hq
  have hD0 : 0 ≤ remA q Ch + 2 * remB q := by linarith
  have hJpow : ∀ u : ℝ, 1 ≤ u →
      |digitSumRemainder q u| ≤ (remA q Ch + 2 * remB q) * u ^ (1/2 : ℝ) := by
    intro u hu
    have hJu : |digitSumRemainder q u| ≤ remA q Ch + remB q * Real.log u :=
      abs_remainder_le hq hCh u hu
    have hlog : Real.log u ≤ 2 * u ^ (1/2 : ℝ) := log_le_two_rpow_half hu
    have hpow1 : (1:ℝ) ≤ u ^ (1/2 : ℝ) := Real.one_le_rpow hu (by norm_num)
    have hA : remA q Ch ≤ remA q Ch * u ^ (1/2 : ℝ) := le_mul_of_one_le_right hA0 hpow1
    have hBlog : remB q * Real.log u ≤ remB q * (2 * u ^ (1/2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog hB0
    calc |digitSumRemainder q u| ≤ remA q Ch * u ^ (1/2 : ℝ) + remB q * (2 * u ^ (1/2 : ℝ)) := by
            linarith [hJu, hBlog, hA]
      _ = (remA q Ch + 2 * remB q) * u ^ (1/2 : ℝ) := by ring
  have hsplit : ∀ u : ℝ, 0 < u → (remA q Ch + 2 * remB q) * u ^ (-3/2 : ℝ)
      = (remA q Ch + 2 * remB q) * (u ^ (1/2 : ℝ) / u ^ 2) := by
    intro u hu0
    congr 1
    rw [← Real.rpow_natCast u 2, ← Real.rpow_sub hu0]
    congr 1
    norm_num
  have hae : ∀ᵐ u ∂volume, u ∈ Set.Ioc (1:ℝ) x →
      ‖digitSumRemainder q u / u ^ 2‖ ≤ (remA q Ch + 2 * remB q) * u ^ (-3/2 : ℝ) := by
    refine Eventually.of_forall fun u hu => ?_
    rw [Set.mem_Ioc] at hu
    have hu0 : (0:ℝ) < u := by linarith [hu.1]
    have hu1 : (1:ℝ) ≤ u := le_of_lt hu.1
    have hJu : |digitSumRemainder q u| ≤ (remA q Ch + 2 * remB q) * u ^ (1/2 : ℝ) := hJpow u hu1
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (pow_pos hu0 2),
      hsplit u hu0]
    have h := div_le_div_of_nonneg_right hJu (show (0:ℝ) ≤ u ^ 2 by positivity)
    rwa [mul_div_assoc] at h
  have hpow_int : IntervalIntegrable (fun u : ℝ => u ^ (-3/2 : ℝ)) volume (1:ℝ) x := by
    refine ContinuousOn.intervalIntegrable (continuousOn_id.rpow_const fun t ht => Or.inl ?_)
    exact ne_of_mem_of_not_mem ht (zero_notMem_uIcc hx)
  have hle : ‖∫ u in (1:ℝ)..x, digitSumRemainder q u / u ^ 2‖
      ≤ ∫ u in (1:ℝ)..x, (remA q Ch + 2 * remB q) * u ^ (-3/2 : ℝ) :=
    intervalIntegral.norm_integral_le_of_norm_le hx
      (g := fun u => (remA q Ch + 2 * remB q) * u ^ (-3/2 : ℝ)) hae
      (hpow_int.const_mul (remA q Ch + 2 * remB q))
  have hrw : ∫ u in (1:ℝ)..x, u ^ (-3/2 : ℝ)
      = (x ^ (-3/2 + 1 : ℝ) - 1 ^ (-3/2 + 1 : ℝ)) / (-3/2 + 1 : ℝ) :=
    integral_rpow (Or.inr ⟨by norm_num, zero_notMem_uIcc hx⟩)
  have hint : ∫ u in (1:ℝ)..x, (remA q Ch + 2 * remB q) * u ^ (-3/2 : ℝ)
      ≤ 2 * (remA q Ch + 2 * remB q) := by
    rw [intervalIntegral.integral_const_mul, hrw]
    have hr1 : (-3/2 : ℝ) + 1 = -1/2 := by norm_num
    rw [hr1, Real.one_rpow]
    have hxpow0 : (0:ℝ) ≤ x ^ (-1/2 : ℝ) := Real.rpow_nonneg hx0.le _
    have h2 : (x ^ (-1/2 : ℝ) - 1) / (-1/2 : ℝ) ≤ 2 := by
      have hneg : ((-1/2 : ℝ))⁻¹ = -2 := by norm_num
      rw [div_eq_mul_inv, hneg]
      linarith
    calc (remA q Ch + 2 * remB q) * ((x ^ (-1/2 : ℝ) - 1) / (-1/2 : ℝ))
          ≤ (remA q Ch + 2 * remB q) * 2 := mul_le_mul_of_nonneg_left h2 hD0
      _ = 2 * (remA q Ch + 2 * remB q) := by ring
  exact hle.trans hint

private lemma abs_remainderDoubleIntegral_le {q : ℕ} {CK : ℝ}
    (hCK : ∀ u : ℝ, 1 ≤ u → |digitSumRemainderIntegral q u| ≤ CK) :
    ∀ x : ℝ, 1 ≤ x → |digitSumRemainderDoubleIntegral q x| ≤ CK * Real.log x := by
  intro x hx
  have hx0 : (0:ℝ) < x := by linarith
  have hae : ∀ᵐ u ∂volume, u ∈ Set.Ioc (1:ℝ) x →
      ‖(∫ v in (1:ℝ)..u, digitSumRemainder q v / v ^ 2) / u‖ ≤ CK * u⁻¹ := by
    refine Eventually.of_forall fun u hu => ?_
    rw [Set.mem_Ioc] at hu
    have hu0 : (0:ℝ) < u := by linarith [hu.1]
    have hu1 : (1:ℝ) ≤ u := le_of_lt hu.1
    change ‖digitSumRemainderIntegral q u / u‖ ≤ CK * u⁻¹
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hu0, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hCK u hu1) (inv_nonneg.mpr hu0.le)
  have hle : ‖∫ u in (1:ℝ)..x, (∫ v in (1:ℝ)..u, digitSumRemainder q v / v ^ 2) / u‖
      ≤ ∫ u in (1:ℝ)..x, CK * u⁻¹ :=
    intervalIntegral.norm_integral_le_of_norm_le hx (g := fun u => CK * u⁻¹) hae
      ((intervalIntegrable_inv_one hx).const_mul CK)
  have hint : ∫ u in (1:ℝ)..x, CK * u⁻¹ = CK * Real.log x := by
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one hx0, div_one]
  exact hle.trans_eq hint

end digitSum_auxiliary_bounds

/-- **Size bounds for the Trollope–Delange auxiliary functions.** Let $q \ge 2$ be an integer.
For base $q$, let $h$ be Delange's series, $F$ the Trollope–Delange fluctuation, $J$ the
remainder of the Trollope–Delange formula, and
$G(x) = \int_1^x F(\log u / \log q) \, du/u$,
$H(x) = \int_1^x \int_1^u F(\log v / \log q) \, dv/v \, du/u$,
$K(x) = \int_1^x J(u) \, du/u^2$ and $L(x) = \int_1^x \int_1^u J(v) \, dv/v^2 \, du/u$.
Then $F$ is bounded on $\mathbb{R}$, and as $x \to \infty$ through the reals, $h(x) = O(1)$,
$J(x) = O(\log x)$, $G(x) = O(\log x)$, $H(x) = O(\log^2 x)$, $K(x) = O(1)$ and
$L(x) = O(\log x)$.

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Lemma 3 (`integers-2026-A43-lem-3`). -/
public theorem digitSum_auxiliary_isBigO (q : ℕ) (hq : 2 ≤ q) :
    trollopeDelangeSeries q =O[atTop] (fun _ => (1 : ℝ)) ∧
      (∃ C : ℝ, ∀ x : ℝ, |trollopeDelangeFluctuation q x| ≤ C) ∧
      digitSumRemainder q =O[atTop] log ∧
      digitSumFluctuationIntegral q =O[atTop] log ∧
      digitSumFluctuationDoubleIntegral q =O[atTop] (fun x => log x ^ 2) ∧
      digitSumRemainderIntegral q =O[atTop] (fun _ => (1 : ℝ)) ∧
      digitSumRemainderDoubleIntegral q =O[atTop] log := by
  obtain ⟨Ch, hCh0, hCh⟩ := digitSum_auxiliary_bounds.series_bounded hq
  obtain ⟨CF, hCF0, hCF⟩ := digitSum_auxiliary_bounds.fluctuation_bounded hq
  have hJ := digitSum_auxiliary_bounds.abs_remainder_le hq hCh
  have hG := digitSum_auxiliary_bounds.abs_fluctuationIntegral_le hCF
  have hK := digitSum_auxiliary_bounds.abs_remainderIntegral_le hq hCh0 hCh
  have hH := digitSum_auxiliary_bounds.abs_fluctuationDoubleIntegral_le hCF0 hCF
  have hL := digitSum_auxiliary_bounds.abs_remainderDoubleIntegral_le hK
  have hA0 := digitSum_auxiliary_bounds.remA_nonneg hq hCh0
  refine ⟨?_, ⟨CF, hCF⟩, ?_, ?_, ?_, ?_, ?_⟩
  · refine Asymptotics.IsBigO.of_bound Ch (Filter.Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    exact hCh x
  · refine Asymptotics.IsBigO.of_bound
      (digitSum_auxiliary_bounds.remA q Ch + digitSum_auxiliary_bounds.remB q) ?_
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 1)] with x hx
    have hx1 : (1:ℝ) ≤ x := by
      have hexp : (1:ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp (1:ℝ)
        linarith
      linarith
    have hlog1 : (1:ℝ) ≤ Real.log x := by
      have hpos : (0:ℝ) < x := by linarith
      have h : Real.log (Real.exp 1) ≤ Real.log x :=
        (Real.log_le_log_iff (Real.exp_pos 1) hpos).mpr hx
      rwa [Real.log_exp] at h
    have hJx := hJ x hx1
    have hAle : digitSum_auxiliary_bounds.remA q Ch
        ≤ digitSum_auxiliary_bounds.remA q Ch * Real.log x :=
      le_mul_of_one_le_right hA0 hlog1
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1)]
    calc |digitSumRemainder q x|
        ≤ digitSum_auxiliary_bounds.remA q Ch * Real.log x
          + digitSum_auxiliary_bounds.remB q * Real.log x := by linarith [hJx, hAle]
      _ = (digitSum_auxiliary_bounds.remA q Ch + digitSum_auxiliary_bounds.remB q)
          * Real.log x := by ring
  · refine Asymptotics.IsBigO.of_bound CF ?_
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with x hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx)]
    exact hG x hx
  · refine Asymptotics.IsBigO.of_bound CF ?_
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with x hx
    simp only [norm_pow, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx)]
    calc |digitSumFluctuationDoubleIntegral q x| ≤ CF * Real.log x * Real.log x := hH x hx
      _ = CF * Real.log x ^ 2 := by ring
  · refine Asymptotics.IsBigO.of_bound
      (2 * (digitSum_auxiliary_bounds.remA q Ch + 2 * digitSum_auxiliary_bounds.remB q)) ?_
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with x hx
    simp only [Real.norm_eq_abs, abs_one, mul_one]
    exact hK x hx
  · refine Asymptotics.IsBigO.of_bound
      (2 * (digitSum_auxiliary_bounds.remA q Ch + 2 * digitSum_auxiliary_bounds.remB q)) ?_
    filter_upwards [Filter.eventually_ge_atTop (1:ℝ)] with x hx
    simp only [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx)]
    exact hL x hx

end

end MetaMathlibExt
