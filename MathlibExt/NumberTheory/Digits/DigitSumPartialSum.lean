/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Digits.TrollopeDelange
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Trollope–Delange formula for real arguments

After one base-`q` scaling, the integrals of the digit sum and the Delange series
have opposite contributions from Delange's function. Iterating their combined
recurrence gives the digit-sum integral. The last partial unit interval then gives
the correction for the inclusive sum.
-/

namespace MetaMathlibExt

open Asymptotics Filter MeasureTheory Real intervalIntegral
open scoped Topology

private noncomputable def digitValue (q : ℕ) (u : ℝ) : ℝ := ((Nat.digits q ⌊u⌋₊).sum : ℝ)

private noncomputable def digitIntegral (q : ℕ) (z : ℝ) : ℝ :=
  ∫ u in 0..z, digitValue q u

private noncomputable def centeredDigit (q : ℕ) (u : ℝ) : ℝ :=
  (⌊(q : ℝ) * u⌋ : ℝ) - q * ⌊u⌋ - ((q : ℝ) - 1) / 2

private theorem digitValue_integrable (q : ℕ) {a b : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) :
    IntervalIntegrable (digitValue q) volume a b := by
  have hmeas : Measurable (digitValue q) :=
    (Measurable.of_discrete (f := fun n : ℕ ↦ ((Nat.digits q n).sum : ℝ))).comp
      Nat.measurable_floor
  apply IntervalIntegrable.mono_fun' (g := fun _ ↦ b) intervalIntegrable_const
    hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_uIoc] with u hu
  rw [Set.uIoc_of_le hab] at hu
  have hfloor : (⌊u⌋₊ : ℝ) ≤ (⌊b⌋₊ : ℝ) := by
    exact_mod_cast Nat.floor_mono hu.2
  have hb' : (⌊u⌋₊ : ℝ) ≤ b := hfloor.trans (Nat.floor_le hb)
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold digitValue; positivity)]
  have hd : digitValue q u ≤ (⌊u⌋₊ : ℝ) := by
    unfold digitValue
    exact_mod_cast Nat.digit_sum_le q ⌊u⌋₊
  exact hd.trans hb'

private theorem centeredDigit_integrable {q : ℕ} (a b : ℝ) :
    IntervalIntegrable (centeredDigit q) volume a b := by
  have hf : Monotone (fun u : ℝ ↦ (⌊u⌋ : ℝ)) := fun _ _ h ↦
    Int.cast_le.mpr (Int.floor_le_floor h)
  have hqf : Monotone (fun u : ℝ ↦ (⌊(q : ℝ) * u⌋ : ℝ)) :=
    hf.comp (fun _ _ h ↦ mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q))
  exact ((hqf.intervalIntegrable).sub (hf.intervalIntegrable.const_mul _)).sub
    intervalIntegrable_const

private theorem digitValue_scale {q : ℕ} (hq : 1 < q) {u : ℝ} (hu : 0 ≤ u) :
    digitValue q ((q : ℝ) * u) = digitValue q u + centeredDigit q u + ((q : ℝ) - 1) / 2 := by
  have hqu : 0 ≤ (q : ℝ) * u := mul_nonneg (Nat.cast_nonneg _) hu
  let n := ⌊(q : ℝ) * u⌋₊
  have hdiv : n / q = ⌊u⌋₊ := Nat.cast_mul_floor_div_cancel (by omega) u
  have hsum : (Nat.digits q n).sum = n % q + (Nat.digits q (n / q)).sum := by
    by_cases hn : n = 0
    · simp [hn]
    · rw [Nat.digits_eq_cons_digits_div hq hn, List.sum_cons]
  have hmod : (n : ℝ) = (n % q : ℕ) + (q : ℝ) * (n / q : ℕ) := by
    exact_mod_cast (Nat.mod_add_div n q).symm
  have hr : ((Nat.digits q n).sum : ℝ) = (n % q : ℕ) + ((Nat.digits q (n / q)).sum : ℝ) := by
    exact_mod_cast hsum
  rw [hdiv] at hmod hr
  unfold digitValue centeredDigit
  rw [← natCast_floor_eq_intCast_floor hu, ← natCast_floor_eq_intCast_floor hqu]
  change ((Nat.digits q n).sum : ℝ) = _
  change (n : ℝ) = _ at hmod
  rw [hr]
  linear_combination -hmod

private theorem digitIntegral_scale {q : ℕ} (hq : 1 < q) {z : ℝ} (hz : 0 ≤ z) :
    digitIntegral q ((q : ℝ) * z) = (q : ℝ) *
      (digitIntegral q z + trollopeDelangeIntegral q z + ((q : ℝ) - 1) / 2 * z) := by
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hscale :
      (∫ u in (0 : ℝ)..z, digitValue q ((q : ℝ) * u)) =
        (q : ℝ)⁻¹ * digitIntegral q ((q : ℝ) * z) := by
    rw [integral_comp_mul_left (digitValue q) hq0, mul_zero, smul_eq_mul, digitIntegral]
  have hcongr : (∫ u in (0 : ℝ)..z, digitValue q ((q : ℝ) * u)) =
      ∫ u in (0 : ℝ)..z, digitValue q u + centeredDigit q u + ((q : ℝ) - 1) / 2 := by
    apply integral_congr_Ioo_of_le hz
    intro u hu
    exact digitValue_scale hq hu.1.le
  have hi := digitValue_integrable q hz hz
  have hd := centeredDigit_integrable (q := q) 0 z
  rw [integral_add (hi.add hd) intervalIntegrable_const, integral_add hi hd] at hcongr
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hcongr
  change _ = digitIntegral q z + trollopeDelangeIntegral q z + _ at hcongr
  rw [hscale] at hcongr
  calc
    _ = (q : ℝ) * ((q : ℝ)⁻¹ * digitIntegral q ((q : ℝ) * z)) := by
      rw [← mul_assoc, mul_inv_cancel₀ hq0, one_mul]
    _ = _ := by rw [hcongr, mul_comm z]

private theorem delangeSeries_scale {q : ℕ} (hq : 2 ≤ q) {z : ℝ} (hz : 0 < z) :
    trollopeDelangeSeries q ((q : ℝ) * z) =
      (q : ℝ) * (trollopeDelangeSeries q z - trollopeDelangeIntegral q z) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  let f (n : ℕ) := trollopeDelangeIntegral q ((q : ℝ) ^ n * z) / (q : ℝ) ^ n
  have ht : Tendsto (fun n : ℕ ↦ (q : ℝ) ^ n * z) atTop atTop := by
    refine tendsto_atTop.2 (fun b ↦ ?_)
    filter_upwards [(tendsto_pow_atTop_atTop_of_one_lt hq1).eventually
      (eventually_ge_atTop (b / z))] with n hn
    exact (div_le_iff₀ hz).mp hn
  obtain ⟨C, hC⟩ := isBigO_iff.mp (trollopeDelangeIntegral_isBigO_one q hq)
  have hB : ∀ᶠ n : ℕ in atTop, ‖trollopeDelangeIntegral q ((q : ℝ) ^ n * z)‖ ≤ C := by
    filter_upwards [ht.eventually hC] with n hn
    simpa using hn
  have hs : Summable f := by
    refine Summable.of_norm_bounded_eventually_nat
      ((summable_geometric_of_lt_one (inv_nonneg.mpr hq0.le)
        (inv_lt_one_of_one_lt₀ hq1)).mul_left C) ?_
    filter_upwards [hB] with n hn
    simp only [f, norm_div, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0.le n), inv_pow]
    exact (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using hn)
      (pow_nonneg hq0.le n)).trans_eq (div_eq_mul_inv _ _)
  have hstep (n : ℕ) :
      trollopeDelangeIntegral q ((q : ℝ) ^ n * ((q : ℝ) * z)) / (q : ℝ) ^ n =
        (q : ℝ) * f (n + 1) := by
    simp only [f, pow_succ, ← mul_assoc ((q : ℝ) ^ n)]
    field_simp
  have hsplit := hs.tsum_eq_zero_add
  have hzero : f 0 = trollopeDelangeIntegral q z := by simp [f]
  rw [hzero] at hsplit
  unfold trollopeDelangeSeries
  rw [tsum_congr hstep, tsum_mul_left]
  congr 1
  exact eq_sub_of_add_eq (by simpa [add_comm] using hsplit.symm)

private theorem digitIntegral_add_series_pow {q : ℕ} (hq : 2 ≤ q) {z : ℝ} (hz : 0 < z)
    (k : ℕ) :
    digitIntegral q ((q : ℝ) ^ k * z) + trollopeDelangeSeries q ((q : ℝ) ^ k * z) =
      (q : ℝ) ^ k * (digitIntegral q z + trollopeDelangeSeries q z) +
        ((q : ℝ) - 1) / 2 * k * ((q : ℝ) ^ k * z) := by
  have hq0 : (0 : ℝ) < q := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    have hz' : 0 < (q : ℝ) ^ k * z := mul_pos (pow_pos hq0 _) hz
    rw [pow_succ', mul_assoc, digitIntegral_scale (show 1 < q by omega) hz'.le,
      delangeSeries_scale hq hz', Nat.cast_succ]
    linear_combination (q : ℝ) * ih

private theorem digitIntegral_of_lt_one (q : ℕ) {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    digitIntegral q z = 0 := by
  unfold digitIntegral
  calc
    _ = ∫ _u in (0 : ℝ)..z, (0 : ℝ) := by
      apply integral_congr_Ioo_of_le hz
      intro u hu
      simp [digitValue, Nat.floor_eq_zero.mpr (hu.2.trans hz1)]
    _ = 0 := by simp

private theorem integral_digitValue_unit (q i : ℕ) {b : ℝ} (hbi : (i : ℝ) ≤ b)
    (hb : b ≤ (i : ℝ) + 1) :
    (∫ u in (i : ℝ)..b, digitValue q u) = (b - i) * ((Nat.digits q i).sum : ℝ) := by
  calc
    _ = (∫ _u in (i : ℝ)..b, ((Nat.digits q i).sum : ℝ)) := by
      apply integral_congr_Ioo_of_le hbi
      intro u hu
      have h0 : 0 ≤ u := (Nat.cast_nonneg i).trans hu.1.le
      simp [digitValue, (Nat.floor_eq_iff h0).mpr ⟨hu.1.le, hu.2.trans_le hb⟩]
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]

private theorem digitIntegral_eq_sum (q : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    digitIntegral q x = (∑ i ∈ Finset.range ⌊x⌋₊, ((Nat.digits q i).sum : ℝ)) +
      (x - ⌊x⌋₊) * ((Nat.digits q ⌊x⌋₊).sum : ℝ) := by
  let n := ⌊x⌋₊
  have hn : (n : ℝ) ≤ x := Nat.floor_le hx
  have hnx : x ≤ (n : ℝ) + 1 := (Nat.lt_floor_add_one _).le
  have hadj := sum_integral_adjacent_intervals (f := digitValue q)
    (a := fun i : ℕ ↦ (i : ℝ)) (n := n)
    (fun k _ ↦ digitValue_integrable q (by exact_mod_cast Nat.le_succ k) (by positivity))
  simp only [Nat.cast_zero, Nat.cast_succ] at hadj
  have hunit (i : ℕ) : (∫ u in (i : ℝ)..((i : ℝ) + 1), digitValue q u) =
      ((Nat.digits q i).sum : ℝ) := by
    rw [integral_digitValue_unit q i (by linarith) le_rfl, add_sub_cancel_left, one_mul]
  simp_rw [hunit] at hadj
  change digitIntegral q x = (∑ i ∈ Finset.range n, ((Nat.digits q i).sum : ℝ)) + _
  rw [digitIntegral, ← integral_add_adjacent_intervals (digitValue_integrable q (by positivity)
    (Nat.cast_nonneg n)) (digitValue_integrable q hn hx), ← hadj,
    integral_digitValue_unit q n hn hnx]

public section

/-- **Trollope–Delange formula for real $x$.** Let $q \ge 2$ be an integer, let $s_q(n)$ denote
the sum of the base-$q$ digits of $n$, and let $F$ be the Trollope–Delange fluctuation and $h$
Delange's series in base $q$. For every real number $x \ge 1$,
$$\sum_{n=1}^{\lfloor x \rfloor} s_q(n) = \frac{q - 1}{2 \log q} \, x \log x +
x F\left(\frac{\log x}{\log q}\right) - h(x) +
(1 + \lfloor x \rfloor - x) \, s_q(\lfloor x \rfloor).$$

Source: Ka Lun Wong and Erdenebileg Erdenebat, *Asymptotics of Partial Sums of Dirichlet
Convolutions of Digital Sum Functions in Arbitrary Bases*, INTEGERS 26 (2026), Article A43,
Theorem 1 (`integers-2026-A43-thm-1`), equation (1). -/
public theorem digitSum_partialSum_trollopeDelange (q : ℕ) (hq : 2 ≤ q) (x : ℝ)
    (hx : 1 ≤ x) :
    ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ((Nat.digits q n).sum : ℝ) =
      ((q : ℝ) - 1) / (2 * log q) * x * log x +
        x * trollopeDelangeFluctuation q (log x / log q) - trollopeDelangeSeries q x +
          (1 + ⌊x⌋₊ - x) * ((Nat.digits q ⌊x⌋₊).sum : ℝ) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hq0 : (0 : ℝ) < q := zero_lt_one.trans hq1
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 < log (q : ℝ) := log_pos hq1
  let t := log x / log (q : ℝ)
  let k := ⌊t⌋₊ + 1
  let y := x / (q : ℝ) ^ k
  have ht0 : 0 ≤ t := div_nonneg (log_nonneg hx) hlog.le
  have hk : (k : ℝ) = 1 + (⌊t⌋ : ℝ) := by
    simp only [k, Nat.cast_add, Nat.cast_one, natCast_floor_eq_intCast_floor ht0, add_comm]
  have htk : t < (k : ℝ) := by
    simpa only [k, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  have hpow : (q : ℝ) ^ t = x := by
    rw [Real.rpow_def_of_pos hq0, show log (q : ℝ) * t = log x by dsimp [t]; field_simp,
      exp_log hx0]
  have hy0 : 0 < y := div_pos hx0 (pow_pos hq0 _)
  have hy1 : y < 1 := by
    dsimp only [y]
    rw [div_lt_one (pow_pos hq0 _), ← hpow, ← Real.rpow_natCast]
    exact Real.rpow_lt_rpow_of_exponent_lt hq1 htk
  have hqy : (q : ℝ) ^ k * y = x := by dsimp [y]; field_simp
  have hsmall : (q : ℝ) ^ (t - (⌊t⌋ : ℝ) - 1) = y := by
    rw [show t - (⌊t⌋ : ℝ) - 1 = t - k by rw [hk]; ring,
      Real.rpow_sub_natCast hq0.ne', hpow]
  have hlarge : x * (q : ℝ) ^ ((k : ℝ) - t) = (q : ℝ) ^ k := by
    rw [Real.rpow_sub hq0, hpow, Real.rpow_natCast]
    field_simp
  have hi := digitIntegral_add_series_pow hq hy0 k
  rw [hqy, digitIntegral_of_lt_one q hy0.le hy1, zero_add] at hi
  have hmain : digitIntegral q x = ((q : ℝ) - 1) / (2 * log q) * x * log x +
      x * trollopeDelangeFluctuation q t - trollopeDelangeSeries q x := by
    rw [trollopeDelangeFluctuation, hsmall, ← hk, mul_add,
      ← mul_assoc x ((q : ℝ) ^ ((k : ℝ) - t)), hlarge]
    have hleading : ((q : ℝ) - 1) / (2 * log q) * x * log x = ((q : ℝ) - 1) / 2 * x * t := by
      dsimp [t]
      field_simp
    rw [hleading]
    linear_combination hi
  let n := ⌊x⌋₊
  have hsum : (∑ i ∈ Finset.range (n + 1), ((Nat.digits q i).sum : ℝ)) =
      ∑ i ∈ Finset.Icc 1 n, ((Nat.digits q i).sum : ℝ) := by
    symm
    refine Finset.sum_subset (fun i hi ↦ ?_) (fun i hi hni ↦ ?_)
    · exact Finset.mem_range.mpr (by have := (Finset.mem_Icc.mp hi).2; omega)
    · have hzero : i = 0 := by
        have hi' := Finset.mem_range.mp hi
        simp only [Finset.mem_Icc, not_and_or] at hni
        omega
      simp [hzero]
  change _ = _ + (1 + (n : ℝ) - x) * _
  rw [← hsum, Finset.sum_range_succ]
  linear_combination (digitIntegral_eq_sum q hx0.le).symm + hmain

end

end MetaMathlibExt
