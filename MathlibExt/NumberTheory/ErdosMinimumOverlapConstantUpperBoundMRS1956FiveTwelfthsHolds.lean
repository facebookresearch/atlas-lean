/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ErdosMinimumOverlapConstant
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Motzkin–Ralston–Selfridge 5/12 upper bound for minimum overlap

This module defines `upperBound_MRS1956_fiveTwelfths` and proves
`upperBound_MRS1956_fiveTwelfths_holds`: the continuous Erdős minimum-overlap
constant satisfies `C₁ᵦ ≤ 5/12`, witnessed by an explicit symmetric three-step
admissible pair.

Source: Optimization Problems, Constant 1b, frozen at commit
`2c1968cd520b60f1cf3cf50749f7285e800e4e15`, `constants/1b.md`, SHA-256
`1c51678108c90a2e841e1b49fa97940e4e1870324e1d949ddcb5b4345a0153ec`.
The source gives an optimization problem with known bounds and a known discrete
equivalence, but no supported exact-value conjecture. The half upper bound, quarter lower bound,
and Moser lower bound are proved in MathlibExt. The remaining claims are explicit
`theorem_wanted` declarations.
The decimal payloads are literal source requests, not certified rounded bounds.
Full primary-paper and numerical-certificate verification remains deferred.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted

/-- **Statement of the Motzkin–Ralston–Selfridge upper bound $5/12$ for the minimum-overlap
constant.** The proposition that the continuous Erdős minimum-overlap constant $C_{1b}$
satisfies $C_{1b} \le 5/12$.

Source: Motzkin--Ralston--Selfridge 1956; Optimization Problems, Constant 1b. -/
def upperBound_MRS1956_fiveTwelfths : Prop := C₁ᵦ ≤ (5 : ℝ) / 12

open scoped Classical in
private noncomputable def stepF : ℝ → ℝ := fun t =>
  if t ∈ Icc (-1 / 2 : ℝ) (1 / 2) then 3 / 4 else if t ∈ Icc (-1 : ℝ) 1 then 1 / 4 else 0

open scoped Classical in
private noncomputable def stepG : ℝ → ℝ := fun t =>
  if t ∈ Icc (-1 / 2 : ℝ) (1 / 2) then 1 / 4 else if t ∈ Icc (-1 : ℝ) 1 then 3 / 4 else 0

private theorem stepF_middle {t : ℝ} (h : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    stepF t = 3 / 4 := by
  unfold stepF
  rw [ite_eq_left h]

private theorem stepF_outer {t : ℝ} (hmid : t ∉ Icc (-1 / 2 : ℝ) (1 / 2))
    (hsup : t ∈ Icc (-1 : ℝ) 1) : stepF t = 1 / 4 := by
  unfold stepF
  rw [ite_eq_right hmid, ite_eq_left hsup]

private theorem stepF_zero {t : ℝ} (hsup : t ∉ Icc (-1 : ℝ) 1) : stepF t = 0 := by
  have hmid : t ∉ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro h
    obtain ⟨h1, h2⟩ := mem_Icc.mp h
    exact hsup (mem_Icc.mpr ⟨by linarith, by linarith⟩)
  unfold stepF
  rw [ite_eq_right hmid, ite_eq_right hsup]

private theorem stepG_middle {t : ℝ} (h : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
    stepG t = 1 / 4 := by
  unfold stepG
  rw [ite_eq_left h]

private theorem stepG_outer {t : ℝ} (hmid : t ∉ Icc (-1 / 2 : ℝ) (1 / 2))
    (hsup : t ∈ Icc (-1 : ℝ) 1) : stepG t = 3 / 4 := by
  unfold stepG
  rw [ite_eq_right hmid, ite_eq_left hsup]

private theorem stepG_zero {t : ℝ} (hsup : t ∉ Icc (-1 : ℝ) 1) : stepG t = 0 := by
  have hmid : t ∉ Icc (-1 / 2 : ℝ) (1 / 2) := by
    intro h
    obtain ⟨h1, h2⟩ := mem_Icc.mp h
    exact hsup (mem_Icc.mpr ⟨by linarith, by linarith⟩)
  unfold stepG
  rw [ite_eq_right hmid, ite_eq_right hsup]

private theorem stepF_neg (t : ℝ) : stepF (-t) = stepF t := by
  have hmid : (-t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) ↔ (t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hsup : (-t ∈ Icc (-1 : ℝ) 1) ↔ (t ∈ Icc (-1 : ℝ) 1) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold stepF
  simp only [hmid, hsup]

private theorem stepG_neg (t : ℝ) : stepG (-t) = stepG t := by
  have hmid : (-t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) ↔ (t ∈ Icc (-1 / 2 : ℝ) (1 / 2)) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hsup : (-t ∈ Icc (-1 : ℝ) 1) ↔ (t ∈ Icc (-1 : ℝ) 1) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  unfold stepG
  simp only [hmid, hsup]

private theorem stepF_measurable : Measurable stepF := by
  unfold stepF
  exact Measurable.piecewise measurableSet_Icc measurable_const
    (Measurable.piecewise measurableSet_Icc measurable_const measurable_const)

private theorem stepG_measurable : Measurable stepG := by
  unfold stepG
  exact Measurable.piecewise measurableSet_Icc measurable_const
    (Measurable.piecewise measurableSet_Icc measurable_const measurable_const)

private theorem stepF_range (t : ℝ) : stepF t ∈ Icc (0 : ℝ) 1 := by
  unfold stepF
  split
  · exact ⟨by norm_num, by norm_num⟩
  · split
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩

private theorem stepG_range (t : ℝ) : stepG t ∈ Icc (0 : ℝ) 1 := by
  unfold stepG
  split
  · exact ⟨by norm_num, by norm_num⟩
  · split
    · exact ⟨by norm_num, by norm_num⟩
    · exact ⟨by norm_num, by norm_num⟩

private theorem stepF_zero_outside (t : ℝ) (ht : t ∉ continuousSupportInterval) :
    stepF t = 0 :=
  stepF_zero ht

private theorem stepG_zero_outside (t : ℝ) (ht : t ∉ continuousSupportInterval) :
    stepG t = 0 :=
  stepG_zero ht

private theorem stepFG_complementary (t : ℝ) (ht : t ∈ continuousSupportInterval) :
    stepF t + stepG t = 1 := by
  by_cases hm : t ∈ Icc (-1 / 2 : ℝ) (1 / 2)
  · rw [stepF_middle hm, stepG_middle hm]
    norm_num
  · rw [stepF_outer hm ht, stepG_outer hm ht]
    norm_num

private theorem FG_measurable (x : ℝ) :
    Measurable fun t => stepF t * stepG (x + t) :=
  stepF_measurable.mul (stepG_measurable.comp (measurable_id.const_add x))

private theorem FG_norm_le (x t : ℝ) : ‖stepF t * stepG (x + t)‖ ≤ 1 := by
  have hf1 := (stepF_range t).1
  have hf2 := (stepF_range t).2
  have hg1 := (stepG_range (x + t)).1
  have hg2 := (stepG_range (x + t)).2
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hf1 hg1)]
  have h1 : stepF t * stepG (x + t) ≤ 1 * stepG (x + t) :=
    mul_le_mul_of_nonneg_right hf2 hg1
  linarith

private theorem FG_integrableOn_Ioc (x a b : ℝ) :
    IntegrableOn (fun t => stepF t * stepG (x + t)) (Ioc a b) volume := by
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ ?_
  · exact (FG_measurable x).aemeasurable.aestronglyMeasurable
  · filter_upwards with t
    exact FG_norm_le x t

private theorem FG_intervalIntegrable (x a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (fun t => stepF t * stepG (x + t)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  exact FG_integrableOn_Ioc x a b

private theorem stepF_intervalIntegrable (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable stepF volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ ?_
  · exact stepF_measurable.aemeasurable.aestronglyMeasurable
  · filter_upwards with t
    have h := stepF_range t
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2

private theorem intervalIntegral_piece_const {a b c : ℝ} {F : ℝ → ℝ} (hab : a ≤ b)
    (h : (Ioo a b).EqOn F fun _ => c) :
    (∫ t in a..b, F t) = (b - a) * c := by
  rw [intervalIntegral.integral_congr_Ioo_of_le hab h, intervalIntegral.integral_const]
  exact smul_eq_mul _ _

private theorem overlap_eq_interval (x : ℝ) :
    continuousOverlap stepF stepG x = ∫ t in (-1 : ℝ)..1, stepF t * stepG (x + t) := by
  unfold continuousOverlap continuousSupportInterval continuousOverlapIntegrand
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]

private theorem stepF_integral : (∫ t : ℝ, stepF t) = 1 := by
  have hset : (∫ t : ℝ, stepF t) = ∫ t in (-1 : ℝ)..1, stepF t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := continuousSupportInterval)
      (fun t ht => stepF_zero_outside t ht)]
    unfold continuousSupportInterval
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hsplit : (∫ t in (-1 : ℝ)..1, stepF t) = (∫ t in (-1 : ℝ)..(-1 / 2), stepF t) +
      ((∫ t in (-1 / 2 : ℝ)..(1 / 2), stepF t) + (∫ t in (1 / 2 : ℝ)..1, stepF t)) := by
    have h1 := intervalIntegral.integral_add_adjacent_intervals
      (stepF_intervalIntegrable (-1) (-1 / 2) (by norm_num))
      (stepF_intervalIntegrable (-1 / 2) 1 (by norm_num))
    have h2 := intervalIntegral.integral_add_adjacent_intervals
      (stepF_intervalIntegrable (-1 / 2) (1 / 2) (by norm_num))
      (stepF_intervalIntegrable (1 / 2) 1 (by norm_num))
    rw [← h1, ← h2]
  have hp1 : (∫ t in (-1 : ℝ)..(-1 / 2), stepF t) = ((-1 / 2) - (-1)) * (1 / 4 : ℝ) := by
    apply intervalIntegral_piece_const (by norm_num)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hmid : t ∉ Icc (-1 / 2 : ℝ) (1 / 2) := by
      intro h
      obtain ⟨a, b⟩ := mem_Icc.mp h
      linarith
    have hsup : t ∈ Icc (-1 : ℝ) 1 := mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact stepF_outer hmid hsup
  have hp2 : (∫ t in (-1 / 2 : ℝ)..(1 / 2), stepF t) = ((1 / 2) - (-1 / 2)) * (3 / 4 : ℝ) := by
    apply intervalIntegral_piece_const (by norm_num)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hmid : t ∈ Icc (-1 / 2 : ℝ) (1 / 2) := mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact stepF_middle hmid
  have hp3 : (∫ t in (1 / 2 : ℝ)..1, stepF t) = (1 - (1 / 2)) * (1 / 4 : ℝ) := by
    apply intervalIntegral_piece_const (by norm_num)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hmid : t ∉ Icc (-1 / 2 : ℝ) (1 / 2) := by
      intro h
      obtain ⟨a, b⟩ := mem_Icc.mp h
      linarith
    have hsup : t ∈ Icc (-1 : ℝ) 1 := mem_Icc.mpr ⟨by linarith, by linarith⟩
    exact stepF_outer hmid hsup
  rw [hset, hsplit, hp1, hp2, hp3]
  norm_num

private theorem step_admissible : ContinuousAdmissible stepF stepG :=
  ⟨stepF_measurable.aemeasurable, stepG_measurable.aemeasurable, stepF_range, stepG_range,
    stepF_zero_outside, stepG_zero_outside, stepFG_complementary, stepF_integral⟩

private theorem overlap_neg (x : ℝ) :
    continuousOverlap stepF stepG (-x) = continuousOverlap stepF stepG x := by
  rw [overlap_eq_interval, overlap_eq_interval]
  have hsub : (∫ t in (-1 : ℝ)..1, stepF t * stepG (-x + t)) =
      (∫ u in (-1 : ℝ)..1, stepF (-u) * stepG (-x + -u)) := by
    have h := intervalIntegral.integral_comp_neg (fun u => stepF (-u) * stepG (-x + -u))
      (a := (-1 : ℝ)) (b := (1 : ℝ))
    simpa using h
  rw [hsub]
  apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
  intro u _
  change stepF (-u) * stepG (-x + -u) = stepF u * stepG (x + u)
  have harg : -x + -u = -(x + u) := by ring
  rw [harg, stepF_neg, stepG_neg]

private theorem overlap_le_of_mem_Icc_zero_half {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    continuousOverlap stepF stepG x ≤ 5 / 12 := by
  have hsplit : (∫ t in (-1 : ℝ)..1, stepF t * stepG (x + t)) =
      (∫ t in (-1 : ℝ)..(-1 / 2 - x), stepF t * stepG (x + t)) +
      ((∫ t in (-1 / 2 - x)..(-1 / 2), stepF t * stepG (x + t)) +
      ((∫ t in (-1 / 2 : ℝ)..(1 / 2 - x), stepF t * stepG (x + t)) +
      ((∫ t in (1 / 2 - x)..(1 / 2), stepF t * stepG (x + t)) +
      ((∫ t in (1 / 2 : ℝ)..(1 - x), stepF t * stepG (x + t)) +
      (∫ t in (1 - x)..1, stepF t * stepG (x + t)))))) := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (-1) (-1 / 2 - x) (by linarith))
      (FG_intervalIntegrable x (-1 / 2 - x) 1 (by linarith))
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (-1 / 2 - x) (-1 / 2) (by linarith))
      (FG_intervalIntegrable x (-1 / 2) 1 (by norm_num))
    have e3 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (-1 / 2) (1 / 2 - x) (by linarith))
      (FG_intervalIntegrable x (1 / 2 - x) 1 (by linarith))
    have e4 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (1 / 2 - x) (1 / 2) (by linarith))
      (FG_intervalIntegrable x (1 / 2) 1 (by norm_num))
    have e5 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (1 / 2) (1 - x) (by linarith))
      (FG_intervalIntegrable x (1 - x) 1 (by linarith))
    rw [← e1, ← e2, ← e3, ← e4, ← e5]
  have hp1 : (∫ t in (-1 : ℝ)..(-1 / 2 - x), stepF t * stepG (x + t)) =
      ((-1 / 2 - x) - (-1)) * (3 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 1 / 4 := by
      refine stepF_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 3 / 4 := by
      refine stepG_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (3 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp2 : (∫ t in (-1 / 2 - x)..(-1 / 2), stepF t * stepG (x + t)) =
      ((-1 / 2) - (-1 / 2 - x)) * (1 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 1 / 4 := by
      refine stepF_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 1 / 4 := by
      apply stepG_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (1 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp3 : (∫ t in (-1 / 2 : ℝ)..(1 / 2 - x), stepF t * stepG (x + t)) =
      ((1 / 2 - x) - (-1 / 2)) * (3 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 3 / 4 := by
      apply stepF_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 1 / 4 := by
      apply stepG_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (3 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp4 : (∫ t in (1 / 2 - x)..(1 / 2), stepF t * stepG (x + t)) =
      ((1 / 2) - (1 / 2 - x)) * (9 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 3 / 4 := by
      apply stepF_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 3 / 4 := by
      refine stepG_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (9 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp5 : (∫ t in (1 / 2 : ℝ)..(1 - x), stepF t * stepG (x + t)) =
      ((1 - x) - (1 / 2)) * (3 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 1 / 4 := by
      refine stepF_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 3 / 4 := by
      refine stepG_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (3 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp6 : (∫ t in (1 - x)..1, stepF t * stepG (x + t)) = ((1 : ℝ) - (1 - x)) * (0 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 1 / 4 := by
      refine stepF_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 0 := by
      apply stepG_zero
      intro h
      obtain ⟨a, b⟩ := mem_Icc.mp h
      linarith
    change stepF t * stepG (x + t) = (0 : ℝ)
    rw [hf, hg]
    norm_num
  rw [overlap_eq_interval, hsplit, hp1, hp2, hp3, hp4, hp5, hp6]
  linarith

private theorem overlap_le_of_mem_Icc_half_one {x : ℝ} (hx0 : 1 / 2 ≤ x) (hx1 : x ≤ 1) :
    continuousOverlap stepF stepG x ≤ 5 / 12 := by
  have hsplit : (∫ t in (-1 : ℝ)..1, stepF t * stepG (x + t)) =
      (∫ t in (-1 : ℝ)..(-1 / 2), stepF t * stepG (x + t)) +
      ((∫ t in (-1 / 2 : ℝ)..(1 / 2 - x), stepF t * stepG (x + t)) +
      ((∫ t in (1 / 2 - x)..(1 - x), stepF t * stepG (x + t)) +
      ((∫ t in (1 - x)..(1 / 2), stepF t * stepG (x + t)) +
      (∫ t in (1 / 2 : ℝ)..1, stepF t * stepG (x + t))))) := by
    have e1 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (-1) (-1 / 2) (by norm_num))
      (FG_intervalIntegrable x (-1 / 2) 1 (by norm_num))
    have e2 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (-1 / 2) (1 / 2 - x) (by linarith))
      (FG_intervalIntegrable x (1 / 2 - x) 1 (by linarith))
    have e3 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (1 / 2 - x) (1 - x) (by linarith))
      (FG_intervalIntegrable x (1 - x) 1 (by linarith))
    have e4 := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (1 - x) (1 / 2) (by linarith))
      (FG_intervalIntegrable x (1 / 2) 1 (by norm_num))
    rw [← e1, ← e2, ← e3, ← e4]
  have hp1 : (∫ t in (-1 : ℝ)..(-1 / 2), stepF t * stepG (x + t)) =
      ((-1 / 2) - (-1)) * (1 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by norm_num)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 1 / 4 := by
      refine stepF_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 1 / 4 := by
      apply stepG_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (1 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp2 : (∫ t in (-1 / 2 : ℝ)..(1 / 2 - x), stepF t * stepG (x + t)) =
      ((1 / 2 - x) - (-1 / 2)) * (3 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 3 / 4 := by
      apply stepF_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 1 / 4 := by
      apply stepG_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (3 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp3 : (∫ t in (1 / 2 - x)..(1 - x), stepF t * stepG (x + t)) =
      ((1 - x) - (1 / 2 - x)) * (9 / 16 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 3 / 4 := by
      apply stepF_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 3 / 4 := by
      refine stepG_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    change stepF t * stepG (x + t) = (9 / 16 : ℝ)
    rw [hf, hg]
    norm_num
  have hp4 : (∫ t in (1 - x)..(1 / 2), stepF t * stepG (x + t)) =
      ((1 / 2 : ℝ) - (1 - x)) * (0 : ℝ) := by
    apply intervalIntegral_piece_const (by linarith)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 3 / 4 := by
      apply stepF_middle
      exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 0 := by
      apply stepG_zero
      intro h
      obtain ⟨a, b⟩ := mem_Icc.mp h
      linarith
    change stepF t * stepG (x + t) = (0 : ℝ)
    rw [hf, hg]
    norm_num
  have hp5 : (∫ t in (1 / 2 : ℝ)..1, stepF t * stepG (x + t)) = ((1 : ℝ) - (1 / 2)) * (0 : ℝ) := by
    apply intervalIntegral_piece_const (by norm_num)
    intro t ht
    obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
    have hf : stepF t = 1 / 4 := by
      refine stepF_outer ?_ ?_
      · intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      · exact mem_Icc.mpr ⟨by linarith, by linarith⟩
    have hg : stepG (x + t) = 0 := by
      apply stepG_zero
      intro h
      obtain ⟨a, b⟩ := mem_Icc.mp h
      linarith
    change stepF t * stepG (x + t) = (0 : ℝ)
    rw [hf, hg]
    norm_num
  rw [overlap_eq_interval, hsplit, hp1, hp2, hp3, hp4, hp5]
  linarith

private theorem stepF_le_three_quarters (t : ℝ) : stepF t ≤ 3 / 4 := by
  unfold stepF
  split
  · norm_num
  · split
    · norm_num
    · norm_num

private theorem Gshift_intervalIntegrable (x a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable (fun t => stepG (x + t)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ ?_
  · exact (stepG_measurable.comp (measurable_id.const_add x)).aemeasurable.aestronglyMeasurable
  · filter_upwards with t
    have h := stepG_range (x + t)
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2

private theorem stepG_intervalIntegrable (a b : ℝ) (hab : a ≤ b) :
    IntervalIntegrable stepG volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  apply Measure.integrableOn_of_bounded (M := 1) measure_Ioc_lt_top.ne ?_ ?_
  · exact stepG_measurable.aemeasurable.aestronglyMeasurable
  · filter_upwards with t
    have h := stepG_range t
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2

private theorem overlap_le_of_mem_Icc_one_two {x : ℝ} (hx0 : 1 ≤ x) (hx1 : x ≤ 2) :
    continuousOverlap stepF stepG x ≤ 5 / 12 := by
  have hsplit : (∫ t in (-1 : ℝ)..1, stepF t * stepG (x + t)) =
      (∫ t in (-1 : ℝ)..(1 - x), stepF t * stepG (x + t)) +
      (∫ t in (1 - x)..1, stepF t * stepG (x + t)) := by
    have e := intervalIntegral.integral_add_adjacent_intervals
      (FG_intervalIntegrable x (-1) (1 - x) (by linarith))
      (FG_intervalIntegrable x (1 - x) 1 (by linarith))
    exact e.symm
  have hzero : (∫ t in (1 - x)..1, stepF t * stepG (x + t)) = 0 := by
    have hmain : (∫ t in (1 - x)..1, stepF t * stepG (x + t)) = (1 - (1 - x)) * (0 : ℝ) := by
      apply intervalIntegral_piece_const (show (1 - x : ℝ) ≤ 1 by linarith)
      intro t ht
      obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
      have hg : stepG (x + t) = 0 := by
        apply stepG_zero
        intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      change stepF t * stepG (x + t) = (0 : ℝ)
      rw [hg, mul_zero]
    rw [hmain]
    exact mul_zero _
  have hmono : (∫ t in (-1 : ℝ)..(1 - x), stepF t * stepG (x + t)) ≤
      (∫ t in (-1 : ℝ)..(1 - x), (3 / 4 : ℝ) * stepG (x + t)) := by
    apply intervalIntegral.integral_mono_on (by linarith)
      (FG_intervalIntegrable x (-1) (1 - x) (by linarith))
      ((Gshift_intervalIntegrable x (-1) (1 - x) (by linarith)).const_mul (3 / 4))
    intro t _
    exact mul_le_mul_of_nonneg_right (stepF_le_three_quarters t) (stepG_range (x + t)).1
  have hsub : (∫ t in (-1 : ℝ)..(1 - x), (3 / 4 : ℝ) * stepG (x + t)) =
      (3 / 4) * (∫ s in (x - 1)..1, stepG s) := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have h := intervalIntegral.integral_comp_add_left (f := stepG) (d := x)
      (a := (-1 : ℝ)) (b := (1 - x))
    rw [show x + -1 = x - 1 by ring, show x + (1 - x) = 1 by ring] at h
    exact h
  have hg01 : (∫ s in (0 : ℝ)..1, stepG s) = 1 / 2 := by
    have hsplit01 : (∫ s in (0 : ℝ)..1, stepG s) =
        (∫ s in (0 : ℝ)..(1 / 2), stepG s) + (∫ s in (1 / 2 : ℝ)..1, stepG s) := by
      have e := intervalIntegral.integral_add_adjacent_intervals
        (stepG_intervalIntegrable 0 (1 / 2) (by norm_num))
        (stepG_intervalIntegrable (1 / 2) 1 (by norm_num))
      exact e.symm
    have hq1 : (∫ s in (0 : ℝ)..(1 / 2), stepG s) = ((1 / 2) - 0) * (1 / 4 : ℝ) := by
      apply intervalIntegral_piece_const (by norm_num)
      intro t ht
      obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
      have hmid : t ∈ Icc (-1 / 2 : ℝ) (1 / 2) := mem_Icc.mpr ⟨by linarith, by linarith⟩
      exact stepG_middle hmid
    have hq2 : (∫ s in (1 / 2 : ℝ)..1, stepG s) = (1 - (1 / 2)) * (3 / 4 : ℝ) := by
      apply intervalIntegral_piece_const (by norm_num)
      intro t ht
      obtain ⟨hlo, hhi⟩ := mem_Ioo.mp ht
      have hmid : t ∉ Icc (-1 / 2 : ℝ) (1 / 2) := by
        intro h
        obtain ⟨a, b⟩ := mem_Icc.mp h
        linarith
      have hsup : t ∈ Icc (-1 : ℝ) 1 := mem_Icc.mpr ⟨by linarith, by linarith⟩
      exact stepG_outer hmid hsup
    rw [hsplit01, hq1, hq2]
    norm_num
  have hsub_le : (∫ s in (x - 1)..1, stepG s) ≤ (∫ s in (0 : ℝ)..1, stepG s) := by
    have hsplitG := intervalIntegral.integral_add_adjacent_intervals
      (stepG_intervalIntegrable 0 (x - 1) (by linarith))
      (stepG_intervalIntegrable (x - 1) 1 (by linarith))
    have hnn : 0 ≤ (∫ s in (0 : ℝ)..(x - 1), stepG s) := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro u _
      exact (stepG_range u).1
    linarith
  have hle : (3 / 4 : ℝ) * (∫ s in (x - 1)..1, stepG s) ≤ (3 / 4) * (1 / 2) :=
    mul_le_mul_of_nonneg_left (hsub_le.trans_eq hg01) (by norm_num)
  rw [overlap_eq_interval, hsplit, hzero, add_zero]
  calc (∫ t in (-1 : ℝ)..(1 - x), stepF t * stepG (x + t))
      ≤ (∫ t in (-1 : ℝ)..(1 - x), (3 / 4 : ℝ) * stepG (x + t)) := hmono
    _ = (3 / 4) * (∫ s in (x - 1)..1, stepG s) := hsub
    _ ≤ (3 / 4) * (1 / 2) := hle
    _ ≤ 5 / 12 := by norm_num

private theorem overlap_le_of_mem_Icc_zero_two {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 2) :
    continuousOverlap stepF stepG x ≤ 5 / 12 := by
  by_cases hxhalf : x ≤ 1 / 2
  · exact overlap_le_of_mem_Icc_zero_half hx0 hxhalf
  · by_cases hxone : x ≤ 1
    · exact overlap_le_of_mem_Icc_half_one (by linarith) hxone
    · exact overlap_le_of_mem_Icc_one_two (by linarith) hx1

/-- **Motzkin–Ralston–Selfridge upper bound $5/12$ for the minimum-overlap constant.** The
continuous Erdős minimum-overlap constant $C_{1b}$ satisfies $C_{1b} \le 5/12$.

Source: Motzkin--Ralston--Selfridge 1956 and Optimization Problems 1b. -/
theorem upperBound_MRS1956_fiveTwelfths_holds : upperBound_MRS1956_fiveTwelfths := by
  refine le_trans (continuousMinimumOverlapConstant_isUniversalLowerBound stepF stepG
    step_admissible) ?_
  apply csSup_le (continuousOverlapValues_nonempty stepF stepG)
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨hx0, hx1⟩ := mem_Icc.mp hx
  by_cases hxnonneg : 0 ≤ x
  · exact overlap_le_of_mem_Icc_zero_two hxnonneg hx1
  · have hnx0 : 0 ≤ -x := by linarith
    have hnx1 : -x ≤ 2 := by linarith
    rw [← overlap_neg x]
    exact overlap_le_of_mem_Icc_zero_two hnx0 hnx1

end MathlibExt.NumberTheory.ErdosMinimumOverlapConstantWanted
