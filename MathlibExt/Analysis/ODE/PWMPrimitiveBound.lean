/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Cast.Order

/-!
# PWM primitive bound

For a pulse-width-modulated signal with carrier period `ε`
and values in `[0, 1]`, the primitive over any interval is
bounded by the duty-scaled envelope: over whole cycles it is
exact, and the constant-duty, ramp, and rational-indicator
cases are computed explicitly. A duty outside `[0, 1]` breaks
the bound. (For varying duty `d` the signal is not itself
periodic; `ε` is the switching-cycle length.)
-/

@[expose] public section

open Set MeasureTheory intervalIntegral
open scoped NNReal

namespace MathlibExt.Analysis.ODE.PWMPrimitiveBound

/-- Left-endpoint-sampled PWM switching signal with carrier (switching-cycle) length
`ε` and duty `d`: on cycle `k = ⌊t / ε⌋`, i.e. (for `0 < ε`) `t ∈ [k ε, (k+1) ε)`, it is `1`
on the first `d (k ε) * ε` of the cycle, `[k ε, k ε + d (k ε) ε)`, and `0` on the remainder.
For varying duty `d` the resulting signal need not be periodic. -/
noncomputable def pwmSignal (ε : ℝ) (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t - (⌊t / ε⌋ : ℝ) * ε < d ((⌊t / ε⌋ : ℝ) * ε) * ε then 1 else 0

/-- Primitive of the switched-minus-averaged discrepancy,
`q(t) = ∫₀ᵗ (s_ε(u) - d(u)) du`. -/
noncomputable def pwmPrimitive (ε : ℝ) (d : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, (pwmSignal ε d u - d u)

/-! ### Private helpers -/

private theorem floor_mul_le_of_pos (t ε : ℝ) (hε : 0 < ε) :
    (⌊t / ε⌋ : ℝ) * ε ≤ t :=
  (le_div_iff₀ hε).mp (Int.floor_le (t / ε))

private theorem lt_floor_add_one_mul_of_pos (t ε : ℝ) (hε : 0 < ε) :
    t < ((⌊t / ε⌋ : ℝ) + 1) * ε :=
  (div_lt_iff₀ hε).mp (Int.lt_floor_add_one (t / ε))

private theorem floor_cast_nonneg (t ε : ℝ) (hε : 0 < ε) (ht : 0 ≤ t) :
    (0 : ℝ) ≤ (⌊t / ε⌋ : ℝ) := by
  exact_mod_cast Int.floor_nonneg.mpr (div_nonneg ht hε.le)

private theorem floor_eq_of_mem_Ico (u ε : ℝ) (k : ℤ) (hε : 0 < ε)
    (hk : u ∈ Ico ((k : ℝ) * ε) (((k : ℝ) + 1) * ε)) :
    ⌊u / ε⌋ = k := by
  rw [Int.floor_eq_iff]
  exact ⟨(le_div_iff₀ hε).mpr hk.1, (div_lt_iff₀ hε).mpr hk.2⟩

private theorem pwmSignal_mem_Icc (ε : ℝ) (d : ℝ → ℝ) (t : ℝ) :
    pwmSignal ε d t ∈ Icc (0 : ℝ) 1 := by
  unfold pwmSignal
  split_ifs <;> simp

private theorem pwmSignal_eq_one (ε : ℝ) (d : ℝ → ℝ) (t : ℝ) (hε : 0 < ε)
    (h : 1 ≤ d ((⌊t / ε⌋ : ℝ) * ε)) : pwmSignal ε d t = 1 := by
  unfold pwmSignal
  have h1 := lt_floor_add_one_mul_of_pos t ε hε
  have h2 : ε ≤ d ((⌊t / ε⌋ : ℝ) * ε) * ε := by nlinarith
  rw [ite_eq_left_iff]
  intro hn
  exact absurd (by nlinarith) hn

private theorem measurable_floor_div (ε : ℝ) : Measurable (fun t : ℝ => ⌊t / ε⌋) := by
  have h : Measurable (Int.floor : ℝ → ℤ) := by
    refine measurable_to_countable' fun k => ?_
    rw [Int.preimage_floor_singleton]
    exact measurableSet_Ico
  exact h.comp (measurable_id.div_const ε)

private theorem measurable_pwmSignal (ε : ℝ) (d : ℝ → ℝ) : Measurable (pwmSignal ε d) := by
  have hfl := measurable_floor_div ε
  have hk : Measurable (fun t : ℝ => ((⌊t / ε⌋ : ℤ) : ℝ)) :=
    (measurable_of_countable (fun k : ℤ => (k : ℝ))).comp hfl
  have hg : Measurable (fun t : ℝ => d ((⌊t / ε⌋ : ℝ) * ε)) :=
    (measurable_of_countable (fun k : ℤ => d ((k : ℝ) * ε))).comp hfl
  unfold pwmSignal
  exact Measurable.ite (measurableSet_lt (measurable_id.sub (hk.mul_const ε)) (hg.mul_const ε))
    measurable_const measurable_const

/-- The PWM signal is interval integrable on every interval: it is measurable and takes values
in `[0, 1]`. -/
theorem intervalIntegrable_pwmSignal (ε : ℝ) (d : ℝ → ℝ) (a b : ℝ) :
    IntervalIntegrable (pwmSignal ε d) volume a b := by
  refine IntervalIntegrable.mono_fun' (g := fun _ => (1 : ℝ)) intervalIntegrable_const
    (measurable_pwmSignal ε d).aestronglyMeasurable (ae_of_all _ fun t => ?_)
  have h := pwmSignal_mem_Icc ε d t
  show ‖pwmSignal ε d t‖ ≤ 1
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [h.1, h.2]

private theorem intervalIntegrable_sub_of_lipschitzOnWith (T ε : ℝ) (Ld : ℝ≥0) (d : ℝ → ℝ)
    (hLip : LipschitzOnWith Ld d (Icc 0 T)) (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ T) :
    IntervalIntegrable (fun u => pwmSignal ε d u - d u) volume a b := by
  refine (intervalIntegrable_pwmSignal ε d a b).sub ?_
  refine (hLip.continuousOn.mono ?_).intervalIntegrable
  rw [uIcc_of_le hab]
  exact fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩

private theorem integral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ∀ u ∈ Ioo a b, f u = g u) : ∫ u in a..b, f u = ∫ u in a..b, g u := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

private theorem integral_id_zero (ε : ℝ) : ∫ u in (0 : ℝ)..ε, u = ε ^ 2 / 2 := by
  have h1 := intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) ε (a := 0) (b := ε)
  simp only [sub_self, sub_zero] at h1
  have h2 : ∫ x in (0 : ℝ)..ε, (ε - x) = ε * ε - ∫ x in (0 : ℝ)..ε, x := by
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      (continuous_id'.intervalIntegrable _ _)]
    simp
  rw [h1] at h2
  nlinarith [h2]

private theorem integral_sub_left_id (a ε : ℝ) :
    ∫ u in a..(a + ε), (u - a) = ε ^ 2 / 2 := by
  have h := intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) a (a := a) (b := a + ε)
  simp only [sub_self, add_sub_cancel_left] at h
  rw [h, integral_id_zero]

/-- On cycle `k`, the signal is the indicator of `[k ε, k ε + d (k ε) ε)`. -/
private theorem pwmSignal_cycle (ε : ℝ) (d : ℝ → ℝ) (k : ℤ) (hε : 0 < ε) (u : ℝ)
    (hu : u ∈ Ico ((k : ℝ) * ε) (((k : ℝ) + 1) * ε)) :
    pwmSignal ε d u = if u < (k : ℝ) * ε + d ((k : ℝ) * ε) * ε then 1 else 0 := by
  unfold pwmSignal
  rw [floor_eq_of_mem_Ico u ε k hε hu]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (by linarith) h2
  · exact absurd (by linarith) h1
  · rfl

/-- Integral of the signal from the start of cycle `k` to a point `x` of that cycle. -/
private theorem integral_pwmSignal_partial (ε : ℝ) (d : ℝ → ℝ) (k : ℤ) (hε : 0 < ε)
    (hdk : d ((k : ℝ) * ε) ∈ Icc 0 1) (x : ℝ)
    (hx : x ∈ Icc ((k : ℝ) * ε) (((k : ℝ) + 1) * ε)) :
    ∫ u in ((k : ℝ) * ε)..x, pwmSignal ε d u =
      min (x - (k : ℝ) * ε) (d ((k : ℝ) * ε) * ε) := by
  have hcε0 : 0 ≤ d ((k : ℝ) * ε) * ε := mul_nonneg hdk.1 hε.le
  have hb : ((k : ℝ) + 1) * ε = (k : ℝ) * ε + ε := by ring
  have hsig : ∀ u ∈ Ioo ((k : ℝ) * ε) x, pwmSignal ε d u =
      if u < (k : ℝ) * ε + d ((k : ℝ) * ε) * ε then 1 else 0 := fun u hu =>
    pwmSignal_cycle ε d k hε u ⟨hu.1.le, lt_of_lt_of_le hu.2 hx.2⟩
  by_cases hxm : x ≤ (k : ℝ) * ε + d ((k : ℝ) * ε) * ε
  · rw [integral_congr_Ioo hx.1 (g := fun _ => (1 : ℝ)) (fun u hu => by
      rw [hsig u hu]
      simp [lt_of_lt_of_le hu.2 hxm])]
    rw [intervalIntegral.integral_const, smul_eq_mul, mul_one, min_eq_left (by linarith)]
  · replace hxm := (not_le.mp hxm)
    have ham : (k : ℝ) * ε ≤ (k : ℝ) * ε + d ((k : ℝ) * ε) * ε := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (b := (k : ℝ) * ε + d ((k : ℝ) * ε) * ε)
      (intervalIntegrable_pwmSignal ε d _ _) (intervalIntegrable_pwmSignal ε d _ _)]
    rw [integral_congr_Ioo ham (g := fun _ => (1 : ℝ)) (fun u hu => by
      rw [hsig u ⟨hu.1, hu.2.trans hxm⟩]
      simp [hu.2])]
    rw [integral_congr_Ioo hxm.le (g := fun _ => (0 : ℝ)) (fun u hu => by
      rw [hsig u ⟨ham.trans_lt hu.1, hu.2⟩]
      simp [not_lt.mpr hu.1.le])]
    rw [intervalIntegral.integral_const, intervalIntegral.integral_const, smul_eq_mul,
      smul_eq_mul, mul_one, mul_zero, add_zero, min_eq_right (by linarith)]
    ring

private theorem integral_pwmSignal_cycle_aux (ε : ℝ) (d : ℝ → ℝ) (k : ℤ) (hε : 0 < ε)
    (hdk : d (k * ε) ∈ Icc 0 1) :
    ∫ u in (k * ε : ℝ)..((k + 1) * ε), pwmSignal ε d u = d (k * ε) * ε := by
  have hb : ((k : ℝ) + 1) * ε = (k : ℝ) * ε + ε := by ring
  rw [integral_pwmSignal_partial ε d k hε hdk _ ⟨by linarith, le_rfl⟩, hb,
    add_sub_cancel_left, min_eq_right (by nlinarith [hdk.2])]

private theorem abs_pwmPrimitive_cycle_le_aux (T ε : ℝ) (Ld : ℝ≥0) (d : ℝ → ℝ) (k : ℕ)
    (hε : 0 < ε) (hd : ∀ t ∈ Icc 0 T, d t ∈ Icc 0 1) (hLip : LipschitzOnWith Ld d (Icc 0 T))
    (hk : ((k : ℝ) + 1) * ε ≤ T) :
    |∫ u in (k * ε : ℝ)..((k + 1) * ε), (pwmSignal ε d u - d u)| ≤ (Ld : ℝ) * ε ^ 2 / 2 := by
  have hε0 := hε.le
  have ha0 : 0 ≤ (k : ℝ) * ε := mul_nonneg (Nat.cast_nonneg k) hε0
  have hb : ((k : ℝ) + 1) * ε = (k : ℝ) * ε + ε := by ring
  have hab : (k : ℝ) * ε ≤ ((k : ℝ) + 1) * ε := by linarith
  have hsub : Icc ((k : ℝ) * ε) (((k : ℝ) + 1) * ε) ⊆ Icc 0 T :=
    fun x hx => ⟨ha0.trans hx.1, hx.2.trans hk⟩
  have haT : (k : ℝ) * ε ∈ Icc 0 T := hsub ⟨le_rfl, hab⟩
  have hdk := hd _ haT
  have hcyc := integral_pwmSignal_cycle_aux ε d (k : ℤ) hε (by simpa using hdk)
  push_cast at hcyc
  have hdint : IntervalIntegrable d volume ((k : ℝ) * ε) (((k : ℝ) + 1) * ε) :=
    (hLip.continuousOn.mono (by rw [uIcc_of_le hab]; exact hsub)).intervalIntegrable
  rw [intervalIntegral.integral_sub (intervalIntegrable_pwmSignal ε d _ _) hdint, hcyc]
  have hconst : d ((k : ℝ) * ε) * ε =
      ∫ _ in ((k : ℝ) * ε)..(((k : ℝ) + 1) * ε), d ((k : ℝ) * ε) := by
    rw [intervalIntegral.integral_const, smul_eq_mul, hb]
    ring
  rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const hdint]
  have hle := intervalIntegral.norm_integral_le_of_norm_le hab (μ := volume)
    (f := fun u => d ((k : ℝ) * ε) - d u) (g := fun u => (Ld : ℝ) * (u - (k : ℝ) * ε))
    (ae_of_all _ fun u hu => by
      have h := hLip.dist_le_mul _ haT u (hsub ⟨hu.1.le, hu.2⟩)
      rw [Real.dist_eq, Real.dist_eq, abs_sub_comm ((k : ℝ) * ε) u,
        abs_of_nonneg (a := u - (k : ℝ) * ε) (by linarith [hu.1])] at h
      rw [Real.norm_eq_abs]
      exact h)
    ((continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _)
  rw [Real.norm_eq_abs] at hle
  refine hle.trans (le_of_eq ?_)
  rw [intervalIntegral.integral_const_mul, hb, integral_sub_left_id]
  ring

private theorem abs_pwmPrimitive_partialCycle_le_aux (T ε : ℝ) (d : ℝ → ℝ) (hε : 0 < ε)
    (hd : ∀ t ∈ Icc 0 T, d t ∈ Icc 0 1) (t : ℝ) (ht : t ∈ Icc 0 T) :
    |∫ u in ((⌊t / ε⌋ : ℝ) * ε)..t, (pwmSignal ε d u - d u)| ≤ ε := by
  have ha := floor_mul_le_of_pos t ε hε
  have hb := lt_floor_add_one_mul_of_pos t ε hε
  have hb' : ((⌊t / ε⌋ : ℝ) + 1) * ε = (⌊t / ε⌋ : ℝ) * ε + ε := by ring
  have ha0 : 0 ≤ (⌊t / ε⌋ : ℝ) * ε := mul_nonneg (floor_cast_nonneg t ε hε ht.1) hε.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := 1)
    (f := fun u => pwmSignal ε d u - d u) (a := (⌊t / ε⌋ : ℝ) * ε) (b := t) (fun u hu => by
      rw [uIoc_of_le ha] at hu
      have hu' : u ∈ Icc 0 T := ⟨by linarith [hu.1], by linarith [hu.2, ht.2]⟩
      have hs := pwmSignal_mem_Icc ε d u
      have hdu := hd u hu'
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2, hdu.1, hdu.2])
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ha), one_mul] at h
  exact h.trans (by linarith)

private theorem pwmPrimitive_const_natCast_mul_aux (ε c : ℝ) (n : ℕ) (hε : 0 < ε)
    (hc : c ∈ Icc 0 1) :
    pwmPrimitive ε (fun _ => c) (n * ε) = 0 := by
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u => pwmSignal ε (fun _ => c) u - c) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) * ε) (n := n)
    (fun k _ => (intervalIntegrable_pwmSignal ε _ _ _).sub intervalIntegrable_const)
  simp only [Nat.cast_zero, zero_mul] at hsum
  simp only [pwmPrimitive]
  rw [← hsum]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [intervalIntegral.integral_sub (intervalIntegrable_pwmSignal ε _ _ _)
    intervalIntegrable_const]
  have h := integral_pwmSignal_cycle_aux ε (fun _ => c) (k : ℤ) hε hc
  push_cast at h
  rw [Nat.cast_succ, h, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- For a rational period, the rational-indicator duty is sampled at rationals only. -/
private theorem pwmSignal_ratIndicator (q : ℚ) (hq : 0 < q) (u : ℝ) :
    pwmSignal (q : ℝ) ((range ((↑) : ℚ → ℝ)).indicator 1) u = 1 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine pwmSignal_eq_one _ _ u hq' (le_of_eq ?_)
  rw [indicator_of_mem]
  · rfl
  · exact ⟨(⌊u / q⌋ : ℚ) * q, by push_cast; rfl⟩

/-! ### Headline -/

/-- **PWM averaging bound.** For `ε > 0`, `T ≥ 0` and an `Ld`-Lipschitz duty `d` with values in
`[0, 1]` on `[0, T]`, the primitive of `s_ε - d` satisfies `|q(t)| ≤ ε (1 + Ld T / 2)` for every
`t ∈ [0, T]`, including times inside a partial final cycle. -/
theorem abs_pwmPrimitive_le (T ε : ℝ) (Ld : ℝ≥0) (d : ℝ → ℝ) (hT : 0 ≤ T) (hε : 0 < ε)
    (hd : ∀ t ∈ Icc 0 T, d t ∈ Icc 0 1) (hLip : LipschitzOnWith Ld d (Icc 0 T))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    |pwmPrimitive ε d t| ≤ ε * (1 + (Ld : ℝ) * T / 2) := by
  have hε0 := hε.le
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = ⌊t / ε⌋ :=
    ⟨(⌊t / ε⌋).toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (div_nonneg ht.1 hε0))⟩
  have hNR : (N : ℝ) = (⌊t / ε⌋ : ℝ) := by rw [← hN]; push_cast; rfl
  have hNt : (N : ℝ) * ε ≤ t := by rw [hNR]; exact floor_mul_le_of_pos t ε hε
  have hN0 : 0 ≤ (N : ℝ) * ε := mul_nonneg (Nat.cast_nonneg N) hε0
  have hint := intervalIntegrable_sub_of_lipschitzOnWith T ε Ld d hLip
  have hsplit : pwmPrimitive ε d t =
      (∫ u in (0 : ℝ)..(N : ℝ) * ε, (pwmSignal ε d u - d u)) +
        ∫ u in (N : ℝ) * ε..t, (pwmSignal ε d u - d u) := by
    unfold pwmPrimitive
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hint 0 _ le_rfl hN0 (hNt.trans ht.2)) (hint _ t hN0 hNt ht.2)]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u => pwmSignal ε d u - d u) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) * ε) (n := N) (fun k hk => by
      have hk1 : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hk
      exact hint _ _ (mul_nonneg (Nat.cast_nonneg k) hε0)
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ k) hε0)
        ((mul_le_mul_of_nonneg_right hk1 hε0).trans (hNt.trans ht.2)))
  simp only [Nat.cast_zero, zero_mul] at hsum
  have hterm : ∀ k ∈ Finset.range N,
      |∫ u in (k : ℝ) * ε..((k + 1 : ℕ) : ℝ) * ε, (pwmSignal ε d u - d u)| ≤
        (Ld : ℝ) * ε ^ 2 / 2 := by
    intro k hk
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Finset.mem_range.mp hk
    have h := abs_pwmPrimitive_cycle_le_aux T ε Ld d k hε hd hLip
      (by push_cast at hk1; exact (mul_le_mul_of_nonneg_right hk1 hε0).trans (hNt.trans ht.2))
    push_cast
    exact h
  have hA : |∫ u in (0 : ℝ)..(N : ℝ) * ε, (pwmSignal ε d u - d u)| ≤
      (N : ℝ) * ((Ld : ℝ) * ε ^ 2 / 2) := by
    rw [← hsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    simp
  have hB : |∫ u in (N : ℝ) * ε..t, (pwmSignal ε d u - d u)| ≤ ε := by
    rw [hNR]
    exact abs_pwmPrimitive_partialCycle_le_aux T ε d hε hd t ht
  have hLd : 0 ≤ (Ld : ℝ) * ε / 2 := by positivity
  have hNT := mul_le_mul_of_nonneg_right (hNt.trans ht.2) hLd
  rw [hsplit]
  refine (abs_add_le _ _).trans ?_
  nlinarith [hA, hB, hNT]

/-! ### Complete cycles and the partial final cycle -/

/-- Over a complete cycle the switch is on for exactly `d (k ε) * ε`. -/
theorem integral_pwmSignal_cycle (ε : ℝ) (d : ℝ → ℝ) (k : ℤ) (hε : 0 < ε)
    (hdk : d (k * ε) ∈ Icc 0 1) :
    ∫ u in (k * ε : ℝ)..((k + 1) * ε), pwmSignal ε d u = d (k * ε) * ε := by
  exact integral_pwmSignal_cycle_aux ε d k hε hdk

/-- Complete-cycle discrepancy: a cycle `[k ε, (k+1) ε] ⊆ [0, T]` contributes at most
`Ld ε² / 2` to the primitive. -/
theorem abs_pwmPrimitive_cycle_le (T ε : ℝ) (Ld : ℝ≥0) (d : ℝ → ℝ) (k : ℕ) (hε : 0 < ε)
    (hd : ∀ t ∈ Icc 0 T, d t ∈ Icc 0 1) (hLip : LipschitzOnWith Ld d (Icc 0 T))
    (hk : ((k : ℝ) + 1) * ε ≤ T) :
    |∫ u in (k * ε : ℝ)..((k + 1) * ε), (pwmSignal ε d u - d u)| ≤ (Ld : ℝ) * ε ^ 2 / 2 := by
  exact abs_pwmPrimitive_cycle_le_aux T ε Ld d k hε hd hLip hk

/-- Partial final cycle: from the start `⌊t / ε⌋ ε` of the cycle containing `t ∈ [0, T]` up to
`t`, the discrepancy integral is at most `ε` in absolute value. -/
theorem abs_pwmPrimitive_partialCycle_le (T ε : ℝ) (d : ℝ → ℝ) (hε : 0 < ε)
    (hd : ∀ t ∈ Icc 0 T, d t ∈ Icc 0 1)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    |∫ u in ((⌊t / ε⌋ : ℝ) * ε)..t, (pwmSignal ε d u - d u)| ≤ ε := by
  exact abs_pwmPrimitive_partialCycle_le_aux T ε d hε hd t ht

/-! ### Constant duty (`Ld = 0`) -/

/-- The headline at `Ld = 0`: a constant duty `c ∈ [0, 1]` gives `|q(t)| ≤ ε` on `[0, T]`. -/
theorem abs_pwmPrimitive_le_of_const (T ε c : ℝ) (hT : 0 ≤ T) (hε : 0 < ε) (hc : c ∈ Icc 0 1)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    |pwmPrimitive ε (fun _ => c) t| ≤ ε * (1 + ((0 : ℝ≥0) : ℝ) * T / 2) := by
  exact abs_pwmPrimitive_le T ε 0 (fun _ => c) hT hε (fun _ _ => hc)
    (LipschitzWith.const c).lipschitzOnWith t ht

/-- Sharp constant-duty envelope: `0 ≤ q(t) ≤ c (1 - c) ε` for all `t ≥ 0`. -/
theorem pwmPrimitive_const_mem_Icc (ε c t : ℝ) (hε : 0 < ε) (hc : c ∈ Icc 0 1) (ht : 0 ≤ t) :
    pwmPrimitive ε (fun _ => c) t ∈ Icc 0 (c * (1 - c) * ε) := by
  have hε0 := hε.le
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (N : ℤ) = ⌊t / ε⌋ :=
    ⟨(⌊t / ε⌋).toNat, Int.toNat_of_nonneg (Int.floor_nonneg.mpr (div_nonneg ht hε0))⟩
  have hNR : (N : ℝ) = (⌊t / ε⌋ : ℝ) := by rw [← hN]; push_cast; rfl
  have ha := floor_mul_le_of_pos t ε hε
  have hb := lt_floor_add_one_mul_of_pos t ε hε
  have hb' : ((⌊t / ε⌋ : ℝ) + 1) * ε = (⌊t / ε⌋ : ℝ) * ε + ε := by ring
  have hq0 : pwmPrimitive ε (fun _ => c) ((⌊t / ε⌋ : ℝ) * ε) = 0 := by
    rw [← hNR]
    exact pwmPrimitive_const_natCast_mul_aux ε c N hε hc
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => pwmSignal ε (fun _ => c) u - c)
      volume a b := fun a b => (intervalIntegrable_pwmSignal ε _ a b).sub intervalIntegrable_const
  have hsplit : pwmPrimitive ε (fun _ => c) t =
      pwmPrimitive ε (fun _ => c) ((⌊t / ε⌋ : ℝ) * ε) +
        ∫ u in ((⌊t / ε⌋ : ℝ) * ε)..t, (pwmSignal ε (fun _ => c) u - c) := by
    simp only [pwmPrimitive]
    rw [intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)]
  have hpart := integral_pwmSignal_partial ε (fun _ => c) ⌊t / ε⌋ hε hc t ⟨ha, hb.le⟩
  rw [hsplit, hq0, zero_add, intervalIntegral.integral_sub (intervalIntegrable_pwmSignal ε _ _ _)
    intervalIntegrable_const, hpart, intervalIntegral.integral_const, smul_eq_mul]
  have hr0 : 0 ≤ t - (⌊t / ε⌋ : ℝ) * ε := sub_nonneg.mpr ha
  have hrε : t - (⌊t / ε⌋ : ℝ) * ε < ε := by linarith
  have hc0 := hc.1
  have hc1 := hc.2
  rcases min_cases (t - (⌊t / ε⌋ : ℝ) * ε) (c * ε) with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1]
    constructor
    · nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hc1)]
    · nlinarith [mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr hc1)]
  · rw [h1]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hrε.le hc0]
    · nlinarith [mul_le_mul_of_nonneg_left h2.le hc0]

/-- A constant duty has zero discrepancy at every cycle end `n ε`. -/
theorem pwmPrimitive_const_natCast_mul (ε c : ℝ) (n : ℕ) (hε : 0 < ε) (hc : c ∈ Icc 0 1) :
    pwmPrimitive ε (fun _ => c) (n * ε) = 0 := by
  exact pwmPrimitive_const_natCast_mul_aux ε c n hε hc

/-! ### Validation cases -/

/-- Duty `0`: the switch is always off. -/
theorem pwmSignal_zero (ε t : ℝ) (hε : 0 < ε) : pwmSignal ε (fun _ => 0) t = 0 := by
  have h := floor_mul_le_of_pos t ε hε
  unfold pwmSignal
  rw [ite_eq_right_iff]
  intro hlt
  exfalso
  linarith

/-- Duty `1`: the switch is always on. -/
theorem pwmSignal_one (ε t : ℝ) (hε : 0 < ε) : pwmSignal ε (fun _ => 1) t = 1 := by
  exact pwmSignal_eq_one ε _ t hε le_rfl

/-- Duty `0` has zero discrepancy. -/
theorem pwmPrimitive_zero (ε t : ℝ) (hε : 0 < ε) : pwmPrimitive ε (fun _ => 0) t = 0 := by
  have h : ∀ u, pwmSignal ε (fun _ => (0 : ℝ)) u = 0 := fun u => pwmSignal_zero ε u hε
  simp [pwmPrimitive, h]

/-- Duty `1` has zero discrepancy. -/
theorem pwmPrimitive_one (ε t : ℝ) (hε : 0 < ε) : pwmPrimitive ε (fun _ => 1) t = 0 := by
  have h : ∀ u, pwmSignal ε (fun _ => (1 : ℝ)) u = 1 := fun u => pwmSignal_one ε u hε
  simp [pwmPrimitive, h]

/-- Partial final cycle with fractional duty: `ε = 1`, `d = 1/2`, `t = 1/2` (inside the first
cycle, at the end of the on-interval) gives `q = 1/2 - 1/4 = 1/4 = c (1 - c) ε`. -/
theorem pwmPrimitive_half_half : pwmPrimitive 1 (fun _ => 1 / 2) (1 / 2) = 1 / 4 := by
  have hpart := integral_pwmSignal_partial 1 (fun _ => 1 / 2) 0 one_pos
    ⟨by norm_num, by norm_num⟩ (1 / 2) ⟨by norm_num, by norm_num⟩
  simp only [Int.cast_zero, zero_mul] at hpart
  unfold pwmPrimitive
  rw [intervalIntegral.integral_sub (intervalIntegrable_pwmSignal _ _ _ _)
    intervalIntegrable_const, hpart, intervalIntegral.integral_const, smul_eq_mul]
  norm_num

/-- Varying Lipschitz duty: `ε = 1`, `T = 2`, `d(u) = u / 2` (`Ld = 1/2`). Each of the two cycles
contributes `-Ld ε² / 2 = -1/4`, so `q(2) = -1/2`, within the headline bound `3/2`. -/
theorem pwmPrimitive_ramp : pwmPrimitive 1 (fun u => u / 2) 2 = -1 / 2 := by
  have h0 := integral_pwmSignal_cycle_aux 1 (fun u => u / 2) 0 one_pos
    ⟨by norm_num, by norm_num⟩
  have h1 := integral_pwmSignal_cycle_aux 1 (fun u => u / 2) 1 one_pos
    ⟨by norm_num, by norm_num⟩
  norm_num at h0 h1
  have hsig : ∫ u in (0 : ℝ)..2, pwmSignal 1 (fun u => u / 2) u = 1 / 2 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
      (intervalIntegrable_pwmSignal _ _ _ _) (intervalIntegrable_pwmSignal _ _ _ _)]
    norm_num [h0, h1]
  have hd : ∫ u in (0 : ℝ)..2, u / 2 = 1 := by
    rw [intervalIntegral.integral_div, integral_id_zero]
    norm_num
  unfold pwmPrimitive
  rw [intervalIntegral.integral_sub (intervalIntegrable_pwmSignal _ _ _ _)
    ((continuous_id'.div_const 2).intervalIntegrable _ _), hsig, hd]
  norm_num

/-- Rapidly discontinuous duty: the indicator of the rationals (values in `[0,1]`, Lipschitz on
no nontrivial interval). For rational `ε > 0` every sample `k ε` is rational, so the switch is
always on while `d = 0` almost everywhere, and `q(t) = t`. -/
theorem pwmPrimitive_ratIndicator (q : ℚ) (hq : 0 < q) (t : ℝ) (ht : 0 ≤ t) :
    pwmPrimitive (q : ℝ) ((range ((↑) : ℚ → ℝ)).indicator 1) t = t := by
  have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ∉ range ((↑) : ℚ → ℝ) :=
    measure_eq_zero_iff_ae_notMem.mp ((countable_range _).measure_zero volume)
  unfold pwmPrimitive
  rw [intervalIntegral.integral_congr_ae (g := fun _ => (1 : ℝ)) (hnull.mono fun x hx _ => by
    rw [pwmSignal_ratIndicator q hq x, indicator_of_notMem hx]
    simp)]
  simp

/-- For the rational-indicator duty no bound of the headline's form `ε (1 + L T / 2)` holds:
for every `L` some period `ε > 0` violates it at `T = t = 1`. -/
theorem exists_lt_abs_pwmPrimitive_ratIndicator (L : ℝ≥0) :
    ∃ ε : ℝ, 0 < ε ∧ ε * (1 + (L : ℝ) * 1 / 2) <
      |pwmPrimitive ε ((range ((↑) : ℚ → ℝ)).indicator 1) 1| := by
  have hpos : (0 : ℝ) < 1 + (L : ℝ) * 1 / 2 := by positivity
  obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (div_pos one_pos hpos)
  have hq : (0 : ℚ) < q := by exact_mod_cast hq0
  refine ⟨q, hq0, ?_⟩
  rw [pwmPrimitive_ratIndicator q hq 1 zero_le_one, abs_one]
  exact (lt_div_iff₀ hpos).mp hq1

/-- Duty outside `[0, 1]`: the constant duty `2` (`Ld = 0`) keeps the switch on and gives
`q(t) = -t`, so the range hypothesis cannot be dropped. -/
theorem pwmPrimitive_two (ε t : ℝ) (hε : 0 < ε) : pwmPrimitive ε (fun _ => 2) t = -t := by
  have h : ∀ u, pwmSignal ε (fun _ => (2 : ℝ)) u = 1 := fun u =>
    pwmSignal_eq_one ε _ u hε (by norm_num)
  simp [pwmPrimitive, h]
  ring

end MathlibExt.Analysis.ODE.PWMPrimitiveBound
