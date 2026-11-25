/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.WeakParabolic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped ContDiff
open Filter
open Set

namespace EarthScience

/-- The quadratic profile `x * (1 - x)` is a `WeakH10` function. -/
noncomputable def quadWeak : WeakH10 where
  toFun := fun x => x * (1 - x)
  weakDeriv := fun x => 1 - 2 * x
  weakDeriv_memLp := by
    refine MemLp.of_bound ?_ 2 ?_
    · exact (continuous_const.sub (continuous_const.mul continuous_id)).aestronglyMeasurable
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Icc).mpr ?_
      filter_upwards with x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : x ≤ 1 := hx.2
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
  toFun_eq_integral := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s => s - s ^ 2) (1 - 2 * t) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact h1.sub h2
    have hcont : Continuous (fun t => (1 : ℝ) - 2 * t) :=
      continuous_const.sub (continuous_const.mul continuous_id)
    intro x hx
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 x)]
    ring
  integral_weakDeriv_eq_zero := by
    have hderiv : ∀ t : ℝ, HasDerivAt (fun s => s - s ^ 2) (1 - 2 * t) t := by
      intro t
      have h1 : HasDerivAt (fun s : ℝ => s) 1 t := hasDerivAt_id t
      have h2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using hasDerivAt_pow 2 t
      exact h1.sub h2
    have hcont : Continuous (fun t => (1 : ℝ) - 2 * t) :=
      continuous_const.sub (continuous_const.mul continuous_id)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
      (hcont.intervalIntegrable 0 1)]
    norm_num

example : quadWeak.weakDeriv 0 = 1 := by simp [quadWeak]
example : quadWeak.toFun 0 = 0 := by simp [quadWeak]

/-- The zero function is a `WeakH10` function (boundary case). -/
noncomputable def zeroWeak : WeakH10 where
  toFun := fun _ => 0
  weakDeriv := fun _ => 0
  weakDeriv_memLp := by simp
  toFun_eq_integral := by
    intro x _
    simp
  integral_weakDeriv_eq_zero := by simp

example : zeroWeak.toFun 0 = 0 := rfl
example : zeroWeak.weakDeriv 1 = 0 := rfl

/-- Fubini bridge on the constant function over the unit square. -/
instance : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  constructor
  rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
  simp [Real.volume_Icc]

example : (∫ _t in (0 : ℝ)..1, ∫ _x in (0 : ℝ)..1, (1 : ℝ))
    = ∫ _p in Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1, (1 : ℝ)
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)) := by
  exact iterated_eq_product (by norm_num) _ (integrable_const _)

/-! ## The time-continuity field and the energy identity -/

/-- A solution of the homogeneous equation that is nonzero only at the time `ts`, where its
profile is `x (1 - x)`. -/
noncomputable def spikeW (ts t x : ℝ) : ℝ := if t = ts then x * (1 - x) else 0

/-- The weak derivative of `spikeW`. -/
noncomputable def spikeWx (ts t x : ℝ) : ℝ := if t = ts then 1 - 2 * x else 0

lemma spike_profile (ts : ℝ) :
    ∀ t, ∃ h : WeakH10, h.toFun = spikeW ts t ∧ h.weakDeriv = spikeWx ts t := by
  intro t
  by_cases ht : t = ts
  · refine ⟨quadWeak, ?_, ?_⟩ <;> funext x <;> simp [spikeW, spikeWx, ht, quadWeak]
  · refine ⟨zeroWeak, ?_, ?_⟩ <;> funext x <;> simp [spikeW, spikeWx, ht, zeroWeak]

lemma rect_isFiniteMeasure (t0 t1 : ℝ) :
    IsFiniteMeasure (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (isCompact_Icc.prod isCompact_Icc).measure_lt_top⟩

lemma quad_memLp : MemLp (fun x : ℝ => x * (1 - x)) 2 (volume.restrict (Set.Icc 0 1)) := by
  refine MemLp.of_bound (by fun_prop : Continuous fun x : ℝ => x * (1 - x)).aestronglyMeasurable 1
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun x hx => ?_))
  obtain ⟨hx0, hx1⟩ := hx
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

lemma spike_slice_memLp (ts t : ℝ) :
    MemLp (fun x => spikeW ts t x) 2 (volume.restrict (Set.Icc 0 1)) := by
  by_cases ht : t = ts
  · simpa [spikeW, ht] using quad_memLp
  · simp [spikeW, ht]

lemma spike_memLp (t0 t1 ts : ℝ) :
    MemLp (Function.uncurry (spikeW ts)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
      ∧ MemLp (Function.uncurry (spikeWx ts)) 2
        (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)) := by
  have := rect_isFiniteMeasure t0 t1
  have hS : MeasurableSet {p : ℝ × ℝ | p.1 = ts} :=
    (measurableSet_singleton ts).preimage measurable_fst
  have hR : MeasurableSet (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1) :=
    measurableSet_Icc.prod measurableSet_Icc
  constructor
  · have hm : Measurable (Function.uncurry (spikeW ts)) :=
      Measurable.ite hS (by fun_prop) measurable_const
    refine MemLp.of_bound hm.aestronglyMeasurable 1 ((ae_restrict_iff' hR).mpr
      (Eventually.of_forall fun p hp => ?_))
    obtain ⟨-, hx0, hx1⟩ : p.1 ∈ Set.Icc t0 t1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := ⟨hp.1, hp.2.1, hp.2.2⟩
    simp only [Function.uncurry, spikeW]
    split_ifs
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith
    · simp
  · have hm : Measurable (Function.uncurry (spikeWx ts)) :=
      Measurable.ite hS (by fun_prop) measurable_const
    refine MemLp.of_bound hm.aestronglyMeasurable 1 ((ae_restrict_iff' hR).mpr
      (Eventually.of_forall fun p hp => ?_))
    obtain ⟨-, hx0, hx1⟩ : p.1 ∈ Set.Icc t0 t1 ∧ 0 ≤ p.2 ∧ p.2 ≤ 1 := ⟨hp.1, hp.2.1, hp.2.2⟩
    simp only [Function.uncurry, spikeWx]
    split_ifs
    · rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    · simp

/-- An iterated integral whose inner integral vanishes off one time is zero. -/
lemma integral_eq_zero_of_ne_time {a b ts : ℝ} (g : ℝ → ℝ)
    (hg : ∀ t, t ≠ ts → g t = 0) : ∫ t in a..b, g t = 0 := by
  have hae : ∀ᵐ t ∂volume, t ∈ Set.uIoc a b → g t = (0 : ℝ → ℝ) t := by
    have hne : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ ts := by
      rw [ae_iff]
      have hset : {t : ℝ | ¬t ≠ ts} = {ts} := by
        ext t
        simp
      rw [hset, measure_singleton]
    filter_upwards [hne] with t ht _
    exact hg t ht
  rw [intervalIntegral.integral_congr_ae hae]
  simp

lemma spike_weak {t0 t1 ts : ℝ} (κ φ : ℝ → ℝ → ℝ) :
    ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
        (-spikeW ts t x * deriv (fun s => φ s x) t
          + κ t x * spikeWx ts t x * deriv (fun y => φ t y) x)
      = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, (0 : ℝ → ℝ → ℝ) t x * φ t x := by
  rw [integral_eq_zero_of_ne_time (ts := ts) _ fun t ht => by simp [spikeW, spikeWx, ht]]
  simp

lemma quad_eLpNorm_ne_zero :
    (eLpNorm (fun x : ℝ => x * (1 - x)) 2 (volume.restrict (Set.Icc 0 1))).toReal ≠ 0 := by
  intro h
  have h0 : eLpNorm (fun x : ℝ => x * (1 - x)) 2 (volume.restrict (Set.Icc 0 1)) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right quad_memLp.eLpNorm_ne_top
  have hae := (eLpNorm_eq_zero_iff two_ne_zero).mp h0
  have heq := Measure.eqOn_Icc_of_ae_eq (μ := volume) zero_ne_one hae
    (by fun_prop : Continuous fun x : ℝ => x * (1 - x)).continuousOn continuousOn_const
  have := heq (show (1 / 2 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  norm_num at this

lemma spike_not_continuous {t0 t1 ts : ℝ} (h0 : t0 ≤ ts) (h1 : ts < t1) :
    ¬ Filter.Tendsto
      (fun t => (eLpNorm (fun x => spikeW ts t x - spikeW ts ts x) 2
        (volume.restrict (Set.Icc 0 1))).toReal) (nhdsWithin ts (Set.Icc t0 t1)) (nhds 0) := by
  intro hT
  have := left_nhdsWithin_Ioo_neBot h1
  have hconst : ∀ t ∈ Set.Ioo ts t1,
      (eLpNorm (fun x => spikeW ts t x - spikeW ts ts x) 2
        (volume.restrict (Set.Icc 0 1))).toReal
        = (eLpNorm (fun x : ℝ => x * (1 - x)) 2 (volume.restrict (Set.Icc 0 1))).toReal := by
    intro t ht
    have hne : t ≠ ts := ne_of_gt ht.1
    have hfun : (fun x => spikeW ts t x - spikeW ts ts x) = -(fun x : ℝ => x * (1 - x)) := by
      funext x
      simp [spikeW, hne]
    rw [hfun, eLpNorm_neg]
  have hT' := hT.mono_left (nhdsWithin_mono ts
    (fun t ht => ⟨h0.trans ht.1.le, ht.2.le⟩ : Set.Ioo ts t1 ⊆ Set.Icc t0 t1))
  have hc : Filter.Tendsto (fun t => (eLpNorm (fun x => spikeW ts t x - spikeW ts ts x) 2
        (volume.restrict (Set.Icc 0 1))).toReal) (nhdsWithin ts (Set.Ioo ts t1))
      (nhds (eLpNorm (fun x : ℝ => x * (1 - x)) 2 (volume.restrict (Set.Icc 0 1))).toReal) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hconst t ht).symm)
  exact quad_eLpNorm_ne_zero (tendsto_nhds_unique hc hT')

lemma spike_energy_ne {t0 ts : ℝ} (h0 : t0 < ts) (κ : ℝ → ℝ → ℝ) :
    (eLpNorm (fun x => spikeW ts ts x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
        + 2 * ∫ t in t0..ts, ∫ x in (0 : ℝ)..1, κ t x * (spikeWx ts t x) ^ 2
      ≠ (eLpNorm (fun x => spikeW ts t0 x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 := by
  have hdiss : (∫ t in t0..ts, ∫ x in (0 : ℝ)..1, κ t x * (spikeWx ts t x) ^ 2) = 0 :=
    integral_eq_zero_of_ne_time (ts := ts) _ fun t ht => by simp [spikeWx, ht]
  have hts : (fun x => spikeW ts ts x) = fun x : ℝ => x * (1 - x) := by
    funext x
    simp [spikeW]
  have ht0 : (fun x => spikeW ts t0 x) = 0 := by
    funext x
    simp [spikeW, h0.ne]
  rw [hdiss, hts, ht0, eLpNorm_zero, ENNReal.toReal_zero, mul_zero, add_zero,
    zero_pow two_ne_zero]
  exact pow_ne_zero 2 quad_eLpNorm_ne_zero

/-- The time-continuity field of `IsWeakParabolicSolution` is what makes the energy-identity
hypothesis of `weak_parabolic_unique` satisfiable. For every `κ`, the time spike `spikeW`
meets every other field of the class for the homogeneous equation (`L²` slices, `H¹₀`
profiles at every time, `L²` on the rectangle, the weak equation), but not the continuity
field, and it violates the energy identity at `ts`. -/
example {t0 t1 ts : ℝ} (h0 : t0 < ts) (h1 : ts < t1) (κ : ℝ → ℝ → ℝ) :
    (∀ t ∈ Set.Icc t0 t1, MemLp (fun x => spikeW ts t x) 2 (volume.restrict (Set.Icc 0 1)))
    ∧ (∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
        ∃ h : WeakH10, h.toFun = spikeW ts t ∧ h.weakDeriv = spikeWx ts t)
    ∧ MemLp (Function.uncurry (spikeW ts)) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    ∧ MemLp (Function.uncurry (spikeWx ts)) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    ∧ (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
            (-spikeW ts t x * deriv (fun s => φ s x) t
              + κ t x * spikeWx ts t x * deriv (fun y => φ t y) x)
          = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, (0 : ℝ → ℝ → ℝ) t x * φ t x)
    ∧ ¬ IsWeakParabolicSolution t0 t1 κ 0 (spikeW ts) (spikeWx ts)
    ∧ (eLpNorm (fun x => spikeW ts ts x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + 2 * ∫ t in t0..ts, ∫ x in (0 : ℝ)..1, κ t x * (spikeWx ts t x) ^ 2
        ≠ (eLpNorm (fun x => spikeW ts t0 x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 :=
  ⟨fun t _ => spike_slice_memLp ts t, Eventually.of_forall (spike_profile ts),
    (spike_memLp t0 t1 ts).1, (spike_memLp t0 t1 ts).2, fun φ _ => spike_weak κ φ,
    fun h => spike_not_continuous h0.le h1 (h.continuous_slice ts ⟨h0.le, h1.le⟩),
    spike_energy_ne h0 κ⟩

/-! ## `weak_parabolic_unique` on concrete data -/

/-- The zero function solves the homogeneous equation, for every diffusivity. -/
lemma zero_isWeakParabolicSolution (t0 t1 : ℝ) (κ : ℝ → ℝ → ℝ) :
    IsWeakParabolicSolution t0 t1 κ 0 (fun _ _ => 0) (fun _ _ => 0) where
  memLp_slice _ _ := MemLp.zero'
  continuous_slice _ _ := by simpa using tendsto_const_nhds
  profile := Eventually.of_forall fun _ => ⟨zeroWeak, rfl, rfl⟩
  memLp := MemLp.zero'
  memLp_deriv := MemLp.zero'
  weak_eq _ _ := by simp

/-- With `κ = 1`, no forcing and zero initial value on `(0, 1) × (0, 1)`, every solution of
the class vanishes in `L²(0,1)` at every time, given the energy identity for `κ = 1`:
`weak_parabolic_unique` compares it with the zero solution. -/
example
    (hEnergyId : ∀ w wx : ℝ → ℝ → ℝ, IsWeakParabolicSolution 0 1 (fun _ _ => 1) 0 w wx →
      ∀ τ ∈ Set.Icc (0 : ℝ) 1,
        (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + 2 * ∫ t in (0 : ℝ)..τ, ∫ x in (0 : ℝ)..1, (fun _ _ => (1 : ℝ)) t x * (wx t x) ^ 2
          = (eLpNorm (fun x => w 0 x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2)
    {u ux : ℝ → ℝ → ℝ} (hu : IsWeakParabolicSolution 0 1 (fun _ _ => 1) 0 u ux)
    (hinit : eLpNorm (fun x => u 0 x) 2 (volume.restrict (Set.Icc 0 1)) = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, (fun x => u t x) =ᵐ[volume.restrict (Set.Icc 0 1)] 0 :=
  weak_parabolic_unique (u0 := 0) zero_lt_one (kmin := 1) (kmax := 1) zero_lt_one
    aestronglyMeasurable_const (Eventually.of_forall fun _ => ⟨le_rfl, le_rfl⟩) hEnergyId
    (zero_isWeakParabolicSolution 0 1 _) hu (by simp) (by simpa using hinit)

end EarthScience
