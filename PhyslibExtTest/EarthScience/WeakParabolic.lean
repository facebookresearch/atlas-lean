/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.WeakParabolic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
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
profiles at every time, `L²` on the rectangle, the forcing condition, the weak equation), but
not the continuity field, and it violates the energy identity at `ts`. -/
example {t0 t1 ts : ℝ} (h0 : t0 < ts) (h1 : ts < t1) (κ : ℝ → ℝ → ℝ) :
    (∀ t ∈ Set.Icc t0 t1, MemLp (fun x => spikeW ts t x) 2 (volume.restrict (Set.Icc 0 1)))
    ∧ (∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
        ∃ h : WeakH10, h.toFun =ᵐ[volume.restrict (Set.Icc 0 1)] spikeW ts t
          ∧ h.weakDeriv =ᵐ[volume.restrict (Set.Icc 0 1)] spikeWx ts t)
    ∧ MemLp (Function.uncurry (spikeW ts)) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    ∧ MemLp (Function.uncurry (spikeWx ts)) 2 (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1))
    ∧ (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        Integrable (fun p : ℝ × ℝ => (0 : ℝ → ℝ → ℝ) p.1 p.2 * φ p.1 p.2)
          (volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc 0 1)))
    ∧ (∀ φ : ℝ → ℝ → ℝ, ParabolicTest t0 t1 φ →
        ∫ t in t0..t1, ∫ x in (0 : ℝ)..1,
            (-spikeW ts t x * deriv (fun s => φ s x) t
              + κ t x * spikeWx ts t x * deriv (fun y => φ t y) x)
          = ∫ t in t0..t1, ∫ x in (0 : ℝ)..1, (0 : ℝ → ℝ → ℝ) t x * φ t x)
    ∧ ¬ IsWeakParabolicSolution t0 t1 κ 0 (spikeW ts) (spikeWx ts)
    ∧ (eLpNorm (fun x => spikeW ts ts x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2
          + 2 * ∫ t in t0..ts, ∫ x in (0 : ℝ)..1, κ t x * (spikeWx ts t x) ^ 2
        ≠ (eLpNorm (fun x => spikeW ts t0 x) 2 (volume.restrict (Set.Icc 0 1))).toReal ^ 2 :=
  ⟨fun t _ => spike_slice_memLp ts t,
    Eventually.of_forall fun t => (spike_profile ts t).imp fun _ h =>
      ⟨EventuallyEq.of_eq h.1, EventuallyEq.of_eq h.2⟩,
    (spike_memLp t0 t1 ts).1, (spike_memLp t0 t1 ts).2, fun _ _ => by simp,
    fun φ _ => spike_weak κ φ,
    fun h => spike_not_continuous h0.le h1 (h.continuous_slice ts ⟨h0.le, h1.le⟩),
    spike_energy_ne h0 κ⟩

/-! ## `weak_parabolic_unique` on concrete data -/

/-- The zero function solves the homogeneous equation, for every diffusivity. -/
lemma zero_isWeakParabolicSolution (t0 t1 : ℝ) (κ : ℝ → ℝ → ℝ) :
    IsWeakParabolicSolution t0 t1 κ 0 (fun _ _ => 0) (fun _ _ => 0) where
  memLp_slice _ _ := MemLp.zero'
  continuous_slice _ _ := by simpa using tendsto_const_nhds
  profile := Eventually.of_forall fun _ => ⟨zeroWeak, EventuallyEq.rfl, EventuallyEq.rfl⟩
  memLp := MemLp.zero'
  memLp_deriv := MemLp.zero'
  forcing_integrable _ _ := by simp
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

/-! ## The class fixes no spatial representative -/

/-- The zero solution changed to `1` at the single point `x = 1/2` of space, at every time. -/
noncomputable def pointSpike (_t x : ℝ) : ℝ := if x = 1 / 2 then 1 else 0

lemma pointSpike_ae_zero (t : ℝ) :
    (fun x => pointSpike t x) =ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] 0 := by
  refine ae_restrict_of_ae (measure_mono_null (fun x hx => ?_) (measure_singleton (1 / 2 : ℝ)))
  by_contra hne
  apply hx
  change (if x = 1 / 2 then (1 : ℝ) else 0) = 0
  exact ite_eq_right_iff.mpr fun h => absurd h hne

lemma pointSpike_ae_zero_rect (t0 t1 : ℝ) :
    Function.uncurry pointSpike =ᵐ[volume.restrict (Set.Icc t0 t1 ×ˢ Set.Icc (0 : ℝ) 1)] 0 := by
  refine ae_restrict_of_ae
    (measure_mono_null (t := Set.univ ×ˢ {(1 / 2 : ℝ)}) (fun p hp => ?_) ?_)
  · by_contra hne
    apply hp
    change (if p.2 = 1 / 2 then (1 : ℝ) else 0) = 0
    exact ite_eq_right_iff.mpr fun h => absurd ⟨Set.mem_univ _, h⟩ hne
  · rw [Measure.volume_eq_prod, Measure.prod_prod, measure_singleton, mul_zero]

/-- **Spatial null sets do not matter.** `pointSpike`, with derivative `0`, solves the
homogeneous equation for every diffusivity: it agrees with the zero solution almost everywhere
on `[0, 1]` at every time. The change is a null set in space at every time, unlike the time
spike above, which changes a whole time slice. -/
lemma pointSpike_isWeakParabolicSolution (t0 t1 : ℝ) (κ : ℝ → ℝ → ℝ) :
    IsWeakParabolicSolution t0 t1 κ 0 pointSpike (fun _ _ => 0) where
  memLp_slice t _ := MemLp.zero.ae_eq (pointSpike_ae_zero t).symm
  continuous_slice _ _ := by simpa [pointSpike] using tendsto_const_nhds
  profile := Eventually.of_forall fun t => ⟨zeroWeak, (pointSpike_ae_zero t).symm, EventuallyEq.rfl⟩
  memLp := MemLp.zero.ae_eq (pointSpike_ae_zero_rect t0 t1).symm
  memLp_deriv := MemLp.zero'
  forcing_integrable _ _ := by simp
  weak_eq φ _ := by
    have hin : ∀ t, (∫ x in (0 : ℝ)..1, pointSpike t x * deriv (fun s => φ s x) t) = 0 := by
      intro t
      rw [intervalIntegral.integral_of_le zero_le_one]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
        (pointSpike_ae_zero t)] with x hx
      simp only [Pi.zero_apply] at hx
      simp [hx]
    simp [hin]

/-- The profile condition needs agreement almost everywhere, not pointwise: no `H¹₀(0,1)`
function with derivative `0` equals `pointSpike t`, since its value at `1/2` is the integral of
`0` from `0` to `1/2`. -/
example (t : ℝ) : ¬ ∃ h : WeakH10, h.toFun = pointSpike t ∧ h.weakDeriv = fun _ => 0 := by
  rintro ⟨h, h1, h2⟩
  have := h.toFun_eq_integral (1 / 2) ⟨by norm_num, by norm_num⟩
  rw [h1, h2] at this
  simp [pointSpike] at this

/-! ## Test functions are supported inside the open rectangle -/

/-- A smooth function on `ℝ` that is nonzero exactly on `(0, 1)`. -/
noncomputable def glue01 (s : ℝ) : ℝ := expNegInvGlue s * expNegInvGlue (1 - s)

lemma glue01_ne_zero_iff (s : ℝ) : glue01 s ≠ 0 ↔ 0 < s ∧ s < 1 := by
  simp only [glue01, ne_eq, mul_eq_zero, expNegInvGlue.zero_iff_nonpos, not_or, not_le, sub_pos]

lemma contDiff_glue01 : ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) glue01 :=
  expNegInvGlue.contDiff.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

/-- Smooth on `ℝ × ℝ` and nonzero exactly on the open unit square, so its support is the
closed square. -/
noncomputable def boundaryBump (t x : ℝ) : ℝ := glue01 t * glue01 x

/-- `ParabolicTest` asks for the support, the closure of the nonzero set, to lie inside the
open rectangle: `boundaryBump` is smooth and nonzero only inside `(0, 1) × (0, 1)`, but its
support touches the boundary, so it is not a test function. -/
example :
    ContDiff ℝ (((⊤ : ℕ∞)) : WithTop ℕ∞) (fun p : ℝ × ℝ => boundaryBump p.1 p.2)
    ∧ (∀ t x, boundaryBump t x ≠ 0 → 0 < t ∧ t < 1 ∧ 0 < x ∧ x < 1)
    ∧ ¬ ParabolicTest 0 1 boundaryBump := by
  refine ⟨(contDiff_glue01.comp contDiff_fst).mul (contDiff_glue01.comp contDiff_snd),
    fun t x h => ?_, fun ⟨_, hsupp⟩ => ?_⟩
  · obtain ⟨ht, hx⟩ := mul_ne_zero_iff.mp h
    exact ⟨((glue01_ne_zero_iff t).mp ht).1, ((glue01_ne_zero_iff t).mp ht).2,
      ((glue01_ne_zero_iff x).mp hx).1, ((glue01_ne_zero_iff x).mp hx).2⟩
  · have hmem : ((0 : ℝ), (1 / 2 : ℝ)) ∈ tsupport (fun p : ℝ × ℝ => boundaryBump p.1 p.2) := by
      refine mem_closure_of_tendsto (b := nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (f := fun ε : ℝ => (ε, (1 / 2 : ℝ))) ?_ ?_
      · exact ((continuous_id.prodMk continuous_const).tendsto (0 : ℝ)).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with ε hε
        exact mul_ne_zero ((glue01_ne_zero_iff ε).mpr hε)
          ((glue01_ne_zero_iff (1 / 2)).mpr (by norm_num))
    exact lt_irrefl (0 : ℝ) (hsupp hmem).1.1

/-! ## The forcing must be integrable against the test functions -/

/-- A smooth bump on `ℝ`, equal to `1` on `[3/8, 5/8]` and supported in `[1/4, 3/4]`. -/
noncomputable def midBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

lemma parabolicTest_midBump :
    ParabolicTest 0 1 (fun t x => midBump t * midBump x) := by
  refine ⟨(midBump.contDiff.comp contDiff_fst).mul (midBump.contDiff.comp contDiff_snd), ?_⟩
  have hsub : Function.support (fun p : ℝ × ℝ => midBump p.1 * midBump p.2)
      ⊆ Set.Icc (1 / 4 : ℝ) (3 / 4) ×ˢ Set.Icc (1 / 4 : ℝ) (3 / 4) := by
    intro p hp
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp
    have hs : ∀ y : ℝ, midBump y ≠ 0 → y ∈ Set.Icc (1 / 4 : ℝ) (3 / 4) := fun y hy => by
      have hy' : y ∈ Function.support midBump := hy
      rw [midBump.support_eq, Real.ball_eq_Ioo] at hy'
      obtain ⟨hlo, hhi⟩ := hy'
      change 1 / 2 - 1 / 4 < y at hlo
      change y < 1 / 2 + 1 / 4 at hhi
      constructor <;> linarith
    exact ⟨hs _ h1, hs _ h2⟩
  refine (closure_minimal hsub (isClosed_Icc.prod isClosed_Icc)).trans ?_
  rintro ⟨t, x⟩ ⟨⟨ht0, ht1⟩, hx0, hx1⟩
  exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

/-- The forcing of the review's example, `|x - 1/2|⁻¹`, not integrable near `x = 1/2`. -/
noncomputable def singularForcing (_t x : ℝ) : ℝ := |x - 1 / 2|⁻¹

/-- No pair is a solution with the forcing `|x - 1/2|⁻¹`, for any diffusivity: the forcing is
not integrable against the test function `midBump t * midBump x`, which is `1` near the
singular line. Without the forcing condition, Lean's integral of the non-integrable product
would read as `0`. -/
example (κ u ux : ℝ → ℝ → ℝ) : ¬ IsWeakParabolicSolution 0 1 κ singularForcing u ux := by
  intro h
  set A : Set ℝ := Set.Icc (3 / 8) (5 / 8) with hA
  have hI := h.forcing_integrable _ parabolicTest_midBump
  have hsub : A ×ˢ A ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    rintro ⟨t, x⟩ ⟨⟨ht0, ht1⟩, hx0, hx1⟩
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hone : ∀ y ∈ A, midBump y = 1 := fun y hy => midBump.one_of_mem_closedBall (by
    rw [Real.closedBall_eq_Icc]
    change y ∈ Set.Icc (1 / 2 - 1 / 8) (1 / 2 + 1 / 8)
    obtain ⟨hlo, hhi⟩ := hy
    constructor <;> linarith)
  have hIA : Integrable (fun p : ℝ × ℝ => |p.2 - 1 / 2|⁻¹) (volume.restrict (A ×ˢ A)) := by
    refine (hI.mono_measure (Measure.restrict_mono hsub le_rfl)).congr ?_
    filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
    simp only [singularForcing, hone _ hp.1, hone _ hp.2, mul_one]
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict] at hIA
  have hslice := hIA.prod_right_ae
  have : (ae (volume.restrict A)).NeBot := ae_restrict_neBot.mpr (by
    rw [hA, Real.volume_Icc]
    norm_num)
  obtain ⟨_, hx⟩ := hslice.exists
  have hx' : IntegrableOn (fun y : ℝ => |y - 1 / 2|⁻¹) A := hx
  have hII : IntervalIntegrable (fun x : ℝ => (x - 1 / 2)⁻¹) volume (3 / 8) (5 / 8) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)]
    refine Integrable.mono (hx'.mono_set Set.Ioc_subset_Icc_self)
      ((continuous_sub_right _).measurable.inv.aestronglyMeasurable) ?_
    filter_upwards with x
    simp
  rcases intervalIntegrable_sub_inv_iff.mp hII with h' | h'
  · norm_num at h'
  · exact h' (by rw [Set.uIcc_of_le (by norm_num)]; constructor <;> norm_num)

/-! ## The energy lemma needs `L²` time slices -/

/-- The `L²(0,1)` hypothesis on the time slices of `weak_parabolic_unique_of_energy` is needed:
`ENNReal.toReal` reads an infinite norm as `0`. Without it, `w t x = x⁻¹` for `t ≠ 0` and
`w 0 = 0` (with `wx = 0`, `κ = 1`) satisfy the energy identity and the initial condition, but
`w 1` does not vanish. -/
example : ¬ ∀ w wx : ℝ → ℝ → ℝ,
    (∀ τ : ℝ, τ ∈ Set.Icc (0 : ℝ) 1 →
      (eLpNorm (fun x => w τ x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2
        + 2 * ∫ t in (0 : ℝ)..τ, ∫ x in (0 : ℝ)..1, (fun _ _ => (1 : ℝ)) t x * (wx t x) ^ 2
        = (eLpNorm (fun x => w 0 x) 2 (volume.restrict (Set.Icc (0 : ℝ) 1))).toReal ^ 2) →
    (fun x => w 0 x) =ᵐ[volume.restrict (Set.Icc 0 1)] 0 →
    ∀ τ ∈ Set.Icc (0 : ℝ) 1, (fun x => w τ x) =ᵐ[volume.restrict (Set.Icc 0 1)] 0 := by
  intro h
  have hinf : eLpNorm (fun x : ℝ => x⁻¹) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) = ⊤ := by
    by_contra hne
    have hmem : MemLp (fun x : ℝ => x⁻¹) 2 (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
      memLp_iff.mpr (lt_top_iff_ne_top.mpr hne)
    have hint : IntegrableOn (fun x : ℝ => x⁻¹) (Set.Icc (0 : ℝ) 1) :=
      (hmem.mono_exponent (by norm_num : (1 : ENNReal) ≤ 2)).integrable le_rfl
    have hII : IntervalIntegrable (fun x : ℝ => x⁻¹) volume 0 1 := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact hint.mono_set Set.Ioc_subset_Icc_self
    rcases intervalIntegrable_inv_iff.mp hII with h' | h'
    · norm_num at h'
    · exact h' (by rw [Set.uIcc_of_le zero_le_one]; exact ⟨le_rfl, zero_le_one⟩)
  have h1 := h (fun t x => if t = 0 then 0 else x⁻¹) (fun _ _ => 0) (fun τ _ => by
      by_cases hτ : τ = 0
      · simp [hτ]
      · simp [hτ, hinf]) (Filter.Eventually.of_forall fun _ => by simp) 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_ne_zero, ↓reduceIte] at h1
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc] at h1
  have hpos : (0 : ENNReal) < volume (Set.Ioc (0 : ℝ) 1) := by simp
  have hnull : volume (Set.Ioc (0 : ℝ) 1) = 0 := by
    rw [← nonpos_iff_eq_zero]
    refine (measure_mono_null (t := {x : ℝ | ¬ (x ∈ Set.Icc 0 1 → x⁻¹ = (0 : ℝ → ℝ) x)})
      ?_ ?_).le
    · intro x hx hcon
      exact inv_ne_zero (ne_of_gt hx.1) (hcon ⟨hx.1.le, hx.2⟩)
    · exact ae_iff.mp h1
  exact hpos.ne' hnull

end EarthScience
