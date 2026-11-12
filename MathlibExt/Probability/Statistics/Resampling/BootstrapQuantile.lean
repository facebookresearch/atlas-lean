/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.CDF
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Stieltjes
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Instances.ENNReal.Lemmas
public import Mathlib.Tactic
public import MathlibExt.Probability.Quantile

/-!
# Weak convergence implies quantile convergence

If real laws converge weakly and the pushforward limit CDF is continuous and strictly
increasing, the `q`-quantile (generalized inverse `cdfQuantile`) converges, for fixed
`q ∈ (0, 1)`. Interface for bootstrap coverage; no finite-sample coverage is claimed.

## Main statements

* `ProbabilityTheory.tendsto_cdfQuantile_of_tendstoInDistribution`: quantile convergence
  from weak convergence, via the imported `cdfQuantile_le_iff`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace ProbabilityTheory

/-! ### Pinned target (prove it; no sorry). -/

/-- **Weak convergence implies quantile convergence.** If `X n ⇒ Y` and the pushforward
limit CDF `F x = (Measure.map Y μ').real (Set.Iic x)` is continuous and strictly
increasing, the `q`-quantile (generalized inverse) of the law of `X n` tends to that of
`Y`, for fixed `q ∈ (0, 1)`, using the imported `cdfQuantile_le_iff` (Quantile.lean:77). -/
theorem tendsto_cdfQuantile_of_tendstoInDistribution
    {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
    {μ : Measure Ω} {μ' : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}
    (hw : TendstoInDistribution X atTop Y (fun _ => μ) μ')
    {F : ℝ → ℝ} (hF : ∀ x, F x = (Measure.map Y μ').real (Set.Iic x))
    (hcont : Continuous F) (hstrict : StrictMono F)
    {q : ℝ} (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    Tendsto (fun n => cdfQuantile (Measure.map (X n) μ) q) atTop
      (𝓝 (cdfQuantile (Measure.map Y μ') q)) := by
  have hCDF_eq : ∀ y, cdf (Measure.map Y μ') y = F y := fun y => by
    rw [cdf_eq_real, hF]
  have hCDF_fun : ⇑(cdf (Measure.map Y μ')) = F := funext hCDF_eq
  have hsing : ∀ a : ℝ, (Measure.map Y μ') {a} = 0 := fun a => by
    have hleft : Function.leftLim (⇑(cdf (Measure.map Y μ')) : ℝ → ℝ) a = F a := by
      rw [hCDF_fun]
      exact (hcont.continuousAt.continuousWithinAt).leftLim_eq
    have h1 : (Measure.map Y μ') {a} = (cdf (Measure.map Y μ')).measure {a} := by
      rw [measure_cdf]
    rw [h1, StieltjesFunction.measure_singleton]
    have h2 : (cdf (Measure.map Y μ')) a
        - Function.leftLim (⇑(cdf (Measure.map Y μ')) : ℝ → ℝ) a = 0 := by
      rw [hCDF_eq a, hleft, sub_self]
    rw [h2]
    simp
  have hCDF : ∀ x : ℝ, Filter.Tendsto (fun n => cdf (Measure.map (X n) μ) x) atTop
      (𝓝 (cdf (Measure.map Y μ') x)) := fun x => by
    have hfront : ((Measure.map Y μ') : Measure ℝ) (frontier (Set.Iic x)) = 0 := by
      rw [frontier_Iic]
      exact hsing x
    have hENN : Filter.Tendsto (fun n => ((⟨Measure.map (X n) μ, inferInstance⟩ :
        ProbabilityMeasure ℝ) : Measure ℝ) (Set.Iic x)) atTop
        (𝓝 (((⟨Measure.map Y μ', inferInstance⟩ : ProbabilityMeasure ℝ) : Measure ℝ)
          (Set.Iic x))) :=
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hw.tendsto hfront
    have hReal : Filter.Tendsto
        (fun n => (((Measure.map (X n) μ) (Set.Iic x)).toReal : ℝ)) atTop
        (𝓝 (((Measure.map Y μ') (Set.Iic x)).toReal : ℝ)) :=
      (ENNReal.tendsto_toReal_iff (fun n => measure_ne_top _ _)
        (measure_ne_top _ _)).mpr hENN
    simpa [cdf_eq_real, measureReal_def] using hReal
  set a : ℝ := cdfQuantile (Measure.map Y μ') q with ha
  have hFa : q ≤ F a := by
    have h1 : q ≤ cdf (Measure.map Y μ') a := (cdfQuantile_le_iff _ hq).mp (le_refl _)
    rwa [hCDF_eq a] at h1
  rw [Metric.tendsto_nhds]
  intro ε hε
  set u : ℝ := a + ε / 2 with hu
  set l : ℝ := a - ε / 2 with hl
  have hau : a < u := by simp [hu]; linarith
  have hla : l < a := by simp [hl]; linarith
  have huε : u < a + ε := by simp [hu]; linarith
  have hεl : a - ε < l := by simp [hl]; linarith
  have hqu : q < F u := lt_of_le_of_lt hFa (hstrict hau)
  have hfl : F l < q := by
    have hcon : ¬ (q ≤ cdf (Measure.map Y μ') l) := by
      intro h
      have hle' : a ≤ l := (cdfQuantile_le_iff _ hq).mpr h
      exact (not_le_of_gt hla) hle'
    have h2 : cdf (Measure.map Y μ') l < q := not_le.mp hcon
    rwa [hCDF_eq l] at h2
  have hCDF_u : Filter.Tendsto (fun n => cdf (Measure.map (X n) μ) u) atTop (𝓝 (F u)) := by
    simpa [hCDF_eq] using hCDF u
  have hCDF_l : Filter.Tendsto (fun n => cdf (Measure.map (X n) μ) l) atTop (𝓝 (F l)) := by
    simpa [hCDF_eq] using hCDF l
  have hevU : ∀ᶠ n in atTop, q < cdf (Measure.map (X n) μ) u :=
    hCDF_u.eventually_const_lt hqu
  have hevU' : ∀ᶠ n in atTop, cdfQuantile (Measure.map (X n) μ) q ≤ u :=
    hevU.mono fun n hn => (cdfQuantile_le_iff _ hq).mpr (le_of_lt hn)
  have hupper : ∀ᶠ n in atTop, cdfQuantile (Measure.map (X n) μ) q < a + ε :=
    hevU'.mono fun n hn => lt_of_le_of_lt hn huε
  have hevL : ∀ᶠ n in atTop, cdf (Measure.map (X n) μ) l < q :=
    hCDF_l.eventually_lt_const hfl
  have hevL' : ∀ᶠ n in atTop, l < cdfQuantile (Measure.map (X n) μ) q := by
    refine hevL.mono fun n hn => ?_
    have hnot : ¬ (cdfQuantile (Measure.map (X n) μ) q ≤ l) := by
      intro hle'
      have hq' : q ≤ cdf (Measure.map (X n) μ) l := (cdfQuantile_le_iff _ hq).mp hle'
      exact (not_le_of_gt hn) hq'
    exact not_le.mp hnot
  have hlower : ∀ᶠ n in atTop, a - ε < cdfQuantile (Measure.map (X n) μ) q :=
    hevL'.mono fun n hn => lt_trans hεl hn
  filter_upwards [hupper, hlower] with n hn_up hn_lo
  rw [Real.dist_eq]
  rw [abs_lt]
  constructor <;> linarith

end ProbabilityTheory
