/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.OccupationStability
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Probability.Process.Filtration
public import Mathlib.Tactic
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.UnitInterval

/-!
# Boundary tests for stopped occupation stability under uniform limits

Constant-sequence readings of the stability identity at the heterozygosity potential
`2y(1-y)`: realization means at frequencies one half and zero, and the integrability and
identity conjuncts for arbitrary neutral-solution data, in diffusion time units.
-/

open MeasureTheory Filter Set
open scoped NNReal unitInterval

open MathlibExt.Biology.PopulationGenetics.Diffusion
  (generator generator_heterozygosity
    integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn
    integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn_modifiedProcess)
open MathlibExt.Biology.PopulationGenetics.Diffusion.KimuraFixationProcess
  (IsWrightFisherSolution absorptionTime)
open MathlibExt.Biology.PopulationGenetics.Diffusion.NeutralWrightFisherRaw
  (modifiedProcess rawMeasure)

@[expose] public section

namespace MathlibExtTest.Biology.PopulationGenetics.Diffusion.OccupationStability

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) ω : ℝ),
    2 * modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
      (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
        (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) = 1 / 2 := by
  have hhet : ContDiff ℝ 2 (fun y : ℝ => 2 * y * (1 - y)) :=
    ((contDiff_const (c := (2 : ℝ))).mul contDiff_id).mul
      ((contDiff_const (c := (1 : ℝ))).sub contDiff_id)
  have hu : ∀ n : ℕ,
      ContDiff ℝ 2 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet
  have hg : ∀ n : ℕ,
      Continuous ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet.continuous
  have hgen : ∀ (n : ℕ) (y : ℝ),
      generator 0 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y =
        -((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y :=
    fun _ y => generator_heterozygosity y
  have hu0 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 0 = 0 := by
    intro n
    norm_num
  have hu1 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 1 = 0 := by
    intro n
    norm_num
  have hgInf : Continuous (fun y : ℝ => 2 * y * (1 - y)) := hhet.continuous
  have hunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    refine Eventually.of_forall fun n y _ => ?_
    simp only [dist_self]
    exact hε
  have hgunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := hunif
  have h : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) ω : ℝ),
    2 * modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
      (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
        (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩)
      = 2 * (1 / 2 : ℝ) * (1 - 1 / 2) :=
    (integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn_modifiedProcess
      ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩ hu hg hgen hu0 hu1 hgInf hunif
      hgunif).2
  norm_num at h
  exact h

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨0, unitInterval.zero_mem⟩) ω : ℝ),
    2 * modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨0, unitInterval.zero_mem⟩) = 0 := by
  have hhet : ContDiff ℝ 2 (fun y : ℝ => 2 * y * (1 - y)) :=
    ((contDiff_const (c := (2 : ℝ))).mul contDiff_id).mul
      ((contDiff_const (c := (1 : ℝ))).sub contDiff_id)
  have hu : ∀ n : ℕ,
      ContDiff ℝ 2 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet
  have hg : ∀ n : ℕ,
      Continuous ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet.continuous
  have hgen : ∀ (n : ℕ) (y : ℝ),
      generator 0 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y =
        -((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y :=
    fun _ y => generator_heterozygosity y
  have hu0 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 0 = 0 := by
    intro n
    norm_num
  have hu1 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 1 = 0 := by
    intro n
    norm_num
  have hgInf : Continuous (fun y : ℝ => 2 * y * (1 - y)) := hhet.continuous
  have hunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    refine Eventually.of_forall fun n y _ => ?_
    simp only [dist_self]
    exact hε
  have hgunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := hunif
  have h : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨0, unitInterval.zero_mem⟩) ω : ℝ),
    2 * modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨0, unitInterval.zero_mem⟩ (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨0, unitInterval.zero_mem⟩) = 2 * (0 : ℝ) * (1 - 0) :=
    (integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn_modifiedProcess
      ⟨0, unitInterval.zero_mem⟩ hu hg hgen hu0 hu1 hgInf hunif hgunif).2
  norm_num at h
  exact h

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) μ := by
  have hhet : ContDiff ℝ 2 (fun y : ℝ => 2 * y * (1 - y)) :=
    ((contDiff_const (c := (2 : ℝ))).mul contDiff_id).mul
      ((contDiff_const (c := (1 : ℝ))).sub contDiff_id)
  have hu : ∀ n : ℕ,
      ContDiff ℝ 2 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet
  have hg : ∀ n : ℕ,
      Continuous ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet.continuous
  have hgen : ∀ (n : ℕ) (y : ℝ),
      generator 0 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y =
        -((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y :=
    fun _ y => generator_heterozygosity y
  have hu0 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 0 = 0 := by
    intro n
    norm_num
  have hu1 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 1 = 0 := by
    intro n
    norm_num
  have hgInf : Continuous (fun y : ℝ => 2 * y * (1 - y)) := hhet.continuous
  have hunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    refine Eventually.of_forall fun n y _ => ?_
    simp only [dist_self]
    exact hε
  have hgunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := hunif
  exact (integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn hX hX0 hu hg
    hgen hu0 hu1 hgInf hunif hgunif hx).1

example {Ω : Type*} {mΩ : MeasurableSpace Ω} {x : ℝ} {ℱ : Filtration ℝ≥0 mΩ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → ℝ}
    (hX : IsWrightFisherSolution 0 ℱ μ X) (hX0 : ∀ᵐ ω ∂μ, X 0 ω = x)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime X ω : ℝ),
      2 * X (Real.toNNReal s) ω * (1 - X (Real.toNNReal s) ω)) ∂μ
      = 2 * x * (1 - x) := by
  have hhet : ContDiff ℝ 2 (fun y : ℝ => 2 * y * (1 - y)) :=
    ((contDiff_const (c := (2 : ℝ))).mul contDiff_id).mul
      ((contDiff_const (c := (1 : ℝ))).sub contDiff_id)
  have hu : ∀ n : ℕ,
      ContDiff ℝ 2 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet
  have hg : ∀ n : ℕ,
      Continuous ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) :=
    fun _ => hhet.continuous
  have hgen : ∀ (n : ℕ) (y : ℝ),
      generator 0 ((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y =
        -((fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n) y :=
    fun _ y => generator_heterozygosity y
  have hu0 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 0 = 0 := by
    intro n
    norm_num
  have hu1 : ∀ n : ℕ,
      (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y)) n 1 = 0 := by
    intro n
    norm_num
  have hgInf : Continuous (fun y : ℝ => 2 * y * (1 - y)) := hhet.continuous
  have hunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    refine Eventually.of_forall fun n y _ => ?_
    simp only [dist_self]
    exact hε
  have hgunif : TendstoUniformlyOn (fun _ : ℕ => fun y : ℝ => 2 * y * (1 - y))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := hunif
  exact (integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn hX hX0 hu hg
    hgen hu0 hu1 hgInf hunif hgunif hx).2

#print axioms integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn
#print axioms integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn_modifiedProcess

example : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) ω : ℝ),
    2 * modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
      (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
        (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) = 1 / 2 := by
  have hhet : ContDiff ℝ 2 (fun y : ℝ => 2 * y * (1 - y)) :=
    ((contDiff_const (c := (2 : ℝ))).mul contDiff_id).mul
      ((contDiff_const (c := (1 : ℝ))).sub contDiff_id)
  have hu : ∀ n : ℕ,
      ContDiff ℝ 2 ((fun n : ℕ => fun y : ℝ =>
        (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) n) := by
    intro n
    exact (contDiff_const (c := (2 + 1 / (n + 1 : ℝ)))).mul
      (contDiff_id.mul ((contDiff_const (c := (1 : ℝ))).sub contDiff_id))
  have hg : ∀ n : ℕ,
      Continuous ((fun n : ℕ => fun y : ℝ =>
        (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) n) :=
    fun n => (hu n).continuous
  have hgen : ∀ (n : ℕ) (y : ℝ),
      generator 0 ((fun n : ℕ => fun y : ℝ =>
        (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) n) y =
        -((fun n : ℕ => fun y : ℝ =>
          (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) n) y := by
    intro n y
    show generator 0
        (fun y : ℝ => (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) y =
        -((2 + 1 / (n + 1 : ℝ)) * (y * (1 - y)))
    have hd : ∀ y : ℝ, HasDerivAt
        (fun y : ℝ => (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y)))
        ((2 + 1 / (n + 1 : ℝ)) * (1 - 2 * y)) y := by
      intro y
      have h1y : HasDerivAt (fun z : ℝ => 1 - z) (-1) y := by
        simpa using (hasDerivAt_id' y).const_sub 1
      convert ((hasDerivAt_id' y).mul h1y).const_mul (2 + 1 / (n + 1 : ℝ)) using 1
      ring
    have hD : deriv (fun y : ℝ => (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) =
        fun y => (2 + 1 / (n + 1 : ℝ)) * (1 - 2 * y) :=
      funext fun y => (hd y).deriv
    have h2 : HasDerivAt
        (fun y : ℝ => (2 + 1 / (n + 1 : ℝ)) * (1 - 2 * y))
        (-2 * (2 + 1 / (n + 1 : ℝ))) y := by
      convert (((hasDerivAt_id' y).const_mul 2).const_sub 1).const_mul
        (2 + 1 / (n + 1 : ℝ)) using 1
      ring
    rw [generator, hD, h2.deriv]
    ring
  have hu0 : ∀ n : ℕ,
      (fun n : ℕ => fun y : ℝ => (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) n
        0 = 0 := by
    intro n
    norm_num
  have hu1 : ∀ n : ℕ,
      (fun n : ℕ => fun y : ℝ => (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y))) n
        1 = 0 := by
    intro n
    norm_num
  have hgInf : Continuous (fun y : ℝ => 2 * y * (1 - y)) := hhet.continuous
  have hunif : TendstoUniformlyOn (fun n : ℕ => fun y : ℝ =>
      (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y)))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hlim : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
        Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h4ε : (0 : ℝ) < 4 * ε := by positivity
    have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < 4 * ε :=
      hlim.eventually (eventually_lt_nhds h4ε)
    filter_upwards [hev] with n hn
    intro y hy
    obtain ⟨hy0, hy1⟩ := Set.mem_Icc.mp hy
    have hQ0 : (0 : ℝ) ≤ y * (1 - y) := mul_nonneg hy0 (sub_nonneg.mpr hy1)
    have hQ4 : y * (1 - y) ≤ 1 / 4 := by nlinarith [sq_nonneg (y - 1 / 2)]
    have hc' : (0 : ℝ) ≤ 1 / ((n : ℝ) + 1) := by positivity
    have hab : (2 + 1 / ((n : ℝ) + 1)) * (y * (1 - y)) - 2 * y * (1 - y) =
        (1 / ((n : ℝ) + 1)) * (y * (1 - y)) := by ring
    rw [dist_comm]
    show dist ((2 + 1 / ((n : ℝ) + 1)) * (y * (1 - y)))
      (2 * y * (1 - y)) < ε
    rw [Real.dist_eq, hab, abs_of_nonneg (mul_nonneg hc' hQ0)]
    calc (1 / ((n : ℝ) + 1)) * (y * (1 - y))
        ≤ (1 / ((n : ℝ) + 1)) * (1 / 4) :=
          mul_le_mul_of_nonneg_left hQ4 hc'
      _ < (4 * ε) * (1 / 4) := mul_lt_mul_of_pos_right hn (by norm_num)
      _ = ε := by ring
  have hgunif : TendstoUniformlyOn (fun n : ℕ => fun y : ℝ =>
      (2 + 1 / (n + 1 : ℝ)) * (y * (1 - y)))
      (fun y : ℝ => 2 * y * (1 - y)) atTop (Set.Icc 0 1) := hunif
  have h : ∫ ω, (∫ s in (0 : ℝ)..(absorptionTime
      (modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩) ω : ℝ),
    2 * modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
      (Real.toNNReal s) ω *
      (1 - modifiedProcess ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩
        (Real.toNNReal s) ω))
    ∂(rawMeasure ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩)
      = 2 * (1 / 2 : ℝ) * (1 - 1 / 2) :=
    (integral_absorptionTime_of_generator_eq_neg_of_tendstoUniformlyOn_modifiedProcess
      ⟨1 / 2, by exact ⟨by norm_num, by norm_num⟩⟩ hu hg hgen hu0 hu1 hgInf hunif
      hgunif).2
  norm_num at h
  exact h

end MathlibExtTest.Biology.PopulationGenetics.Diffusion.OccupationStability
