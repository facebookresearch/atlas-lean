/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Causality.RegressionDiscontinuity
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.MeasurableSpace.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.MeasureTheory.OuterMeasure.AE
public import Mathlib.MeasureTheory.OuterMeasure.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.NhdsWithin
public import Mathlib.Topology.Order.LeftRightNhds
public import Mathlib.Topology.Separation.Hausdorff

/-!
# Tests for sharp regression discontinuity at the cutoff

Instances of `sharpRD_condExp_observed_ae_eq` and
`MathlibExt.Probability.Causality.sharpRD_jump_eq_sub_of_tendsto` on
concrete laws. The running variable is
`X`, the cutoff is `1/2`, and treatment is received exactly when
`1/2 ≤ X`, matching the sharp rule `c ≤ X` of the production module.

* `μ01`, the uniform law on `[0,1]`: `RD_T1_jump_zero` (with no treatment
  effect every version has zero jump) with witness `RD_T1_nonvac_exists`
  (the version `id`), and `RD_T2_jump_two` (with treated mean `x + 2`
  every version jumps by two) with witness `RD_T2_nonvac_exists`.
* `μhalf`, the uniform law on `[1/2,3/2]`: left support fails
  (`RD_T3_left_support_zero`), so two versions of the observed regression
  have different jumps (`RD_T3_nonident_exists`).
* Sorting (`m0Sort`, discontinuous at the cutoff, with treated mean
  `m1Sort`): every version still jumps by three (`RD_T4_jump_three`)
  while the true effect `m1Sort - m0Sort` is two (`RD_T4_effect_two`,
  `RD_T4_jump_ne_effect`), with witness `RD_T4_nonvac_exists`.
* `μprod`, a product law whose treated outcome reads the second
  coordinate (genuine noise beyond `X`): the jump is still identified
  (`RD_noise_jump`), and the noise is not a function of `X`
  (`RD_noise_genuine`).
* `μmix`, the mixture of `μ01` with an atom at the cutoff: the atom has
  positive mass (`RD_atom_mass`) and the jump is still two
  (`RD_atom_jump_two`).
* `μleft`, the uniform law on `[0,1/2]`: right support fails
  (`RD_right_support_zero`), so two versions jump differently
  (`RD_right_nonident_exists`).

What is not covered (as in the production module): the fuzzy design and
its local instrumental-variable contract, estimation by local polynomial
regression and bandwidth choice, inference, and manipulation tests.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Causality.RegressionDiscontinuity

open MeasureTheory Filter
open scoped Topology ENNReal

/-- The uniform law on `[0,1]`. -/
noncomputable abbrev μ01 : Measure ℝ :=
  volume.restrict (Set.Icc (0:ℝ) 1)

/-- The uniform law on `[1/2,3/2]` (no mass left of the cutoff). -/
noncomputable abbrev μhalf : Measure ℝ :=
  volume.restrict (Set.Icc (1/2:ℝ) (3/2))

/-- The uniform law on `[0,1/2]` (no mass right of the cutoff). -/
noncomputable abbrev μleft : Measure ℝ :=
  volume.restrict (Set.Icc (0:ℝ) (1/2))

/-- Half `μ01` plus half a Dirac atom at the cutoff. -/
noncomputable abbrev μmix : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • μ01 + (2⁻¹ : ℝ≥0∞) • Measure.dirac (1/2:ℝ)

/-- The product law `μ01 × μ01` on `ℝ × ℝ` (noise beyond `X = Prod.fst`). -/
noncomputable abbrev μprod : Measure (ℝ × ℝ) :=
  μ01.prod μ01

/-- Treated mean shifted by two on the right. -/
noncomputable def mPieceAdd2 : ℝ → ℝ :=
  fun x => if (1/2:ℝ) ≤ x then x + 2 else x

/-- Second witness for non-identification, constant on the left. -/
noncomputable def mPieceAdd2Seven : ℝ → ℝ :=
  fun x => if (1/2:ℝ) ≤ x then x + 2 else 7

/-- Sorting mean with a unit jump at the cutoff. -/
noncomputable def m0Sort : ℝ → ℝ :=
  fun x => x + (if (1/2:ℝ) ≤ x then (1:ℝ) else 0)

/-- Treated sorting mean, two above the untreated one. -/
noncomputable def m1Sort : ℝ → ℝ :=
  fun x => m0Sort x + 2

/-- Piecewise witness for the sorting case: `x` below, `x + 3` above. -/
noncomputable def mWitnessAdd3 : ℝ → ℝ :=
  fun x => if (1/2:ℝ) ≤ x then x + 3 else x

/-- Piecewise witness missing right support: `x` below, `7` above. -/
noncomputable def mRightSeven : ℝ → ℝ :=
  fun x => if (1/2:ℝ) ≤ x then 7 else x

private theorem prob_of_length_one (a b : ℝ) (h : b - a = 1) :
    IsProbabilityMeasure (volume.restrict (Set.Icc a b)) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc, h, ENNReal.ofReal_one]

instance : IsProbabilityMeasure μ01 :=
  prob_of_length_one 0 1 (by norm_num)

instance : IsProbabilityMeasure μhalf :=
  prob_of_length_one (1/2) (3/2) (by norm_num)

instance : IsFiniteMeasure μleft := by
  constructor
  show (volume.restrict (Set.Icc (0:ℝ) (1/2))) Set.univ < ∞
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  norm_num [ENNReal.ofReal_lt_top]

instance : IsProbabilityMeasure μmix := by
  show IsProbabilityMeasure
    (((2⁻¹ : ℝ≥0∞) • μ01) + (2⁻¹ : ℝ≥0∞) • Measure.dirac (1/2:ℝ))
  constructor
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, measure_univ,
    measure_univ]
  simp only [smul_eq_mul, mul_one]
  exact ENNReal.inv_two_add_inv_two

private theorem integrable_restrict_Icc (f : ℝ → ℝ) (hf : Continuous f)
    (a b : ℝ) : Integrable f (volume.restrict (Set.Icc a b)) :=
  hf.locallyIntegrable.integrableOn_isCompact isCompact_Icc

/-- Conditional expectation given `X = id` is the function itself. -/
private theorem version_comap_id {μ : Measure ℝ} [IsFiniteMeasure μ]
    (f : ℝ → ℝ) (hf : Integrable f μ) :
    μ[f | MeasurableSpace.comap (id : ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μ] fun ω => f (id ω) := by
  rw [MeasurableSpace.comap_id]
  have hver := MeasureTheory.condExp_of_aestronglyMeasurable'
    (le_rfl : (inferInstance : MeasurableSpace ℝ) ≤ _) hf.aestronglyMeasurable hf
  exact hver.trans (Filter.Eventually.of_forall fun ω => rfl)

/-- `μ01` charges every open subinterval of `[0,1]`. -/
private theorem μ01_of_Ioo_superset {l r l' r' : ℝ} (hl : 0 ≤ l')
    (hr : r' ≤ 1) (hlt : l' < r')
    (hsub : Set.Ioo l' r' ⊆ Set.Ioo l r) :
    μ01 (Set.Ioo l r) ≠ 0 := by
  have hvol : (0:ℝ≥0∞) < volume (Set.Ioo l' r') := by
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_pos.mpr (by linarith)
  have hle : volume (Set.Ioo l' r') ≤ μ01 (Set.Ioo l r) := by
    show volume (Set.Ioo l' r')
      ≤ (volume.restrict (Set.Icc (0:ℝ) 1)) (Set.Ioo l r)
    rw [Measure.restrict_apply measurableSet_Ioo]
    apply measure_mono
    intro x hx
    have hx' : l' < x ∧ x < r' := hx
    have hmem : x ∈ Set.Ioo l r := hsub hx
    have hx'' : l < x ∧ x < r := hmem
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc]
    exact ⟨hx'', ⟨by linarith, by linarith⟩⟩
  exact ne_of_gt (lt_of_lt_of_le hvol hle)

/-- Left support holds on `[0,1]`. -/
private theorem μ01_support_left (δ : ℝ) (hδ : 0 < δ) :
    μ01 (Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0 := by
  have hpos : (0:ℝ) < min δ (1/2) := lt_min hδ (by norm_num)
  have hη1 : min δ (1/2:ℝ) / 2 ≤ δ := by
    have h := min_le_left δ (1/2:ℝ)
    linarith
  have hη2 : min δ (1/2:ℝ) / 2 ≤ 1/2 := by
    have h := min_le_right δ (1/2:ℝ)
    linarith
  exact μ01_of_Ioo_superset (show (0:ℝ) ≤ 1/2 - min δ (1/2) / 2 by linarith)
    (show (1/2:ℝ) ≤ 1 by norm_num)
    (show (1/2:ℝ) - min δ (1/2) / 2 < 1/2 by linarith)
    (show Set.Ioo (1/2 - min δ (1/2) / 2) (1/2) ⊆ Set.Ioo (1/2 - δ) (1/2) by
      intro x hx
      simp only [Set.mem_Ioo] at hx ⊢
      exact ⟨by linarith, hx.2⟩)

/-- Right support holds on `[0,1]`. -/
private theorem μ01_support_right (δ : ℝ) (hδ : 0 < δ) :
    μ01 (Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0 := by
  have hpos : (0:ℝ) < min δ (1/2) := lt_min hδ (by norm_num)
  have hη1 : min δ (1/2:ℝ) / 2 ≤ δ := by
    have h := min_le_left δ (1/2:ℝ)
    linarith
  have hη2 : min δ (1/2:ℝ) / 2 ≤ 1/2 := by
    have h := min_le_right δ (1/2:ℝ)
    linarith
  exact μ01_of_Ioo_superset (show (0:ℝ) ≤ 1/2 by norm_num)
    (show (1/2:ℝ) + min δ (1/2) / 2 ≤ 1 by linarith)
    (show (1/2:ℝ) < 1/2 + min δ (1/2) / 2 by linarith)
    (show Set.Ioo (1/2) (1/2 + min δ (1/2) / 2) ⊆ Set.Ioo (1/2) (1/2 + δ) by
      intro x hx
      simp only [Set.mem_Ioo] at hx ⊢
      exact ⟨hx.1, by linarith⟩)

/-- A piecewise function agreeing with `L` left of the cutoff has left
limit `L c`. -/
private theorem tendsto_piece_left {L R : ℝ → ℝ} {c : ℝ}
    (hL : ContinuousAt L c) :
    Tendsto (fun x => if c ≤ x then R x else L x) (𝓝[<] c) (𝓝 (L c)) := by
  have heq : (fun x => if c ≤ x then R x else L x) =ᶠ[𝓝[<] c] L := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Iio] at hx
    exact ite_eq_right (not_le.mpr hx)
  exact Filter.Tendsto.congr' heq.symm
    (tendsto_nhdsWithin_of_tendsto_nhds hL.tendsto)

/-- A piecewise function agreeing with `R` right of the cutoff has right
limit `R c`. -/
private theorem tendsto_piece_right {L R : ℝ → ℝ} {c : ℝ}
    (hR : ContinuousAt R c) :
    Tendsto (fun x => if c ≤ x then R x else L x) (𝓝[>] c) (𝓝 (R c)) := by
  have heq : (fun x => if c ≤ x then R x else L x) =ᶠ[𝓝[>] c] R := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Ioi] at hx
    exact ite_eq_left hx.le
  exact Filter.Tendsto.congr' heq.symm
    (tendsto_nhdsWithin_of_tendsto_nhds hR.tendsto)

private theorem integrable_mPieceAdd2 : Integrable mPieceAdd2 μ01 := by
  have hfun : mPieceAdd2
      = (id : ℝ → ℝ) + (Set.Ici (1/2:ℝ)).indicator (fun _ => (2:ℝ)) := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ ω
    · have hmem : ω ∈ Set.Ici (1/2:ℝ) := h
      simp only [mPieceAdd2, ite_eq_left h, Set.indicator_of_mem hmem,
        Pi.add_apply, id_eq]
    · have hmem : ω ∉ Set.Ici (1/2:ℝ) := h
      simp only [mPieceAdd2, ite_eq_right h, Set.indicator_of_notMem hmem,
        Pi.add_apply, id_eq, add_zero]
  rw [hfun]
  exact (integrable_restrict_Icc id continuous_id 0 1).add
    ((integrable_const 2).indicator measurableSet_Ici)

private theorem integrable_mPieceAdd2Seven :
    Integrable mPieceAdd2Seven μ01 := by
  have hfun : mPieceAdd2Seven
      = (fun x : ℝ => x + 2)
        + (Set.Iio (1/2:ℝ)).indicator (fun x : ℝ => 5 - x) := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ ω
    · have hmem : ω ∉ Set.Iio (1/2:ℝ) := by simpa using h
      simp only [mPieceAdd2Seven, ite_eq_left h,
        Set.indicator_of_notMem hmem, Pi.add_apply, add_zero]
    · have h' : ω < 1/2 := lt_of_not_ge h
      have hmem : ω ∈ Set.Iio (1/2:ℝ) := h'
      have eL : mPieceAdd2Seven ω = 7 := by simp only [mPieceAdd2Seven, ite_eq_right h]
      have eR : ((fun x : ℝ => x + 2)
          + (Set.Iio (1/2:ℝ)).indicator (fun x : ℝ => 5 - x)) ω = 7 := by
        simp only [Pi.add_apply, Set.indicator_of_mem hmem]
        ring
      rw [eL, eR]
  rw [hfun]
  exact (integrable_restrict_Icc _ (continuous_id.add continuous_const) 0 1).add
    ((integrable_restrict_Icc _ (continuous_const.sub continuous_id) 0 1).indicator
      measurableSet_Iio)

private theorem integrable_m0Sort : Integrable m0Sort μ01 := by
  have hfun : m0Sort
      = (id : ℝ → ℝ) + (Set.Ici (1/2:ℝ)).indicator (fun _ => (1:ℝ)) := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ ω
    · have hmem : ω ∈ Set.Ici (1/2:ℝ) := h
      simp only [m0Sort, ite_eq_left h, Set.indicator_of_mem hmem,
        Pi.add_apply, id_eq]
    · have hmem : ω ∉ Set.Ici (1/2:ℝ) := h
      simp only [m0Sort, ite_eq_right h, Set.indicator_of_notMem hmem,
        Pi.add_apply, id_eq, add_zero]
  rw [hfun]
  exact (integrable_restrict_Icc id continuous_id 0 1).add
    ((integrable_const 1).indicator measurableSet_Ici)

private theorem integrable_mWitnessAdd3 : Integrable mWitnessAdd3 μ01 := by
  have hfun : mWitnessAdd3
      = (fun x : ℝ => x + 3)
        + (Set.Iio (1/2:ℝ)).indicator (fun _ => (-3:ℝ)) := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ ω
    · have hmem : ω ∉ Set.Iio (1/2:ℝ) := by simpa using h
      simp only [mWitnessAdd3, ite_eq_left h,
        Set.indicator_of_notMem hmem, Pi.add_apply, add_zero]
    · have h' : ω < 1/2 := lt_of_not_ge h
      have hmem : ω ∈ Set.Iio (1/2:ℝ) := h'
      have eL : mWitnessAdd3 ω = ω := by simp only [mWitnessAdd3, ite_eq_right h]
      have eR : ((fun x : ℝ => x + 3)
          + (Set.Iio (1/2:ℝ)).indicator (fun _ => (-3:ℝ))) ω = ω := by
        simp only [Pi.add_apply, Set.indicator_of_mem hmem]
        ring
      rw [eL, eR]
  rw [hfun]
  exact (integrable_restrict_Icc _ (continuous_id.add continuous_const) 0 1).add
    ((integrable_const (-3)).indicator measurableSet_Iio)

/-- The observed regression is the piecewise mean (pointwise). -/
private theorem observed_eq_mPieceAdd2 :
    MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
      (fun x : ℝ => x + 2) = mPieceAdd2 := by
  funext ω
  by_cases h : (1/2:ℝ) ≤ id ω
  · have h' : (1/2:ℝ) ≤ ω := h
    have hmem : ω ∈ {ω | (1/2:ℝ) ≤ id ω} := h
    have hmemc : ω ∉ {ω | (1/2:ℝ) ≤ id ω}ᶜ := by simpa using hmem
    simp only [MathlibExt.Probability.Causality.observed, Pi.add_apply,
      Set.indicator_of_mem hmem, Set.indicator_of_notMem hmemc, add_zero]
    have e : mPieceAdd2 ω = ω + 2 := by simp only [mPieceAdd2, ite_eq_left h']
    exact e.symm
  · have h' : ¬(1/2:ℝ) ≤ ω := h
    have hmem : ω ∉ {ω | (1/2:ℝ) ≤ id ω} := h
    have hmemc : ω ∈ {ω | (1/2:ℝ) ≤ id ω}ᶜ := h
    simp only [MathlibExt.Probability.Causality.observed, Pi.add_apply,
      Set.indicator_of_notMem hmem, Set.indicator_of_mem hmemc, zero_add]
    have e : mPieceAdd2 ω = ω := by simp only [mPieceAdd2, ite_eq_right h']
    exact e.symm

/-- Null case: every version has zero jump. -/
theorem RD_T1_jump_zero (m : ℝ → ℝ) (a b : ℝ)
    (hm : μ01[MathlibExt.Probability.Causality.observed
          {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ) (id : ℝ → ℝ) |
        MeasurableSpace.comap (id : ℝ → ℝ)
          (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μ01] fun ω => m (id ω))
    (ha : Tendsto m (𝓝[<] (1/2:ℝ)) (𝓝 a))
    (hb : Tendsto m (𝓝[>] (1/2:ℝ)) (𝓝 b)) :
    b - a = 0 := by
  have h := MathlibExt.Probability.Causality.sharpRD_jump_eq_sub_of_tendsto
    (X := (id : ℝ → ℝ)) (c := (1/2:ℝ))
    (Y₀ := (id : ℝ → ℝ)) (Y₁ := (id : ℝ → ℝ))
    (m₀ := (id : ℝ → ℝ)) (m₁ := (id : ℝ → ℝ)) (m := m) (a := a) (b := b)
    measurable_id
    (integrable_restrict_Icc id continuous_id 0 1)
    (integrable_restrict_Icc id continuous_id 0 1)
    (version_comap_id id (integrable_restrict_Icc id continuous_id 0 1))
    (version_comap_id id (integrable_restrict_Icc id continuous_id 0 1))
    continuousAt_id continuousAt_id
    (fun δ hδ => by
      show μ01 (Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0
      exact μ01_support_left δ hδ)
    (fun δ hδ => by
      show μ01 (Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0
      exact μ01_support_right δ hδ)
    hm ha hb
  norm_num at h
  exact h

/-- Nonvacuity: the version `id` has zero jump. -/
theorem RD_T1_nonvac_exists :
    (μ01[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ) (id : ℝ → ℝ) |
        MeasurableSpace.comap (id : ℝ → ℝ)
          (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μ01] fun ω => id (id ω))
      ∧ Tendsto id (𝓝[<] (1/2:ℝ)) (𝓝 (1/2:ℝ))
      ∧ Tendsto id (𝓝[>] (1/2:ℝ)) (𝓝 (1/2:ℝ)) := by
  have hobs :
      MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω}
        (id : ℝ → ℝ) (id : ℝ → ℝ)
      = id := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ id ω
    · have hmem : ω ∈ {ω | (1/2:ℝ) ≤ id ω} := h
      have hmemc : ω ∉ {ω | (1/2:ℝ) ≤ id ω}ᶜ := by simpa using hmem
      simp only [MathlibExt.Probability.Causality.observed, Pi.add_apply, Set.indicator_of_mem hmem,
        Set.indicator_of_notMem hmemc, add_zero]
    · have hmem : ω ∉ {ω | (1/2:ℝ) ≤ id ω} := h
      have hmemc : ω ∈ {ω | (1/2:ℝ) ≤ id ω}ᶜ := h
      simp only [MathlibExt.Probability.Causality.observed,
        Pi.add_apply, Set.indicator_of_notMem hmem,
        Set.indicator_of_mem hmemc, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [hobs]
    exact version_comap_id id (integrable_restrict_Icc id continuous_id 0 1)
  · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id.tendsto
  · exact tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id.tendsto

/-- Jump of size two: every version jumps by two. -/
theorem RD_T2_jump_two (m : ℝ → ℝ) (a b : ℝ)
    (hm : μ01[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
          (fun x : ℝ => x + 2) |
        MeasurableSpace.comap (id : ℝ → ℝ)
          (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μ01] fun ω => m (id ω))
    (ha : Tendsto m (𝓝[<] (1/2:ℝ)) (𝓝 a))
    (hb : Tendsto m (𝓝[>] (1/2:ℝ)) (𝓝 b)) :
    b - a = 2 := by
  have h := MathlibExt.Probability.Causality.sharpRD_jump_eq_sub_of_tendsto
    (X := (id : ℝ → ℝ)) (c := (1/2:ℝ))
    (Y₀ := (id : ℝ → ℝ)) (Y₁ := fun x : ℝ => x + 2)
    (m₀ := (id : ℝ → ℝ)) (m₁ := fun x : ℝ => x + 2) (m := m) (a := a) (b := b)
    measurable_id
    (integrable_restrict_Icc id continuous_id 0 1)
    (integrable_restrict_Icc _ (continuous_id.add continuous_const) 0 1)
    (version_comap_id id (integrable_restrict_Icc id continuous_id 0 1))
    (version_comap_id _
      (integrable_restrict_Icc _ (continuous_id.add continuous_const) 0 1))
    continuousAt_id (continuous_id.add continuous_const).continuousAt
    (fun δ hδ => by
      show μ01 (Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0
      exact μ01_support_left δ hδ)
    (fun δ hδ => by
      show μ01 (Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0
      exact μ01_support_right δ hδ)
    hm ha hb
  norm_num at h
  exact h

/-- Nonvacuity: the piecewise mean is a version with limits. -/
theorem RD_T2_nonvac_exists :
    ((μ01[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
            (fun x : ℝ => x + 2) |
          MeasurableSpace.comap (id : ℝ → ℝ)
            (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μ01] fun ω => mPieceAdd2 (id ω))
      ∧ Tendsto mPieceAdd2 (𝓝[<] (1/2:ℝ)) (𝓝 (1/2:ℝ))
      ∧ Tendsto mPieceAdd2 (𝓝[>] (1/2:ℝ)) (𝓝 (5/2:ℝ))) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [observed_eq_mPieceAdd2]
    exact version_comap_id mPieceAdd2 integrable_mPieceAdd2
  · exact tendsto_piece_left (L := (id : ℝ → ℝ)) (R := fun x : ℝ => x + 2)
      (c := (1/2:ℝ)) continuousAt_id
  · have hlim := tendsto_piece_right (L := (id : ℝ → ℝ))
      (R := fun x : ℝ => x + 2) (c := (1/2:ℝ))
      (continuous_id.add continuous_const).continuousAt
    rw [show ((1/2:ℝ) + 2) = 5/2 from by norm_num] at hlim
    exact hlim

/-- Left support fails on `[1/2,3/2]`. -/
theorem RD_T3_left_support_zero (δ : ℝ) :
    μhalf ((id : ℝ → ℝ) ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)) = 0 := by
  show (volume.restrict (Set.Icc (1/2:ℝ) (3/2)))
    ((id : ℝ → ℝ) ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)) = 0
  have hset : (id : ℝ → ℝ) ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)
      = Set.Ioo ((1/2:ℝ) - δ) (1/2) := by
    ext x
    simp
  rw [hset, Measure.restrict_apply measurableSet_Ioo]
  have hempty : Set.Ioo ((1/2:ℝ) - δ) (1/2) ∩ Set.Icc (1/2:ℝ) (3/2)
      = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    intro h
    exact absurd h.2.1 (not_le.mpr h.1.2)
  rw [hempty, measure_empty]

/-- On `[1/2,3/2]` a piecewise function agreeing with `x + 2` on the
support is a version of it. -/
private theorem ae_eq_add2_half (F : ℝ → ℝ)
    (hF : ∀ x : ℝ, 1/2 ≤ x → F x = x + 2) :
    (fun x : ℝ => x + 2) =ᵐ[μhalf] F := by
  show ∀ᵐ x ∂(volume.restrict (Set.Icc (1/2:ℝ) (3/2))), (fun x : ℝ => x + 2) x = F x
  rw [ae_restrict_iff' measurableSet_Icc]
  filter_upwards with x hx
  exact (hF x hx.1).symm

/-- The two piecewise means agree almost everywhere on `[1/2,3/2]`. -/
private theorem ae_piece_eq_seven_half :
    mPieceAdd2 =ᵐ[μhalf] mPieceAdd2Seven := by
  show ∀ᵐ x ∂μhalf, mPieceAdd2 x = mPieceAdd2Seven x
  rw [MeasureTheory.ae_iff]
  have hsub : {x : ℝ | ¬mPieceAdd2 x = mPieceAdd2Seven x} ⊆ Set.Iio (1/2:ℝ) := by
    intro x hx
    simp only [Set.mem_Iio]
    by_contra hle
    push Not at hle
    exact hx (by simp only [mPieceAdd2, mPieceAdd2Seven, ite_eq_left hle])
  have hnull : μhalf (Set.Iio (1/2:ℝ)) = 0 := by
    show (volume.restrict (Set.Icc (1/2:ℝ) (3/2))) (Set.Iio (1/2:ℝ)) = 0
    rw [Measure.restrict_apply measurableSet_Iio]
    have hempty : Set.Iio (1/2:ℝ) ∩ Set.Icc (1/2:ℝ) (3/2) = ∅ := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Iio, Set.mem_Icc,
        Set.mem_empty_iff_false, iff_false]
      intro h
      exact absurd h.2.1 (not_le.mpr h.1)
    rw [hempty, measure_empty]
  exact MeasureTheory.measure_mono_null hsub hnull

/-- The two piecewise means agree almost everywhere on `[0,1/2]`. -/
private theorem ae_piece_eq_rightSeven_left :
    mPieceAdd2 =ᵐ[μleft] mRightSeven := by
  show ∀ᵐ x ∂μleft, mPieceAdd2 x = mRightSeven x
  rw [MeasureTheory.ae_iff]
  have hsub : {x : ℝ | ¬mPieceAdd2 x = mRightSeven x} ⊆ Set.Ici (1/2:ℝ) := by
    intro x hx
    simp only [Set.mem_Ici]
    by_contra hle
    push Not at hle
    exact hx (by simp only [mPieceAdd2, mRightSeven,
      ite_eq_right (not_le.mpr hle)])
  have hnull : μleft (Set.Ici (1/2:ℝ)) = 0 := by
    show (volume.restrict (Set.Icc (0:ℝ) (1/2))) (Set.Ici (1/2:ℝ)) = 0
    rw [Measure.restrict_apply measurableSet_Ici]
    have hempty : Set.Ici (1/2:ℝ) ∩ Set.Icc (0:ℝ) (1/2) = {(1/2:ℝ)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc,
        Set.mem_singleton_iff]
      constructor
      · rintro ⟨h1, _, h2⟩
        linarith
      · rintro rfl
        exact ⟨le_rfl, by norm_num, le_rfl⟩
    rw [hempty, Real.volume_singleton]
  exact MeasureTheory.measure_mono_null hsub hnull

private theorem version_mPieceAdd2_half :
    μhalf[mPieceAdd2 | MeasurableSpace.comap (id : ℝ → ℝ)
        (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μhalf] fun ω => mPieceAdd2 (id ω) := by
  have hae : (fun x : ℝ => x + 2) =ᵐ[μhalf] mPieceAdd2 :=
    ae_eq_add2_half mPieceAdd2
      (fun x hx => by simp only [mPieceAdd2, ite_eq_left hx])
  have hInt : Integrable (fun x : ℝ => x + 2) μhalf :=
    integrable_restrict_Icc _ (continuous_id.add continuous_const) (1/2) (3/2)
  have h1 := MeasureTheory.condExp_congr_ae
    (m := MeasurableSpace.comap (id : ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ)) hae
  have h2 := version_comap_id (fun x : ℝ => x + 2) hInt
  have h3 : (fun ω => (fun x : ℝ => x + 2) (id ω))
      =ᵐ[μhalf] fun ω => mPieceAdd2 (id ω) := by
    filter_upwards [hae] with ω hω
    exact hω
  show μhalf[mPieceAdd2 | _] =ᵐ[μhalf] fun ω => mPieceAdd2 (id ω)
  exact (h1.symm.trans h2).trans h3

private theorem version_mPieceAdd2Seven_half :
    μhalf[mPieceAdd2Seven | MeasurableSpace.comap (id : ℝ → ℝ)
        (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μhalf] fun ω => mPieceAdd2Seven (id ω) := by
  have hae : (fun x : ℝ => x + 2) =ᵐ[μhalf] mPieceAdd2Seven :=
    ae_eq_add2_half mPieceAdd2Seven
      (fun x hx => by simp only [mPieceAdd2Seven, ite_eq_left hx])
  have hInt : Integrable (fun x : ℝ => x + 2) μhalf :=
    integrable_restrict_Icc _ (continuous_id.add continuous_const) (1/2) (3/2)
  have h1 := MeasureTheory.condExp_congr_ae
    (m := MeasurableSpace.comap (id : ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ)) hae
  have h2 := version_comap_id (fun x : ℝ => x + 2) hInt
  have h3 : (fun ω => (fun x : ℝ => x + 2) (id ω))
      =ᵐ[μhalf] fun ω => mPieceAdd2Seven (id ω) := by
    filter_upwards [hae] with ω hω
    exact hω
  show μhalf[mPieceAdd2Seven | _] =ᵐ[μhalf] fun ω => mPieceAdd2Seven (id ω)
  exact (h1.symm.trans h2).trans h3

/-- Non-identification: two versions give different jumps. -/
theorem RD_T3_nonident_exists :
    ∃ (m m' : ℝ → ℝ) (a b a' b' : ℝ),
      (((μhalf[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
                (fun x : ℝ => x + 2) |
              MeasurableSpace.comap (id : ℝ → ℝ)
                (inferInstance : MeasurableSpace ℝ)]
            =ᵐ[μhalf] fun ω => m (id ω))
          ∧ Tendsto m (𝓝[<] (1/2:ℝ)) (𝓝 a)
          ∧ Tendsto m (𝓝[>] (1/2:ℝ)) (𝓝 b))
        ∧ (((μhalf[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
                (fun x : ℝ => x + 2) |
              MeasurableSpace.comap (id : ℝ → ℝ)
                (inferInstance : MeasurableSpace ℝ)]
            =ᵐ[μhalf] fun ω => m' (id ω))
          ∧ Tendsto m' (𝓝[<] (1/2:ℝ)) (𝓝 a')
          ∧ Tendsto m' (𝓝[>] (1/2:ℝ)) (𝓝 b'))
        ∧ b - a ≠ b' - a')) := by
  refine ⟨mPieceAdd2, mPieceAdd2Seven, 1/2, 5/2, 7, 5/2, ⟨?_, ?_, ?_⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [observed_eq_mPieceAdd2]
    exact version_mPieceAdd2_half
  · exact tendsto_piece_left (L := (id : ℝ → ℝ)) (R := fun x : ℝ => x + 2)
      (c := (1/2:ℝ)) continuousAt_id
  · have hlim := tendsto_piece_right (L := (id : ℝ → ℝ))
      (R := fun x : ℝ => x + 2) (c := (1/2:ℝ))
      (continuous_id.add continuous_const).continuousAt
    rw [show ((1/2:ℝ) + 2) = 5/2 from by norm_num] at hlim
    exact hlim
  · rw [observed_eq_mPieceAdd2]
    have h1 := MeasureTheory.condExp_congr_ae
      (m := MeasurableSpace.comap (id : ℝ → ℝ)
        (inferInstance : MeasurableSpace ℝ)) ae_piece_eq_seven_half
    exact h1.trans version_mPieceAdd2Seven_half
  · exact tendsto_piece_left (L := fun _ : ℝ => (7:ℝ))
      (R := fun x : ℝ => x + 2) (c := (1/2:ℝ)) continuous_const.continuousAt
  · have hlim := tendsto_piece_right (L := fun _ : ℝ => (7:ℝ))
      (R := fun x : ℝ => x + 2) (c := (1/2:ℝ))
      (continuous_id.add continuous_const).continuousAt
    rw [show ((1/2:ℝ) + 2) = 5/2 from by norm_num] at hlim
    exact hlim
  · norm_num

/-- The sorting mean is not continuous at the cutoff. -/
theorem RD_T4_m0Sort_not_continuous : ¬ContinuousAt m0Sort (1/2:ℝ) := by
  intro h
  have hL : Tendsto m0Sort (𝓝[<] (1/2:ℝ)) (𝓝 (m0Sort (1/2:ℝ))) :=
    tendsto_nhdsWithin_of_tendsto_nhds h.tendsto
  have hLeq : m0Sort =ᶠ[𝓝[<] (1/2:ℝ)] id := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_Iio] at hx
    have hn : ¬(1/2:ℝ) ≤ x := not_le.mpr hx
    simp only [m0Sort, ite_eq_right hn, add_zero, id_eq]
  have hLimL : Tendsto m0Sort (𝓝[<] (1/2:ℝ)) (𝓝 (1/2:ℝ)) :=
    Filter.Tendsto.congr' hLeq.symm
      (tendsto_nhdsWithin_of_tendsto_nhds continuousAt_id.tendsto)
  have heq : m0Sort (1/2:ℝ) = 1/2 := tendsto_nhds_unique hL hLimL
  have e0 : m0Sort (1/2:ℝ) = 3/2 := by simp [m0Sort]; norm_num
  rw [e0] at heq
  linarith

/-- With sorting, every version with limits still jumps by three. -/
theorem RD_T4_jump_three (m : ℝ → ℝ) (a b : ℝ)
    (hm : μ01[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} m0Sort m1Sort |
        MeasurableSpace.comap (id : ℝ → ℝ)
          (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μ01] fun ω => m (id ω))
    (ha : Tendsto m (𝓝[<] (1/2:ℝ)) (𝓝 a))
    (hb : Tendsto m (𝓝[>] (1/2:ℝ)) (𝓝 b)) :
    b - a = 3 := by
  have hobs : MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} m0Sort m1Sort
      = MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
        (fun x : ℝ => x + 3) := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ id ω
    · have h' : (1/2:ℝ) ≤ ω := h
      have hmem : ω ∈ {ω | (1/2:ℝ) ≤ id ω} := h
      have hmemc : ω ∉ {ω | (1/2:ℝ) ≤ id ω}ᶜ := by simpa using hmem
      simp only [MathlibExt.Probability.Causality.observed, Pi.add_apply, Set.indicator_of_mem hmem,
        Set.indicator_of_notMem hmemc, add_zero]
      have e0 : m0Sort ω = ω + 1 := by simp only [m0Sort, ite_eq_left h']
      simp only [m1Sort]
      rw [e0]
      ring
    · have h' : ¬(1/2:ℝ) ≤ ω := h
      have hmem : ω ∉ {ω | (1/2:ℝ) ≤ id ω} := h
      have hmemc : ω ∈ {ω | (1/2:ℝ) ≤ id ω}ᶜ := h
      simp only [MathlibExt.Probability.Causality.observed,
        Pi.add_apply, Set.indicator_of_notMem hmem,
        Set.indicator_of_mem hmemc, zero_add]
      have e0 : m0Sort ω = ω := by simp only [m0Sort, ite_eq_right h', add_zero]
      exact e0
  have hm' : μ01[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
          (fun x : ℝ => x + 3) |
        MeasurableSpace.comap (id : ℝ → ℝ)
          (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μ01] fun ω => m (id ω) := by
    rw [← hobs]
    exact hm
  have h := MathlibExt.Probability.Causality.sharpRD_jump_eq_sub_of_tendsto
    (X := (id : ℝ → ℝ)) (c := (1/2:ℝ))
    (Y₀ := (id : ℝ → ℝ)) (Y₁ := fun x : ℝ => x + 3)
    (m₀ := (id : ℝ → ℝ)) (m₁ := fun x : ℝ => x + 3) (m := m) (a := a) (b := b)
    measurable_id
    (integrable_restrict_Icc id continuous_id 0 1)
    (integrable_restrict_Icc _ (continuous_id.add continuous_const) 0 1)
    (version_comap_id id (integrable_restrict_Icc id continuous_id 0 1))
    (version_comap_id _
      (integrable_restrict_Icc _ (continuous_id.add continuous_const) 0 1))
    continuousAt_id (continuous_id.add continuous_const).continuousAt
    (fun δ hδ => by
      show μ01 (Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0
      exact μ01_support_left δ hδ)
    (fun δ hδ => by
      show μ01 (Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0
      exact μ01_support_right δ hδ)
    hm' ha hb
  norm_num at h
  exact h

/-- The true effect under sorting is two. -/
theorem RD_T4_effect_two : m1Sort (1/2:ℝ) - m0Sort (1/2:ℝ) = 2 := by
  have e0 : m0Sort (1/2:ℝ) = 3/2 := by simp [m0Sort]; norm_num
  have e1 : m1Sort (1/2:ℝ) = 7/2 := by simp only [m1Sort, e0]; norm_num
  rw [e1, e0]
  norm_num

/-- The observed jump differs from the true effect. -/
theorem RD_T4_jump_ne_effect :
    (3:ℝ) ≠ m1Sort (1/2:ℝ) - m0Sort (1/2:ℝ) := by
  rw [RD_T4_effect_two]
  norm_num

/-- Nonvacuity: the sorting witness is a version with limits. -/
theorem RD_T4_nonvac_exists :
    ((μ01[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} m0Sort m1Sort |
          MeasurableSpace.comap (id : ℝ → ℝ)
            (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μ01] fun ω => mWitnessAdd3 (id ω))
      ∧ Tendsto mWitnessAdd3 (𝓝[<] (1/2:ℝ)) (𝓝 (1/2:ℝ))
      ∧ Tendsto mWitnessAdd3 (𝓝[>] (1/2:ℝ)) (𝓝 (7/2:ℝ))) := by
  have hobs : MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} m0Sort m1Sort
      = mWitnessAdd3 := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ id ω
    · have h' : (1/2:ℝ) ≤ ω := h
      have hmem : ω ∈ {ω | (1/2:ℝ) ≤ id ω} := h
      have hmemc : ω ∉ {ω | (1/2:ℝ) ≤ id ω}ᶜ := by simpa using hmem
      simp only [MathlibExt.Probability.Causality.observed, Pi.add_apply, Set.indicator_of_mem hmem,
        Set.indicator_of_notMem hmemc, add_zero]
      have e0 : m0Sort ω = ω + 1 := by simp only [m0Sort, ite_eq_left h']
      have e1 : m1Sort ω = ω + 3 := by simp only [m1Sort]; rw [e0]; ring
      have e : mWitnessAdd3 ω = ω + 3 := by simp only [mWitnessAdd3, ite_eq_left h']
      rw [e1, e]
    · have h' : ¬(1/2:ℝ) ≤ ω := h
      have hmem : ω ∉ {ω | (1/2:ℝ) ≤ id ω} := h
      have hmemc : ω ∈ {ω | (1/2:ℝ) ≤ id ω}ᶜ := h
      simp only [MathlibExt.Probability.Causality.observed,
        Pi.add_apply, Set.indicator_of_notMem hmem,
        Set.indicator_of_mem hmemc, zero_add]
      have e0 : m0Sort ω = ω := by simp only [m0Sort, ite_eq_right h', add_zero]
      have e : mWitnessAdd3 ω = ω := by simp only [mWitnessAdd3, ite_eq_right h']
      rw [e0, e]
  refine ⟨?_, ?_, ?_⟩
  · rw [hobs]
    exact version_comap_id mWitnessAdd3 integrable_mWitnessAdd3
  · exact tendsto_piece_left (L := (id : ℝ → ℝ)) (R := fun x : ℝ => x + 3)
      (c := (1/2:ℝ)) continuousAt_id
  · have hlim := tendsto_piece_right (L := (id : ℝ → ℝ))
      (R := fun x : ℝ => x + 3) (c := (1/2:ℝ))
      (continuous_id.add continuous_const).continuousAt
    rw [show ((1/2:ℝ) + 3) = 7/2 from by norm_num] at hlim
    exact hlim

/-- Almost every pair under `μprod` lies in the unit square. -/
private theorem mem_support_prod :
    ∀ᵐ ω ∂μprod, ω.1 ∈ Set.Icc (0:ℝ) 1 ∧ ω.2 ∈ Set.Icc (0:ℝ) 1 := by
  show ∀ᵐ ω ∂(μ01.prod μ01), _
  rw [MeasureTheory.ae_iff]
  have hsub : {ω : ℝ × ℝ | ¬(ω.1 ∈ Set.Icc (0:ℝ) 1 ∧
      ω.2 ∈ Set.Icc (0:ℝ) 1)}
      ⊆ (Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set ℝ)
        ∪ (Set.univ : Set ℝ) ×ˢ (Set.Icc (0:ℝ) 1)ᶜ := by
    intro ω hω
    have hω' : ω.1 ∉ Set.Icc (0:ℝ) 1 ∨ ω.2 ∉ Set.Icc (0:ℝ) 1 := by
      by_contra hcon
      push Not at hcon
      exact hω hcon
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and,
      Set.mem_compl_iff]
    exact hω'
  have h2null : μ01.prod μ01 {ω : ℝ × ℝ | ¬(ω.1 ∈ Set.Icc (0:ℝ) 1 ∧
      ω.2 ∈ Set.Icc (0:ℝ) 1)} = 0 := by
    apply MeasureTheory.measure_mono_null hsub
    · have hA : μ01.prod μ01
          ((Set.Icc (0:ℝ) 1)ᶜ ×ˢ (Set.univ : Set ℝ)
            ∪ (Set.univ : Set ℝ) ×ˢ (Set.Icc (0:ℝ) 1)ᶜ) = 0 := by
        rw [measure_union_null_iff]
        constructor
        · show μ01.prod μ01 ((Set.Icc (0:ℝ) 1)ᶜ ×ˢ Set.univ) = 0
          rw [Measure.prod_prod, measure_univ, mul_one]
          show (volume.restrict (Set.Icc (0:ℝ) 1)) _ = 0
          rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Icc)]
          have hempty : (Set.Icc (0:ℝ) 1)ᶜ ∩ Set.Icc (0:ℝ) 1 = ∅ :=
            Set.compl_inter_self _
          rw [hempty, measure_empty]
        · show μ01.prod μ01 (Set.univ ×ˢ (Set.Icc (0:ℝ) 1)ᶜ) = 0
          rw [Measure.prod_prod, measure_univ, one_mul]
          show (volume.restrict (Set.Icc (0:ℝ) 1)) _ = 0
          rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Icc)]
          have hempty : (Set.Icc (0:ℝ) 1)ᶜ ∩ Set.Icc (0:ℝ) 1 = ∅ :=
            Set.compl_inter_self _
          rw [hempty, measure_empty]
      exact hA
  exact h2null

/-- A continuous function bounded on the unit square is `μprod`-integrable. -/
private theorem integrable_prod_of_continuous (f : ℝ × ℝ → ℝ)
    (hf : Continuous f) (C : ℝ)
    (hC : ∀ ω : ℝ × ℝ, ω.1 ∈ Set.Icc (0:ℝ) 1 → ω.2 ∈ Set.Icc (0:ℝ) 1 →
      ‖f ω‖ ≤ C) :
    Integrable f μprod := by
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [mem_support_prod] with ω hω
  exact hC ω hω.1 hω.2

/-- The mean of the identity on `μ01` is `1/2`. -/
private theorem integral_id_μ01 : ∫ y, y ∂μ01 = 1 / 2 := by
  show ∫ y in Set.Icc (0:ℝ) 1, y ∂volume = 1 / 2
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), integral_id]
  norm_num

/-- Versions of functions of `X = Prod.fst` under `μprod`. -/
private theorem version_fst (f : ℝ → ℝ) (hf : StronglyMeasurable f)
    (hint : Integrable (fun ω : ℝ × ℝ => f ω.1) μprod) :
    μprod[fun ω : ℝ × ℝ => f ω.1 | MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μprod] fun ω => f (Prod.fst ω) := by
  have hle : MeasurableSpace.comap Prod.fst
      (inferInstance : MeasurableSpace ℝ)
      ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    continuous_fst.measurable.comap_le
  have hfst : Measurable[MeasurableSpace.comap (Prod.fst : ℝ × ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ)] (Prod.fst : ℝ × ℝ → ℝ) := by
    rw [measurable_iff_comap_le]
  have hmeas : StronglyMeasurable[MeasurableSpace.comap Prod.fst
      (inferInstance : MeasurableSpace ℝ)] (fun ω : ℝ × ℝ => f ω.1) :=
    hf.comp_measurable hfst
  have hver := MeasureTheory.condExp_of_stronglyMeasurable hle hmeas hint
  rw [hver]

/-- The second coordinate has constant conditional mean `1/2` given the
first. -/
private theorem version_snd_const :
    μprod[fun ω : ℝ × ℝ => ω.2 | MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μprod] fun _ : ℝ × ℝ => (1/2:ℝ) := by
  have hle : MeasurableSpace.comap Prod.fst
      (inferInstance : MeasurableSpace ℝ)
      ≤ (inferInstance : MeasurableSpace (ℝ × ℝ)) :=
    continuous_fst.measurable.comap_le
  have hSnd : Integrable (fun ω : ℝ × ℝ => ω.2) μprod :=
    integrable_prod_of_continuous _ continuous_snd 1 (by
      intro ω h1 h2
      simp only [Set.mem_Icc] at h2
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ ω.2)]
      linarith [h2.2])
  have hI : ∫ y, y ∂μ01 = 1 / 2 := integral_id_μ01
  have heq : ∀ s : Set (ℝ × ℝ),
      MeasurableSet[MeasurableSpace.comap Prod.fst
        (inferInstance : MeasurableSpace ℝ)] s → μprod s < ∞ →
        (∫ x in s, (1/2:ℝ) ∂μprod)
          = ∫ x in s, (fun ω : ℝ × ℝ => ω.2) x ∂μprod := by
    intro s hs _
    obtain ⟨t, ht, rfl⟩ := MeasurableSpace.measurableSet_comap.mp hs
    have hset : Prod.fst ⁻¹' t = t ×ˢ (Set.univ : Set ℝ) := by
      ext ⟨x, y⟩
      simp
    have hinner : (∫ y in (Set.univ : Set ℝ), y ∂μ01) = 1 / 2 := by
      rw [setIntegral_univ]
      exact hI
    have hprod := MeasureTheory.setIntegral_prod (f := fun ω : ℝ × ℝ => ω.2)
      (s := t) (t := Set.univ) (hSnd.integrableOn)
    rw [hset, setIntegral_const, hprod]
    simp_rw [hinner, setIntegral_const]
    rw [measureReal_def, measureReal_def, Measure.prod_prod, measure_univ,
      mul_one]
  have h := MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq
    (f := fun ω : ℝ × ℝ => ω.2) (g := fun _ : ℝ × ℝ => (1/2:ℝ)) hle hSnd
    (fun s _ hs => integrableOn_const hs.ne) heq aestronglyMeasurable_const
  exact h.symm

private theorem μprod_support_left (δ : ℝ) (hδ : 0 < δ) :
    μprod (Prod.fst ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0 := by
  show μ01.prod μ01 (Prod.fst ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0
  have hset : Prod.fst ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)
      = Set.Ioo ((1/2:ℝ) - δ) (1/2) ×ˢ (Set.univ : Set ℝ) := by
    ext ⟨x, y⟩
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  exact μ01_support_left δ hδ

private theorem μprod_support_right (δ : ℝ) (hδ : 0 < δ) :
    μprod (Prod.fst ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0 := by
  show μ01.prod μ01 (Prod.fst ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0
  have hset : Prod.fst ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)
      = Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ) ×ˢ (Set.univ : Set ℝ) := by
    ext ⟨x, y⟩
    simp
  rw [hset, Measure.prod_prod, measure_univ, mul_one]
  exact μ01_support_right δ hδ

/-- The treated outcome reads the second coordinate, so it is not a
function of `X = Prod.fst`. -/
theorem RD_noise_genuine : ∃ ω ω' : ℝ × ℝ, ω.1 = ω'.1 ∧
    (ω.1 + 2 + ω.2) ≠ (ω'.1 + 2 + ω'.2) := by
  exact ⟨(1/2, 0), (1/2, 1), rfl, by norm_num⟩

/-- With noise beyond `X`, the jump is still identified. -/
theorem RD_noise_jump (m : ℝ → ℝ) (a b : ℝ)
    (hm : μprod[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ Prod.fst ω}
          (fun ω : ℝ × ℝ => ω.1) (fun ω : ℝ × ℝ => ω.1 + 2 + ω.2) |
        MeasurableSpace.comap Prod.fst
          (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μprod] fun ω => m (Prod.fst ω))
    (ha : Tendsto m (𝓝[<] (1/2:ℝ)) (𝓝 a))
    (hb : Tendsto m (𝓝[>] (1/2:ℝ)) (𝓝 b)) :
    b - a = 5 / 2 := by
  have hIntA : Integrable (fun ω : ℝ × ℝ => (fun x : ℝ => x + 2) ω.1)
      μprod :=
    integrable_prod_of_continuous _ ((continuous_id.add continuous_const).comp
      continuous_fst) 3 (by
      intro ω h1 h2
      simp only [Set.mem_Icc] at h1
      show ‖(fun x : ℝ => x + 2) ω.1‖ ≤ 3
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ ω.1 + 2)]
      linarith [h1.2])
  have hIntB : Integrable (fun ω : ℝ × ℝ => ω.2) μprod :=
    integrable_prod_of_continuous _ continuous_snd 1 (by
      intro ω h1 h2
      simp only [Set.mem_Icc] at h2
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ ω.2)]
      linarith [h2.2])
  have hY : μprod[(fun ω : ℝ × ℝ => ω.1 + 2 + ω.2) |
        MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μprod] fun ω : ℝ × ℝ => (fun x : ℝ => x + 5/2) (Prod.fst ω) := by
    have hAdd := MeasureTheory.condExp_add hIntA hIntB
      (MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ))
    have h1 := version_fst (fun x : ℝ => x + 2)
      (continuous_id.add continuous_const).measurable.stronglyMeasurable hIntA
    have h2 := version_snd_const
    have hcomb : (μprod[fun ω : ℝ × ℝ => (fun x : ℝ => x + 2) ω.1 |
            MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ)]
          + μprod[fun ω : ℝ × ℝ => ω.2 |
            MeasurableSpace.comap Prod.fst (inferInstance : MeasurableSpace ℝ)])
        =ᵐ[μprod] fun ω : ℝ × ℝ =>
          (fun x : ℝ => x + 2) (Prod.fst ω) + 1/2 := by
      exact h1.add h2
    have hfin : (fun ω : ℝ × ℝ => (fun x : ℝ => x + 2) (Prod.fst ω) + 1/2)
        =ᵐ[μprod] fun ω : ℝ × ℝ => (fun x : ℝ => x + 5/2) (Prod.fst ω) := by
      filter_upwards with ω
      show (fun x : ℝ => x + 2) (Prod.fst ω) + 1/2
        = (fun x : ℝ => x + 5/2) (Prod.fst ω)
      ring
    exact (hAdd.trans hcomb).trans hfin
  have h := MathlibExt.Probability.Causality.sharpRD_jump_eq_sub_of_tendsto
    (X := Prod.fst) (c := (1/2:ℝ))
    (Y₀ := fun ω : ℝ × ℝ => ω.1) (Y₁ := fun ω : ℝ × ℝ => ω.1 + 2 + ω.2)
    (m₀ := id) (m₁ := fun x : ℝ => x + 5/2) (m := m) (a := a) (b := b)
    continuous_fst.measurable
    (integrable_prod_of_continuous _ continuous_fst 1 (by
      intro ω h1 h2
      simp only [Set.mem_Icc] at h1
      show ‖(Prod.fst ω)‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ ω.1)]
      linarith [h1.2]))
    (integrable_prod_of_continuous _ ((continuous_fst.add continuous_const).add
      continuous_snd) 4 (by
      intro ω h1 h2
      simp only [Set.mem_Icc] at h1 h2
      show ‖ω.1 + 2 + ω.2‖ ≤ 4
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith [h1.2, h2.2]))
    (version_fst id continuous_id.measurable.stronglyMeasurable
      (integrable_prod_of_continuous _ continuous_fst 1 (by
        intro ω h1 h2
        simp only [Set.mem_Icc] at h1
        show ‖(Prod.fst ω)‖ ≤ 1
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0:ℝ) ≤ ω.1)]
        linarith [h1.2])))
    hY
    continuousAt_id (continuous_id.add continuous_const).continuousAt
    (fun δ hδ => μprod_support_left δ hδ)
    (fun δ hδ => μprod_support_right δ hδ)
    hm ha hb
  norm_num at h
  exact h

private theorem integrable_mix_of (f : ℝ → ℝ) (h1 : Integrable f μ01)
    (h2 : Integrable f (Measure.dirac (1/2:ℝ))) : Integrable f μmix := by
  show Integrable f (((2⁻¹ : ℝ≥0∞) • μ01)
    + ((2⁻¹ : ℝ≥0∞) • Measure.dirac (1/2:ℝ)))
  exact (h1.smul_measure (by simp)).add_measure (h2.smul_measure (by simp))

private theorem integrable_dirac_of_continuous (f : ℝ → ℝ)
    (hf : Continuous f) (a : ℝ) : Integrable f (Measure.dirac a) :=
  integrable_dirac' hf.measurable.stronglyMeasurable (by simp)

private theorem μmix_support_left (δ : ℝ) (hδ : 0 < δ) :
    μmix (Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0 := by
  show ((2⁻¹ : ℝ≥0∞) • μ01 + (2⁻¹ : ℝ≥0∞) • Measure.dirac (1/2:ℝ))
    (Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  have hmain := μ01_support_left δ hδ
  have hpos : (0:ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) * μ01 (Set.Ioo ((1/2:ℝ) - δ) (1/2)) :=
    ENNReal.mul_pos (by simp) hmain
  exact ne_of_gt (lt_of_lt_of_le hpos (le_add_of_nonneg_right (by simp)))

private theorem μmix_support_right (δ : ℝ) (hδ : 0 < δ) :
    μmix (Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0 := by
  show ((2⁻¹ : ℝ≥0∞) • μ01 + (2⁻¹ : ℝ≥0∞) • Measure.dirac (1/2:ℝ))
    (Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
  simp only [smul_eq_mul]
  have hmain := μ01_support_right δ hδ
  have hpos : (0:ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) * μ01 (Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) :=
    ENNReal.mul_pos (by simp) hmain
  exact ne_of_gt (lt_of_lt_of_le hpos (le_add_of_nonneg_right (by simp)))

/-- The mixture puts positive mass on the cutoff atom. -/
theorem RD_atom_mass : μmix {(1/2:ℝ)} ≠ 0 := by
  show ((2⁻¹ : ℝ≥0∞) • μ01 + (2⁻¹ : ℝ≥0∞) • Measure.dirac (1/2:ℝ))
    {(1/2:ℝ)} ≠ 0
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.dirac_apply_of_mem (Set.mem_singleton_iff.mpr rfl)]
  simp only [smul_eq_mul]
  have hpos : (0:ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) * 1 := ENNReal.mul_pos (by simp) (by simp)
  exact ne_of_gt (lt_of_lt_of_le hpos (le_add_of_nonneg_left (by simp)))

/-- With an atom at the cutoff, every version still jumps by two. -/
theorem RD_atom_jump_two (m : ℝ → ℝ) (a b : ℝ)
    (hm : μmix[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
          (fun x : ℝ => x + 2) |
        MeasurableSpace.comap (id : ℝ → ℝ)
          (inferInstance : MeasurableSpace ℝ)]
        =ᵐ[μmix] fun ω => m (id ω))
    (ha : Tendsto m (𝓝[<] (1/2:ℝ)) (𝓝 a))
    (hb : Tendsto m (𝓝[>] (1/2:ℝ)) (𝓝 b)) :
    b - a = 2 := by
  have hIntId : Integrable (id : ℝ → ℝ) μmix :=
    integrable_mix_of id (integrable_restrict_Icc id continuous_id 0 1)
      (integrable_dirac_of_continuous id continuous_id _)
  have hIntAdd : Integrable (fun x : ℝ => x + 2) μmix :=
    integrable_mix_of _ (integrable_restrict_Icc _
      (continuous_id.add continuous_const) 0 1)
      (integrable_dirac_of_continuous _ (continuous_id.add continuous_const) _)
  have h := MathlibExt.Probability.Causality.sharpRD_jump_eq_sub_of_tendsto
    (X := (id : ℝ → ℝ)) (c := (1/2:ℝ))
    (Y₀ := (id : ℝ → ℝ)) (Y₁ := fun x : ℝ => x + 2)
    (m₀ := (id : ℝ → ℝ)) (m₁ := fun x : ℝ => x + 2) (m := m) (a := a) (b := b)
    measurable_id hIntId hIntAdd
    (version_comap_id id hIntId) (version_comap_id _ hIntAdd)
    continuousAt_id (continuous_id.add continuous_const).continuousAt
    (fun δ hδ => by
      show μmix ((id : ℝ → ℝ) ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)) ≠ 0
      have hset : (id : ℝ → ℝ) ⁻¹' Set.Ioo ((1/2:ℝ) - δ) (1/2)
          = Set.Ioo ((1/2:ℝ) - δ) (1/2) := by
        ext x
        simp
      rw [hset]
      exact μmix_support_left δ hδ)
    (fun δ hδ => by
      show μmix ((id : ℝ → ℝ) ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) ≠ 0
      have hset : (id : ℝ → ℝ) ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)
          = Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ) := by
        ext x
        simp
      rw [hset]
      exact μmix_support_right δ hδ)
    hm ha hb
  norm_num at h
  exact h

/-- On `[0,1/2]` a function agreeing with `id` left of the cutoff is a
version of it. -/
private theorem ae_eq_id_left (F : ℝ → ℝ)
    (hF : ∀ x : ℝ, x < 1/2 → F x = x) : F =ᵐ[μleft] id := by
  show ∀ᵐ x ∂(volume.restrict (Set.Icc (0:ℝ) (1/2))), F x = id x
  rw [ae_restrict_iff' measurableSet_Icc]
  have hnull : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ (1/2:ℝ) := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : ℝ | ¬x ≠ 1/2} = {(1/2:ℝ)} := by
      ext x
      simp
    rw [hset, Real.volume_singleton]
  filter_upwards [hnull] with x hx hmem
  have hlt : x < 1/2 := lt_of_le_of_ne hmem.2 hx
  exact hF x hlt

private theorem version_mPieceAdd2_left :
    μleft[mPieceAdd2 | MeasurableSpace.comap (id : ℝ → ℝ)
        (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μleft] fun ω => mPieceAdd2 (id ω) := by
  have hae : mPieceAdd2 =ᵐ[μleft] id :=
    ae_eq_id_left mPieceAdd2
      (fun x hx => by simp only [mPieceAdd2, ite_eq_right (not_le.mpr hx)])
  have hInt : Integrable (id : ℝ → ℝ) μleft :=
    integrable_restrict_Icc id continuous_id 0 (1/2)
  have h1 := MeasureTheory.condExp_congr_ae
    (m := MeasurableSpace.comap (id : ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ)) hae
  have h2 := version_comap_id (id : ℝ → ℝ) hInt
  have h3 : (fun ω => id (id ω)) =ᵐ[μleft] fun ω => mPieceAdd2 (id ω) := by
    filter_upwards [hae] with ω hω
    exact hω.symm
  show μleft[mPieceAdd2 | _] =ᵐ[μleft] fun ω => mPieceAdd2 (id ω)
  exact h1.trans (h2.trans h3)

private theorem integrable_mRightSeven : Integrable mRightSeven μ01 := by
  have hfun : mRightSeven
      = (fun _ : ℝ => (7:ℝ))
        + (Set.Iio (1/2:ℝ)).indicator (fun x : ℝ => x - 7) := by
    funext ω
    by_cases h : (1/2:ℝ) ≤ ω
    · have hmem : ω ∉ Set.Iio (1/2:ℝ) := by simpa using h
      simp only [mRightSeven, ite_eq_left h,
        Set.indicator_of_notMem hmem, Pi.add_apply, add_zero]
    · have h' : ω < 1/2 := lt_of_not_ge h
      have hmem : ω ∈ Set.Iio (1/2:ℝ) := h'
      have eL : mRightSeven ω = ω := by simp only [mRightSeven, ite_eq_right h]
      have eR : ((fun _ : ℝ => (7:ℝ))
          + (Set.Iio (1/2:ℝ)).indicator (fun x : ℝ => x - 7)) ω = ω := by
        simp only [Pi.add_apply, Set.indicator_of_mem hmem]
        ring
      rw [eL, eR]
  rw [hfun]
  exact (integrable_const 7).add
    ((integrable_restrict_Icc _ (continuous_id.sub continuous_const) 0 1).indicator
      measurableSet_Iio)

private theorem version_mRightSeven_left :
    μleft[mRightSeven | MeasurableSpace.comap (id : ℝ → ℝ)
        (inferInstance : MeasurableSpace ℝ)]
      =ᵐ[μleft] fun ω => mRightSeven (id ω) := by
  have hae : mRightSeven =ᵐ[μleft] id :=
    ae_eq_id_left mRightSeven
      (fun x hx => by simp only [mRightSeven, ite_eq_right (not_le.mpr hx)])
  have hInt : Integrable (id : ℝ → ℝ) μleft :=
    integrable_restrict_Icc id continuous_id 0 (1/2)
  have h1 := MeasureTheory.condExp_congr_ae
    (m := MeasurableSpace.comap (id : ℝ → ℝ)
      (inferInstance : MeasurableSpace ℝ)) hae
  have h2 := version_comap_id (id : ℝ → ℝ) hInt
  have h3 : (fun ω => id (id ω)) =ᵐ[μleft] fun ω => mRightSeven (id ω) := by
    filter_upwards [hae] with ω hω
    exact hω.symm
  show μleft[mRightSeven | _] =ᵐ[μleft] fun ω => mRightSeven (id ω)
  exact h1.trans (h2.trans h3)

/-- Right support fails on `[0,1/2]`. -/
theorem RD_right_support_zero (δ : ℝ) :
    μleft ((id : ℝ → ℝ) ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) = 0 := by
  show (volume.restrict (Set.Icc (0:ℝ) (1/2)))
    ((id : ℝ → ℝ) ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)) = 0
  have hset : (id : ℝ → ℝ) ⁻¹' Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ)
      = Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ) := by
    ext x
    simp
  rw [hset, Measure.restrict_apply measurableSet_Ioo]
  have hempty : Set.Ioo (1/2:ℝ) ((1/2:ℝ) + δ) ∩ Set.Icc (0:ℝ) (1/2)
      = ∅ := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Icc,
      Set.mem_empty_iff_false, iff_false]
    intro h
    exact absurd h.2.2 (not_le.mpr h.1.1)
  rw [hempty, measure_empty]

/-- Non-identification: without right support two versions jump
differently. -/
theorem RD_right_nonident_exists :
    ∃ (m m' : ℝ → ℝ) (a b a' b' : ℝ),
      (((μleft[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
                (fun x : ℝ => x + 2) |
              MeasurableSpace.comap (id : ℝ → ℝ)
                (inferInstance : MeasurableSpace ℝ)]
            =ᵐ[μleft] fun ω => m (id ω))
          ∧ Tendsto m (𝓝[<] (1/2:ℝ)) (𝓝 a)
          ∧ Tendsto m (𝓝[>] (1/2:ℝ)) (𝓝 b))
        ∧ (((μleft[MathlibExt.Probability.Causality.observed {ω | (1/2:ℝ) ≤ id ω} (id : ℝ → ℝ)
                (fun x : ℝ => x + 2) |
              MeasurableSpace.comap (id : ℝ → ℝ)
                (inferInstance : MeasurableSpace ℝ)]
            =ᵐ[μleft] fun ω => m' (id ω))
          ∧ Tendsto m' (𝓝[<] (1/2:ℝ)) (𝓝 a')
          ∧ Tendsto m' (𝓝[>] (1/2:ℝ)) (𝓝 b'))
        ∧ b - a ≠ b' - a')) := by
  refine ⟨mPieceAdd2, mRightSeven, 1/2, 5/2, 1/2, 7, ⟨?_, ?_, ?_⟩,
    ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [observed_eq_mPieceAdd2]
    exact version_mPieceAdd2_left
  · exact tendsto_piece_left (L := (id : ℝ → ℝ)) (R := fun x : ℝ => x + 2)
      (c := (1/2:ℝ)) continuousAt_id
  · have hlim := tendsto_piece_right (L := (id : ℝ → ℝ))
      (R := fun x : ℝ => x + 2) (c := (1/2:ℝ))
      (continuous_id.add continuous_const).continuousAt
    rw [show ((1/2:ℝ) + 2) = 5/2 from by norm_num] at hlim
    exact hlim
  · rw [observed_eq_mPieceAdd2]
    have h1 := MeasureTheory.condExp_congr_ae
      (m := MeasurableSpace.comap (id : ℝ → ℝ)
        (inferInstance : MeasurableSpace ℝ)) ae_piece_eq_rightSeven_left
    exact h1.trans version_mRightSeven_left
  · exact tendsto_piece_left (L := (id : ℝ → ℝ)) (R := fun _ : ℝ => (7:ℝ))
      (c := (1/2:ℝ)) continuousAt_id
  · have hlim := tendsto_piece_right (L := (id : ℝ → ℝ))
      (R := fun _ : ℝ => (7:ℝ)) (c := (1/2:ℝ)) continuous_const.continuousAt
    exact hlim
  · norm_num

end MathlibExtTest.Probability.Causality.RegressionDiscontinuity




