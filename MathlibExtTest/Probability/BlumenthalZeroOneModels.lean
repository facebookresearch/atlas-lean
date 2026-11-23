/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BlumenthalZeroOne
public import Mathlib.Probability.Distributions.Bernoulli

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace MathlibExt.Probability.BlumenthalZeroOneTest

open MathlibExt.Probability.BlumenthalZeroOne

/-!
# A fair-coin model for the arbitrary-filtration boundary

The measure and process below are constructed, with no assumed process witness
or event probability. The natural germ of the zero process is trivial; a
filtration containing an independent coin at every time has a nontrivial germ.
-/

/-- The canonical two-point distribution giving each Boolean probability `1/2`. -/
noncomputable def fairBool : Measure Bool :=
  bernoulliMeasure true false ⟨1 / 2, by constructor <;> norm_num⟩

instance fairBool_isProbabilityMeasure : IsProbabilityMeasure fairBool := by
  unfold fairBool
  infer_instance

/-- The deterministic zero path on the fair-coin space. -/
def zeroProcess : NNReal → Bool → ℝ := fun _ _ => 0

theorem zeroProcess_measurable (t : NNReal) : Measurable (zeroProcess t) :=
  measurable_const

/-- A real-valued coin, equal to `1` on `true` and `0` on `false`. -/
def coin (b : Bool) : ℝ := if b then 1 else 0

theorem coin_measurable : Measurable coin := measurable_from_top

/-- The zero process satisfies the continuous-independent-increment contract,
for any filtration on the fair-coin space. -/
theorem zeroProcess_spec (𝓕 : Filtration NNReal (inferInstance : MeasurableSpace Bool)) :
    IsContinuousIndependentIncrementProcess zeroProcess 𝓕 fairBool 0 where
  isProbabilityMeasure := inferInstance
  start := Filter.Eventually.of_forall (fun _ => rfl)
  adapted := fun _ => measurable_const
  indep_incr := by
    intro s t _
    simpa [zeroProcess] using (indep_bot_right (𝓕 s) (μ := fairBool))
  continuous_path := Filter.Eventually.of_forall (fun _ => continuous_const)

/-- The nontrivial coin event has its computed probability, without an `hHalf` assumption. -/
theorem coin_event_probability : fairBool {b | coin b = 1} = 1 / 2 := by
  have hset : {b | coin b = 1} = {true} := by
    ext b
    cases b <;> norm_num [coin]
  rw [hset]
  have hreal : (fairBool {true}).toReal = (1 / 2 : ℝ) := by
    change (bernoulliMeasure true false ⟨1 / 2, by constructor <;> norm_num⟩).real {true}
      = (1 / 2 : ℝ)
    simp
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top fairBool _) (by norm_num)).mp
  simpa using hreal

/-- The computed coin event is neither null nor conull. -/
theorem coin_event_nontrivial :
    fairBool {b | coin b = 1} ≠ 0 ∧ fairBool {b | coin b = 1} ≠ 1 := by
  rw [coin_event_probability]
  constructor
  · intro h
    have hreal := congrArg ENNReal.toReal h
    norm_num at hreal
  · intro h
    have hreal := congrArg ENNReal.toReal h
    norm_num at hreal

/-- The coin completely reveals the Boolean sample point. -/
theorem coin_comap_eq_top : MeasurableSpace.comap coin inferInstance = ⊤ := by
  have hinj : Function.Injective coin := by
    intro a b h
    cases a <;> cases b <;> simp_all [coin]
  apply le_antisymm le_top
  intro s _
  refine MeasurableSpace.measurableSet_comap.mpr ⟨coin '' s, ?_, ?_⟩
  · exact ((Set.toFinite s).image coin).measurableSet
  · ext b
    constructor
    · rintro ⟨a, ha, h⟩
      exact hinj h ▸ ha
    · intro hb
      exact ⟨b, hb, rfl⟩

/-- Every event is visible in the germ of the constant top filtration. -/
theorem top_germ_eq_top :
    germSigmaAlgebraZero (⊤ : Filtration NNReal (inferInstance : MeasurableSpace Bool)) = ⊤ := by
  change (⨅ (t : NNReal) (_ : 0 < t), (⊤ : MeasurableSpace Bool)) = ⊤
  simp

/-- A constructed countermodel to an arbitrary-filtration zero-one claim
under the original weak specification. -/
theorem constant_zero_top_countermodel :
    IsContinuousIndependentIncrementProcess zeroProcess ⊤ fairBool 0 ∧
      MeasurableSet[germSigmaAlgebraZero
        (⊤ : Filtration NNReal (inferInstance : MeasurableSpace Bool))] {b | coin b = 1} ∧
      fairBool {b | coin b = 1} = 1 / 2 ∧
      fairBool {b | coin b = 1} ≠ 0 ∧ fairBool {b | coin b = 1} ≠ 1 := by
  refine ⟨zeroProcess_spec _, ?_, coin_event_probability,
    coin_event_nontrivial.1, coin_event_nontrivial.2⟩
  rw [top_germ_eq_top]
  trivial

/-- The zero process reveals no information at any time in its natural filtration. -/
theorem zeroProcess_naturalFiltration (t : NNReal) :
    naturalFiltration zeroProcess zeroProcess_measurable t = ⊥ := by
  change (⨆ (u : NNReal) (_ : u ≤ t),
    MeasurableSpace.comap (fun _ : Bool => (0 : ℝ)) inferInstance) = ⊥
  simp

/-- The natural germ of the same zero process is the bottom sigma-algebra. -/
theorem zeroProcess_naturalGerm : naturalGerm zeroProcess zeroProcess_measurable = ⊥ := by
  apply le_antisymm ?_ bot_le
  exact (germ_le_of_pos (naturalFiltration zeroProcess zeroProcess_measurable) one_pos).trans
    (le_of_eq (zeroProcess_naturalFiltration 1))

/-- The nontrivial coin event is excluded from the natural germ. -/
theorem coin_event_not_mem_naturalGerm :
    ¬ MeasurableSet[naturalGerm zeroProcess zeroProcess_measurable] {b | coin b = 1} := by
  intro h
  have hzeroOne := zero_one_naturalGerm (zeroProcess_spec ⊤) zeroProcess_measurable h
  exact hzeroOne.elim coin_event_nontrivial.1 coin_event_nontrivial.2

end MathlibExt.Probability.BlumenthalZeroOneTest
