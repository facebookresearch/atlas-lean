/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.StoppedSumMaximal

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Set
open MathlibExt.Probability.StoppedSumMaximal

namespace MathlibExtTest.Probability.StoppedSumMaximal

/-- Signature restatement: square-integrability of a stopped partial sum,
general-filtration form. -/
theorem integrable_stopped_partialSum_sq_test {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_int : Integrable (X 0) μ)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    {ℱ : Filtration ℕ m0}
    (hIndep : ∀ k, Indep (MeasurableSpace.comap (X k) inferInstance) (ℱ k) μ)
    (hadapt : ∀ k, Measurable[ℱ (k + 1)] (X k))
    {τ : Ω → ℕ} (hT : IsStoppingTime ℱ (fun ω => (τ ω : WithTop ℕ)))
    (hτ_int : Integrable (fun ω => (τ ω : ℝ)) μ) :
    Integrable (fun ω => (∑ i ∈ Finset.range (τ ω), X i ω) ^ 2) μ :=
  integrable_stopped_partialSum_sq hX_iid hX_int hX_sq_int hmean hIndep hadapt hT hτ_int

/-- Signature restatement: square-integrability of the maximal stopped partial
sum, in v1's form. -/
theorem integrable_maximal_stopped_partial_sum_sq_test {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_iid : ∀ i j, IdentDistrib (X i) (X j) μ μ)
    (hX_ind : iIndepFun (β := fun _ => ℝ) X μ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_int : Integrable (X 0) μ)
    (hmean : ∫ ω, X 0 ω ∂μ = 0)
    (hX_sq_int : Integrable (fun ω => (X 0 ω) ^ 2) μ)
    {T : Ω → ℕ}
    (hT : IsStoppingTime (predictableFiltration m0 X hX_meas) (fun ω => (T ω : WithTop ℕ)))
    (hT_int : Integrable (fun ω => (T ω : ℝ)) μ) :
    Integrable (fun ω => (Finset.range (T ω + 1)).sup'
      ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
      (fun k => (∑ i ∈ Finset.range k, X i ω) ^ 2)) μ :=
  integrable_maximal_stopped_partial_sum_sq hX_iid hX_ind hX_meas hX_int hmean hX_sq_int hT
    hT_int

/-- Degenerate example: the zero sequence, stopped at the constant time `5`,
has a square-integrable stopped partial sum (it is `0`). This exercises the
general-filtration theorem with the trivial filtration `⊥`. -/
theorem integrable_stopped_partialSum_sq_zero {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] :
    Integrable (fun ω => (∑ i ∈ Finset.range (5 : ℕ),
      (fun _ : ℕ => fun _ : Ω => (0 : ℝ)) i ω) ^ 2) μ := by
  apply integrable_stopped_partialSum_sq (X := fun _ _ => (0 : ℝ))
    (ℱ := ⊥) (τ := fun _ => 5)
  · intro i j
    exact IdentDistrib.refl measurable_const.aemeasurable
  · exact integrable_const _
  · simp
  · simp
  · intro k
    exact indep_bot_right _
  · intro k
    exact measurable_const
  · exact isStoppingTime_const ⊥ _
  · exact integrable_const _

#print axioms integrable_stopped_partialSum_sq_zero

/-- The zero sequence is jointly independent on the nonempty Dirac probability space. -/
private theorem zero_sequence_iIndep :
    iIndepFun (fun _ : ℕ => fun _ : Unit => (0 : ℝ)) (Measure.dirac ()) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro s sets hsets
  simp [Set.indicator, Finset.prod_boole]

/-- The maximal theorem applies at `T = 0`, including the empty partial sum `S₀`. -/
theorem integrable_maximal_stopped_partial_sum_sq_zero :
    Integrable (fun ω : Unit => (Finset.range ((0 : ℕ) + 1)).sup'
      Finset.nonempty_range_add_one
      (fun k => (∑ i ∈ Finset.range k,
        (fun _ : ℕ => fun _ : Unit => (0 : ℝ)) i ω) ^ 2)) (Measure.dirac ()) := by
  exact integrable_maximal_stopped_partial_sum_sq
    (X := fun _ _ => (0 : ℝ)) (T := fun _ => 0)
    (fun _ _ => IdentDistrib.refl measurable_const.aemeasurable) zero_sequence_iIndep
    (fun _ => measurable_const) (integrable_const _) (by simp) (by simp)
    (isStoppingTime_const _ _) (integrable_const _)

/-- The predictable filtration starts with the trivial measurable space. -/
theorem predictableFiltration_zero_test {Ω : Type*} {m0 : MeasurableSpace Ω}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i)) :
    predictableFiltration m0 X hX_meas 0 = ⊥ :=
  predictableFiltration_zero hX_meas

/-- One identity observation generates the ambient Borel measurable space at time one. -/
theorem predictableFiltration_one_identity :
    predictableFiltration (inferInstance : MeasurableSpace ℝ) (fun _ : ℕ => id)
      (fun _ => measurable_id) 1 = (inferInstance : MeasurableSpace ℝ) := by
  simpa using predictableFiltration_succ (X := fun _ : ℕ => id) (fun _ => measurable_id) 0

/-- The successor characterization supplies the adaptedness needed by the general API. -/
theorem measurable_predictableFiltration_succ_test {Ω : Type*} {m0 : MeasurableSpace Ω}
    {X : ℕ → Ω → ℝ} (hX_meas : ∀ i, Measurable (X i)) (k : ℕ) :
    Measurable[predictableFiltration m0 X hX_meas (k + 1)] (X k) := by
  rw [measurable_iff_comap_le, predictableFiltration_succ]
  exact le_sup_right

/-- The zero process uses the canonical Wald independence orientation without
a separate global-measurability premise. -/
theorem integrable_stopped_partialSum_sq_canonical_zero :
    Integrable (fun ω : Unit => (∑ i ∈ Finset.range (5 : ℕ),
      (fun _ : ℕ => fun _ : Unit => (0 : ℝ)) i ω) ^ 2) (Measure.dirac ()) := by
  exact integrable_stopped_partialSum_sq
    (X := fun _ _ => (0 : ℝ)) (ℱ := ⊥) (τ := fun _ => 5)
    (fun _ _ => IdentDistrib.refl measurable_const.aemeasurable)
    (integrable_const _) (by simp) (by simp)
    (fun _ => indep_bot_right _) (fun _ => measurable_const)
    (isStoppingTime_const ⊥ _) (integrable_const _)

/-- At time zero the maximum includes `S₀` and has value zero for every sequence. -/
theorem maximal_time_zero_eq {Ω : Type*} (X : ℕ → Ω → ℝ) (ω : Ω) :
    (Finset.range ((0 : ℕ) + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (∑ i ∈ Finset.range k, X i ω) ^ 2) = 0 := by
  simp

/-- The same concrete independent process also exercises a positive maximal horizon. -/
theorem integrable_maximal_stopped_partial_sum_sq_zero_at_five :
    Integrable (fun ω : Unit => (Finset.range ((5 : ℕ) + 1)).sup'
      Finset.nonempty_range_add_one
      (fun k => (∑ i ∈ Finset.range k,
        (fun _ : ℕ => fun _ : Unit => (0 : ℝ)) i ω) ^ 2)) (Measure.dirac ()) := by
  exact integrable_maximal_stopped_partial_sum_sq
    (X := fun _ _ => (0 : ℝ)) (T := fun _ => 5)
    (fun _ _ => IdentDistrib.refl measurable_const.aemeasurable) zero_sequence_iIndep
    (fun _ => measurable_const) (integrable_const _) (by simp) (by simp)
    (isStoppingTime_const _ _) (integrable_const _)

/-- The maximum squares before taking the supremum and includes the final index. -/
theorem maximal_time_one_includes_endpoint :
    (Finset.range ((1 : ℕ) + 1)).sup' Finset.nonempty_range_add_one
      (fun k => (∑ _i ∈ Finset.range k, (-3 : ℝ)) ^ 2) = 9 := by
  norm_num [Finset.range_add_one]

end MathlibExtTest.Probability.StoppedSumMaximal
