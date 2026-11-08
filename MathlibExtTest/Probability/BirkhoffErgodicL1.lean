/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BirkhoffErgodicL1

@[expose] public section

open MeasureTheory Filter Topology
open scoped Topology

namespace MathlibExtTest.Probability.BirkhoffErgodicL1

open MathlibExt.Probability.BirkhoffErgodicL1

/-- The main theorem, restated with hypotheses inlined, as a smoke test. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : Ergodic T μ) {g : α → ℝ} (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖ ∂μ)
      atTop (𝓝 0) :=
  birkhoff_ergodic_theorem_L1 hT hg

/-- Contraction: averaging cannot increase the `L¹` distance. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hmp : MeasurePreserving T μ μ) {g h : α → ℝ}
    (hg : Integrable g μ) (hh : Integrable h μ) (n : ℕ) :
    ∫ x, ‖birkhoffAverage ℝ T g n x - birkhoffAverage ℝ T h n x‖ ∂μ ≤
      ∫ x, ‖g x - h x‖ ∂μ :=
  integral_norm_birkhoffAverage_sub_le hmp hg hh n

/-- For `0 < n`, averaging preserves the integral. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hmp : MeasurePreserving T μ μ) {u : α → ℝ} (hu : Integrable u μ)
    {n : ℕ} (hn : 0 < n) :
    ∫ x, birkhoffAverage ℝ T u n x ∂μ = ∫ x, u x ∂μ :=
  integral_birkhoffAverage_of_measurePreserving hmp hu hn

/-- Averages of a bounded observable converge in `L¹`. -/
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (hT : Ergodic T μ) {g : α → ℝ} (hg : Integrable g μ)
    {M : ℝ} (hM : 0 ≤ M) (hgb : ∀ x, ‖g x‖ ≤ M) :
    Tendsto (fun n => ∫ x, ‖birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ‖ ∂μ)
      atTop (𝓝 0) :=
  tendsto_integral_norm_birkhoffAverage_of_bounded hT hg hM hgb

/-- The identity on a one-point probability space is ergodic: the only
measurable sets are `∅` and the whole space, each of measure `0` or `1`. -/
theorem ergodic_id_unit : Ergodic (id : Unit → Unit) (Measure.dirac ()) := by
  refine ⟨MeasurePreserving.id _, ⟨fun s _hs _hinv => ?_⟩⟩
  rw [Filter.eventuallyEmptyOrUniv_iff]
  by_cases hs : s = ∅
  · right
    filter_upwards with x
    simp [hs]
  · left
    have hsu : s = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hs
      rw [Subsingleton.elim x y]
      exact hy
    filter_upwards with x
    rw [hsu]
    exact Set.mem_univ x

/-- Concrete check: on the one-point space, the Birkhoff averages of the
constant observable `3` converge in `L¹` to `∫ 3 = 3`. -/
example : Tendsto
    (fun n => ∫ x, ‖birkhoffAverage ℝ (id : Unit → Unit) (fun _ => (3 : ℝ)) n x
      - ∫ _y, (3 : ℝ) ∂(Measure.dirac ())‖ ∂(Measure.dirac ()))
    atTop (𝓝 0) :=
  birkhoff_ergodic_theorem_L1 ergodic_id_unit (integrable_const (3 : ℝ))

/-- Concrete check: averaging preserves the integral on the one-point space. -/
example : ∀ n : ℕ, 0 < n →
    ∫ x, birkhoffAverage ℝ (id : Unit → Unit) (fun _ => (3 : ℝ)) n x
      ∂(Measure.dirac ()) = 3 := by
  intro n hn
  have h := integral_birkhoffAverage_of_measurePreserving (μ := Measure.dirac ())
    (T := id) (MeasurePreserving.id _) (integrable_const (3 : ℝ)) hn
  rw [h]
  simp

#print axioms birkhoff_ergodic_theorem_L1
#print axioms tendsto_integral_norm_birkhoffAverage_of_bounded
#print axioms integral_norm_birkhoffAverage_sub_le
#print axioms ergodic_id_unit

end MathlibExtTest.Probability.BirkhoffErgodicL1
