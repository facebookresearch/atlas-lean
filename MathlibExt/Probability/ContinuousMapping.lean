/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Continuous mapping theorem

If `μs n` converges weakly to `μ` on `ℝ` and `g : ℝ → ℝ` is measurable with
`μ`-almost every point a continuity point of `g`, then the pushforwards
`(μs n).map g` converge weakly to `μ.map g`. The hypothesis is that the
discontinuity set of `g` is `μ`-null; in particular `g` need not be
continuous. This is the textbook continuous mapping theorem (see below).

## Source

This formalizes the target "Theorem (continuous mapping theorem)"
(Lecture 12, Convergence results section) of
`v1/Atlas/TheoryOfProbability/targets.yaml`: "Suppose `g` is measurable and
its set of discontinuity points has `μ_X` measure zero. Then
`X_n ⟹ X_∞` implies `g(X_n) ⟹ g(X)`." Its v1 formalization is
`v1/Atlas/TheoryOfProbability/code/ContinuousMapping.lean`
(`ProbabilityTheory.continuous_mapping`, fully proved in v1).

## Relation to Mathlib

Mathlib already has the continuous case:
`MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`
(pushforward by a *continuous* map preserves weak convergence). The
theorem below is strictly more general: `g` is only assumed measurable
and continuous `μ`-almost everywhere. It is not in Mathlib or MathlibExt.

## Main results

* `ProbabilityTheory.continuous_mapping`: the integral / bounded-continuous
  form of the theorem, in the shape of the v1 statement.
* `MeasureTheory.ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous`:
  the same theorem stated as weak convergence (`Tendsto`) of the
  pushforward probability measures.

## Proof outline

Use the Portmanteau open-set characterization of weak convergence in both
directions. For an open set `O`, the preimage `g ⁻¹' O` differs from its
interior only on the discontinuity set of `g`, hence has the same `μ`-measure
as its interior. The Portmanteau liminf bound for the interior then transfers
to the preimage, and hence to the pushforward measure of `O`.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory Set
open scoped Topology BoundedContinuousFunction

namespace ProbabilityTheory

/-- **Continuous mapping theorem** (Lecture 12), integral form.

If `g : ℝ → ℝ` is measurable and its set of discontinuity points has
`μ`-measure zero, and `μs n` converges weakly to `μ` (in the sense that
integrals of every bounded continuous test function converge), then the
pushforwards `(μs n).map g` converge weakly to `μ.map g` in the same sense. -/
theorem continuous_mapping
    (μs : ℕ → Measure ℝ) [∀ n, IsProbabilityMeasure (μs n)]
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (g : ℝ → ℝ) (hg_meas : Measurable g)
    (hg_ae : μ {x | ¬ContinuousAt g x} = 0)
    (hconv : ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂(μs n)) atTop (𝓝 (∫ x, f x ∂μ))) :
    ∀ f : ℝ →ᵇ ℝ,
      Tendsto (fun n ↦ ∫ x, f x ∂((μs n).map g)) atTop
        (𝓝 (∫ x, f x ∂(μ.map g))) := by
  let pμs : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨μs n, inferInstance⟩
  let pμ : ProbabilityMeasure ℝ := ⟨μ, inferInstance⟩
  have htendsto_orig : Tendsto pμs atTop (𝓝 pμ) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    exact hconv f
  have h_open_orig : ∀ G : Set ℝ, IsOpen G →
      μ G ≤ atTop.liminf (fun i ↦ μs i G) :=
    fun G hG ↦ ProbabilityMeasure.le_liminf_measure_open_of_tendsto htendsto_orig hG
  have h_open_push : ∀ O : Set ℝ, IsOpen O →
      (μ.map g) O ≤ atTop.liminf (fun i ↦ ((μs i).map g) O) := by
    intro O hO
    rw [Measure.map_apply hg_meas hO.measurableSet]
    have h_eq : μ (g ⁻¹' O) = μ (interior (g ⁻¹' O)) := by
      apply le_antisymm
      · have hsub : g ⁻¹' O \ interior (g ⁻¹' O) ⊆ {x | ¬ContinuousAt g x} := by
          intro x ⟨hx1, hx2⟩ hcont
          exact hx2 (mem_interior_iff_mem_nhds.mpr (hcont.preimage_mem_nhds (hO.mem_nhds hx1)))
        have h0 : μ (g ⁻¹' O \ interior (g ⁻¹' O)) = 0 := measure_mono_null hsub hg_ae
        calc μ (g ⁻¹' O)
            = μ (interior (g ⁻¹' O) ∪ (g ⁻¹' O \ interior (g ⁻¹' O))) := by
                rw [union_sdiff_cancel interior_subset]
          _ ≤ μ (interior (g ⁻¹' O)) + μ (g ⁻¹' O \ interior (g ⁻¹' O)) :=
                measure_union_le _ _
          _ = μ (interior (g ⁻¹' O)) := by rw [h0, add_zero]
      · exact measure_mono interior_subset
    rw [h_eq]
    calc μ (interior (g ⁻¹' O))
        ≤ atTop.liminf (fun i ↦ μs i (interior (g ⁻¹' O))) :=
          h_open_orig _ isOpen_interior
      _ ≤ atTop.liminf (fun i ↦ μs i (g ⁻¹' O)) :=
          liminf_le_liminf (Eventually.of_forall (fun i ↦ measure_mono interior_subset))
      _ = atTop.liminf (fun i ↦ ((μs i).map g) O) := by
          congr 1
          ext i
          rw [Measure.map_apply hg_meas hO.measurableSet]
  let pμs_push : ℕ → ProbabilityMeasure ℝ := fun n ↦ ⟨(μs n).map g, inferInstance⟩
  let pμ_push : ProbabilityMeasure ℝ := ⟨μ.map g, inferInstance⟩
  have htendsto_push : Tendsto pμs_push atTop (𝓝 pμ_push) := by
    apply tendsto_of_forall_isOpen_le_liminf_nat'
    exact h_open_push
  intro f
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp htendsto_push) f
  exact h

end ProbabilityTheory

namespace MeasureTheory

/-- **Continuous mapping theorem** (Lecture 12), probability-measure form.

If `g : ℝ → ℝ` is measurable and continuous `μ`-almost everywhere, then
weak convergence `μs n ⟹ μ` implies weak convergence of the pushforwards
`(μs n).map g ⟹ μ.map g`. This generalizes Mathlib's
`ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous`, which assumes
`g` continuous everywhere. -/
theorem ProbabilityMeasure.tendsto_map_of_tendsto_of_ae_continuous
    {μs : ℕ → ProbabilityMeasure ℝ} {μ : ProbabilityMeasure ℝ}
    {g : ℝ → ℝ} (hg_meas : Measurable g)
    (hg_ae : (μ : Measure ℝ) {x | ¬ContinuousAt g x} = 0)
    (hconv : Tendsto μs atTop (𝓝 μ)) :
    Tendsto (fun n ↦ (μs n).map g) atTop (𝓝 (μ.map g)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hconv ⊢
  intro f
  have h := ProbabilityTheory.continuous_mapping
    (fun n ↦ (μs n : Measure ℝ)) (μ : Measure ℝ) g hg_meas hg_ae (hconv) f
  exact h

end MeasureTheory
