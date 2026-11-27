/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.ApproximateDifferentialPrivacy
public import CSLibExt.Crypto.Privacy.Basic
public import Mathlib.Probability.Kernel.Defs

/-!
# Measure-valued differential privacy for Markov kernels

`IsMeasureDP` is the kernel analogue of `IsApproxDP`: a Markov kernel
satisfies `(ε, δ)`-DP when every measurable event obeys the
`exp ε`-multiplicative plus `δ`-additive bound on ordered adjacent pairs.
It is a compatibility layer over `Cslib.Crypto.Privacy.DifferentiallyPrivate`,
so that predicate's monotonicity, post-processing, group-privacy and
composition API applies directly to the kernel measures.

`pmfKernel` turns a discrete `D → PMF Ω` mechanism into a Markov kernel,
and `isApproxDP_iff_isMeasureDP` shows the two predicates coincide on
countable discrete spaces, via the bridge
`isApproxDP_iff_differentiallyPrivate_toMeasure`.
-/

@[expose] public section

namespace CSLibExt.Privacy.DifferentialPrivacy

/-- Approximate `(ε, δ)`-DP for a Markov kernel: nonnegative budgets plus
the existing measure-valued predicate applied to the kernel measures. -/
def IsMeasureDP {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    (κ : ProbabilityTheory.Kernel D Ω) [ProbabilityTheory.IsMarkovKernel κ]
    (adj : D → D → Prop) (ε δ : ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ Cslib.Crypto.Privacy.DifferentiallyPrivate adj
    (fun d => κ d) ε (ENNReal.ofReal δ)

/-- With `δ = 0`, kernel DP is the pure multiplicative event bound. -/
theorem isMeasureDP_delta_zero_iff {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] {κ : ProbabilityTheory.Kernel D Ω}
    [ProbabilityTheory.IsMarkovKernel κ] {adj : D → D → Prop} {ε : ℝ} :
    IsMeasureDP κ adj ε 0 ↔
      0 ≤ ε ∧ ∀ d d₂, adj d d₂ → ∀ s : Set Ω, MeasurableSet s →
        κ d s ≤ ENNReal.ofReal (Real.exp ε) * κ d₂ s := by
  simp only [IsMeasureDP, Cslib.Crypto.Privacy.DifferentiallyPrivate,
    ENNReal.ofReal_zero, add_zero, le_refl, true_and]

/-- A discrete mechanism as a Markov kernel via `PMF.toMeasure`.
Every function out of a countable space with measurable singletons is
measurable, which supplies the kernel measurability proof. -/
noncomputable def pmfKernel {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    (M : D → PMF Ω) : ProbabilityTheory.Kernel D Ω :=
  ProbabilityTheory.Kernel.mk (fun d => (M d).toMeasure)
    (measurable_of_countable _)

instance {D Ω : Type*} [MeasurableSpace D] [MeasurableSpace Ω]
    [Countable D] [MeasurableSingletonClass D] (M : D → PMF Ω) :
    ProbabilityTheory.IsMarkovKernel (pmfKernel M) where
  isProbabilityMeasure _ := PMF.toMeasure.isProbabilityMeasure _

@[simp]
theorem pmfKernel_apply {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    (M : D → PMF Ω) (d : D) : (pmfKernel M) d = (M d).toMeasure := rfl

/-- On countable discrete spaces, event-level approximate DP and the
existing measure-valued predicate coincide on `PMF.toMeasure`.
`DiscreteMeasurableSpace Ω` is derived, not assumed: it comes
from `Countable Ω` plus `MeasurableSingletonClass Ω` via
`MeasurableSingletonClass.toDiscreteMeasurableSpace`. -/
theorem isApproxDP_iff_differentiallyPrivate_toMeasure {D Ω : Type*}
    [MeasurableSpace Ω]
    [Countable Ω] [MeasurableSingletonClass Ω]
    {M : D → PMF Ω} {adj : D → D → Prop} {ε δ : ℝ} :
    IsApproxDP M adj ε δ ↔ 0 ≤ ε ∧ 0 ≤ δ ∧
      Cslib.Crypto.Privacy.DifferentiallyPrivate adj
        (fun d => (M d).toMeasure) ε (ENNReal.ofReal δ) := by
  constructor
  · rintro ⟨hε, hδ, h⟩
    refine ⟨hε, hδ, fun d d₂ hadj s _ => ?_⟩
    simp only [PMF.toMeasure_apply_eq_toOuterMeasure]
    exact h d d₂ hadj s
  · rintro ⟨hε, hδ, h⟩
    refine ⟨hε, hδ, fun d d₂ hadj s => ?_⟩
    have h' := h hadj s MeasurableSet.of_discrete
    simp only [PMF.toMeasure_apply_eq_toOuterMeasure] at h'
    exact h'

/-- On countable discrete spaces, event-level approximate DP and kernel DP
coincide. -/
theorem isApproxDP_iff_isMeasureDP {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    [Countable Ω] [MeasurableSingletonClass Ω]
    {M : D → PMF Ω} {adj : D → D → Prop} {ε δ : ℝ} :
    IsApproxDP M adj ε δ ↔ IsMeasureDP (pmfKernel M) adj ε δ := by
  simp only [isApproxDP_iff_differentiallyPrivate_toMeasure, IsMeasureDP,
    pmfKernel_apply]

/-- A database-independent PMF mechanism is private with zero budgets. -/
theorem isApproxDP_const {D A : Type*} (p : PMF A)
    (adj : D → D → Prop) : IsApproxDP (fun _ => p) adj 0 0 :=
  isApproxDP_zero_iff.mpr (isDP_const p adj)

/-- A database-independent PMF mechanism is kernel-private with zero budgets. -/
theorem isMeasureDP_const {D Ω : Type*} [MeasurableSpace D]
    [MeasurableSpace Ω] [Countable D] [MeasurableSingletonClass D]
    [Countable Ω] [MeasurableSingletonClass Ω]
    (p : PMF Ω) (adj : D → D → Prop) :
    IsMeasureDP (pmfKernel fun _ => p) adj 0 0 :=
  isApproxDP_iff_isMeasureDP.mp (isApproxDP_const p adj)

end CSLibExt.Privacy.DifferentialPrivacy
