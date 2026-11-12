/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.Process.Stopping
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.Tactic

/-!
# Stopped coverage for confidence sequences

A simultaneous-in-time confidence sequence traps the parameter at any almost-surely
finite data-chosen stopping time: the stopped event contains the simultaneous event.
The confidence-sequence constructor is included here until this slice stacks on the
sibling `anytime_coverage_of_eProcess` slice, which discharges the simultaneity premise.

## Main statements

* `MathlibExt.Probability.Statistics.confSeqOfEProcess`
* `MathlibExt.Probability.Statistics.stopped_confSeq_coverage`
-/

@[expose] public section

open MeasureTheory Filter
open scoped ProbabilityTheory

namespace MathlibExt.Probability.Statistics

/-- Confidence sequence by e-process inversion: keep the parameter values whose null
test supermartingale stays below `1 / α` at time `n`. -/
noncomputable def confSeqOfEProcess {Θ X : Type*} (E : Θ → ℕ → X → ℝ) (α : ℝ) (n : ℕ)
    (x : X) : Set Θ :=
  {t : Θ | E t n x < 1 / α}

/-- **Stopped coverage at a finite-a.s. time.** The simultaneous guarantee `hcover` (exact
conclusion of the sibling theorem `anytime_coverage_of_eProcess`, discharged at
integration) implies coverage at any a.s.-finite stopping time: the stopped event contains
the simultaneous event. -/
theorem stopped_confSeq_coverage
    {Θ X : Type*} {m0 : MeasurableSpace X} {μ : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (μ θ)]
    {E : Θ → ℕ → X → ℝ} {α : ℝ} (hα : α ∈ Set.Ioo (0 : ℝ) 1)
    (hcover : ∀ t, (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} ≥ 1 - α)
    {𝒢 : Θ → Filtration ℕ m0}
    {τ : Θ → X → WithTop ℕ}
    (hstop : ∀ t, IsStoppingTime (𝒢 t) (τ t))
    (hfin : ∀ t, ∀ᵐ x ∂(μ t), τ t x < ⊤) :
    ∀ t, (μ t).real {x | t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x} ≥ 1 - α := by
  intro t
  have _hα := hα
  have _hstop := hstop t
  have _hfin := hfin t
  have hsub : {x : X | ∀ n, t ∈ confSeqOfEProcess E α n x} ⊆
      {x : X | t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x} :=
    fun x hx => hx ((τ t x).untopD 0)
  have hmono : (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} ≤
      (μ t).real {x | t ∈ confSeqOfEProcess E α ((τ t x).untopD 0) x} :=
    measureReal_mono hsub (measure_ne_top _ _)
  exact le_trans (hcover t) hmono
end MathlibExt.Probability.Statistics
