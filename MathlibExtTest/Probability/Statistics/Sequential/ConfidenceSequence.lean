/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sequential.ConfidenceSequence

/-!
# Tests for stopped coverage of confidence sequences

A finite deterministic time recovers fixed-time coverage through the main theorem, and
the infinite time is outside the almost-sure-finiteness hypothesis.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace MathlibExt.Probability.Statistics

-- Positive: a finite deterministic time recovers fixed-time coverage through the main
-- theorem. The two-argument constant family is a stopping time (via
-- isStoppingTime_const) and is a.s. finite (every constant is below top); the
-- conclusion follows by applying stopped_confSeq_coverage to that exact tau.
example {Θ X : Type*} {m0 : MeasurableSpace X} {μ : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (μ θ)]
    {E : Θ → ℕ → X → ℝ} {α : ℝ}
    (hEmeas : ∀ t n, Measurable (E t n))
    (hcover : ∀ t, (μ t).real {x | ∀ n, t ∈ confSeqOfEProcess E α n x} ≥ 1 - α)
    {𝒢 : Θ → Filtration ℕ m0} (n : ℕ) :
    ∀ t, (μ t).real {x | ((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t x) < ⊤ ∧ t ∈ confSeqOfEProcess E α (((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t x).untopD 0) x} ≥ 1 - α := by
  have hstop : ∀ t, IsStoppingTime (𝒢 t) ((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t) :=
    fun t => isStoppingTime_const (𝒢 t) n
  have hfin : ∀ t, ∀ᵐ x ∂(μ t), ((fun (_ : Θ) (_ : X) => (↑n : WithTop ℕ)) t x) < ⊤ :=
    fun t => ae_of_all _ fun _ => WithTop.coe_lt_top n
  exact stopped_confSeq_coverage hEmeas hcover hstop hfin
