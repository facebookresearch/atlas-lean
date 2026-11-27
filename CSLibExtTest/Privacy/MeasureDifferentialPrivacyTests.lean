/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Privacy.MeasureDifferentialPrivacy
public import Mathlib.MeasureTheory.MeasurableSpace.Instances
public import Cslib.Probability.PMF

/-!
# Tests for measure-valued differential privacy

Constant `Bool` mechanisms with explicit PMFs go through the
`IsApproxDP`/`IsMeasureDP` bridge in both directions, including the
fair Bernoulli distribution, plus the `δ = 0` specialization.
-/

@[expose] public section

namespace CSLibExtTest.Privacy.DifferentialPrivacy

open CSLibExt.Privacy.DifferentialPrivacy

/-- The fair Bernoulli(1/2) distribution on `Bool`, as an explicit PMF. -/
noncomputable def fairBernoulli : PMF Bool :=
  Cslib.Probability.PMF.uniformOfFintype Bool

theorem approxDP_pure_const (adj : Bool → Bool → Prop) :
    IsApproxDP (fun _ : Bool => PMF.pure true) adj 0 0 :=
  isApproxDP_const (PMF.pure true) adj

theorem measureDP_pure_const (adj : Bool → Bool → Prop) :
    IsMeasureDP (pmfKernel fun _ : Bool => PMF.pure true) adj 0 0 :=
  isApproxDP_iff_isMeasureDP.mp (isApproxDP_const (PMF.pure true) adj)

theorem approxDP_of_measureDP_pure {adj : Bool → Bool → Prop}
    (h : IsMeasureDP (pmfKernel fun _ : Bool => PMF.pure true) adj 0 0) :
    IsApproxDP (fun _ : Bool => PMF.pure true) adj 0 0 :=
  isApproxDP_iff_isMeasureDP.mpr h

theorem measureDP_bernoulli_const (adj : Bool → Bool → Prop) :
    IsMeasureDP (pmfKernel fun _ : Bool => fairBernoulli) adj 0 0 :=
  isApproxDP_iff_isMeasureDP.mp (isApproxDP_const fairBernoulli adj)

theorem approxDP_of_measureDP_bernoulli {adj : Bool → Bool → Prop}
    (h : IsMeasureDP (pmfKernel fun _ : Bool => fairBernoulli) adj 0 0) :
    IsApproxDP (fun _ : Bool => fairBernoulli) adj 0 0 :=
  isApproxDP_iff_isMeasureDP.mpr h

theorem measureDP_delta_zero_pure (adj : Bool → Bool → Prop) :
    0 ≤ (0 : ℝ) ∧ ∀ d d₂, adj d d₂ → ∀ s : Set Bool, MeasurableSet s →
      (pmfKernel fun _ : Bool => PMF.pure true) d s ≤
        ENNReal.ofReal (Real.exp 0) *
          (pmfKernel fun _ : Bool => PMF.pure true) d₂ s :=
  isMeasureDP_delta_zero_iff.mp
    (isApproxDP_iff_isMeasureDP.mp (isApproxDP_const (PMF.pure true) adj))

theorem measureDP_of_delta_zero_pure (adj : Bool → Bool → Prop) :
    IsMeasureDP (pmfKernel fun _ : Bool => PMF.pure true) adj 0 0 :=
  isMeasureDP_delta_zero_iff.mpr (measureDP_delta_zero_pure adj)

/-- The bridge needs no discreteness on the index type: it applies to
mechanisms indexed by the non-countable type `Real`. -/
theorem approxDP_bridge_real_index (M : Real → PMF (Fin 2))
    (adj : Real → Real → Prop) (ε δ : ℝ) :
    IsApproxDP M adj ε δ ↔ 0 ≤ ε ∧ 0 ≤ δ ∧
      Cslib.Crypto.Privacy.DifferentiallyPrivate adj
        (fun d => (M d).toMeasure) ε (ENNReal.ofReal δ) :=
  isApproxDP_iff_differentiallyPrivate_toMeasure

#print axioms CSLibExt.Privacy.DifferentialPrivacy.isApproxDP_iff_isMeasureDP
#print axioms CSLibExt.Privacy.DifferentialPrivacy.isMeasureDP_const
#print axioms CSLibExtTest.Privacy.DifferentialPrivacy.measureDP_bernoulli_const

end CSLibExtTest.Privacy.DifferentialPrivacy
