/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GeneralizationBounds.FiniteClass
public import Mathlib.MeasureTheory.Constructions.Pi

/-! # Representative samples and uniform convergence -/

@[expose] public section

set_option autoImplicit false

namespace Cslib.MachineLearning.PACLearning

open MeasureTheory
open CSLibExt.MachineLearning.GeneralizationBounds (empiricalRisk risk measurable_empiricalRisk)

variable {Z H : Type*} [MeasurableSpace Z]

/-- A nonempty sample is `ε`-representative if every hypothesis in `H` satisfies
`|empiricalRisk L S h - risk L D h| ≤ ε`. This formulation also covers the empty class.

For the textbook interpretation as a comparison with expected losses, each `L h` must be
integrable under `D`. This predicate itself uses the existing real-valued `risk` as is:
for a nonintegrable loss, the Bochner integral returns zero (`integral_undef`), not an
infinite expected loss. `IsUniformConvergenceBound` restricts to laws with integrable losses.
The API also allows signed real losses.

Source: Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Definition 4.1. -/
def IsRepresentative {m : ℕ} [NeZero m] (L : H → Z → ℝ) (D : Measure Z)
    [IsProbabilityMeasure D] (S : Fin m → Z) (ε : ℝ) : Prop :=
  ∀ h : H, |empiricalRisk L S h - risk L D h| ≤ ε

/-- For a countable hypothesis class with measurable losses, the representative-sample event
is measurable. No countability hypothesis is built into representativeness itself. -/
theorem measurableSet_isRepresentative [Countable H] {m : ℕ} [NeZero m]
    {L : H → Z → ℝ} (hL : ∀ h, Measurable (L h)) (D : Measure Z)
    [IsProbabilityMeasure D] (ε : ℝ) :
    MeasurableSet {S : Fin m → Z | IsRepresentative L D S ε} := by
  have hevent : {S : Fin m → Z | IsRepresentative L D S ε} =
      ⋂ h : H, {S : Fin m → Z | |empiricalRisk L S h - risk L D h| ≤ ε} := by
    ext S
    simp [IsRepresentative]
  rw [hevent]
  exact MeasurableSet.iInter fun h => measurableSet_le
    (continuous_abs.measurable.comp
      ((measurable_empiricalRisk (fun i => measurable_pi_apply i) hL h).sub_const (risk L D h)))
    measurable_const

/-- `N` is a distribution-independent uniform convergence bound for `L` if, for each
`ε, δ ∈ (0, 1)`, every probability law under which the losses are integrable, and every positive
sample size `m ≥ N ε δ`, an i.i.d. sample is `ε`-representative with probability at least `1 - δ`.
The event is required to be measurable; this definition does not use inner probability.

Source: Shalev-Shwartz and Ben-David, *Understanding Machine Learning*, Definition 4.3. -/
def IsUniformConvergenceBound (L : H → Z → ℝ) (N : ℝ → ℝ → ℕ) : Prop :=
  ∀ ε δ : ℝ, ε ∈ Set.Ioo 0 1 → δ ∈ Set.Ioo 0 1 →
    ∀ (D : Measure Z) [IsProbabilityMeasure D], (∀ h, Integrable (L h) D) →
      ∀ (m : ℕ) [NeZero m], N ε δ ≤ m →
        MeasurableSet {S : Fin m → Z | IsRepresentative L D S ε} ∧
          1 - δ ≤ (Measure.pi fun _ : Fin m => D).real
            {S : Fin m → Z | IsRepresentative L D S ε}

/-- The loss on the hypothesis class has the uniform convergence property if it admits a
uniform convergence bound. This does not assert that a given bound is pointwise minimal. -/
def HasUniformConvergence (L : H → Z → ℝ) : Prop :=
  ∃ N : ℝ → ℝ → ℕ, IsUniformConvergenceBound L N

end Cslib.MachineLearning.PACLearning
