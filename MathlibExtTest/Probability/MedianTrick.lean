/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MedianTrick

open MeasureTheory ProbabilityTheory

/-- The median of a one-element family is that element. -/
example (c : ℝ) : medianOf (fun _ : Fin 1 => c) = c := by
  simp [medianOf]

/-- Boundary check `r = 1`: the median trick is the input bound amplified
to `exp (-1 / 8) > 1 / 4`. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {μ ε : ℝ} {X : Fin 1 → Ω → ℝ} (hX : iIndepFun X P) (hXm : ∀ i, Measurable (X i))
    (hbd : ∀ i, P {ω | ε < |X i ω - μ|} ≤ 1 / 4) :
    P {ω | ε < |medianOf (fun i => X i ω) - μ|} ≤
      ENNReal.ofReal (Real.exp (-(1 / 8 : ℝ))) := by
  simpa using median_trick (by decide) hX hXm hbd
