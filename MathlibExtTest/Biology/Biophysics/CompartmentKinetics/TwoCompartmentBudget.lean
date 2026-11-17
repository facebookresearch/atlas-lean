/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget

/-! Tests: zero-window budget. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget

open MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget

/-- Zero window: both sides are zero for arbitrary differentiable
amounts satisfying the derivative forms (which hold trivially here). -/
example {A1 A2 u : ℝ → ℝ}
    (hA1 : ∀ s ∈ Set.Icc 0 0, HasDerivAt A1 (u s - (1 + 1) * A1 s + 1 * A2 s) s)
    (hA2 : ∀ s ∈ Set.Icc 0 0, HasDerivAt A2 (1 * A1 s - 1 * A2 s) s)
    (hu : IntervalIntegrable u MeasureTheory.volume 0 0)
    (hA1i : IntervalIntegrable A1 MeasureTheory.volume 0 0) :
    (A1 0 + A2 0) - (A1 0 + A2 0) = ∫ s in (0:ℝ)..0, (u s - 1 * A1 s) :=
  two_compartment_budget (le_refl 0) hA1 hA2 hu hA1i

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget
