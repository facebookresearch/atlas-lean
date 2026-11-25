/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget

/-! Tests: zero-window budget. -/

namespace MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget

open MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget

/-- Zero window: both sides are zero for arbitrary differentiable
amounts satisfying the derivative forms at the single point `0`. -/
example {A1 A2 u : ℝ → ℝ}
    (hA1 : ∀ s ∈ Set.Icc 0 0, HasDerivAt A1 (u s - (1 + 1) * A1 s + 1 * A2 s) s)
    (hA2 : ∀ s ∈ Set.Icc 0 0, HasDerivAt A2 (1 * A1 s - 1 * A2 s) s)
    (hu : IntervalIntegrable u MeasureTheory.volume 0 0) :
    (A1 0 + A2 0) - (A1 0 + A2 0) = ∫ s in (0:ℝ)..0, (u s - 1 * A1 s) :=
  two_compartment_budget (le_refl 0) hA1 hA2 hu
/-- Nonzero window `T = 1`, rates `1`, `A1 s = 1 + s`, `A2 s = s`,
`u s = 3 + s`: both sides equal `2`. -/
example : ((fun s => 1 + s) 1 + (fun s => s) 1) -
      ((fun s => 1 + s) 0 + (fun s => s) 0) =
    ∫ s in (0:ℝ)..1, ((fun s => 3 + s) s - 1 * (fun s => 1 + s) s) := by
  refine two_compartment_budget (A1 := fun s => 1 + s) (A2 := fun s => s)
    (u := fun s => 3 + s) (k10 := 1) (k12 := 1) (k21 := 1) (T := 1)
    (by norm_num) ?_ ?_ ?_
  · intro s hs
    have h : HasDerivAt (fun s => 1 + s) 1 s := by
      simpa using (hasDerivAt_id s).const_add 1
    convert h using 1
    ring
  · intro s hs
    have h : HasDerivAt (fun s => s) 1 s := hasDerivAt_id s
    convert h using 1
    ring
  · exact (by fun_prop : Continuous (fun s : ℝ => 3 + s)).intervalIntegrable 0 1

end MathlibExtTest.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget
