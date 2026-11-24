/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Two-compartment mass budget

For the two-compartment system, total amount change over `[0, T]` is the integrated input
minus `k10` times the integrated central amount: only input and central elimination cross the boundary.
-/

@[expose] public section

open MeasureTheory intervalIntegral

namespace MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget

/-- **Two-compartment mass budget.** If `(A1, A2)` solves the
two-compartment system in derivative form on (no sign assumptions on the rates are needed) on
`[0, T]` (`A1' = u - (k10 + k12) A1 + k21 A2` and
`A2' = k12 A1 - k21 A2`), then the total amount satisfies
`(A1 + A2)(T) - (A1 + A2)(0) =
∫ s in 0..T, u s - k10 * ∫ s in 0..T, A1 s`: only the input and the
central elimination cross the system boundary. -/
lemma two_compartment_budget {k10 k12 k21 T : ℝ} (hT : 0 ≤ T)
    {A1 A2 u : ℝ → ℝ}
    (hA1 : ∀ s ∈ Set.Icc 0 T,
      HasDerivAt A1 (u s - (k10 + k12) * A1 s + k21 * A2 s) s)
    (hA2 : ∀ s ∈ Set.Icc 0 T,
      HasDerivAt A2 (k12 * A1 s - k21 * A2 s) s)
    (hu : IntervalIntegrable u volume 0 T) :
    (A1 T + A2 T) - (A1 0 + A2 0) =
      ∫ s in (0:ℝ)..T, (u s - k10 * A1 s) := by
  have hA1cont : ContinuousOn A1 (Set.uIcc 0 T) := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    exact (hA1 x hx).continuousAt.continuousWithinAt
  have hA1i : IntervalIntegrable A1 volume 0 T :=
    hA1cont.intervalIntegrable
  have hsum : ∀ x ∈ Set.uIcc 0 T,
      HasDerivAt (A1 + A2) (u x - k10 * A1 x) x := by
    intro x hx
    rw [Set.uIcc_of_le hT] at hx
    have h1 := hA1 x hx
    have h2 := hA2 x hx
    have hadd := h1.add h2
    have heq : (u x - (k10 + k12) * A1 x + k21 * A2 x) +
        (k12 * A1 x - k21 * A2 x) = u x - k10 * A1 x := by ring
    simpa [heq] using hadd
  have hint : IntervalIntegrable (fun s => u s - k10 * A1 s) volume 0 T :=
    hu.sub (hA1i.const_mul k10)
  have hFTC := integral_eq_sub_of_hasDerivAt hsum hint
  simpa [Pi.add_apply] using hFTC.symm

end MathlibExt.Biology.Biophysics.CompartmentKinetics.TwoCompartmentBudget
