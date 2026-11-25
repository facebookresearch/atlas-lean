/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Dynamics.Ergodic.Mixing
public import MathlibExt.Dynamics.Ergodic.PoincareRecurrence
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

import Mathlib.Tactic

@[expose] public section

open MeasureTheory Filter Topology
open MathlibExt.Dynamics.Ergodic.Mixing MathlibExt.Dynamics.Ergodic.PoincareRecurrence

namespace MathlibExtTest.Dynamics.Ergodic.Mixing

/-- Non-vacuity: the Dirac mass at a fixed point is a mixing invariant measure. -/
theorem isMixing_dirac_of_fixed {α : Type*} [MeasurableSpace α] {T : α → α}
    (hT : Measurable T) {a : α} (ha : T a = a) : IsMixing T (Measure.dirac a) where
  measurePreserving := ⟨hT, by rw [Measure.map_dirac' hT, ha]⟩
  tendsto_measure_inter_preimage A B hA hB := by
    have hfix : ∀ n : ℕ, T^[n] a = a := fun n => Function.iterate_fixed ha n
    have hconst : (fun n : ℕ => Measure.dirac a (A ∩ T^[n] ⁻¹' B)) =
        fun _ => Measure.dirac a A * Measure.dirac a B := by
      funext n
      rw [Measure.dirac_apply' _ (hA.inter (hB.preimage (hT.iterate n))),
        Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hB]
      by_cases hA' : a ∈ A <;> by_cases hB' : a ∈ B <;>
        simp [Set.indicator, hA', hB', hfix n]
    rw [hconst]
    exact tendsto_const_nhds

/-! Mixing is defined for probability measures only: `IsMixing T 0` does not elaborate, because
the zero measure, for which the condition `μ (A ∩ T⁻ⁿ B) → μ A · μ B` would hold for every map,
is not a probability measure. -/

/--
error: failed to synthesize instance of type class
  IsProbabilityMeasure 0

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
example {α : Type} [MeasurableSpace α] (T : α → α) : Prop := IsMixing T (0 : Measure α)

-- Mixing gives ergodicity, here for the Dirac mass at a fixed point.
example {α : Type*} [MeasurableSpace α] {T : α → α} (hT : Measurable T) {a : α}
    (ha : T a = a) : Ergodic T (Measure.dirac a) :=
  (isMixing_dirac_of_fixed hT ha).ergodic

-- Total ergodicity: the square of a mixing map is ergodic.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {T : α → α} (h : IsMixing T μ) : Ergodic T^[2] μ :=
  h.ergodic_iterate (by norm_num)

-- Poincaré recurrence for the identity map: every point of `E` is in `E` at all times.
example {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {E : Set α} (hE : MeasurableSet E) :
    ∀ᵐ x ∂μ, x ∈ E → ∃ᶠ n in atTop, (id : α → α)^[n] x ∈ E :=
  ae_frequently_mem_of_mem (MeasurePreserving.id μ) hE

end MathlibExtTest.Dynamics.Ergodic.Mixing
