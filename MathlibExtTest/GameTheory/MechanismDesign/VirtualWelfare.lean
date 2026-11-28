/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.MechanismDesign.VirtualWelfare
import Mathlib.Tactic.NormNum

open MeasureTheory Set
open MathlibExt.GameTheory.MechanismDesign.SingleParameter

/-- The uniform density `1` on `[0, 1]`, for two bidders. -/
private def unif : Fin 2 → ℝ → ℝ := fun _ _ => 1

-- The uniform value law is a probability measure.
example (i : Fin 2) :
    IsProbabilityMeasure (valueLaw unif (fun _ => 0) (fun _ => 1) i) :=
  isProbabilityMeasure_valueLaw zero_lt_one continuousOn_const
    (fun _ _ => zero_lt_one) (by simp [unif])

-- Overwriting the report: with `p t i = t i`, the interim allocation at report
-- `s` is `s` itself, whatever the profile law's `i`-th factor is.
example (μ : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure μ] (i : Fin 2) (s : ℝ) :
    interimAlloc μ (fun t i => t i) i s = s := by
  simp [interimAlloc]

-- The report does not leak into other coordinates: with `p t i = t 1` for
-- bidder `0`, the interim allocation of bidder `0` integrates bidder `1`'s
-- coordinate against the whole profile law.
example (μ : Measure (Fin 2 → ℝ)) (s : ℝ) :
    interimAlloc μ (fun t _ => t 1) 0 s = ∫ t, t 1 ∂μ := by
  simp [interimAlloc]

/-- The zero mechanism: never allocate, never charge. -/
private def zeroMech : (Fin 2 → ℝ) → Fin 2 → ℝ := fun _ _ => 0

-- The revenue identity for the zero mechanism under uniform values: both
-- sides are the integrals the theorem equates, with every hypothesis
-- discharged (measurability, `[0, 1]` allocations, joint and slice
-- integrability, incentive compatibility of the interim rules).
example :
    ∫ t, ∑ i, zeroMech t i ∂(Measure.pi (valueLaw unif (fun _ => 0) (fun _ => 1))) =
      ∫ t, ∑ i, virtualValue (unif i) 0 1 (by simp [unif]) (t i) * zeroMech t i
          ∂(Measure.pi (valueLaw unif (fun _ => 0) (fun _ => 1))) -
        ∑ i, truthfulUtility
          (interimAlloc (Measure.pi (valueLaw unif (fun _ => 0) (fun _ => 1))) zeroMech i)
          (interimPayment (Measure.pi (valueLaw unif (fun _ => 0) (fun _ => 1))) zeroMech i)
          0 := by
  exact integral_sum_payment_eq unif (fun _ => 0) (fun _ => 1)
    (fun _ => zero_lt_one) (fun _ => continuousOn_const)
    (fun _ _ _ => zero_lt_one) (fun _ => by simp [unif])
    (fun _ => measurable_const)
    (fun _ _ => ⟨le_rfl, zero_le_one⟩)
    (fun _ => by simp [zeroMech])
    (fun _ _ _ => by simp [zeroMech])
    (fun i s _ t _ => by simp [interimAlloc, interimPayment, zeroMech, truthfulUtility])
