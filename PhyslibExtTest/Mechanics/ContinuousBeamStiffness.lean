/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.ContinuousBeamStiffness
import Mathlib.Tactic.NormNum

/-!
# Continuous-beam stiffness checks

Concrete consumers of
`PhyslibExt.Mechanics.ContinuousBeamStiffness` at unit spans:
gather and support-injection values, the supported energy at a
unit end rotation, positive definiteness and unique response
clients, and the assembled rigid modes.

## i. Overview

These are elaboration and sign checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Gather, injection, and supported energy
- B. Positive definiteness, uniqueness, and rigid modes

## iv. References

- `PhyslibExt.Mechanics.ContinuousBeamStiffness`
-/

open Matrix
open Mechanics.EulerBernoulli

namespace PhyslibExtTest.Mechanics.ContinuousBeamStiffness

/-! ## A. Gather, injection, and supported energy -/

/-- Gather values on a concrete global vector. -/
example : spanOneGather *ᵥ ![5, 6, 7, 8, 9, 10] = ![5, 6, 7, 8] :=
  spanOneGather_mulVec _

example : spanTwoGather *ᵥ ![5, 6, 7, 8, 9, 10] = ![7, 8, 9, 10] :=
  spanTwoGather_mulVec _

example : supportInjection *ᵥ ![2, 3, 5] = ![0, 2, 0, 3, 0, 5] :=
  supportInjection_mulVec _

/-- Supported energy at a unit left-end rotation, unit spans:
`12 * (1/2)^2 + 1 = 4`. -/
example : (![1, 0, 0] : Fin 3 → ℝ)
    ⬝ᵥ (supportedStiffness 1 1 1 1 *ᵥ ![1, 0, 0]) = 4 := by
  rw [supportedStiffness_quad_form_factor]
  norm_num

/-- The zero rotation has zero supported energy. -/
example : (0 : Fin 3 → ℝ)
    ⬝ᵥ (supportedStiffness 1 1 1 1 *ᵥ (0 : Fin 3 → ℝ)) = 0 := by
  rw [supportedStiffness_quad_form_factor]
  norm_num

/-! ## B. Positive definiteness, uniqueness, and rigid modes -/

/-- Positive definiteness and unique supported response at
unit data, as clients of the general statements. -/
example : (supportedStiffness 1 1 1 1).PosDef :=
  supportedStiffness_posDef (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

example : ∃! w : Fin 3 → ℝ,
    supportedStiffness 1 1 1 1 *ᵥ w = ![3, -2, 5] :=
  supportedStiffness_existsUnique
    (supportedStiffness_posDef (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)) _

/-- Assembled rigid modes at unit spans. -/
example : continuousBeamStiffness 1 1 1 1 *ᵥ ![1, 0, 1, 0, 1, 0]
    = 0 :=
  continuousBeamStiffness_mulVec_translation 1 1 1 1

example : continuousBeamStiffness 1 1 1 1 *ᵥ ![0, 1, 1, 1, 2, 1]
    = 0 := by
  have h := (continuousBeamStiffness_mulVec_rotation 1 1 1 1).1
  norm_num at h
  exact h

example : (![0, 1, 1, 1, 2, 1] : Fin 6 → ℝ) ≠ 0 := by
  intro h
  have h1 := congrFun h 1
  simp at h1

#print axioms Mechanics.EulerBernoulli.spanOneGather_mulVec
#print axioms Mechanics.EulerBernoulli.continuousBeamStiffness_quad_form_split
#print axioms Mechanics.EulerBernoulli.supportedStiffness_quad_form_factor
#print axioms Mechanics.EulerBernoulli.supportedStiffness_posDef
#print axioms Mechanics.EulerBernoulli.supportedStiffness_existsUnique
#print axioms Mechanics.EulerBernoulli.continuousBeamStiffness_mulVec_translation
#print axioms Mechanics.EulerBernoulli.continuousBeamStiffness_mulVec_rotation

end PhyslibExtTest.Mechanics.ContinuousBeamStiffness
