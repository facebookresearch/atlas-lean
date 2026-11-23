/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.LogicObservationBands
import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhyslibExtTest.Electronics.LogicObservationBands

open PhyslibExt.Electronics.LogicObservationBands

/-- Valid low voltages, below and at the low threshold `Vil = 1`. -/
example : observe 1 2 0 = some false := observe_eq_false_of_le (by norm_num) _
example : observe 1 2 1 = some false := observe_eq_false_of_le (by norm_num) _

/-- Valid high voltages, at and above the high threshold `Vih = 2`. -/
example : observe 1 2 2 = some true :=
  observe_eq_true_of_le (by norm_num) (by norm_num)
example : observe 1 2 3 = some true :=
  observe_eq_true_of_le (by norm_num) (by norm_num)

/-- A mid-gap voltage is invalid, not a Boolean value at all. -/
example : observe 1 2 (3 / 2 : ℝ) = none :=
  (observe_eq_none_iff (by norm_num)).mpr ⟨by norm_num, by norm_num⟩
example : ¬ ∃ b, observe 1 2 (3 / 2 : ℝ) = some b := by
  rintro ⟨b, hb⟩
  have h := (observe_eq_some_iff (by norm_num : (1 : ℝ) < 2) b).mp hb
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ <;> norm_num at h

/-- Noise below the low margin preserves a promised low output
(`Vol = 0`, margin `1`, noise `1/2`). -/
example : observe 1 2 ((0 : ℝ) + 1 / 2) = some false :=
  observe_noisy_low (Vol := 0) (y := 0) (e := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num)

/-- Noise below the high margin preserves a promised high output
(`Voh = 3`, margin `1`, noise `1/4`, through the output contract). -/
example (b : Bool) (y : ℝ)
    (hy : (b = false ∧ y <= 0) ∨ (b = true ∧ (3 : ℝ) <= y)) :
    observe 1 2 (y + 1 / 4) = some b :=
  observe_noisy_output (by norm_num) (by norm_num) (by norm_num) b y (1 / 4) hy
    (by norm_num)

end PhyslibExtTest.Electronics.LogicObservationBands
