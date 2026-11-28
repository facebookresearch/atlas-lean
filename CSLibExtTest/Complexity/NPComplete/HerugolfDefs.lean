/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HerugolfDefs

namespace MetaMathlibExt.Complexity.NPComplete.Herugolf

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : HerugolfInstance) :
    herugolfDec (bitEncode i) = true ↔ WellFormed i ∧ HerugolfFeasible i := by
  simp [herugolfDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : herugolfDec [true] = false := by
  have h : bitDecode (α := HerugolfInstance) [true] = none := rfl
  simp [herugolfDec, h]

/-- A ball with number `2`, an empty cell and a hole: one shot of length `2` to the right stops
in the hole. -/
example : herugolfDec (bitEncode ([[4, 0, 1]] : HerugolfInstance)) = true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, fun _ => [0], ?_, ?_, ?_⟩
  · have ball : ∀ c ∈ balls [[4, 0, 1]], c = (0, 0) := by decide
    intro c hc
    obtain rfl := ball c hc
    unfold LegalShots InGrid
    exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
  · decide
  · decide

/-- With number `1` the ball has a single shot of length `1`, which cannot reach the hole two
cells away. -/
example : herugolfDec (bitEncode ([[3, 0, 1]] : HerugolfInstance)) = false := by
  have h : ¬ HerugolfFeasible [[3, 0, 1]] := by
    rintro ⟨plan, legal, -, -⟩
    obtain ⟨h₁, h₂, -, -, ⟨q, hq, hlast⟩, -⟩ := legal (0, 0) (by decide)
    have hole : ∀ q ∈ holes [[3, 0, 1]], q = (2, 0) := by decide
    obtain rfl := hole q hq
    have miss : ∀ d : Fin 4,
        (stops (cell (0, 0)) (code [[3, 0, 1]] (0, 0) - 2) [d]).getLast? ≠ some (cell (2, 0)) := by
      decide
    generalize plan (0, 0) = ds at h₁ h₂ hlast
    match ds, h₁, h₂ with
    | [d], _, _ => exact miss d hlast
  simpa [herugolfDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.Herugolf
