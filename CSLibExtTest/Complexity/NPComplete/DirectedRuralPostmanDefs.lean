/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DirectedRuralPostmanDefs

namespace MetaMathlibExt.Complexity.NPComplete.DirectedRuralPostman

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem dec_bitEncode (i : DirectedRuralPostmanInstance) :
    directedRuralPostmanDec (bitEncode i) = true ↔
      WellFormed i ∧ DirectedRuralPostmanFeasible i := by
  simp [directedRuralPostmanDec, bitDecode_bitEncode]

/-- Two opposite unit arcs: the closed walk `0 → 1 → 0` uses the required arc `(0, 1)` and has
length `2 ≤ B = 2`. -/
example :
    directedRuralPostmanDec
      (bitEncode ((2, [(0, 1, 1), (1, 0, 1)], [(0, 1)], 2) : DirectedRuralPostmanInstance)) =
        true := by
  rw [dec_bitEncode]
  refine ⟨by unfold WellFormed; decide, [0, 1], ?_⟩
  unfold arc
  decide

/-- A single arc `0 → 1` is required but nothing returns to `0`, so no closed walk exists,
whatever the bound. -/
example :
    directedRuralPostmanDec
      (bitEncode ((2, [(0, 1, 1)], [(0, 1)], 5) : DirectedRuralPostmanInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, walk, hlt, hchain, hclose, hreq, -⟩
  have h0 : ∀ j ∈ walk, j = 0 := fun j hj => by simpa using hlt j hj
  match walk, h0, hchain, hclose, hreq with
  | [], _, _, _, hreq =>
    obtain ⟨j, hj, -⟩ := hreq (0, 1) (by simp)
    simp at hj
  | [j], h0, _, hclose, _ =>
    rw [h0 j (by simp)] at hclose
    simp [arc] at hclose
  | j :: k :: rest, h0, hchain, _, _ =>
    rw [h0 j (by simp), h0 k (by simp)] at hchain
    simp [arc] at hchain

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := DirectedRuralPostmanInstance) bits = none) :
    directedRuralPostmanDec bits = false := by
  simp [directedRuralPostmanDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : directedRuralPostmanDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.DirectedRuralPostman
