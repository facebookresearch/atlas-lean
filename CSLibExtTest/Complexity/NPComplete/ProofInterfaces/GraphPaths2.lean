/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.InducedCycleDefs

namespace MetaMathlibExt.Complexity.NPComplete.InducedCycle

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open InducedPath (InducedPathInstance)

example (i : InducedPathInstance) :
    inducedCycleDec (bitEncode i) = true ↔ InducedPath.WellFormed i ∧ InducedCycleFeasible i := by
  simp [inducedCycleDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := InducedPathInstance) bits = none) :
    inducedCycleDec bits = false := by
  simp [inducedCycleDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : inducedCycleDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : InducedPathInstance)
    (h : ¬ InducedPath.WellFormed i) :
    inducedCycleDec (bitEncode i) = false := by
  simp [inducedCycleDec, bitDecode_bitEncode, h]

/-- A requested cycle length of four exceeds the number of vertices. -/
example :
    inducedCycleDec
      (bitEncode ((3, [(0, 1), (1, 2), (0, 2)], 4) : InducedPathInstance)) =
        false := by
  apply rejects_malformed _
  intro h
  exact (by decide : ¬ (4 : Nat) ≤ 3) h.2.2

end MetaMathlibExt.Complexity.NPComplete.InducedCycle
