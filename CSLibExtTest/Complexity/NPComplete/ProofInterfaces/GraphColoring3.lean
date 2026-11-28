/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.FixedKColorabilityDefs

namespace MetaMathlibExt.Complexity.NPComplete.FixedKColorability

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open GraphColoring (GraphColoringInstance)

example (k : Nat) (i : GraphColoringInstance) :
    fixedKColorabilityDec k (bitEncode i) = true ↔
      WellFormed k i ∧ GraphColoring.GraphColoringFeasible i := by
  simp [fixedKColorabilityDec, bitDecode_bitEncode]

private theorem rejects_undecodable (k : Nat) (bits : List Bool)
    (h : bitDecode (α := GraphColoringInstance) bits = none) :
    fixedKColorabilityDec k bits = false := by
  simp [fixedKColorabilityDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example (k : Nat) : fixedKColorabilityDec k [true] = false :=
  rejects_undecodable k [true] rfl

private theorem rejects_malformed (k : Nat) (i : GraphColoringInstance)
    (h : ¬ (WellFormed k i)) :
    fixedKColorabilityDec k (bitEncode i) = false := by
  simp [fixedKColorabilityDec, bitDecode_bitEncode, h]

/-- The three-color language rejects an instance asking for two colors. -/
example :
    fixedKColorabilityDec 3 (bitEncode ((2, [(0, 1)], 2) : GraphColoringInstance)) = false := by
  apply rejects_malformed 3 _
  intro h
  exact (by decide : (2 : Nat) ≠ 3) h.2

end MetaMathlibExt.Complexity.NPComplete.FixedKColorability
