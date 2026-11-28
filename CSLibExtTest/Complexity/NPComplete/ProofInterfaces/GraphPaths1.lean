/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DirectedHamiltonianPathDefs

namespace MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open HamiltonianCycleDirected (HamiltonianCycleDirectedInstance)

example (i : HamiltonianCycleDirectedInstance) :
    directedHamiltonianPathDec (bitEncode i) = true ↔
      HamiltonianCycleDirected.WellFormed i ∧ DirectedHamiltonianPathFeasible i := by
  simp [directedHamiltonianPathDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := HamiltonianCycleDirectedInstance) bits = none) :
    directedHamiltonianPathDec bits = false := by
  simp [directedHamiltonianPathDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : directedHamiltonianPathDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : HamiltonianCycleDirectedInstance)
    (h : ¬ HamiltonianCycleDirected.WellFormed i) :
    directedHamiltonianPathDec (bitEncode i) = false := by
  simp [directedHamiltonianPathDec, bitDecode_bitEncode, h]

/-- An arc cannot refer to a vertex outside the graph. -/
example :
    directedHamiltonianPathDec
      (bitEncode ((2, [(0, 2)]) : HamiltonianCycleDirectedInstance)) =
        false := by
  apply rejects_malformed _
  unfold HamiltonianCycleDirected.WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath
