/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.BalancedBicliqueDefs

namespace MetaMathlibExt.Complexity.NPComplete.BalancedBiclique

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

example (i : BalancedBicliqueInstance) :
    balancedBicliqueDec (bitEncode i) = true ↔ WellFormed i ∧ BalancedBicliqueFeasible i := by
  simp [balancedBicliqueDec, bitDecode_bitEncode]

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := BalancedBicliqueInstance) bits = none) :
    balancedBicliqueDec bits = false := by
  simp [balancedBicliqueDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : balancedBicliqueDec [true] = false :=
  rejects_undecodable [true] rfl

private theorem rejects_malformed (i : BalancedBicliqueInstance)
    (h : ¬ WellFormed i) :
    balancedBicliqueDec (bitEncode i) = false := by
  simp [balancedBicliqueDec, bitDecode_bitEncode, h]

/-- Listing an undirected edge in both directions is malformed. -/
example :
    balancedBicliqueDec
      (bitEncode ((2, [(0, 1), (1, 0)], 1) : BalancedBicliqueInstance)) =
        false := by
  apply rejects_malformed _
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.BalancedBiclique
