/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Karp.Cooper

namespace Cslib.Complexity.Cooper

/-- Cooper's worked example has output probability `5 / 8`: 10 of the 16 root
assignments satisfy it. -/
example : (cooperNet cooperEx).outProb = 5 / 8 := outProb_cooperEx

/-- The unsatisfiable control has output probability `0`. -/
example : (cooperNet cooperUnsat).outProb = 0 := outProb_cooperUnsat

/-- A formula is satisfiable iff its network's output probability is positive. -/
example (φ : Cslib.Logic.LegacyPL.CNF) :
    Cslib.Logic.LegacyPL.CNFSat φ ↔ 0 < (cooperNet φ).outProb :=
  cnfSat_iff_outProb_pos φ

/-- The reduction map is correct on every bit string. -/
example (x : List Bool) : Cslib.CookLevin.satDec x = bnPosDec (reduceBN x) :=
  satDec_eq_bnPosDec_reduceBN x

/-- Direct computation: the example's network has 20 nodes, with roots for
variables 1, 2, 3, 4 at indices 12, 6, 4, 2 (latest occurrence first). -/
example : (cooperNet cooperEx).length = 20 := by decide

example : (coopSt cooperEx).roots = [(1, 12), (2, 6), (3, 4), (4, 2)] := by decide

/-- The rational-network codec round-trips a small network's encoding by
direct computation, and the worked example's encoding by the round-trip
theorem. -/
example : decodeRatNet (encodeRatNet [constNode true, rootNode]) =
    some [constNode true, rootNode] := by decide

example : decodeRatNet (encodeRatNet (cooperNet cooperEx)) = some (cooperNet cooperEx) :=
  decodeRatNet_encodeRatNet _

/-- The decoder rejects empty and truncated input. -/
example : decodeRatNet [] = none := by decide

example : decodeRatNet [true] = none := by decide

/-- The decoder rejects trailing bits after a complete encoding. -/
example : decodeRatNet (encodeRatNet [constNode false] ++ [true]) = none := by decide

/-- `bnPosDec` on a bit string that does not decode is `false`;
on the encoded unsatisfiable control it is also `false`. -/
example : bnPosDec [true] = false := by
  classical
  unfold bnPosDec
  rw [show decodeRatNet [true] = none from by decide]

example : bnPosDec (encodeRatNet (cooperNet cooperUnsat)) = false := by
  classical
  unfold bnPosDec
  rw [decodeRatNet_encodeRatNet]
  exact decide_eq_false (by
    rw [outProb_cooperUnsat]; exact fun h => lt_irrefl (0 : ℝ) h.2)

/-- `reduceBN` sends a decodable formula to its encoded network, and an
undecodable string to the fixed constant-false network. -/
example : reduceBN (Cslib.CookLevin.encodeCNF cooperEx) = encodeRatNet (cooperNet cooperEx) := by
  unfold reduceBN
  rw [Cslib.CookLevin.decodeCNF_encodeCNF]

example : reduceBN [true] = encodeRatNet noBN := by
  unfold reduceBN
  rfl

end Cslib.Complexity.Cooper
