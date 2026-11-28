/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.HitoriDefs
-- Decidability of connectivity on finite graphs, used to check the connection rule.
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

namespace MetaMathlibExt.Complexity.NPComplete.Hitori

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

/-- Adjacency in a box product of graphs with decidable adjacency is decidable. -/
local instance {α β : Type*} [DecidableEq α] [DecidableEq β] (G : SimpleGraph α)
    (H : SimpleGraph β) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := fun _ _ =>
  decidable_of_iff' _ SimpleGraph.boxProd_adj

private theorem accepts_encoding (i : HitoriInstance) :
    hitoriDec (bitEncode i) = true ↔ WellFormed i ∧ HitoriFeasible i := by
  simp [hitoriDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : hitoriDec [true] = false := by
  have h : bitDecode (α := HitoriInstance) [true] = none := rfl
  simp [hitoriDec, h]

/-- The grid `1 1 / 1 2`: shading the top left cell removes every repeated number, and the three
unshaded cells stay connected through the bottom right cell. -/
example : hitoriDec (bitEncode ([[1, 1], [1, 2]] : HitoriInstance)) = true := by
  refine (accepts_encoding _).2
    ⟨by unfold WellFormed; decide, fun x => decide (x.1.val = 0 ∧ x.2.val = 0), ?_⟩
  unfold Solves
  decide

/-- The row `1 1 1 1`: every pair of its cells needs a shaded member, so at least three cells are
shaded, and two of them share an edge. -/
example : hitoriDec (bitEncode ([[1, 1, 1, 1]] : HitoriInstance)) = false := by
  have h : ¬ HitoriFeasible [[1, 1, 1, 1]] := by
    rintro ⟨s, uniq, sep, -⟩
    revert s
    decide
  simpa [hitoriDec, bitDecode_bitEncode] using fun _ => h

end MetaMathlibExt.Complexity.NPComplete.Hitori
