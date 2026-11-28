/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumAxiomSetDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : MinimumAxiomSetInstance) :
    minimumAxiomSetDec (bitEncode i) = true ↔ WellFormed i ∧ MinimumAxiomSetFeasible i := by
  simp [minimumAxiomSetDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumAxiomSetDec [true] = false := by
  have h : bitDecode (α := MinimumAxiomSetInstance) [true] = none := rfl
  simp [minimumAxiomSetDec, h]

/-- The single axiom `0` derives sentence `1` in one round. -/
example :
    minimumAxiomSetDec (bitEncode ((2, [0, 1], [([0], 1)], 1) : MinimumAxiomSetInstance)) =
      true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, {0}, by decide, by decide, 1, by decide, ?_⟩
  decide

/-- Without implications, one axiom cannot reach both true sentences. -/
example :
    minimumAxiomSetDec (bitEncode ((2, [0, 1], [], 1) : MinimumAxiomSetInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, S₀, -, hcard, n, -, hn⟩ := (accepts_encoding _).1 h
  have hid : derive [] = id := by
    funext X
    simp [derive]
  rw [hid, Function.iterate_id, id] at hn
  subst hn
  simp at hcard
