/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.MinimumAxiomSetAllSentencesTrueDefs

namespace MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSetAllSentencesTrue

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSet
  (MinimumAxiomSetInstance MinimumAxiomSetFeasible derive)

private theorem accepts_encoding (i : MinimumAxiomSetInstance) :
    minimumAxiomSetAllSentencesTrueDec (bitEncode i) = true ↔
      WellFormed i ∧ MinimumAxiomSetFeasible i := by
  simp [minimumAxiomSetAllSentencesTrueDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : minimumAxiomSetAllSentencesTrueDec [true] = false := by
  have h : bitDecode (α := MinimumAxiomSetInstance) [true] = none := rfl
  simp [minimumAxiomSetAllSentencesTrueDec, h]

/-- Both sentences are true, and the single axiom `0` derives sentence `1` in one round. -/
example :
    minimumAxiomSetAllSentencesTrueDec
      (bitEncode ((2, [0, 1], [([0], 1)], 1) : MinimumAxiomSetInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed MinimumAxiomSet.WellFormed; decide, {0}, by decide, by decide, 1,
    by decide, ?_⟩
  decide

/-- Sentence `2` is not true, so the instance is outside the restriction `T = S`, although
the axiom `0` would reach exactly `T` in the unrestricted problem. -/
example :
    minimumAxiomSetAllSentencesTrueDec
      (bitEncode ((3, [0, 1], [([0], 1)], 1) : MinimumAxiomSetInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  have hw := ((accepts_encoding _).1 h).1.2 2 (by decide)
  revert hw
  decide

/-- Without implications, one axiom cannot reach both true sentences. -/
example :
    minimumAxiomSetAllSentencesTrueDec
      (bitEncode ((2, [0, 1], [], 1) : MinimumAxiomSetInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro h
  obtain ⟨-, S₀, -, hcard, n, -, hn⟩ := (accepts_encoding _).1 h
  have hid : derive [] = id := by
    funext X
    simp [derive]
  rw [hid, Function.iterate_id, id] at hn
  subst hn
  simp at hcard

end MetaMathlibExt.Complexity.NPComplete.MinimumAxiomSetAllSentencesTrue
