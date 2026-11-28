/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.IndependentSequenceDefs

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSequence

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : IndependentSequenceInstance) :
    independentSequenceDec (bitEncode i) = true ↔
      WellFormed i ∧ IndependentSequenceFeasible i := by
  simp [independentSequenceDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : independentSequenceDec [true] = false := by
  have h : bitDecode (α := IndependentSequenceInstance) [true] = none := rfl
  simp [independentSequenceDec, h]

/-- In the matching `0 - 1, 2 - 3`, the sequence `0, 2` is independent, and `3` is adjacent to
`2` but not to `0`. -/
example :
    independentSequenceDec
      (bitEncode ((4, [(0, 1), (2, 3)], 2) : IndependentSequenceInstance)) = true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [0, 2], le_refl _, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
      simp_all [Graph, Cslib.Complexity.Karp.edgeGraph]
  · intro i hi
    obtain rfl : i = 0 := by simp at hi; omega
    refine ⟨3, ?_, ?_⟩
    · simp [Graph, Cslib.Complexity.Karp.edgeGraph]
    · simp [Graph, Cslib.Complexity.Karp.edgeGraph]

/-- In the path `0 - 1 - 2` the set `{0, 2}` is independent, but its only possible witness `1`
is adjacent to both ends, so no independent sequence has length `2`. -/
example :
    independentSequenceDec
      (bitEncode ((3, [(0, 1), (1, 2)], 2) : IndependentSequenceInstance)) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, l, hlen, hind, hseq⟩ := (accepts_encoding _).1 hacc
  have key : ∀ a b w : Fin 3, (Graph (3, [(0, 1), (1, 2)], 2)).Adj w b →
      ¬ (Graph (3, [(0, 1), (1, 2)], 2)).Adj w a →
        (Graph (3, [(0, 1), (1, 2)], 2)).Adj a b := by
    simp only [Graph, Cslib.Complexity.Karp.edgeGraph, SimpleGraph.fromRel_adj, List.mem_cons,
      Prod.mk.injEq, List.not_mem_nil, or_false]
    decide
  have h1 : 0 + 1 < l.length := by simp at hlen; omega
  obtain ⟨w, hwb, hwa⟩ := hseq 0 h1
  have h0 : l[0] ∈ l.take (0 + 1) := by simp [List.take_one, List.head?_eq_getElem?]
  have hab := key l[0] l[0 + 1] w hwb (hwa _ h0)
  exact hind (List.getElem_mem _) (List.getElem_mem _) hab.ne hab

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed ((3, [(0, 1), (1, 2)], 2) : IndependentSequenceInstance) :=
  by unfold WellFormed; decide

end MetaMathlibExt.Complexity.NPComplete.IndependentSequence
