/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.GeneralRoutingDefs

namespace MetaMathlibExt.Complexity.NPComplete.GeneralRouting

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem dec_bitEncode (i : GeneralRoutingInstance) :
    generalRoutingDec (bitEncode i) = true ↔ WellFormed i ∧ GeneralRoutingFeasible i := by
  simp [generalRoutingDec, bitDecode_bitEncode]

/-- One edge `{0, 1}` of length `1`, required edge `{0, 1}`, required vertex `1`, `B = 2`: the
closed walk `0, 1, 0` has length `2`. -/
example :
    generalRoutingDec
      (bitEncode (((2, [(0, 1, 1)], [(0, 1)], 2), [1]) : GeneralRoutingInstance)) = true := by
  rw [dec_bitEncode]
  have h01 : (RuralPostman.Graph (2, [(0, 1, 1)], [(0, 1)], 2)).Adj 0 1 := by
    unfold RuralPostman.Graph Cslib.Complexity.Karp.edgeGraph
    rw [SimpleGraph.fromRel_adj]
    exact ⟨by simp, Or.inl (by simp)⟩
  refine ⟨by unfold WellFormed RuralPostman.WellFormed; decide, 0,
    SimpleGraph.Walk.cons h01 (SimpleGraph.Walk.cons h01.symm SimpleGraph.Walk.nil), ?_, ?_, ?_⟩
  · simp
  · simp
  · simp only [SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    unfold RuralPostman.edgeLength
    decide

/-- One edge `{0, 1}` and an isolated vertex `2` that is required: no closed walk both
traverses the required edge `{0, 1}` and visits `2`. -/
example :
    generalRoutingDec
      (bitEncode (((3, [(0, 1, 1)], [(0, 1)], 5), [2]) : GeneralRoutingInstance)) = false := by
  rw [Bool.eq_false_iff, ne_eq, dec_bitEncode]
  rintro ⟨-, v, c, hvert, hedge, -⟩
  obtain ⟨x, hx, hx2⟩ := List.mem_map.1 (hvert 2 (by simp))
  obtain ⟨e, he, he01⟩ := List.mem_map.1 (hedge (0, 1) (by simp))
  induction e using Sym2.ind with
  | _ a b =>
    have ha : a ∈ c.support := c.fst_mem_support_of_mem_edges he
    have hreach : (RuralPostman.Graph (3, [(0, 1, 1)], [(0, 1)], 5)).Reachable x a :=
      ⟨(c.takeUntil x hx).reverse.append (c.takeUntil a ha)⟩
    have ha2 : a.val ≠ 2 := by
      have : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) := by
        simpa [Sym2.eq_iff] using he01
      omega
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact ha2 hx2
    | cons h _ =>
      unfold RuralPostman.Graph Cslib.Complexity.Karp.edgeGraph at h
      rw [SimpleGraph.fromRel_adj] at h
      simp [hx2] at h

private theorem rejects_undecodable (bits : List Bool)
    (h : bitDecode (α := GeneralRoutingInstance) bits = none) :
    generalRoutingDec bits = false := by
  simp [generalRoutingDec, h]

/-- A lone continuation bit is a truncated instance encoding. -/
example : generalRoutingDec [true] = false :=
  rejects_undecodable [true] rfl

end MetaMathlibExt.Complexity.NPComplete.GeneralRouting
