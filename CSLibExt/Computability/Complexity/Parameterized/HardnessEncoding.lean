/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.Parameterized.Defs
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Writing finite graphs in the parameterized Clique input format

Given an explicit numbering and adjacency decision procedure, enumerate the edges
and serialize the result in the encoding consumed by `CliqueParam`.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.Parameterized

variable {V : Type*} {n : ℕ} (G : SimpleGraph V) [DecidableRel G.Adj] (vertex : Fin n ≃ V)

/-- Enumerate both orientations of each edge of a numbered graph. -/
def numberedEdges : List (ℕ × ℕ) :=
  (List.finRange n).flatMap fun i => ((List.finRange n).filter fun j =>
    decide (G.Adj (vertex i) (vertex j))).map fun j => (i.val, j.val)

private theorem mem_numberedEdges {i j : Fin n} :
    (i.val, j.val) ∈ numberedEdges G vertex ↔ G.Adj (vertex i) (vertex j) := by
  simp only [numberedEdges, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map,
    List.mem_filter, decide_eq_true_eq, Prod.mk.injEq, Fin.val_inj]
  grind

/-- Serialize the graph with its order and its explicitly enumerated edge list. -/
def encodeNumberedGraph : List Bool :=
  MetaMathlibExt.BitstringEncoding.bitEncode (n, numberedEdges G vertex)

/-- `CliqueParam` on the emitted bits accepts exactly ordinary cliques of the requested size. -/
theorem cliqueParam_encodeNumberedGraph_iff (k : ℕ) :
    CliqueParam (encodeNumberedGraph G vertex) k ↔ ∃ s, G.IsNClique k s := by
  classical
  simp only [CliqueParam, encodeNumberedGraph, MetaMathlibExt.BitstringEncoding.bitDecode_bitEncode,
    decide_eq_true_eq]
  constructor
  · rintro ⟨l, hnd, hlen, hbound, hpair⟩
    let f (v : {v // v ∈ l}) := vertex ⟨v.val, hbound _ v.property⟩
    have inj : Function.Injective f :=
      fun u v h => Subtype.ext (congrArg Fin.val (vertex.injective h))
    refine ⟨Finset.univ.image f, ?_, ?_⟩
    · intro u hu v hv hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hv
      have hi := hbound i.val i.property
      have hj := hbound j.val j.property
      have hij : i.val ≠ j.val := fun h => hne (congrArg f (Subtype.ext h))
      rcases hpair _ i.property _ j.property hij with h | h
      · exact (mem_numberedEdges G vertex (i := ⟨_, hi⟩) (j := ⟨_, hj⟩)).mp h
      · exact ((mem_numberedEdges G vertex (i := ⟨_, hj⟩) (j := ⟨_, hi⟩)).mp h).symm
    · rw [Finset.card_image_of_injective _ inj, Finset.card_univ]
      let equiv : {v // v ∈ l} ≃ l.toFinset := Equiv.subtypeEquivRight (by simp)
      rw [Fintype.card_congr equiv, Fintype.card_coe, l.toFinset_card_of_nodup hnd, hlen]
  · rintro ⟨s, hs⟩
    let index := vertex.symm.toEmbedding.trans Fin.valEmbedding
    refine ⟨(s.map index).toList, Finset.nodup_toList _, ?_, ?_, ?_⟩
    · simpa using hs.card_eq
    · intro i hi
      obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp (Finset.mem_toList.mp hi)
      exact (vertex.symm v).isLt
    · intro i hi j hj hij
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp (Finset.mem_toList.mp hi)
      obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp (Finset.mem_toList.mp hj)
      left
      apply (mem_numberedEdges G vertex (i := vertex.symm u) (j := vertex.symm v)).mpr
      simpa using hs.isClique hu hv (fun heq => hij (congrArg index heq))

end MetaMathlibExt.Complexity.KeyTheorems.Parameterized
