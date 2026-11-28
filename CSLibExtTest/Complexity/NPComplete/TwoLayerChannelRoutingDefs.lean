/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TwoLayerChannelRoutingDefs

namespace MetaMathlibExt.Complexity.NPComplete.TwoLayerChannelRouting

open MetaMathlibExt.BitstringEncoding
open StatMech.Lattice (Site hypercubicLattice)

private theorem sum_two {M : Type} [AddCommMonoid M] (g : Fin 2 → M) :
    ∑ i, g i = g 0 + (g 1 + 0) := rfl

/-- The lower and upper ends `(0, 0)` and `(0, 1)` of a vertical grid segment. -/
private def p0 : Site 2 := ![0, 0]

private def p1 : Site 2 := ![0, 1]

private theorem p0_adj_p1 : (hypercubicLattice 2).Adj p0 p1 := by
  simp only [StatMech.Lattice.hypercubicLattice_adj, sum_two]
  decide

/-- A channel of width `1` with one net, whose upper terminal `(0, 1)` sits right above its
lower terminal `(0, 0)`. -/
private abbrev straight : TwoLayerChannelRoutingInstance := (1, 1, [((0, 0), 0)], [((0, 0), 0)])

/-- The same channel with the lower terminal moved to `(1, 0)`. -/
private abbrev skew : TwoLayerChannelRoutingInstance := (1, 1, [((0, 0), 0)], [((1, 0), 0)])

private theorem straight_wellFormed : WellFormed straight := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro e he
    simp only [terminals, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide
  · intro k hk
    change k < 1 at hk
    exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), by simp; omega⟩

private theorem skew_wellFormed : WellFormed skew := by
  refine ⟨by decide, by decide, by decide, ?_, ?_⟩
  · intro e he
    simp only [terminals, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> decide
  · intro k hk
    change k < 1 at hk
    exact ⟨_, List.mem_append_left _ (List.mem_singleton_self _), by simp; omega⟩

/-- The single vertical segment from `(0, 0)` to `(0, 1)` routes `straight`: it is a tree
whose two leaves are the two terminals, and it lies inside the channel. -/
private theorem straight_feasible : TwoLayerChannelRoutingFeasible straight := by
  refine ⟨fun _ => (hypercubicLattice 2).subgraphOfAdj p0_adj_p1, fun k => ⟨?_, ?_, ?_⟩, ?_,
    fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
  · exact (Set.finite_singleton _).insert _
  · exact SimpleGraph.IsTree.coe_subgraphOfAdj p0_adj_p1
  · intro v
    have hleaf : IsLeaf ((hypercubicLattice 2).subgraphOfAdj p0_adj_p1) v ↔ v = p0 ∨ v = p1 := by
      constructor
      · rintro ⟨hv, -⟩
        simpa using hv
      · intro hv
        refine ⟨by simpa using hv, fun u w h1 h2 => ?_⟩
        simp only [SimpleGraph.subgraphOfAdj_adj] at h1 h2
        exact Sym2.congr_right.mp (h1.symm.trans h2)
    rw [hleaf]
    simp only [terminals, toInt, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, Fin.val_eq_zero, and_true,
      Nat.cast_zero, Nat.cast_one, sub_self, p0, p1]
    exact or_comm
  · intro k u v huv
    simp only [SimpleGraph.subgraphOfAdj_adj, Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> unfold InChannel <;> decide

/-- In a channel of width `1`, every segment inside the channel is vertical: a horizontal one
would run along `y = 0` or `y = 1`. -/
private theorem vertical {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hin : InChannel 1 u v) : u 0 = v 0 := by
  rw [StatMech.Lattice.hypercubicLattice_adj, sum_two] at hadj
  obtain ⟨h0, h1, h2, h3, hb⟩ := hin
  push_cast at h1 h3
  omega

/-- `skew` is infeasible: a route from `(0, 1)` to `(1, 0)` would have to change its
`x`-coordinate, but only vertical segments fit in a channel of width `1`. -/
private theorem skew_infeasible : ¬ TwoLayerChannelRoutingFeasible skew := by
  rintro ⟨T, htree, hin, -⟩
  obtain ⟨-, htr, hleaf⟩ := htree 0
  have hup : (![0, 1] : Site 2) ∈ (T 0).verts :=
    ((hleaf _).mpr (by simp [terminals, toInt])).1
  have hlow : (![1, 0] : Site 2) ∈ (T 0).verts :=
    ((hleaf _).mpr (by simp [terminals, toInt])).1
  obtain ⟨w⟩ := htr.1.preconnected ⟨_, hup⟩ ⟨_, hlow⟩
  have key : ∀ {a b : (T 0).verts}, (T 0).coe.Walk a b → (a : Site 2) 0 = (b : Site 2) 0 := by
    intro a b q
    induction q with
    | nil => rfl
    | cons h _ ih =>
      exact (vertical ((T 0).adj_sub h) (hin 0 _ _ h)).trans ih
  exact absurd (key w) (by simp)

/-- A net with no terminal is malformed. -/
example : ¬ WellFormed ((1, 2, [((0, 0), 0)], [((0, 0), 0)]) : TwoLayerChannelRoutingInstance) := by
  rintro ⟨-, -, -, -, h⟩
  obtain ⟨e, he, hk⟩ := h 1 (by decide)
  simp only [terminals, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl <;> exact absurd hk (by decide)

/-- Two upper terminals at the same `x`-coordinate are malformed; `(2, 2)` and `(0, 0)` both
encode `0`. -/
example : ¬ WellFormed ((1, 1, [((0, 0), 0), ((2, 2), 0)], [((0, 0), 0)]) :
    TwoLayerChannelRoutingInstance) := by
  rintro ⟨-, h, -⟩
  exact absurd h (by decide)

/-- The decision problem accepts the encoding of `straight`. -/
example : twoLayerChannelRoutingDec (bitEncode straight) = true := by
  simp [twoLayerChannelRoutingDec, straight_wellFormed, straight_feasible]

/-- It rejects the encoding of the well-formed but infeasible `skew`. -/
example : twoLayerChannelRoutingDec (bitEncode skew) = false := by
  simp [twoLayerChannelRoutingDec, skew_infeasible]

/-- `skew` is well formed, so infeasibility is what rejects it. -/
example : WellFormed skew := skew_wellFormed

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : twoLayerChannelRoutingDec [true] = false := by
  have h : bitDecode (α := TwoLayerChannelRoutingInstance) [true] = none := rfl
  simp [twoLayerChannelRoutingDec, h]

end MetaMathlibExt.Complexity.NPComplete.TwoLayerChannelRouting
