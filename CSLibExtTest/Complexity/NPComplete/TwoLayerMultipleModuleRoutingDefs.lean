/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.TwoLayerMultipleModuleRoutingDefs

namespace MetaMathlibExt.Complexity.NPComplete.TwoLayerMultipleModuleRouting

open MetaMathlibExt.BitstringEncoding
open StatMech.Lattice (Site hypercubicLattice)
open TwoLayerChannelRouting (toInt IsLeaf)

private theorem sum_two {M : Type} [AddCommMonoid M] (g : Fin 2 → M) :
    ∑ i, g i = g 0 + (g 1 + 0) := rfl

/-- The points `(1, 0)` and `(2, 0)`. -/
private def q1 : Site 2 := ![1, 0]

private def q2 : Site 2 := ![2, 0]

private theorem q1_adj_q2 : (hypercubicLattice 2).Adj q1 q2 := by
  simp only [StatMech.Lattice.hypercubicLattice_adj, sum_two]
  decide

/-- The unit squares `[0, 1] × [0, 1]` and `[2, 3] × [0, 1]` (each coordinate `p - q` written
as `(p, q)`), one net joining the terminals `(1, 0)` and `(2, 0)` on their facing sides, and
the area bound `B`. -/
private abbrev twoSquares (B : ℕ) : TwoLayerMultipleModuleRoutingInstance :=
  ([((0, 0), (0, 0), (1, 0), (1, 0)), ((2, 0), (0, 0), (3, 0), (1, 0))],
    [(((1, 0), (0, 0)), 0), (((2, 0), (0, 0)), 0)], 1, B)

private theorem twoSquares_wellFormed (B : ℕ) : WellFormed (twoSquares B) := by
  unfold WellFormed
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro M hM
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl <;> decide
  · intro a b hab
    have h : ∀ a b : Fin 2, a ≠ b → RectsDisjoint
        (moduleRect ([((0, 0), (0, 0), (1, 0), (1, 0)), ((2, 0), (0, 0), (3, 0), (1, 0))].get a))
        (moduleRect ([((0, 0), (0, 0), (1, 0), (1, 0)), ((2, 0), (0, 0), (3, 0), (1, 0))].get
          b)) := by
      unfold RectsDisjoint moduleRect toInt; decide
    exact h a b hab
  · unfold terminals toInt; dsimp only; decide
  · intro e he
    simp only [terminals, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl
    · exact ⟨_, List.mem_cons_self .., by unfold OnPerimeter InRect moduleRect toInt; decide⟩
    · exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..),
        by unfold OnPerimeter InRect moduleRect toInt; decide⟩
  · intro e he
    simp only [terminals, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at he
    rcases he with rfl | rfl <;> decide
  · intro k hk
    exact ⟨_, List.mem_cons_self .., by simp; omega⟩

/-- The segment from `(1, 0)` to `(2, 0)` routes the net inside the `3 × 1` rectangle
`[0, 3] × [0, 1]`, which includes both squares; neither square contains the segment. -/
private theorem twoSquares_three_feasible : TwoLayerMultipleModuleRoutingFeasible (twoSquares 3) := by
  refine ⟨fun _ => (hypercubicLattice 2).subgraphOfAdj q1_adj_q2, (0, 0, 3, 1), by decide,
    by decide, by decide, ?_, ?_, fun k => ⟨?_, ?_, ?_⟩,
    fun k l hkl => absurd (Subsingleton.elim k l) hkl⟩
  · intro M hM
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hM
    rcases hM with rfl | rfl <;> unfold RectIncluded moduleRect toInt <;> decide
  · intro k u v huv
    simp only [SimpleGraph.subgraphOfAdj_adj, Sym2.eq_iff] at huv
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      unfold InRect moduleRect toInt q1 q2 <;> decide
  · exact (Set.finite_singleton _).insert _
  · exact SimpleGraph.IsTree.coe_subgraphOfAdj q1_adj_q2
  · intro v
    have hleaf : IsLeaf ((hypercubicLattice 2).subgraphOfAdj q1_adj_q2) v ↔ v = q1 ∨ v = q2 := by
      constructor
      · rintro ⟨hv, -⟩
        simpa using hv
      · intro hv
        refine ⟨by simpa using hv, fun u w h1 h2 => ?_⟩
        simp only [SimpleGraph.subgraphOfAdj_adj] at h1 h2
        exact Sym2.congr_right.mp (h1.symm.trans h2)
    rw [hleaf]
    simp only [terminals, toInt, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false, Prod.mk.injEq, Fin.val_eq_zero, and_true, Nat.cast_zero, Nat.cast_one,
      sub_zero, q1, q2]
    rfl

/-- With area bound `2` the instance is infeasible: any rectangle including both squares
spans `[0, 3] × [0, 1]`, of area at least `3`. -/
private theorem twoSquares_two_infeasible :
    ¬ TwoLayerMultipleModuleRoutingFeasible (twoSquares 2) := by
  rintro ⟨T, ⟨x₁, y₁, x₂, y₂⟩, hx, hy, harea, hinc, -⟩
  have h1 := hinc _ (List.mem_cons_self ..)
  have h2 := hinc _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  simp only [RectIncluded, moduleRect, toInt] at h1 h2 hx hy harea
  push_cast at h1 h2 harea
  have hw : 3 ≤ x₂ - x₁ := by omega
  have hh : 1 ≤ y₂ - y₁ := by omega
  have := Int.mul_le_mul hw hh (by decide) (by omega)
  exact absurd (le_trans this harea) (by decide)

/-- Overlapping modules are malformed. -/
example : ¬ WellFormed (([((0, 0), (0, 0), (2, 0), (1, 0)), ((1, 0), (0, 0), (3, 0), (1, 0))],
    [(((0, 0), (0, 0)), 0)], 1, 9) : TwoLayerMultipleModuleRoutingInstance) := by
  rintro ⟨-, h, -⟩
  have := h 0 1 (by decide)
  revert this
  unfold RectsDisjoint moduleRect toInt
  decide

/-- A terminal off every module's perimeter is malformed: `(5, 5)` is far from the square. -/
example : ¬ WellFormed (([((0, 0), (0, 0), (1, 0), (1, 0))], [(((5, 0), (5, 0)), 0)], 1, 9) :
    TwoLayerMultipleModuleRoutingInstance) := by
  rintro ⟨-, -, -, h, -⟩
  obtain ⟨M, hM, hp⟩ := h _ (List.mem_singleton_self _)
  simp only [List.mem_singleton] at hM
  subst hM
  revert hp
  unfold OnPerimeter InRect moduleRect toInt
  decide

/-- The decision problem accepts the encoding of `twoSquares 3`. -/
example : twoLayerMultipleModuleRoutingDec (bitEncode (twoSquares 3)) = true := by
  simp [twoLayerMultipleModuleRoutingDec, twoSquares_wellFormed, twoSquares_three_feasible]

/-- It rejects the encoding of the well-formed but infeasible `twoSquares 2`. -/
example : twoLayerMultipleModuleRoutingDec (bitEncode (twoSquares 2)) = false := by
  simp [twoLayerMultipleModuleRoutingDec, twoSquares_two_infeasible]

/-- It rejects a lone continuation bit, which decodes to no instance. -/
example : twoLayerMultipleModuleRoutingDec [true] = false := by
  have h : bitDecode (α := TwoLayerMultipleModuleRoutingInstance) [true] = none := rfl
  simp [twoLayerMultipleModuleRoutingDec, h]

end MetaMathlibExt.Complexity.NPComplete.TwoLayerMultipleModuleRouting
