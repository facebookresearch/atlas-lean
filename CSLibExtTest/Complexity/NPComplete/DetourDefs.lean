/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DetourDefs

namespace MetaMathlibExt.Complexity.NPComplete.Detour

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : DetourInstance) :
    detourDec (bitEncode i) = true ↔ WellFormed i ∧ DetourFeasible i := by
  simp [detourDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : detourDec [true] = false := by
  have h : bitDecode (α := DetourInstance) [true] = none := rfl
  simp [detourDec, h]

/-- A two-by-two grid forming one region labeled `0`, with the clue that this region has `k`
turns. -/
private abbrev square (k : ℕ) : DetourInstance := (2, [[0, 0], [0, 0]], [(0, k)])

/-- The 2 × 2 grid graph. -/
private abbrev G₂ : SimpleGraph (Fin 2 × Fin 2) :=
  SimpleGraph.pathGraph 2 □ SimpleGraph.pathGraph 2

private instance : DecidableRel G₂.Adj := fun x y =>
  decidable_of_iff ((x.1.val + 1 = y.1.val ∨ y.1.val + 1 = x.1.val) ∧ x.2 = y.2 ∨
      (x.2.val + 1 = y.2.val ∨ y.2.val + 1 = x.2.val) ∧ x.1 = y.1)
    (by simp [SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj])

/-- The loop around the four cells of the 2 × 2 grid. -/
private def loop : G₂.Walk (0, 0) (0, 0) :=
  .cons (v := (0, 1)) (by decide) <| .cons (v := (1, 1)) (by decide) <|
    .cons (v := (1, 0)) (by decide) <| .cons (by decide) .nil

private theorem loop_isHamiltonianCycle : loop.IsHamiltonianCycle :=
  SimpleGraph.Walk.isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one.2
    ⟨(SimpleGraph.Walk.isCycle_def _).2 ⟨⟨by decide⟩, by simp [loop], by decide⟩, by decide⟩

/-- The four edges of the 2 × 2 grid. -/
private abbrev gridEdges : List (Sym2 (Fin 2 × Fin 2)) :=
  [s((0, 0), (0, 1)), s((0, 1), (1, 1)), s((1, 1), (1, 0)), s((1, 0), (0, 0))]

/-- Every Hamiltonian cycle of the 2 × 2 grid turns at every cell: its four distinct edges are
the four grid edges, and the two grid neighbors of a cell differ in both coordinates. -/
private theorem turns_everywhere {v : Fin 2 × Fin 2} (W : G₂.Walk v v)
    (hW : W.IsHamiltonianCycle) (u : Fin 2 × Fin 2) :
    ∃ a b : Fin 2 × Fin 2, s(u, a) ∈ W.edges ∧ s(u, b) ∈ W.edges ∧ a.1 ≠ b.1 ∧ a.2 ≠ b.2 := by
  have key : ∀ x y, G₂.Adj x y → s(x, y) ∈ gridEdges := by decide
  have hsub : W.edges ⊆ gridEdges := fun e he => by
    have := W.edges_subset_edgeSet he
    induction e using Sym2.ind with
    | h x y => exact key x y this
  have hlen : gridEdges.length ≤ W.edges.length := by
    rw [SimpleGraph.Walk.length_edges, hW.length_eq]; decide
  have hperm := (List.subperm_of_subset hW.edges_nodup hsub).perm_of_length_le hlen
  obtain ⟨a, b, ha, hb, h₁, h₂⟩ : ∃ a b : Fin 2 × Fin 2,
      s(u, a) ∈ gridEdges ∧ s(u, b) ∈ gridEdges ∧ a.1 ≠ b.1 ∧ a.2 ≠ b.2 := by
    revert u; decide
  exact ⟨a, b, hperm.mem_iff.2 ha, hperm.mem_iff.2 hb, h₁, h₂⟩

/-- With the clue `4`, the loop around the four cells solves the puzzle: it turns at all four
cells of the region. -/
example : detourDec (bitEncode (square 4)) = true := by
  classical
  refine (accepts_encoding _).2
    ⟨by unfold WellFormed; decide, (0, 0), loop, loop_isHamiltonianCycle, ?_⟩
  intro q hq
  obtain rfl : q = (0, 4) := List.mem_singleton.1 hq
  rw [Finset.filter_true_of_mem fun u _ =>
    ⟨by revert u; decide, turns_everywhere loop loop_isHamiltonianCycle u⟩]
  rfl

/-- With the clue `3`, the grid is well formed and has a Hamiltonian cycle, but every
Hamiltonian cycle turns at all four cells. -/
example : detourDec (bitEncode (square 3)) = false := by
  cases h : detourDec (bitEncode (square 3)) with
  | false => rfl
  | true =>
    classical
    obtain ⟨-, v, W, hW, hq⟩ := (accepts_encoding _).1 h
    have := hq (0, 3) (List.mem_singleton_self _)
    rw [Finset.filter_true_of_mem fun u _ =>
      ⟨by revert u; decide, turns_everywhere W hW u⟩] at this
    exact absurd this (by decide)

/-- A one-by-two grid is well formed, but two cells cannot carry a cycle, which needs at least
three edges. -/
example : detourDec (bitEncode ((2, [[0, 0]], []) : DetourInstance)) = false := by
  cases h : detourDec (bitEncode ((2, [[0, 0]], []) : DetourInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, v, W, hW, -⟩ := (accepts_encoding _).1 h
    have h₃ := hW.isCycle.three_le_length
    rw [hW.length_eq] at h₃
    exact absurd h₃ (by decide)

end MetaMathlibExt.Complexity.NPComplete.Detour
