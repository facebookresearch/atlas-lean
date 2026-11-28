/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DirectedHamiltonianPathDefs

namespace MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath

open HamiltonianCycleDirected (HamiltonianCycleDirectedInstance WellFormed)
open Cslib.Complexity.Karp (IsHamPath)
open Cslib.Complexity.Path (arc)

/-- The directed path `0 → 1 → 2`. -/
private abbrev line : HamiltonianCycleDirectedInstance := (3, [(0, 1), (1, 2)])

/-- The same arcs as an out-star at `1`: `1 → 0` and `1 → 2`. -/
private abbrev outStar : HamiltonianCycleDirectedInstance := (3, [(1, 0), (1, 2)])

private theorem line_wellFormed : WellFormed line := by unfold WellFormed; decide

private theorem outStar_wellFormed : WellFormed outStar := by unfold WellFormed; decide

/-- `0, 1, 2` is a Hamiltonian path of the directed path. -/
private theorem line_feasible : DirectedHamiltonianPathFeasible line :=
  ⟨0, 2, [0, 1, 2], by simp [IsHamPath, arc]⟩

/-- The reversed order `2, 1, 0` follows no arcs. -/
example : ¬ IsHamPath 3 [(0, 1), (1, 2)] 2 0 [2, 1, 0] := by simp [IsHamPath, arc]

/-- A path on three vertices has the shape `[a, b, c]`. -/
private theorem eq_triple {p : List ℕ} (h : p.length = 3) : ∃ a b c, p = [a, b, c] := by
  match p, h with
  | [a, b, c], _ => exact ⟨a, b, c, rfl⟩

/-- Both arcs of the out-star leave `1`, so no two of them chain: no Hamiltonian path. -/
private theorem outStar_infeasible : ¬ DirectedHamiltonianPathFeasible outStar := by
  rintro ⟨s, t, p, hnd, hlen, -, -, -, hch⟩
  obtain ⟨a, b, c, rfl⟩ := eq_triple hlen
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, arc] at hch
  obtain ⟨⟨hab, -⟩, ⟨hbc, -⟩⟩ := hch
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab hbc
  have ha : a = 1 := by omega
  have hb : b = 1 := by omega
  simp [ha, hb] at hnd

/-- One arc cannot cover three vertices. -/
example : ¬ DirectedHamiltonianPathFeasible ((3, [(0, 1)]) : HamiltonianCycleDirectedInstance) := by
  rintro ⟨s, t, p, -, hlen, -, -, -, hch⟩
  obtain ⟨a, b, c, rfl⟩ := eq_triple hlen
  simp only [List.isChain_cons_cons, List.isChain_singleton, and_true, arc] at hch
  obtain ⟨⟨hab, -⟩, ⟨hbc, -⟩⟩ := hch
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hab hbc
  omega

/-- A single vertex with no arcs is a path by itself. -/
private theorem single_feasible :
    DirectedHamiltonianPathFeasible ((1, []) : HamiltonianCycleDirectedInstance) :=
  ⟨0, 0, [0], by simp [IsHamPath]⟩

private theorem single_wellFormed : WellFormed ((1, []) : HamiltonianCycleDirectedInstance) := by
  unfold WellFormed; decide

/-- The empty digraph is malformed, and also has no path (a path has a first vertex). -/
example : ¬ WellFormed ((0, []) : HamiltonianCycleDirectedInstance) := by unfold WellFormed; decide

example : ¬ DirectedHamiltonianPathFeasible ((0, []) : HamiltonianCycleDirectedInstance) := by
  rintro ⟨s, t, p, -, hlen, -, hs, -⟩
  simp [List.length_eq_zero_iff.mp hlen] at hs

/-- Malformed instances that still have a Hamiltonian path `0, 1`: a repeated arc, a loop, and
an arc to a vertex outside the digraph. -/
private abbrev repeated : HamiltonianCycleDirectedInstance := (2, [(0, 1), (0, 1)])
private abbrev loop : HamiltonianCycleDirectedInstance := (2, [(0, 1), (1, 1)])
private abbrev outOfRange : HamiltonianCycleDirectedInstance := (2, [(0, 1), (1, 5)])

private theorem malformed :
    ¬ WellFormed repeated ∧ ¬ WellFormed loop ∧ ¬ WellFormed outOfRange := by
  unfold WellFormed; decide

private theorem malformed_feasible :
    DirectedHamiltonianPathFeasible repeated ∧ DirectedHamiltonianPathFeasible loop ∧
      DirectedHamiltonianPathFeasible outOfRange :=
  ⟨⟨0, 1, [0, 1], by simp [IsHamPath, arc]⟩, ⟨0, 1, [0, 1], by simp [IsHamPath, arc]⟩,
    ⟨0, 1, [0, 1], by simp [IsHamPath, arc]⟩⟩

open MetaMathlibExt.BitstringEncoding

/-- The decision problem accepts the directed path and the single vertex. -/
example : directedHamiltonianPathDec (bitEncode line) = true := by
  simp [directedHamiltonianPathDec, line_wellFormed, line_feasible]

example : directedHamiltonianPathDec (bitEncode ((1, []) : HamiltonianCycleDirectedInstance)) =
    true := by
  simp [directedHamiltonianPathDec, single_wellFormed, single_feasible]

/-- It rejects the well-formed out-star. -/
example : directedHamiltonianPathDec (bitEncode outStar) = false := by
  simp [directedHamiltonianPathDec, outStar_infeasible]

/-- It rejects the feasible malformed instances. -/
example :
    directedHamiltonianPathDec (bitEncode repeated) = false ∧
      directedHamiltonianPathDec (bitEncode loop) = false ∧
      directedHamiltonianPathDec (bitEncode outOfRange) = false := by
  simp [directedHamiltonianPathDec, malformed.1, malformed.2.1, malformed.2.2]

example : DirectedHamiltonianPathFeasible repeated ∧ DirectedHamiltonianPathFeasible loop ∧
    DirectedHamiltonianPathFeasible outOfRange := malformed_feasible

/-- It rejects the empty bitstring, which decodes to no instance. -/
example : directedHamiltonianPathDec [] = false := by
  have h : bitDecode (α := HamiltonianCycleDirectedInstance) [] = none := rfl
  simp [directedHamiltonianPathDec, h]

end MetaMathlibExt.Complexity.NPComplete.DirectedHamiltonianPath
