/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Automata.NA.BuchiKosarajuEmptiness
public meta import CSLibExt.Computability.Automata.NA.BuchiKosarajuEmptiness

/-!
# Tests for the Kosaraju Büchi emptiness scanner

* `splitPreorder` cuts a DFS preorder at its forest roots, and its costed version returns the same
  blocks within the proved cost bound.
* `kosarajuSCCs` returns the strongly connected components of a three-vertex graph with a
  two-cycle and a self-loop, and of a graph without edges.
* `kosarajuIsEmptyB` agrees with `Buchi.isEmptyB` on three automata: an accepting state with no
  successor (empty), an accepting self-loop (nonempty), and an accepting cycle that no start state
  reaches (empty). The costed scanner returns the same result within its proved bound.
-/

@[expose] public section

namespace Cslib.BuchiKosarajuEmptiness.Tests

open Cslib.Automata.NA Cslib.Automata.ωAcceptor
open Cslib.Algorithms.Lean

/-! ## Splitting a preorder at forest roots -/

#guard splitPreorder [0, 3] [0, 1, 2, 3, 4] == [[0, 1, 2], [3, 4]]

#guard splitPreorder [0] [0, 1, 2] == [[0, 1, 2]]

#guard splitPreorder ([] : List ℕ) [] == []

#guard (splitPreorderC [0, 3] [0, 1, 2, 3, 4]).1 == splitPreorder [0, 3] [0, 1, 2, 3, 4]

#guard (splitPreorderC [0, 3] [0, 1, 2, 3, 4]).2 ≤ 2 + 2 * 5 + 1

/-! ## Strongly connected components -/

/-- `0 ⇄ 1 → 2`, with a self-loop at `2`: components `{0, 1}` and `{2}`. -/
def cycleGraph : DirectedAdjacency (Fin 3) where
  vertices := List.finRange 3
  vertices_nodup := List.nodup_finRange 3
  vertices_complete := List.mem_finRange
  adjacency
    | 0 => [1]
    | 1 => [0, 2]
    | _ => [2]

#guard kosarajuSCCs cycleGraph == [[0, 1], [2]]

/-- Three vertices and no edges: three singleton components. -/
def edgelessGraph : DirectedAdjacency (Fin 3) where
  vertices := List.finRange 3
  vertices_nodup := List.nodup_finRange 3
  vertices_complete := List.mem_finRange
  adjacency _ := []

#guard (kosarajuSCCs edgelessGraph).length == 3

#guard (kosarajuSCCs edgelessGraph).all (·.length == 1)

/-- A block is cyclic when it has two states or a self-loop. -/
example : blockCyclicB cycleGraph [0, 1] = true := by decide

example : blockCyclicB cycleGraph [2] = true := by decide

example : blockCyclicB edgelessGraph [2] = false := by decide

/-! ## Emptiness -/

/-- The start state `0` moves to the accepting state `1`, which has no successor: empty. -/
def deadEnd : Buchi (Fin 2) Unit where
  Tr s _ t := s = 0 ∧ t = 1
  start := {0}
  accept := {1}

instance : ∀ s x t, Decidable (deadEnd.Tr s x t) := fun s _ t =>
  inferInstanceAs (Decidable (s = 0 ∧ t = 1))

instance : DecidablePred (· ∈ deadEnd.start) := fun s => inferInstanceAs (Decidable (s = 0))

instance : DecidablePred (· ∈ deadEnd.accept) := fun s => inferInstanceAs (Decidable (s = 1))

/-- The start state `0` moves to the accepting state `1`, which loops: nonempty. -/
def acceptingLoop : Buchi (Fin 2) Unit where
  Tr _ _ t := t = 1
  start := {0}
  accept := {1}

instance : ∀ s x t, Decidable (acceptingLoop.Tr s x t) := fun _ _ t =>
  inferInstanceAs (Decidable (t = 1))

instance : DecidablePred (· ∈ acceptingLoop.start) := fun s =>
  inferInstanceAs (Decidable (s = 0))

instance : DecidablePred (· ∈ acceptingLoop.accept) := fun s =>
  inferInstanceAs (Decidable (s = 1))

/-- The accepting state `2` lies on the cycle `1 ⇄ 2`, but the start state `0` only loops on
itself: empty. -/
def unreachableCycle : Buchi (Fin 3) Unit where
  Tr s _ t := (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 2) ∨ (s = 2 ∧ t = 1)
  start := {0}
  accept := {2}

instance : ∀ s x t, Decidable (unreachableCycle.Tr s x t) := fun s _ t =>
  inferInstanceAs (Decidable ((s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 2) ∨ (s = 2 ∧ t = 1)))

instance : DecidablePred (· ∈ unreachableCycle.start) := fun s =>
  inferInstanceAs (Decidable (s = 0))

instance : DecidablePred (· ∈ unreachableCycle.accept) := fun s =>
  inferInstanceAs (Decidable (s = 2))

/-- The scanner on the transition graph of a Büchi automaton over `Fin n`. -/
abbrev scan {n : ℕ} (na : Buchi (Fin n) Unit) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)] : Bool :=
  kosarajuIsEmptyB (List.finRange n) (List.nodup_finRange n) List.mem_finRange na
    (buchiGraph (List.finRange n) (List.nodup_finRange n) List.mem_finRange na) rfl

/-- The costed scanner on the same graph. -/
abbrev scanC {n : ℕ} (na : Buchi (Fin n) Unit) [∀ s x t, Decidable (na.Tr s x t)]
    [DecidablePred (· ∈ na.start)] [DecidablePred (· ∈ na.accept)] : Bool × ℕ :=
  kosarajuIsEmptyBC (List.finRange n) (List.nodup_finRange n) List.mem_finRange na
    (buchiGraph (List.finRange n) (List.nodup_finRange n) List.mem_finRange na) rfl

#guard scan deadEnd

#guard !scan acceptingLoop

#guard scan unreachableCycle

#guard scan deadEnd == deadEnd.isEmptyB

#guard scan acceptingLoop == acceptingLoop.isEmptyB

#guard scan unreachableCycle == unreachableCycle.isEmptyB

#guard (scanC deadEnd).1 == scan deadEnd

#guard (scanC acceptingLoop).1 == scan acceptingLoop

#guard (scanC unreachableCycle).1 == scan unreachableCycle

/-- The costed scanner's cost stays within its proved bound. -/
example : (scanC unreachableCycle).2 ≤
    (startReachable (· ∈ unreachableCycle.start)
        (buchiGraph (List.finRange 3) (List.nodup_finRange 3) List.mem_finRange
          unreachableCycle)).length +
      ((kosarajuSCCs (buchiGraph (List.finRange 3) (List.nodup_finRange 3) List.mem_finRange
          unreachableCycle)).map fun block => 1 +
        (block.map fun s => ((buchiGraph (List.finRange 3) (List.nodup_finRange 3)
          List.mem_finRange unreachableCycle).adjacency s).length).sum +
        2 * block.length).sum :=
  kosarajuIsEmptyBC_cost_le _ _ _ _ _ rfl

end Cslib.BuchiKosarajuEmptiness.Tests
