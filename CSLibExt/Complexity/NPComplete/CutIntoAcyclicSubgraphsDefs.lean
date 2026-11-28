/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUT INTO ACYCLIC SUBGRAPHS: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [7] CUT INTO ACYCLIC SUBGRAPHS (reference: P. Gács,
"Partitioning a directed graph into two acyclic subgraphs is NP-complete", manuscript (1981);
transformation from 3SAT);
D. Bokal, G. Fijavž, M. Juvan, P. M. Kayll and B. Mohar, "The circular chromatic number of a
digraph", J. Graph Theory 46 (2004), 227-240, doi:10.1002/jgt.20003.
-/
module

public import MathlibExt.Combinatorics.SimpleGraph.Dichromatic
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CutIntoAcyclicSubgraphs

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and the arc list (an entry `(u, v)`
is the arc `u → v`). -/
abbrev CutIntoAcyclicSubgraphsInstance := ℕ × List (ℕ × ℕ)

/-- The arc relation of the digraph on `Fin n`: `Arc i u v` when `(u, v)` is a listed arc. -/
def Arc (i : CutIntoAcyclicSubgraphsInstance) (u v : Fin i.1) : Prop :=
  ((u : ℕ), (v : ℕ)) ∈ i.2

/-- Well-formedness of an instance: the arc list describes a digraph on `0, …, n - 1` without
loops or repeated arcs (no arc listed twice, both endpoints below `n`, no arc from a vertex to
itself). -/
def WellFormed (i : CutIntoAcyclicSubgraphsInstance) : Prop :=
  i.2.Nodup ∧ ∀ a ∈ i.2, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2

/-- Some partition of the vertices into two classes (a colouring `c : Fin n → Fin 2`) leaves no
directed cycle (closed directed walk of positive length, `SimpleGraph.IsDirectedCycle`) inside
one class, so both classes induce acyclic subgraphs. -/
def CutIntoAcyclicSubgraphsFeasible (i : CutIntoAcyclicSubgraphsInstance) : Prop :=
  ∃ c : Fin i.1 → Fin 2, ∀ (m : ℕ) (f : Fin (m + 2) → Fin i.1),
    SimpleGraph.IsDirectedCycle (Arc i) m f → ¬ ∃ col, ∀ j, c (f j) = col

open Classical in
/-- CUT INTO ACYCLIC SUBGRAPHS as a decision problem over bitstrings. -/
noncomputable def cutIntoAcyclicSubgraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CutIntoAcyclicSubgraphsInstance) x with
  | some i => decide (WellFormed i ∧ CutIntoAcyclicSubgraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CutIntoAcyclicSubgraphs
