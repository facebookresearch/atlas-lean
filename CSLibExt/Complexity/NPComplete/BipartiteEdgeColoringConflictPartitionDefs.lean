/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BIPARTITE EDGE COLORING WITH CONFLICT PARTITION: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 5 (1984), 147-160,
doi:10.1016/0196-6774(84)90045-2, Section 2, entry CHROMATIC INDEX (reference: A. A. Bertossi,
"An NP-complete coloring problem in bipartite graphs", manuscript (1983); the manuscript was not
available);
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 2 (1981), 393-405,
doi:10.1016/0196-6774(81)90037-7, problem [5] CHROMATIC INDEX (the base problem).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteEdgeColoringConflictPartition

open EdgeColoring (EdgeColoringInstance)

/-- An instance: a CHROMATIC INDEX instance (vertex count, edge list, bound `K`) and the list of
partition labels, one per listed edge. -/
abbrev BipartiteEdgeColoringConflictPartitionInstance := EdgeColoringInstance × List ℕ

/-- Well-formedness of an instance: the edge list is a simple edge list on `Fin n`, the graph is
bipartite, there is one partition label per edge, and `K` is positive. -/
def WellFormed (i : BipartiteEdgeColoringConflictPartitionInstance) : Prop :=
  EdgeColoring.WellFormed i.1 ∧ (Cslib.Complexity.Karp.edgeGraph i.1.1 i.1.2.1).IsBipartite ∧
    i.2.length = i.1.2.1.length ∧ 0 < i.1.2.2

/-- A coloring of the edges with colors below `K` in which two edges at distinct positions get
distinct colors whenever they share an endpoint or have the same partition label. -/
def BipartiteEdgeColoringConflictPartitionFeasible
    (i : BipartiteEdgeColoringConflictPartitionInstance) : Prop :=
  ∃ coloring : List ℕ, coloring.length = i.1.2.1.length ∧ (∀ c ∈ coloring, c < i.1.2.2) ∧
    ∀ a < i.1.2.1.length, ∀ b < i.1.2.1.length, a ≠ b →
      ((i.1.2.1.getD a (0, 0)).1 = (i.1.2.1.getD b (0, 0)).1 ∨
        (i.1.2.1.getD a (0, 0)).1 = (i.1.2.1.getD b (0, 0)).2 ∨
        (i.1.2.1.getD a (0, 0)).2 = (i.1.2.1.getD b (0, 0)).1 ∨
        (i.1.2.1.getD a (0, 0)).2 = (i.1.2.1.getD b (0, 0)).2 ∨
        i.2.getD a 0 = i.2.getD b 0) →
      coloring.getD a 0 ≠ coloring.getD b 0

open Classical in
/-- BIPARTITE EDGE COLORING WITH CONFLICT PARTITION as a decision problem over bitstrings. -/
noncomputable def bipartiteEdgeColoringConflictPartitionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BipartiteEdgeColoringConflictPartitionInstance) x with
  | some i => decide (WellFormed i ∧ BipartiteEdgeColoringConflictPartitionFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BipartiteEdgeColoringConflictPartition
