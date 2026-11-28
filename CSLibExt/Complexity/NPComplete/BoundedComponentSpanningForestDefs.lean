/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED COMPONENT SPANNING FOREST: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND10] BOUNDED COMPONENT SPANNING
FOREST; F. O. Hadlock, "Minimum spanning forests of bounded trees", Proceedings of the 5th
Southeastern Conference on Combinatorics, Graph Theory and Computing, Utilitas Mathematica
(1974), 449-460; M. E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into
connected subgraphs", Discrete Applied Mathematics 10 (1985), 139-153,
doi:10.1016/0166-218X(85)90008-3.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, vertex weights
`[w 0, ..., w (n - 1)]`, the bound `K` on the number of parts, and the weight bound `B`. -/
abbrev BoundedComponentSpanningForestInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BoundedComponentSpanningForestInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one weight
per vertex, `0 < K ≤ |V|`, and `0 < B`. -/
def WellFormed (i : BoundedComponentSpanningForestInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧ 0 < i.2.2.2.1 ∧ i.2.2.2.1 ≤ i.1 ∧ 0 < i.2.2.2.2

/-- For some `k ≤ K`, a surjective assignment `c` of the vertices to `k` parts makes every part
induce a connected subgraph of total weight at most `B`. -/
def BoundedComponentSpanningForestFeasible
    (i : BoundedComponentSpanningForestInstance) : Prop :=
  ∃ k ≤ i.2.2.2.1, ∃ c : Fin i.1 → Fin k, Function.Surjective c ∧
    ∀ j, ((Graph i).induce {v | c v = j}).Connected ∧
      ∑ v with c v = j, i.2.2.1.getD v 0 ≤ i.2.2.2.2

open Classical in
/-- BOUNDED COMPONENT SPANNING FOREST as a decision problem over bitstrings. -/
noncomputable def boundedComponentSpanningForestDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BoundedComponentSpanningForestInstance) x with
  | some i => decide (WellFormed i ∧ BoundedComponentSpanningForestFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest
