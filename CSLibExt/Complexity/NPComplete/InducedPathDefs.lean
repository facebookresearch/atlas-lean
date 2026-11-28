/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDUCED PATH: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT23] INDUCED PATH;
M. Yannakakis, "Node- and edge-deletion NP-complete problems", Proceedings of
the 10th Annual ACM Symposium on Theory of Computing (STOC 1978), 253-264,
doi:10.1145/800133.804355 (Theorem 4, the connected node-deletion problem, for
the property "is a path").
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.Hasse

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.InducedPath

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev InducedPathInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : InducedPathInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K ≤ |V|`. -/
def WellFormed (i : InducedPathInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- Some set of `m ≥ K` vertices induces a simple path on `m` vertices: the path graph on `m`
vertices is an induced subgraph of the instance graph. -/
def InducedPathFeasible (i : InducedPathInstance) : Prop :=
  ∃ m, i.2.2 ≤ m ∧ (SimpleGraph.pathGraph m).IsIndContained (Graph i)

open Classical in
/-- INDUCED PATH as a decision problem over bitstrings. -/
noncomputable def inducedPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := InducedPathInstance) x with
  | some i => decide (WellFormed i ∧ InducedPathFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.InducedPath
