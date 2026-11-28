/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO FORESTS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT14] PARTITION INTO
FORESTS (unpublished result; NP-complete already for `K = 2`);
S. L. Hakimi and E. F. Schmeichel, "A note on the vertex arboricity of a
graph", SIAM Journal on Discrete Mathematics 2 (1989), 64-67,
doi:10.1137/0402007 (NP-complete for `K = 2` already on planar graphs).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoForests

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev PartitionIntoForestsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoForestsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K ≤ |V|`. -/
def WellFormed (i : PartitionIntoForestsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The vertices split into at most `K` sets, each inducing an acyclic subgraph: for some
`k ≤ K` there is a block map `c : Fin n → Fin k` such that every block `{v | c v = j}` induces
a forest. -/
def PartitionIntoForestsFeasible (i : PartitionIntoForestsInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ c : Fin i.1 → Fin k,
    ∀ j, ((Graph i).induce {v | c v = j}).IsAcyclic

open Classical in
/-- PARTITION INTO FORESTS as a decision problem over bitstrings. -/
noncomputable def partitionIntoForestsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoForestsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoForestsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoForests
