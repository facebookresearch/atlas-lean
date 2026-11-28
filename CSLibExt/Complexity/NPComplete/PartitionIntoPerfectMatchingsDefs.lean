/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTITION INTO PERFECT MATCHINGS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT16] PARTITION INTO
PERFECT MATCHINGS;
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the
10th Annual ACM Symposium on Theory of Computing (STOC 1978), 216-226,
doi:10.1145/800133.804350 (already for `K = 2`, by a transformation from
NOT-ALL-EQUAL 3SAT);
see also E. D. Demaine, K. Karntikoon, and N. Pitimanaaree, "2-Colorable
perfect matching is NP-complete in 2-connected 3-regular planar graphs",
Theory of Computing Systems (2025), doi:10.1007/s00224-025-10221-2.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Matching

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchings

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev PartitionIntoPerfectMatchingsInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : PartitionIntoPerfectMatchingsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and
`0 < K ≤ |V| = n`. -/
def WellFormed (i : PartitionIntoPerfectMatchingsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The vertices split into at most `K` blocks, each inducing a perfect matching: for some
`k ≤ K` there is a partition into blocks `c⁻¹(j)`, `j : Fin k`, such that the subgraph induced
by each block is a matching on that block. -/
def PartitionIntoPerfectMatchingsFeasible (i : PartitionIntoPerfectMatchingsInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ c : Fin i.1 → Fin k,
    ∀ j : Fin k, ((⊤ : (Graph i).Subgraph).induce {v | c v = j}).IsMatching

open Classical in
/-- PARTITION INTO PERFECT MATCHINGS as a decision problem over bitstrings. -/
noncomputable def partitionIntoPerfectMatchingsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartitionIntoPerfectMatchingsInstance) x with
  | some i => decide (WellFormed i ∧ PartitionIntoPerfectMatchingsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.PartitionIntoPerfectMatchings
