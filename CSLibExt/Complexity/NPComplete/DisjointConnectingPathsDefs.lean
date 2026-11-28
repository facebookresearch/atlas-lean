/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DISJOINT CONNECTING PATHS: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND40] DISJOINT
CONNECTING PATHS;
R. M. Karp, "On the computational complexity of combinatorial problems",
Networks 5 (1975), 45-68, doi:10.1002/net.1975.5.1.45;
J. F. Lynch, "The equivalence of theorem proving and the interconnection
problem", ACM SIGDA Newsletter 5 (1975), 31-36, doi:10.1145/1061425.1061430.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPaths

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), edge list, and the list of vertex
pairs `(sᵢ, tᵢ)`. -/
abbrev DisjointConnectingPathsInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : DisjointConnectingPathsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list is simple (endpoints in range, no self-loops,
no repeated or reversed edges), every `sᵢ` and `tᵢ` is a vertex, and the pairs are disjoint:
the `2k` vertices `s₁, t₁, ..., sₖ, tₖ` are pairwise distinct. -/
def WellFormed (i : DisjointConnectingPathsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (∀ p ∈ i.2.2, p.1 < i.1 ∧ p.2 < i.1) ∧
    (i.2.2.flatMap fun p => [p.1, p.2]).Nodup

/-- There are paths `pⱼ`, one for each pair `(sⱼ, tⱼ)`, where `pⱼ` is a path in `G` from `sⱼ` to
`tⱼ`, and the paths of different pairs have no vertex in common. -/
def DisjointConnectingPathsFeasible (i : DisjointConnectingPathsInstance) : Prop :=
  ∃ paths : Fin i.2.2.length → (u : Fin i.1) × (v : Fin i.1) × (Graph i).Walk u v,
    (∀ j, ((paths j).1 : ℕ) = (i.2.2.get j).1 ∧ ((paths j).2.1 : ℕ) = (i.2.2.get j).2 ∧
      (paths j).2.2.IsPath) ∧
    ∀ j l, j ≠ l → (paths j).2.2.support.Disjoint (paths l).2.2.support

open Classical in
/-- DISJOINT CONNECTING PATHS as a decision problem over bitstrings. -/
noncomputable def disjointConnectingPathsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DisjointConnectingPathsInstance) x with
  | some i => decide (WellFormed i ∧ DisjointConnectingPathsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DisjointConnectingPaths
