/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LONGEST DIRECTED PATH is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND29] LONGEST PATH, p. 213,
comment: "Remains NP-complete if l(e) = 1 for all e ∈ E, as does the corresponding problem for
directed paths in directed graphs"; problems [GT38] DIRECTED HAMILTONIAN CIRCUIT and [GT39]
HAMILTONIAN PATH (directed variant);
R. M. Karp, "Reducibility among combinatorial problems", in Complexity of Computer
Computations (R. E. Miller and J. W. Thatcher, eds.), Plenum Press (1972), 85-103,
doi:10.1007/978-1-4684-2001-2_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Algorithms.Lean.Graph.ShortestPath.Dijkstra
public import Cslib.Foundations.Data.List.IsChainFromTo

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LongestDirectedPath

/-!
# LONGEST DIRECTED PATH is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a length `l(a) ∈ ℤ⁺` for each `a ∈ A`, a positive
integer `K`, and specified vertices `s, t ∈ V`. QUESTION: is there a simple directed path in
`G` from `s` to `t` of length `K` or more, i.e., whose arc lengths sum to at least `K`?

This is LONGEST PATH (Garey and Johnson [ND29]) for directed paths in directed graphs. The
vertices are `Fin n`; the arcs are listed with their lengths (an entry `(u, v, l)` is the arc
`u → v` of length `l`), with no loops and no two entries for the same ordered pair. The graph is
a `Cslib.Algorithms.Lean.DirectedAdjacency`. A directed path from `s` to `t` is a
`List.IsChainFromTo` chain of arcs from `s` to `t` (a nonempty vertex list starting at `s`,
ending at `t`, each vertex joined to the next by an arc), and it is simple when its vertices
are distinct. Its length is `DirectedAdjacency.pathWeight` of the arc lengths, the measure of
CSLib's Dijkstra specification.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the arc list with lengths (an entry
`(u, v, l)` is the arc `u → v` of length `l`), the bound `K`, and the vertices `s` and `t`. -/
abbrev LongestDirectedPathInstance := ℕ × List (ℕ × ℕ × ℕ) × ℕ × ℕ × ℕ

/-- The directed graph of the instance on `Fin n`: the out-neighbors of `u` are the vertices
`v` with an entry `(u, v, l)` in the arc list. -/
def Graph (i : LongestDirectedPathInstance) :
    Cslib.Algorithms.Lean.DirectedAdjacency (Fin i.1) where
  vertices := List.finRange i.1
  vertices_nodup := List.nodup_finRange i.1
  vertices_complete := List.mem_finRange
  adjacency u := (List.finRange i.1).filter fun v =>
    ((u : ℕ), (v : ℕ)) ∈ i.2.1.map fun a => (a.1, a.2.1)

/-- The length `l(u → v)`: the length recorded for the arc-list entry `(u, v, l)` (unique
under `WellFormed`). -/
def arcLength (i : LongestDirectedPathInstance) (u v : Fin i.1) : ℕ :=
  ((i.2.1.find? fun a => a.1 = (u : ℕ) ∧ a.2.1 = (v : ℕ)).map fun a => a.2.2).getD 0

/-- Well-formedness of an instance: the arc list describes a directed graph on `Fin n` (no two
entries for the same ordered pair, no loops, endpoints in range), every length is positive,
`0 < K`, and `s, t ∈ V`. -/
def WellFormed (i : LongestDirectedPathInstance) : Prop :=
  (i.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1 ∧ 0 < a.2.2) ∧ 0 < i.2.2.1 ∧
    i.2.2.2.1 < i.1 ∧ i.2.2.2.2 < i.1

/-- Some simple directed path from `s` to `t` has length at least `K`: a chain of arcs `p`
from the vertex `s` to the vertex `t` with distinct vertices whose arc lengths sum to at
least `K`. -/
def LongestDirectedPathFeasible (i : LongestDirectedPathInstance) : Prop :=
  ∃ s t : Fin i.1, (s : ℕ) = i.2.2.2.1 ∧ (t : ℕ) = i.2.2.2.2 ∧
    ∃ p : List (Fin i.1), p.IsChainFromTo (Graph i).Edge s t ∧ p.Nodup ∧
      i.2.2.1 ≤ Cslib.Algorithms.Lean.DirectedAdjacency.pathWeight (arcLength i) p

open Classical in
/-- LONGEST DIRECTED PATH as a decision problem over bitstrings. -/
noncomputable def longestDirectedPathDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LongestDirectedPathInstance) x with
  | some i => decide (WellFormed i ∧ LongestDirectedPathFeasible i)
  | none => false

/-- **LONGEST DIRECTED PATH is NP-complete.** Source: Garey and Johnson (1979), [ND29],
comment; Karp (1972), DIRECTED HAMILTONIAN CIRCUIT. -/
public theorem_wanted longestDirectedPath_npComplete :
    longestDirectedPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L longestDirectedPathDec

end MetaMathlibExt.Complexity.NPComplete.LongestDirectedPath
