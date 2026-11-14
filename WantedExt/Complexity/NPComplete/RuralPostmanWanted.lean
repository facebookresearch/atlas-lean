/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RURAL POSTMAN is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN;
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems",
Networks 6 (1976), 273-280, doi:10.1002/net.3230060305 (Theorem: the rural
postman problem is polynomial complete for undirected and for directed graphs).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Walks.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RuralPostman

/-!
# RURAL POSTMAN is NP-complete

INSTANCE: a graph `G = (V, E)`, a length `l(e) ∈ ℤ₀⁺` for each `e ∈ E`, a subset `E' ⊆ E`, and
a positive integer `B`. QUESTION: is there a circuit in `G` that includes each edge in `E'` and
that has total length no more than `B`?

A circuit here is a closed walk that may repeat vertices and edges, as in the source's
"postman's tour (i.e. an undirected cycle traversing each arc in a given subset R ⊆ A at least
once)" (Lenstra and Rinnooy Kan); its length counts every traversal of an edge. It is a Mathlib
`SimpleGraph.Walk v v`, and its total length is the sum of the edge lengths along
`SimpleGraph.Walk.edges` (with repetitions).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list with lengths (an entry
`(u, v, l)` is the edge `{u, v}` of length `l`), the required edges `E'` (pairs of endpoints),
and the bound `B`. -/
abbrev RuralPostmanInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : RuralPostmanInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 (i.2.1.map fun e => (e.1, e.2.1))

/-- The length of an edge `s`: the length recorded for the list entry whose endpoints are the
endpoints of `s` (unique under `WellFormed`). -/
def edgeLength (i : RuralPostmanInstance) (s : Sym2 (Fin i.1)) : ℕ :=
  ((i.2.1.find? fun e => s.map Fin.val = s(e.1, e.2.1)).map fun e => e.2.2).getD 0

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), every required pair
is an edge of the graph (in either orientation), and `0 < B`. -/
def WellFormed (i : RuralPostmanInstance) : Prop :=
  ((i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1 ∧
      (e.2.1, e.1) ∉ i.2.1.map fun e => (e.1, e.2.1)) ∧
    (∀ r ∈ i.2.2.1, r ∈ (i.2.1.map fun e => (e.1, e.2.1)) ∨
      (r.2, r.1) ∈ i.2.1.map fun e => (e.1, e.2.1)) ∧
    0 < i.2.2.2

/-- Some closed walk traverses every required edge and has total length at most `B` (each
traversal of an edge counts its length). -/
def RuralPostmanFeasible (i : RuralPostmanInstance) : Prop :=
  ∃ v, ∃ c : (Graph i).Walk v v,
    (∀ r ∈ i.2.2.1, s(r.1, r.2) ∈ c.edges.map (Sym2.map Fin.val)) ∧
      (c.edges.map (edgeLength i)).sum ≤ i.2.2.2

open Classical in
/-- RURAL POSTMAN as a decision problem over bitstrings. -/
noncomputable def ruralPostmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RuralPostmanInstance) x with
  | some i => decide (WellFormed i ∧ RuralPostmanFeasible i)
  | none => false

/-- **RURAL POSTMAN is NP-complete.** Source: Garey and Johnson (1979), [ND27]; Lenstra and
Rinnooy Kan (1976). -/
public theorem_wanted ruralPostman_npComplete :
    ruralPostmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L ruralPostmanDec

end MetaMathlibExt.Complexity.NPComplete.RuralPostman
