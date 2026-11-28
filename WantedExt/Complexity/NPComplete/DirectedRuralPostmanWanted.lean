/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIRECTED RURAL POSTMAN is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND27] RURAL POSTMAN, comment on
p. 213 ("as does the corresponding problem for directed graphs");
J. K. Lenstra and A. H. G. Rinnooy Kan, "On general routing problems", Networks 6 (1976),
273-280, doi:10.1002/net.3230060305, Theorem (p. 275: the rural postman problem is
NP-complete "both in the case that G is undirected and in the case that G is directed").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DirectedRuralPostman

/-!
# DIRECTED RURAL POSTMAN is NP-complete

INSTANCE: a directed graph `G = (V, A)`, a length `l(a) ∈ Z₀⁺` for each `a ∈ A`, a subset
`A' ⊆ A`, and a bound `B ∈ Z⁺`.
QUESTION: is there a directed circuit in `G` that includes each arc in `A'` and that has total
length no more than `B`?

This is the directed version of RURAL POSTMAN
(`WantedExt.Complexity.NPComplete.RuralPostmanWanted`), which Garey and Johnson's comment
records as NP-complete; Lenstra and Rinnooy Kan define it as asking for "a postman's tour (i.e.
an undirected (directed) cycle traversing each arc in a given subset R ⊆ A at least once)" of
weight at most the bound, and reduce directed HAMILTONIAN CIRCUIT to it.

The vertices are `0, ..., n - 1`. An arc is a triple `(u, v, l)` (from `u` to `v`, length `l`);
there are no loops and no two arcs with the same tail and head. The required arcs `A'` are
given by their pairs `(u, v)`, each the pair of some arc. As in the undirected parent, a circuit
is a closed walk that may repeat vertices and arcs, and its length counts every traversal: it is
a list of arc indices, each arc ending where the next one starts and the last ending where the
first starts, and arcs are traversed only from tail to head. When `A'` is empty, the empty walk
qualifies, as the trivial walk at a vertex does in the parent; `WellFormed` asks for a vertex
(`0 < n`), so a graph without vertices, where the parent finds no walk, is not a yes-instance.
Membership in NP: replacing every stretch of a qualifying walk between consecutive first
traversals of required arcs, and the closing stretch, by a shortest path keeps it qualifying, so
some qualifying walk has at most `|A'| (|A| + 1)` steps; it is a certificate of polynomial
size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n`, the arcs `(u, v, l)` (from `u` to `v`, length `l`), the
required arcs `A'` as pairs `(u, v)`, and the bound `B`. -/
abbrev DirectedRuralPostmanInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- The arc with index `j` (a default triple for an index out of range). -/
def arc (i : DirectedRuralPostmanInstance) (j : ℕ) : ℕ × ℕ × ℕ :=
  i.2.1.getD j (0, 0, 0)

/-- Well-formedness of an instance: the graph has a vertex (`0 < n`), every arc joins two
distinct vertices below `n`, no two arcs have the same tail and head, every required pair is the
pair of an arc, and `0 < B`. -/
def WellFormed (i : DirectedRuralPostmanInstance) : Prop :=
  0 < i.1 ∧ (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2.1 < i.1 ∧ a.1 ≠ a.2.1) ∧
    (i.2.1.map fun a => (a.1, a.2.1)).Nodup ∧
    (∀ r ∈ i.2.2.1, r ∈ i.2.1.map fun a => (a.1, a.2.1)) ∧ 0 < i.2.2.2

/-- Some closed directed walk, given as a list of arc indices, traverses every required arc and
has total length at most `B` (each traversal of an arc counts its length). -/
def DirectedRuralPostmanFeasible (i : DirectedRuralPostmanInstance) : Prop :=
  ∃ walk : List ℕ, (∀ j ∈ walk, j < i.2.1.length) ∧
    walk.IsChain (fun j k => (arc i j).2.1 = (arc i k).1) ∧
    walk.getLast?.map (fun j => (arc i j).2.1) = walk.head?.map (fun j => (arc i j).1) ∧
    (∀ r ∈ i.2.2.1, ∃ j ∈ walk, ((arc i j).1, (arc i j).2.1) = r) ∧
    (walk.map fun j => (arc i j).2.2).sum ≤ i.2.2.2

open Classical in
/-- DIRECTED RURAL POSTMAN as a decision problem over bitstrings. -/
noncomputable def directedRuralPostmanDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DirectedRuralPostmanInstance) x with
  | some i => decide (WellFormed i ∧ DirectedRuralPostmanFeasible i)
  | none => false

/-- **DIRECTED RURAL POSTMAN is NP-complete.** Source: Garey and Johnson (1979), [ND27];
Lenstra and Rinnooy Kan (1976). -/
public theorem_wanted directedRuralPostman_npComplete :
    directedRuralPostmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L directedRuralPostmanDec

end MetaMathlibExt.Complexity.NPComplete.DirectedRuralPostman
