/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE on dually chordal graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE (the parent problem);
A. Brandstädt, V. D. Chepoi and F. F. Dragan, "The algorithmic use of hypertree structure and
maximum neighbourhood orderings", Discrete Applied Mathematics 82(1-3) (1998), 43-77,
doi:10.1016/s0166-218x(97)00125-x (cited by Wikipedia, "Dually chordal graph", for this
result);
A. Leitert, "3-Colourability of dually chordal graphs in linear time", arXiv:1206.0233 (2012),
Section 3 (adding a universal vertex makes any graph dually chordal, which reduces several
NP-complete problems to dually chordal graphs; the idea is credited to Brandstädt et al.);
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_185` (dually
chordal), problem Clique: NP-complete (note `ref_1504`: the universal-vertex reduction,
communicated by V. Santos).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.CliqueClawFreeWanted
public import WantedExt.Complexity.NPComplete.IndependentSetDuallyChordalWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueDuallyChordal

open CliqueClawFree (CliqueClawFreeInstance Graph CliqueClawFreeFeasible)
open IndependentSetDuallyChordal (DuallyChordal)

/-!
# CLIQUE on dually chordal graphs is NP-complete

INSTANCE: a dually chordal graph `G = (V, E)`, and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain a clique of size `K` or more, that is, a subset `V' ⊆ V` with
`|V'| ≥ K` such that every two vertices of `V'` are joined by an edge in `E`?

This is CLIQUE ([GT19]) on the ISGCI class `gc_185`. Dually chordal graphs are those with a
maximum neighbourhood ordering; the predicate is `IndependentSetDuallyChordal.DuallyChordal`,
which states ISGCI's definition and is reused here unchanged.

The instance type (vertex count `n`, edge list, bound `K`), the graph
(`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at least `K`
vertices whose coercion is Mathlib's `SimpleGraph.IsClique`) are those of the edge-list CLIQUE
statement on `main`, `WantedExt.Complexity.NPComplete.CliqueClawFreeWanted`, whose claw-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT19]'s instance class), and the class.

Reduction from CLIQUE: adding a vertex adjacent to all others yields a dually chordal graph (any
ordering that puts the new vertex last is a maximum neighbourhood ordering, the new vertex being
a maximum neighbour of every vertex), and it raises the size of a largest clique by exactly one.
Wikipedia ("Dually chordal graph", Complexity of problems) records maximum clique as
NP-complete on dually chordal graphs, citing Brandstädt, Chepoi and Dragan (1998); ISGCI records
the same, with the universal-vertex reduction.

Membership in NP, with `n` written in binary (so most vertices may be isolated): an isolated
vertex is its own maximum neighbour and lies in no other closed neighbourhood, so it can sit
anywhere in a maximum neighbourhood ordering, and the graph is dually chordal exactly when the
subgraph induced by the at most `2|E|` endpoints of edges is; dually chordal graphs are
recognizable in linear time (Brandstädt, Chepoi and Dragan 1998). For `K = 1` the answer is yes
(`n ≥ K`); for `K ≥ 2` a clique of size `K` consists of endpoints of edges, and such a clique is
a certificate of polynomial size.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) that is dually
chordal, and `0 < K ≤ |V|`. -/
def WellFormed (i : CliqueClawFreeInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    DuallyChordal (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- CLIQUE on dually chordal graphs as a decision problem over bitstrings. -/
noncomputable def cliqueDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueClawFreeInstance) x with
  | some i => decide (WellFormed i ∧ CliqueClawFreeFeasible i)
  | none => false

/-- **CLIQUE on dually chordal graphs is NP-complete.** Source: Brandstädt, Chepoi and Dragan
(1998); Leitert (2012); ISGCI (`gc_185`); Garey and Johnson (1979), [GT19] (parent problem). -/
public theorem_wanted cliqueDuallyChordal_npComplete :
    cliqueDuallyChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cliqueDuallyChordalDec

end MetaMathlibExt.Complexity.NPComplete.CliqueDuallyChordal
