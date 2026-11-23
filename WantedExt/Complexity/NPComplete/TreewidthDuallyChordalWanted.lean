/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF DUALLY CHORDAL GRAPHS is NP-complete

Source:
A. Brandstädt, V. D. Chepoi and F. F. Dragan, "The algorithmic use of hypertree structure and
maximum neighbourhood orderings", Discrete Applied Mathematics 82 (1998), 43-77,
doi:10.1016/S0166-218X(97)00125-X (Section 9, Theorem 9.2: "The problem of computing the
treewidth of a dually chordal graph is NP-complete.");
S. Arnborg, D. G. Corneil and A. Proskurowski, "Complexity of finding embeddings in a k-tree",
SIAM Journal on Algebraic and Discrete Methods 8 (1987), 277-284, doi:10.1137/0608024
(NP-completeness of TREEWIDTH on all graphs, the source problem of the reduction).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.IndependentSetDuallyChordalWanted
public import WantedExt.Complexity.NPComplete.TreewidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthDuallyChordal

open MetaMathlibExt.Complexity.NPComplete.Treewidth
open MetaMathlibExt.Complexity.NPComplete.IndependentSetDuallyChordal (DuallyChordal)

/-!
# TREEWIDTH OF DUALLY CHORDAL GRAPHS is NP-complete

INSTANCE: a dually chordal graph `G = (V, E)` and an integer `K`.
QUESTION: is the treewidth of `G` at most `K`?

This is TREEWIDTH (`WantedExt.Complexity.NPComplete.TreewidthWanted`) restricted to dually
chordal graphs: the instance type, graph, well-formedness and question are those of that
module, and the restriction is added to well-formedness. The class is ISGCI's `gc_185`, with the
predicate `IndependentSetDuallyChordal.DuallyChordal` from
`WantedExt.Complexity.NPComplete.IndependentSetDuallyChordalWanted` (the existence of a maximum
neighbourhood ordering, ISGCI's definition: "A vertex `u` in `N[v]` is a maximum neighbour of
`v` if for all `w` in `N[v]`: `N[w] ⊆ N[u]`. A vertex ordering `v_1 … v_n` is a maximum
neighbourhood ordering if for each `i < n` `v_i` has a maximum neighbour in `G_i`. A graph is
dually chordal if it has a maximum neighbourhood ordering."), reused unchanged.

Brandstädt, Chepoi and Dragan prove hardness by adding to an arbitrary graph `G` a new vertex
adjacent to all vertices of `G`; the result `H` is dually chordal (with the new vertex last in
the ordering, it is a maximum neighbour of every vertex) and connected. A tree decomposition of
`G` with the new vertex added to every bag is one of `H`, and restricting a tree decomposition
of `H` to the nodes whose bags contain the new vertex, and removing that vertex, gives one of
`G`; so the treewidth of `H` is that of `G` plus one, and `(G, K) ↦ (H, K + 1)` reduces
TREEWIDTH to this problem. ISGCI records TREEWIDTH as NP-complete on this class, citing
Brandstädt, Chepoi and Dragan (1998).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed TREEWIDTH instance (simple edge list) whose
graph is dually chordal (has a maximum neighbourhood ordering). -/
def DuallyChordalWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ DuallyChordal (Graph i)

open Classical in
/-- TREEWIDTH OF DUALLY CHORDAL GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthDuallyChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (DuallyChordalWellFormed i ∧ TreewidthFeasible i)
  | none => false

/-- **TREEWIDTH OF DUALLY CHORDAL GRAPHS is NP-complete.** Source: Brandstädt, Chepoi and
Dragan (1998), Theorem 9.2; Arnborg, Corneil and Proskurowski (1987). -/
public theorem_wanted treewidthDuallyChordal_npComplete :
    treewidthDuallyChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthDuallyChordalDec

end MetaMathlibExt.Complexity.NPComplete.TreewidthDuallyChordal
