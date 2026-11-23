/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# TREEWIDTH OF PERFECT ELIMINATION BIPARTITE GRAPHS is NP-complete

Source:
T. Liu, "Restricted bipartite graphs: comparison and hardness results", in Algorithmic Aspects
in Information and Management (AAIM 2014), Lecture Notes in Computer Science 8546, Springer
(2014), 241-252, doi:10.1007/978-3-319-07956-1_22 (abstract: "We also show the
NP-completeness of treewidth and feedback vertex set for perfect elimination bipartite
graphs.").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartiteWanted
public import WantedExt.Complexity.NPComplete.TreewidthWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.TreewidthPerfectEliminationBipartite

open MetaMathlibExt.Complexity.NPComplete.Treewidth
open MetaMathlibExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartite
  (IsPerfectEliminationBipartite)

/-!
# TREEWIDTH OF PERFECT ELIMINATION BIPARTITE GRAPHS is NP-complete

INSTANCE: a perfect elimination bipartite graph `G = (V, E)` and an integer `K`.
QUESTION: is the treewidth of `G` at most `K`?

This is TREEWIDTH (`WantedExt.Complexity.NPComplete.TreewidthWanted`) restricted to perfect
elimination bipartite graphs: the instance type, graph, well-formedness and question are those
of that module, and the restriction is added to well-formedness. The class is ISGCI's `gc_122`
(Golumbic and Goss): "An edge `(u,v)` in a bipartite graph `B` is called bisimplicial if
`N(u) ∪ N(v)` induces a biclique in `B`. For an edge ordering `e_1 … e_k` let `S_i` be the set
of endpoints of `e_1 … e_i` and `S_0 = ∅`. `e_1 … e_k` is a perfect edge elimination ordering
for a bipartite graph `B = (V,E)` if `B[V ∖ S_k]` has no edges, and each edge `e_i` is
bisimplicial in `B[V ∖ S_{i-1}]`. `B` is perfect elimination bipartite if it admits a perfect
edge elimination ordering." The predicate is
`FeedbackVertexSetPerfectEliminationBipartite.IsPerfectEliminationBipartite` from
`WantedExt.Complexity.NPComplete.FeedbackVertexSetPerfectEliminationBipartiteWanted` (Mathlib's
`SimpleGraph.IsBipartite` plus a perfect edge elimination ordering, given as a list of vertex
pairs), reused unchanged. ISGCI records TREEWIDTH as NP-complete on this class, citing Liu
(2014).

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
graph is perfect elimination bipartite (bipartite, with a perfect edge elimination ordering). -/
def PerfectEliminationBipartiteWellFormed (i : TreewidthInstance) : Prop :=
  WellFormed i ∧ IsPerfectEliminationBipartite (Graph i)

open Classical in
/-- TREEWIDTH OF PERFECT ELIMINATION BIPARTITE GRAPHS as a decision problem over bitstrings. -/
noncomputable def treewidthPerfectEliminationBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TreewidthInstance) x with
  | some i => decide (PerfectEliminationBipartiteWellFormed i ∧ TreewidthFeasible i)
  | none => false

/-- **TREEWIDTH OF PERFECT ELIMINATION BIPARTITE GRAPHS is NP-complete.** Source: Liu (2014). -/
public theorem_wanted treewidthPerfectEliminationBipartite_npComplete :
    treewidthPerfectEliminationBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L treewidthPerfectEliminationBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.TreewidthPerfectEliminationBipartite
