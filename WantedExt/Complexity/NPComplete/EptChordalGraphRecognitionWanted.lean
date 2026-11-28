/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECOGNITION OF EPT ∩ CHORDAL GRAPHS is NP-complete

Source:
M. C. Golumbic and R. E. Jamison, "Edge and vertex intersection of paths in a tree", Discrete
Mathematics 55 (1985), 151-159, doi:10.1016/0012-365X(85)90043-3, Theorem 3 ("It is an
NP-complete problem to decide whether a path graph is an EPT graph");
M. M. Sysło, "Triangulated edge intersection graphs of paths in a tree", Discrete Mathematics 55
(1985), 217-220, doi:10.1016/0012-365X(85)90050-0 (the reference ISGCI gives for this
recognition problem, class `gc_127`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.EptChordalGraphRecognitionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.EptChordalGraphRecognition

open EptGraphRecognition
  (EptGraphRecognitionInstance Graph WellFormed EptGraphRecognitionFeasible)

/-!
# RECOGNITION OF EPT ∩ CHORDAL GRAPHS is NP-complete

INSTANCE: a graph `G = (V, E)`. QUESTION: is `G` in the class `EPT ∩ chordal` (ISGCI `gc_127`),
i.e. is `G` chordal (every cycle of length at least `4` has a chord) and an EPT graph (the edge
intersection graph of a family of paths in a tree)?

Golumbic and Jamison (1985), Theorem 3, prove that deciding whether a path graph (a vertex
intersection graph of paths in a tree) is an EPT graph is NP-complete. Path graphs are chordal,
being intersection graphs of subtrees of a tree, so their reduction (from graph 3-colorability)
outputs chordal graphs, and on those the question here is the EPT question. ISGCI records this
recognition problem as NP-complete with the reference Sysło (1985).

The instance (vertex count and edge list on `Fin n`), the graph, the well-formedness (a simple
edge list) and the EPT condition are those of `EptGraphRecognitionWanted`; chordality is added to
the question. Chordality is stated as in
`PathwidthChordalGraphsWanted`: no cycle graph `Cₖ` with `k ≥ 4` is an induced subgraph
(Mathlib's `SimpleGraph.cycleGraph` and `SimpleGraph.IsIndContained`; a cycle has a chord exactly
when its vertices do not induce a cycle graph). The EPT condition `EptGraphRecognitionFeasible`
asks for a host tree on `Fin m` for some `m`, one path of the tree per vertex, and two distinct
vertices adjacent exactly when their paths share an edge.

Membership in NP: chordality is decidable in polynomial time, and EPT graph recognition is in NP
(Golumbic and Jamison, Theorem 3 and Corollary 1). Isolated vertices are chordal and EPT (a new
pendant edge of the tree each), so they do not change the answer and the binary vertex count does
not make the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **RECOGNITION OF EPT ∩ CHORDAL GRAPHS is NP-complete.** Source: Golumbic and Jamison (1985),
Theorem 3; Sysło (1985). -/
public theorem_wanted eptChordalGraphRecognition_npComplete :
    eptChordalGraphRecognitionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L eptChordalGraphRecognitionDec

end MetaMathlibExt.Complexity.NPComplete.EptChordalGraphRecognition
