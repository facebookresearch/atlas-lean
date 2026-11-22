/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT on co-bipartite graphs is NP-complete

Source:
H. L. Bodlaender and K. Jansen, "On the complexity of the maximum cut problem", Nordic Journal
of Computing 7 (2000), 14-31 (STACS 1994, LNCS 775, 769-780, doi:10.1007/3-540-57785-8_189);
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y (records
"Max Cut remains NP-hard even for ... co-bipartite graphs [Bodlaender and Jansen]");
ISGCI, class "co-bipartite" (gc_486), problem Maximum cut, NP-complete.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MaxCutWanted
public import Mathlib.Combinatorics.SimpleGraph.Bipartite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCoBipartite

open MetaMathlibExt.Complexity.NPComplete.MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT on co-bipartite graphs is NP-complete

INSTANCE: a co-bipartite graph `G = (V, E)` (the complement of a bipartite graph) and a positive
integer `K`.
QUESTION: is there a partition of `V` into sets `A`, `B` such that at least `K` edges have one
endpoint in `A` and the other in `B`?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to co-bipartite graphs,
which Bodlaender and Jansen prove NP-complete. The instance, the simple-edge-list conditions and
the question are those of MAXIMUM CUT (`WantedExt.Complexity.NPComplete.MaxCutWanted`, whose
question counts edges), reused as in `SimpleMaxCutDegreeThreeWanted`; the restriction adds to
`WellFormed` that the complement of `Cslib.Complexity.Karp.edgeGraph` is bipartite (Mathlib's
`SimpleGraph.IsBipartite`, as in `TreewidthCoBipartiteWanted`), i.e. the vertices split into two
cliques, and `0 < K`. A co-bipartite graph has a clique on at least `⌈|V| / 2⌉` vertices, so
its edge list has at least `C(⌈|V| / 2⌉, 2)` entries and the binary vertex count does not make
the problem succinct.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: a well-formed MAXIMUM CUT instance (a simple edge list on
the vertices `0, ..., n - 1`) whose graph is co-bipartite (its complement is bipartite), and
`0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧ (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1)ᶜ.IsBipartite ∧ 0 < i.2.2

/-- A partition `A = S`, `B = V - S` with at least `K` edges between the two sets (the MAXIMUM
CUT question). -/
def SimpleMaxCutCoBipartiteFeasible (i : MaxCutInstance) : Prop :=
  MaxCutFeasible i

open Classical in
/-- SIMPLE MAX CUT on co-bipartite graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutCoBipartiteDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ SimpleMaxCutCoBipartiteFeasible i)
  | none => false

/-- **SIMPLE MAX CUT on co-bipartite graphs is NP-complete.** Source: Bodlaender and Jansen
(2000); ISGCI (gc_486). -/
public theorem_wanted simpleMaxCutCoBipartite_npComplete :
    simpleMaxCutCoBipartiteDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutCoBipartiteDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutCoBipartite
