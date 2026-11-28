/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHINESE POSTMAN FOR MIXED GRAPHS, planar, maximum degree 3, equal lengths, is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND25] CHINESE POSTMAN FOR MIXED
GRAPHS, comment on p. 212 ("Remains NP-complete even if all edge lengths are equal, G is planar,
and the maximum vertex degree is 3");
C. H. Papadimitriou, "On the complexity of edge traversing", Journal of the ACM 23 (1976),
544-554, doi:10.1145/321958.321974.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.ChinesePostmanMixedGraphsWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphsPlanarDegreeThree

open MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphs
  (ChinesePostmanMixedGraphsInstance ChinesePostmanMixedGraphsFeasible)

/-!
# CHINESE POSTMAN FOR MIXED GRAPHS, planar, maximum degree 3, equal lengths, is NP-complete

INSTANCE: a mixed graph `G = (V, A, E)`, where `A` is a set of directed edges and `E` a set of
undirected edges on `V`, a length `l(e) ∈ Z₀⁺` for each `e ∈ A ∪ E`, and a bound `B ∈ Z⁺`, where
all edge lengths are equal, `G` is planar, and the maximum vertex degree is 3.
QUESTION: is there a cycle in `G` that includes each directed and undirected edge at least once,
traversing directed edges only in the specified direction, and that has total length no more
than `B`?

The instance and the question are those of CHINESE POSTMAN FOR MIXED GRAPHS
(`WantedExt.Complexity.NPComplete.ChinesePostmanMixedGraphsWanted`: vertices `0, ..., n - 1`,
directed and undirected edges as triples `(u, v, l)` without loops or repeated edges, `B > 0`;
the question asks for a closed walk through every edge, directed edges forward only, of total
length at most `B`). The restriction adds three conditions on the instance:

* all edge lengths are equal: one `c` is the length of every directed and undirected edge;
* `G` is planar: the simple graph on `Fin n` joining two vertices exactly when some directed or
  undirected edge joins them is `SimpleGraph.IsPlanar` (`MathlibExt`: a crossing-free
  straight-line drawing). A directed and an undirected edge, or two opposite directed edges,
  may join the same pair; such parallel edges can be drawn next to each other, so the mixed
  graph is planar exactly when this simple graph is;
* the maximum vertex degree is 3: every vertex is an endpoint of at most 3 edges of `A ∪ E`,
  each edge counted separately (`mixedDegree`).

Garey and Johnson record the restriction in the entry whose reference is Papadimitriou (1976),
a transformation from 3SAT; the paper's abstract states NP-completeness of the mixed case and
its body was not available. Membership in NP is inherited from CHINESE POSTMAN FOR MIXED GRAPHS;
the added conditions are checked in polynomial time (planarity by Hopcroft and Tarjan, degrees
and lengths directly).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- The underlying simple graph on `Fin n`: two vertices are adjacent exactly when a directed
or an undirected edge joins them. -/
def underlyingGraph (i : ChinesePostmanMixedGraphsInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 ((i.2.1 ++ i.2.2.1).map fun e => (e.1, e.2.1))

/-- The degree of `v` in the mixed graph: the number of directed and undirected edges with `v`
as an endpoint. -/
def mixedDegree (i : ChinesePostmanMixedGraphsInstance) (v : ℕ) : ℕ :=
  (i.2.1 ++ i.2.2.1).countP fun e => e.1 = v ∨ e.2.1 = v

/-- Well-formedness of an instance: a well-formed CHINESE POSTMAN FOR MIXED GRAPHS instance in
which all edge lengths are equal, the underlying graph is planar, and every vertex has degree at
most 3. -/
def WellFormed (i : ChinesePostmanMixedGraphsInstance) : Prop :=
  ChinesePostmanMixedGraphs.WellFormed i ∧ (∃ c, ∀ e ∈ i.2.1 ++ i.2.2.1, e.2.2 = c) ∧
    (underlyingGraph i).IsPlanar ∧ ∀ v, mixedDegree i v ≤ 3

open Classical in
/-- CHINESE POSTMAN FOR MIXED GRAPHS, planar, maximum degree 3, equal lengths, as a decision
problem over bitstrings. -/
noncomputable def chinesePostmanMixedGraphsPlanarDegreeThreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChinesePostmanMixedGraphsInstance) x with
  | some i => decide (WellFormed i ∧ ChinesePostmanMixedGraphsFeasible i)
  | none => false

/-- **CHINESE POSTMAN FOR MIXED GRAPHS is NP-complete for planar graphs of maximum degree 3
with equal edge lengths.** Source: Garey and Johnson (1979), [ND25]; Papadimitriou (1976). -/
public theorem_wanted chinesePostmanMixedGraphsPlanarDegreeThree_npComplete :
    chinesePostmanMixedGraphsPlanarDegreeThreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L chinesePostmanMixedGraphsPlanarDegreeThreeDec

end MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphsPlanarDegreeThree
