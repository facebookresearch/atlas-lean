/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHINESE POSTMAN FOR MIXED GRAPHS, planar, maximum degree 3, equal lengths,: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND25] CHINESE POSTMAN FOR MIXED
GRAPHS, comment on p. 212 ("Remains NP-complete even if all edge lengths are equal, G is planar,
and the maximum vertex degree is 3");
C. H. Papadimitriou, "On the complexity of edge traversing", Journal of the ACM 23 (1976),
544-554, doi:10.1145/321958.321974.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Planarity
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.ChinesePostmanMixedGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphsPlanarDegreeThree

open MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphs
  (ChinesePostmanMixedGraphsInstance ChinesePostmanMixedGraphsFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.ChinesePostmanMixedGraphsPlanarDegreeThree
