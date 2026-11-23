/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET on (C_4, C_5, C_6, C_7, C_8, H, X_85, triangle)-free ∩ K_1,4-free graphs

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 190, problem [GT2] DOMINATING SET,
comment: "Remains NP-complete for planar graphs with maximum vertex degree 3" [Garey and
Johnson, unpublished];
I. E. Zverovich and O. I. Zverovich, "Independent domination in hereditary classes",
Theoretical Computer Science 352 (2006), 215-225, doi:10.1016/j.tcs.2005.10.049;
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_529`
((C_4,C_5,C_6,C_7,C_8,H,X_85,triangle)-free ∩ K_1,4-free), problem Domination: NP-complete
(Zverovich and Zverovich 2006); small graphs `H` and `X_85` as defined at
https://www.graphclasses.org/smallgraphs.html.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetGirthNineHX85K14Free

open MetaMathlibExt.Complexity.NPComplete.DominatingSet

/-!
# DOMINATING SET on (C_4, C_5, C_6, C_7, C_8, H, X_85, triangle)-free ∩ K_1,4-free graphs

INSTANCE: a graph `G = (V, E)` with no induced subgraph isomorphic to a cycle `C_k`,
`3 ≤ k ≤ 8` (`C_3` is the triangle), to the star `K_1,4`, or to either of the trees `H` and
`X_85` below, and a positive integer `K ≤ |V|`.
QUESTION: is there a dominating set of size `K` or less for `G`, i.e. a subset `V' ⊆ V` with
`|V'| ≤ K` such that every vertex of `V - V'` is adjacent to a vertex of `V'`?

This is DOMINATING SET on the ISGCI class `gc_529`. ISGCI's small graphs are
`H` (graph6 `EgSG`): vertices `0, …, 5`, edges `01, 12, 14, 34, 45` (two adjacent vertices of
degree `3`, each with two further neighbours), and
`X_85` (graph6 `FhD?_`): vertices `0, …, 6`, edges `01, 12, 23, 34, 15, 36` (a path on five
vertices with a pendant vertex at its second and at its fourth vertex).
"`X`-free" means no induced subgraph isomorphic to `X`, which is Mathlib's
`SimpleGraph.IsIndContained` (an induced embedding); cycles are Mathlib's `SimpleGraph.cycleGraph`
and the star is `completeBipartiteGraph (Fin 1) (Fin 4)`.

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.DominatingSetWanted` ([GT2]: a simple graph on `Fin n` given by
an edge list, and the bound `K`). The restriction adds `0 < K ≤ |V|` ([GT2]'s instance class)
and the class.

Garey and Johnson record DOMINATING SET as NP-complete on planar graphs of maximum degree `3`.
Replacing every edge by a path with three inner vertices raises the domination number by exactly
the number of edges and yields a graph in this class: every cycle length is multiplied by `4`, so
there is no cycle of length at most `8`; degrees stay at most `3`, so there is no induced
`K_1,4`; and the vertices of degree `3` are original vertices, pairwise at distance at least `4`,
while `H` and `X_85` have two vertices of degree `3` at distance `1` and `2`. ISGCI records the
NP-completeness of this class with the citation Zverovich and Zverovich (2006).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- ISGCI's small graph `H` (graph6 `EgSG`): two adjacent vertices `1` and `4` of degree `3`,
with further neighbours `0, 2` and `3, 5`. -/
def graphH : SimpleGraph (Fin 6) :=
  Cslib.Complexity.Karp.edgeGraph 6 [(0, 1), (1, 2), (1, 4), (3, 4), (4, 5)]

/-- ISGCI's small graph `X_85` (graph6 `FhD?_`): the path `0, 1, 2, 3, 4` with pendant
vertices `5` at `1` and `6` at `3`. -/
def graphX85 : SimpleGraph (Fin 7) :=
  Cslib.Complexity.Karp.edgeGraph 7 [(0, 1), (1, 2), (2, 3), (3, 4), (1, 5), (3, 6)]

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance with `0 < K ≤ |V|`
whose graph has no induced `C_3, …, C_8`, `H`, `X_85` or `K_1,4`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1 ∧
    (∀ k, 3 ≤ k → k ≤ 8 → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)) ∧
    ¬ graphH.IsIndContained (Graph i) ∧ ¬ graphX85.IsIndContained (Graph i) ∧
    ¬ (completeBipartiteGraph (Fin 1) (Fin 4)).IsIndContained (Graph i)

open Classical in
/-- DOMINATING SET on (C_4, C_5, C_6, C_7, C_8, H, X_85, triangle)-free ∩ K_1,4-free graphs, as a
decision problem over bitstrings. -/
noncomputable def dominatingSetGirthNineHX85K14FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET on (C_4, C_5, C_6, C_7, C_8, H, X_85, triangle)-free ∩ K_1,4-free graphs is
NP-complete.** Source: Garey and Johnson (1979), [GT2], comment, with edge subdivision;
Zverovich and Zverovich (2006); ISGCI (`gc_529`). -/
public theorem_wanted dominatingSetGirthNineHX85K14Free_npComplete :
    dominatingSetGirthNineHX85K14FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetGirthNineHX85K14FreeDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetGirthNineHX85K14Free
