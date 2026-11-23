/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on P-free (banner-free) graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 195, problem [GT20] INDEPENDENT SET,
comment: remains NP-complete "for graphs containing no triangles [Poljak, 1974]";
S. Poljak, "A note on stable sets and colorings of graphs", Commentationes
Mathematicae Universitatis Carolinae 15 (1974), 307-309;
V. E. Alekseev, "On the local restrictions effect on the complexity of finding the graph
independence number", in *Combinatorial-algebraic methods in applied mathematics*, Gorkiy
University Press (1983), 3-13 (in Russian; not available to us, cited as recorded by ISGCI);
T. Abrishami, M. Chudnovsky, C. Dibek and P. Rzążewski, "Polynomial-time algorithm for Maximum
Independent Set in bounded-degree graphs with no long induced claws", arXiv:2107.05434 (2021),
Introduction: "Already in the early 1980s Alekseev observed that if H is connected, then the
Max Weight Independent Set problem (MWIS) remains NP-hard in H-free graphs, unless H is a path
or a subdivided claw";
ISGCI, *Information System on Graph Classes and their Inclusions*, class `gc_814` (P-free),
problem Independent set: NP-complete (Alekseev 1983; V. E. Alekseev and V. V. Lozin,
"Augmenting graphs for independent sets", Discrete Applied Mathematics 145(1) (2004), 3-10,
doi:10.1016/j.dam.2003.09.003); small graph `P` (= 4-pan = banner) as defined at
https://www.graphclasses.org/smallgraphs.html.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetBannerFree

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-!
# INDEPENDENT SET on P-free (banner-free) graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no induced subgraph isomorphic to ISGCI's small graph `P`
(the banner, or 4-pan: a cycle on four vertices with one pendant vertex attached to a vertex of
the cycle), and a positive integer `K ≤ |V|`.
QUESTION: does `G` contain an independent set of size `K` or more, that is, a subset `V' ⊆ V`
with `|V'| ≥ K` such that no two vertices of `V'` are joined by an edge in `E`?

This is INDEPENDENT SET ([GT20]) on the ISGCI class `gc_814`. ISGCI's small graph `P`
(graph6 `DrG`) has vertices `0, …, 4` and edges `01, 02, 13, 23, 24`: the cycle `0, 1, 3, 2`
with the pendant vertex `4` at `2`. The instance type (vertex count `n`, edge list, bound `K`),
the graph (`Cslib.Complexity.Karp.edgeGraph` on `Fin n`) and the question (a `Finset` of at
least `K` vertices whose coercion is Mathlib's `SimpleGraph.IsIndepSet`) are those of the
edge-list INDEPENDENT SET statement on `main`,
`WantedExt.Complexity.NPComplete.TriangleFreeIndependentSetWanted`, whose triangle-free
restriction lives only in its `WellFormed`, which this module does not use. `WellFormed` here
asks for a simple edge list on `Fin n`, `0 < K ≤ |V|` ([GT20]'s instance class), and the class:
"`P`-free" means no induced subgraph isomorphic to `P`, Mathlib's `SimpleGraph.IsIndContained`
(an induced embedding), as in `DominatingSetGirthNineHX85K14FreeWanted`.

Poljak's construction gives the reduction from INDEPENDENT SET: replacing every edge of a graph
with `m` edges by a path of three edges raises the independence number by exactly `m`, and
multiplies every cycle length by `3`, so the new graph has no cycle of length less than `9`.
`P` contains a cycle of length `4`, so the new graph has no induced (indeed no) copy of `P`.
This is the case "`H` contains a cycle" of Alekseev's classification, which ISGCI cites for
this class.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- ISGCI's small graph `P` (the banner, graph6 `DrG`): the cycle `0, 1, 3, 2` with the pendant
vertex `4` attached at `2`. -/
def graphP : SimpleGraph (Fin 5) :=
  Cslib.Complexity.Karp.edgeGraph 5 [(0, 1), (0, 2), (1, 3), (2, 3), (2, 4)]

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) with no induced `P`,
and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ¬ graphP.IsIndContained (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on `P`-free graphs as a decision problem over bitstrings. -/
noncomputable def independentSetBannerFreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

/-- **INDEPENDENT SET on `P`-free (banner-free) graphs is NP-complete.** Source: Garey and
Johnson (1979), [GT20], comment; Poljak (1974); Alekseev (1983); ISGCI (`gc_814`). -/
public theorem_wanted independentSetBannerFree_npComplete :
    independentSetBannerFreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L independentSetBannerFreeDec

end MetaMathlibExt.Complexity.NPComplete.IndependentSetBannerFree
