/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on P-free (banner-free) graphs: definitions

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

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetBannerFree

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.IndependentSetBannerFree
