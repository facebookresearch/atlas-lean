/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SIMPLE MAX CUT for rooted directed path graphs is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (SIMPLE MAX CUT
for directed path graphs, open there);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for
the 21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (entry N [1]);
R. Adhikary, K. Bose, S. Mukherjee and B. Roy, "Complexity of maximum cut on interval graphs",
Discrete & Computational Geometry 70 (2023), 307-322, doi:10.1007/s00454-022-00472-y, Theorem 1;
F. Gavril, "A recognition algorithm for the intersection graphs of directed paths in directed
trees", Discrete Mathematics 13 (1975), 237-249, doi:10.1016/0012-365X(75)90021-7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RootedDirectedPathGraphCompletionWanted
public import WantedExt.Complexity.NPComplete.MaxCutWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutRootedDirectedPathGraphs

open MaxCut (MaxCutInstance MaxCutFeasible)

/-!
# SIMPLE MAX CUT for rooted directed path graphs is NP-complete

INSTANCE: a directed path graph `G = (V, E)` in the sense of Johnson's column: an undirected
path graph with a representation in which, for some root vertex of the tree, all paths are
subpaths of paths from the root to a leaf (a rooted directed path graph); and a positive
integer `K`.
QUESTION: is there a partition of `V` into two sets with at least `K` edges between them?

This is SIMPLE MAX CUT (MAX CUT with all edge weights one) restricted to Johnson's directed path
graphs, which are the rooted directed path graphs (a proper subclass of the directed path graphs
with arbitrary tree orientation of `HamiltonianCircuitDirectedPathGraphs.IsDirectedPathGraph`),
an entry of his Table 1 that de Figueiredo, de Melo, Sasaki and Silva resolve as
NP-complete by Adhikary, Bose, Mukherjee and Roy: they prove SIMPLE MAX CUT NP-complete on
interval graphs, and every interval graph is a rooted directed path graph (sort the interval
endpoints into a path, rooted at its first point; each interval is a directed subpath).
The instance, the simple-edge-list conditions and the question are those of MAXIMUM CUT
(`MaxCutWanted`, whose question counts edges), reused as in
`SimpleMaxCutUndirectedPathGraphsWanted`; the restriction adds to `WellFormed` that
`Cslib.Complexity.Karp.edgeGraph` is a rooted directed path graph, and `0 < K`.

"Rooted directed path graph" is the repository's predicate
`RootedDirectedPathGraphCompletion.IsRootedDirectedPathGraph`: for some finite tree `T` with
root `r`, each vertex `v` has the vertex set `P v` of a path of `T` whose every step moves away
from `r`, and distinct vertices are adjacent exactly when their paths share a vertex of `T`.

Membership in NP: a cut is a polynomial certificate, and rooted directed path graphs are
recognized in polynomial time (Gavril's algorithm is for intersection graphs of directed paths
in rooted directed trees; his clique-tree characterization of this class is Theorem 2.1 of
Panda and Pradhan, arXiv:0809.2443). Vertices outside the edge list are isolated; they change
neither the answer nor membership in the class (an isolated vertex takes the one-vertex path of
a new leaf below the root), so the check runs on the non-isolated vertices and the binary vertex
count does not make the problem succinct.

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
`Fin n`) whose graph is a rooted directed path graph, and `0 < K`. -/
def WellFormed (i : MaxCutInstance) : Prop :=
  MaxCut.WellFormed i ∧
    RootedDirectedPathGraphCompletion.IsRootedDirectedPathGraph
      (Cslib.Complexity.Karp.edgeGraph i.1 i.2.1) ∧
    0 < i.2.2

open Classical in
/-- SIMPLE MAX CUT for rooted directed path graphs as a decision problem over bitstrings. -/
noncomputable def simpleMaxCutRootedDirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MaxCutInstance) x with
  | some i => decide (WellFormed i ∧ MaxCutFeasible i)
  | none => false

/-- **SIMPLE MAX CUT for rooted directed path graphs is NP-complete.**
Source: Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva (2022);
Adhikary, Bose, Mukherjee and Roy (2023). -/
public theorem_wanted simpleMaxCutRootedDirectedPathGraphs_npComplete :
    simpleMaxCutRootedDirectedPathGraphsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L simpleMaxCutRootedDirectedPathGraphsDec

end MetaMathlibExt.Complexity.NPComplete.SimpleMaxCutRootedDirectedPathGraphs
