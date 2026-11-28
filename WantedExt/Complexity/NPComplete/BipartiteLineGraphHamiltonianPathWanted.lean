/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN PATH on line graphs of bipartite graphs is NP-complete

Source:
T.-H. Lai and S.-S. Wei, "The edge Hamiltonian path problem is NP-complete for bipartite
graphs", Information Processing Letters 46 (1993), 21-26, doi:10.1016/0020-0190(93)90191-B;
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT39] HAMILTONIAN PATH.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianPathDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianPath

open MetaMathlibExt.Complexity.NPComplete.HamiltonianPathUndirected

/-!
# HAMILTONIAN PATH on line graphs of bipartite graphs is NP-complete

INSTANCE: a graph `G = (V, E)` isomorphic to the line graph `L(H)` of some finite bipartite
graph `H` (the vertices of `L(H)` are the edges of `H`, two being adjacent when they share an
endpoint).
QUESTION: does `G` contain a Hamiltonian path, that is, a simple path through every vertex
(endpoints not specified)?

Lai and Wei (1993, abstract): "The Edge Hamiltonian Path Problem for general graphs was shown by
Bertossi to be NP-complete. [...] We show that the problem remains NP-complete even if
restricted to bipartite graphs." The edge Hamiltonian path problem asks for an ordering of the
edges of `H` in which consecutive edges share an endpoint, which is a Hamiltonian path of `L(H)`
(`WantedExt.Complexity.NPComplete.LineGraphHamiltonianPathWanted` states Bertossi's general
case with the root graph as the instance). The ISGCI database lists HAMILTONIAN PATH as
NP-complete on the class "line graphs of bipartite graphs" (gc_251), citing Lai and Wei. Here
the instance is the line graph itself, as in the ISGCI class: the instance class is the set of
graphs isomorphic to `L(H)` for a bipartite `H`. A root of a line graph is computed in linear
time (P. G. H. Lehot, Journal of the ACM 21 (1974), 569-575), so the two formulations are
polynomially equivalent.

The instance, its well-formedness and the question are those of
`WantedExt.Complexity.NPComplete.HamiltonianPathUndirectedWanted` ([GT39]: a simple graph on
`Fin n`, `n > 0`, given by an edge list; a Hamiltonian path is an ordering of all vertices in
which consecutive vertices are adjacent). The restriction adds that the graph is isomorphic to
Mathlib's `SimpleGraph.lineGraph` of a graph `H` on some `Fin k` with `H.IsBipartite`
(Mathlib's `Colorable 2`); this is `MetaMathlibExt.SimpleGraph.IsLineGraph` with the root
required to be bipartite. Isolated vertices of `H` do not change `L(H)`, so a finite vertex type
`Fin k` loses nothing.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HAMILTONIAN PATH on line graphs of bipartite graphs is NP-complete.** Source: Lai and Wei
(1993); Garey and Johnson (1979), [GT39]. -/
public theorem_wanted bipartiteLineGraphHamiltonianPath_npComplete :
    bipartiteLineGraphHamiltonianPathDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bipartiteLineGraphHamiltonianPathDec

end MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianPath
