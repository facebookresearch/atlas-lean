/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HAMILTONIAN CIRCUIT on line graphs of bipartite graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT37] HAMILTONIAN CIRCUIT
(comment (1): NP-complete for cubic graphs, from M. R. Garey, D. S. Johnson and R. E. Tarjan,
"The planar Hamiltonian circuit problem is NP-complete", SIAM Journal on Computing 5 (1976),
704-714, doi:10.1137/0205049);
T.-H. Lai and S.-S. Wei, "The edge Hamiltonian path problem is NP-complete for bipartite
graphs", Information Processing Letters 46 (1993), 21-26, doi:10.1016/0020-0190(93)90191-B.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianCircuit

open MetaMathlibExt.Complexity.NPComplete.HamiltonianCycleUndirected

/-!
# HAMILTONIAN CIRCUIT on line graphs of bipartite graphs is NP-complete

INSTANCE: a graph `G = (V, E)` isomorphic to the line graph `L(H)` of some finite bipartite
graph `H` (the vertices of `L(H)` are the edges of `H`, two being adjacent when they share an
endpoint).
QUESTION: does `G` contain a Hamiltonian circuit?

The ISGCI database (class "line graphs of bipartite graphs", gc_251) lists HAMILTONIAN CYCLE as
NP-complete on this class, citing Lai and Wei (1993), whose title result is the path version:
EDGE HAMILTONIAN PATH on bipartite graphs, that is, Hamiltonian path in line graphs of
bipartite graphs. The circuit version also follows from the cubic case of [GT37]: for a cubic
graph `K`, let `S(K)` be its 1-subdivision (every edge `uv` replaced by a path `u - x - v`), a
bipartite graph. In `L(S(K))` every vertex `v` of `K` becomes a
triangle `T_v` (the three edges of `S(K)` at `v`), and every edge `uv` of `K` joins one vertex of
`T_u` to one vertex of `T_v`; each vertex of `L(S(K))` has exactly one such external edge.
A Hamiltonian circuit of `L(S(K))` uses an even number of the three external edges at each
`T_v`, and not zero (it is not `T_v` alone), so exactly two; the edges of `K` it uses form a
connected 2-regular spanning subgraph, a Hamiltonian circuit of `K`. Conversely a Hamiltonian
circuit of `K` lifts to one of `L(S(K))`. Membership in NP holds because line graphs are
recognized and a root found in linear time (P. G. H. Lehot, Journal of the ACM 21 (1974),
569-575), and the root of a connected line graph other than the triangle is unique up to
isomorphism (H. Whitney, 1932), the triangle being `L(K_{1,3})` with a bipartite root.

The instance, its well-formedness and the question are those of
`CSLibExt.Complexity.NPComplete.HamiltonianCycleUndirectedDefs` ([GT37]: a simple graph on
`Fin n`, `n > 0`, given by an edge list; a Hamiltonian circuit needs at least three vertices).
The restriction adds that the graph is isomorphic to Mathlib's `SimpleGraph.lineGraph` of a
graph `H` on some `Fin k` with `H.IsBipartite` (Mathlib's `Colorable 2`); this is
`MetaMathlibExt.SimpleGraph.IsLineGraph` with the root required to be bipartite.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` is the line graph of a bipartite graph: isomorphic to `L(H)` for a bipartite graph `H`
on some `Fin k`. -/
def IsBipartiteLineGraph {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (H : SimpleGraph (Fin k)), H.IsBipartite ∧ Nonempty (G ≃g H.lineGraph)

/-- Well-formedness of an instance: a well-formed HAMILTONIAN CIRCUIT instance whose graph is
the line graph of a bipartite graph. -/
def WellFormed (i : HamiltonianCycleUndirectedInstance) : Prop :=
  HamiltonianCycleUndirected.WellFormed i ∧ IsBipartiteLineGraph (Graph i)

open Classical in
/-- HAMILTONIAN CIRCUIT on line graphs of bipartite graphs as a decision problem over
bitstrings. -/
noncomputable def bipartiteLineGraphHamiltonianCircuitDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HamiltonianCycleUndirectedInstance) x with
  | some i => decide (WellFormed i ∧ HamiltonianCycleUndirectedFeasible i)
  | none => false

/-- **HAMILTONIAN CIRCUIT on line graphs of bipartite graphs is NP-complete.** Source: Garey
and Johnson (1979), [GT37]; Lai and Wei (1993). -/
public theorem_wanted bipartiteLineGraphHamiltonianCircuit_npComplete :
    bipartiteLineGraphHamiltonianCircuitDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bipartiteLineGraphHamiltonianCircuitDec

end MetaMathlibExt.Complexity.NPComplete.BipartiteLineGraphHamiltonianCircuit
