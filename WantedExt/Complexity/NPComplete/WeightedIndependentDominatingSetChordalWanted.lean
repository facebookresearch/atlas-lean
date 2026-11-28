/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs is NP-complete

Source:
G. J. Chang, "The weighted independent domination problem is NP-complete for chordal graphs",
Discrete Applied Mathematics 143 (2004), 351-352, doi:10.1016/j.dam.2003.05.004;
D. S. Johnson, "The NP-completeness column: an ongoing guide" (tenth edition), Journal of
Algorithms 5 (1984), 147-160, doi:10.1016/0196-6774(84)90045-2 (records the result as a personal
communication of Chang to Farber, and that 0/1 weights are polynomial by Farber's algorithm);
K. Khoshkhah, M. Khosravian Ghadikolaei, J. Monnot and F. Sikora, "Weighted upper edge cover:
complexity and approximability", Journal of Graph Algorithms and Applications 24 (2020),
doi:10.7155/jgaa.00519 (records that Chang's result holds with two positive weight values).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.WeightedIndependentDominatingSetChordalDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.WeightedIndependentDominatingSetChordal

/-!
# WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs is NP-complete

INSTANCE: a chordal graph `G = (V, E)`, that is, a graph in which every cycle of length at least
`4` has a chord; a weight `w(v) ∈ ℤ₀⁺` for each vertex `v ∈ V`; and a bound `B ∈ ℤ₀⁺`.
QUESTION: is there an independent dominating set `D ⊆ V` (no two vertices of `D` adjacent, and
every vertex not in `D` adjacent to a vertex of `D`) with `Σ_{v ∈ D} w(v) ≤ B`?

Chang (2004, abstract) states the weighted independent domination problem (find an independent
dominating set of minimum total weight, for vertex weights that are real numbers) is NP-complete
for chordal graphs, recording a result of about twenty years earlier; Johnson's tenth column
reports it as a communication of Chang to Farber and notes that 0/1 weights are polynomial
(Farber). This module states the decision version with natural-number weights in binary, the bit
model of the weights; Khoshkhah et al. (2020) record that Chang's hardness holds with two
positive weight values, so natural-number weights keep the problem NP-complete. An independent
dominating set is a polynomial certificate, so the problem is in NP.

The graph is given by its vertex count `n` and an edge list, as a `SimpleGraph (Fin n)` through
`Cslib.Complexity.Karp.edgeGraph`, and the weights as a list with one entry per vertex.
Chordality is stated as in `DominatingSetChordalGraphsWanted`: no cycle graph `Cₖ` with `k ≥ 4` is
an induced subgraph (Mathlib's `SimpleGraph.cycleGraph` and `SimpleGraph.IsIndContained`).
Independent domination is MathlibExt's `SimpleGraph.IsIndepDominating`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs is NP-complete.** Source: Chang
(2004); Johnson, NP-completeness column (1984). -/
public theorem_wanted weightedIndependentDominatingSetChordal_npComplete :
    weightedIndependentDominatingSetChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedIndependentDominatingSetChordalDec

end MetaMathlibExt.Complexity.NPComplete.WeightedIndependentDominatingSetChordal
