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
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Combinatorics.SimpleGraph.Copy
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

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

/-- An instance: the vertex count `n` (vertices `0, ..., n - 1`), the edge list, the vertex
weights `w(0), ..., w(n - 1)`, and the bound `B`. -/
abbrev WeightedIndependentDominatingSetChordalInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : WeightedIndependentDominatingSetChordalInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), there is one weight
per vertex, and the graph is chordal (no induced cycle of length at least `4`). -/
def WellFormed (i : WeightedIndependentDominatingSetChordalInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.1.length = i.1 ∧
    ∀ k, 4 ≤ k → ¬ (SimpleGraph.cycleGraph k).IsIndContained (Graph i)

/-- Some independent dominating set has total weight at most `B`. -/
def WeightedIndependentDominatingSetChordalFeasible
    (i : WeightedIndependentDominatingSetChordalInstance) : Prop :=
  ∃ D : Finset (Fin i.1), (Graph i).IsIndepDominating (D : Set (Fin i.1)) ∧
    ∑ v ∈ D, i.2.2.1.getD v 0 ≤ i.2.2.2

open Classical in
/-- WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs as a decision problem over
bitstrings. -/
noncomputable def weightedIndependentDominatingSetChordalDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedIndependentDominatingSetChordalInstance) x with
  | some i => decide (WellFormed i ∧ WeightedIndependentDominatingSetChordalFeasible i)
  | none => false

/-- **WEIGHTED INDEPENDENT DOMINATING SET for chordal graphs is NP-complete.** Source: Chang
(2004); Johnson, NP-completeness column (1984). -/
public theorem_wanted weightedIndependentDominatingSetChordal_npComplete :
    weightedIndependentDominatingSetChordalDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedIndependentDominatingSetChordalDec

end MetaMathlibExt.Complexity.NPComplete.WeightedIndependentDominatingSetChordal
