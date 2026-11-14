/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CHROMATIC INDEX of k-regular graphs (fixed k ≥ 3) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), open problem [OPEN5] CHROMATIC INDEX;
I. Holyer, "The NP-completeness of edge-coloring", SIAM Journal on Computing 10(4) (1981),
718-720, doi:10.1137/0210055 (`k = 3`);
D. Leven and Z. Galil, "NP completeness of finding the chromatic index of regular graphs",
Journal of Algorithms 4(1) (1983), 35-44, doi:10.1016/0196-6774(83)90032-9 (`k ≥ 4`);
restated as Theorem 2 of E. Galby, P. T. Lima, D. Paulusma and B. Ries, "Classifying
k-Edge Colouring for H-free graphs", Information Processing Letters 146 (2019), 39-43,
doi:10.1016/j.ipl.2019.02.006 (arXiv:1810.04379).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegular

/-!
# CHROMATIC INDEX of k-regular graphs (fixed k ≥ 3) is NP-complete

Fix an integer `k ≥ 3`. An instance is a `k`-regular graph `G = (V, E)`: a finite simple
graph in which every vertex has degree exactly `k`. The question is whether the edges of `G`
can be colored with `k` colors so that edges sharing an endpoint get different colors, i.e.
whether the chromatic index of `G` is `k` (it is at least `k` when `G` has a vertex, and at
most `k + 1` by Vizing's theorem). This is `k`-EDGE COLOURING restricted to `k`-regular graphs:
Holyer (1981) proved it NP-complete for `k = 3`, and Leven and Galil (1983) for every `k ≥ 4`;
Galby, Lima, Paulusma and Ries (2019, Theorem 2) state both together: "For `k ≥ 3`,
`k`-Edge Colouring is NP-complete even for `k`-regular graphs." The case `k = 3` is
`MetaMathlibExt.Complexity.NPComplete.CubicChromaticIndex`.

`k` is fixed, not part of the instance: the decision problem is `chromaticIndexRegularDec k`,
and the theorem holds for every `k ≥ 3`. The graph is given by an edge list on `Fin n`. An
edge coloring is a vertex coloring of the line graph `SimpleGraph.lineGraph`, whose vertices
are the edges of `G`, two being adjacent when they are distinct and share an endpoint.
`k`-regular is Mathlib's `SimpleGraph.IsRegularOfDegree k`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, …, n - 1`) and edge list. -/
abbrev ChromaticIndexRegularInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : ChromaticIndexRegularInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

open Classical in
/-- Well-formedness of an instance for the fixed degree `k`: the edge list describes a simple
graph (no duplicate edges in either orientation, no self-loops, endpoints in range), and the
graph is `k`-regular: every vertex has degree exactly `k`. -/
def WellFormed (k : ℕ) (i : ChromaticIndexRegularInstance) : Prop :=
  (i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2) ∧
    (Graph i).IsRegularOfDegree k

/-- The edges can be colored with `k` colors, edges sharing an endpoint getting different
colors: the line graph is `k`-colorable (chromatic index at most `k`). -/
def ChromaticIndexRegularFeasible (k : ℕ) (i : ChromaticIndexRegularInstance) : Prop :=
  (Graph i).lineGraph.Colorable k

open Classical in
/-- CHROMATIC INDEX of `k`-regular graphs, for the fixed `k`, as a decision problem over
bitstrings. -/
noncomputable def chromaticIndexRegularDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ChromaticIndexRegularInstance) x with
  | some i => decide (WellFormed k i ∧ ChromaticIndexRegularFeasible k i)
  | none => false

/-- **CHROMATIC INDEX of k-regular graphs is NP-complete for every fixed `k ≥ 3`.** Source:
Holyer (1981) for `k = 3`; Leven and Galil (1983) for `k ≥ 4`; Galby, Lima, Paulusma and Ries
(2019), Theorem 2. -/
public theorem_wanted chromaticIndexRegular_npComplete (k : ℕ) (_hk : 3 ≤ k) :
    chromaticIndexRegularDec k ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (chromaticIndexRegularDec k)

end MetaMathlibExt.Complexity.NPComplete.ChromaticIndexRegular
