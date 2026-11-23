/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIAMETERS DECOMPOSITION is NP-complete

Source:
J. Plesník, "Complexity of decomposing graphs into factors with given diameters or radii",
Mathematica Slovaca 32 (1982), 379-388, Theorem 1 and Section 5 (concluding remarks);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
MINIMUM DIAMETERS DECOMPOSITION (citing Plesník).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted
public import Mathlib.Combinatorics.SimpleGraph.Diam

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DiametersDecomposition

open GraphColoring (GraphColoringInstance Graph)

/-!
# DIAMETERS DECOMPOSITION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K`.
QUESTION: is there a decomposition of `G` into two factors `F₁` and `F₂` (edge-disjoint spanning
subgraphs whose union is `G`) with equal diameters, such that the diameter of `F₁` is at most
`K`?

This is the decision version, with bound `K`, of Crescenzi and Kann's MINIMUM DIAMETERS
DECOMPOSITION (measure: the diameter of `F₁`), which is Plesník's optimization problem "decompose
`G` into two factors `F₁, F₂` with minimum equal diameters" (Section 5). Plesník defines a factor
as an edge-disjoint spanning subgraph and the diameter as `d(G) = max {d_G(x, y) | x, y ∈ V(G)}`.
His Theorem 1 proves the diameter decomposition problem NP-hard already for two factors with
diameter bound 2, Section 5 observes that his results also hold for the strict version (factors of
diameter exactly the given bounds) and that the decision versions are in NP, hence NP-complete.
For a graph with at least two vertices, two edge-disjoint factors of equal diameter at most 2
both have diameter exactly 2 (a factor of diameter 1 is complete, which leaves the other factor
without edges), so the case `K = 2` of this problem is Plesník's strict problem with two factors
of diameter 2.

The instance type and the graph are GRAPH COLORING's (`GraphColoringWanted`): a vertex count `n`,
an edge list describing a simple graph on `Fin n`, and the bound `K`. A factor is a
`SimpleGraph (Fin n)`, a spanning subgraph by construction; `F₁` and `F₂` decompose `G` when
`F₁ ⊔ F₂ = G` and `F₁`, `F₂` are disjoint (no common edge). The diameter is Mathlib's
`SimpleGraph.ediam`, the supremum of the distances `SimpleGraph.edist`, which is `⊤` for a
disconnected graph, so both factors of a solution are connected. Plesník's maximum over vertex
pairs needs a vertex, and Mathlib's `ediam` of the graph on `Fin 0` is `0`, so `WellFormed` asks
for `n ≥ 1` (as in `ThreeColorabilityDiameterThreeWanted`). `K` is a positive integer as in
Crescenzi and Kann.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Well-formedness of an instance: well-formed for GRAPH COLORING (the edge list describes a
simple graph on `Fin n`), `n ≥ 1`, and `0 < K`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.1 ∧ 0 < i.2.2

/-- The graph decomposes into two edge-disjoint factors `F₁`, `F₂` with equal diameters, the
diameter of `F₁` being at most `K`. -/
def DiametersDecompositionFeasible (i : GraphColoringInstance) : Prop :=
  ∃ F₁ F₂ : SimpleGraph (Fin i.1), F₁ ⊔ F₂ = Graph i ∧ Disjoint F₁ F₂ ∧
    F₁.ediam = F₂.ediam ∧ F₁.ediam ≤ (i.2.2 : ℕ∞)

open Classical in
/-- DIAMETERS DECOMPOSITION as a decision problem over bitstrings. -/
noncomputable def diametersDecompositionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ DiametersDecompositionFeasible i)
  | none => false

/-- **DIAMETERS DECOMPOSITION is NP-complete.** Source: Plesník (1982), Theorem 1 and Section 5;
Crescenzi and Kann, MINIMUM DIAMETERS DECOMPOSITION. -/
public theorem_wanted diametersDecomposition_npComplete :
    diametersDecompositionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L diametersDecompositionDec

end MetaMathlibExt.Complexity.NPComplete.DiametersDecomposition
