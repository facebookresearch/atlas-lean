/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CUT COVER is NP-complete

Source:
R. Motwani and J. Naor, "On exact and approximate cut covers of graphs", Technical Note
STAN-CS-TN-94-11, Department of Computer Science, Stanford University (1994), Theorem 2.1;
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
MINIMUM CUT COVER (citing Motwani and Naor);
R. Loulou, "Minimal cut cover of a graph with an application to the testing of electronic
boards", Operations Research Letters 12 (1992), 301-305, doi:10.1016/0167-6377(92)90089-L
(introduces the problem).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.GraphColoringWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CutCover

open GraphColoring (GraphColoringInstance Graph WellFormed)

/-!
# CUT COVER is NP-complete

INSTANCE: a graph `G = (V, E)` and a bound `K`.
QUESTION: is there a collection `V₁, ..., Vₘ` of cuts, i.e., a collection of subsets
`Vᵢ ⊆ V` such that, for each edge `(u, v) ∈ E`, a subset `Vᵢ` exists such that either
`u ∈ Vᵢ` and `v ∉ Vᵢ` or `u ∉ Vᵢ` and `v ∈ Vᵢ`, with `m ≤ K`?

This is the decision version, with bound `K`, of Crescenzi and Kann's MINIMUM CUT COVER (measure:
the cardinality `m` of the collection). Motwani and Naor (Theorem 2.1) prove that deciding, for a
graph `G` and an integer `k`, whether the minimum number of cuts covering the edges of `G` is at
most `k` is NP-complete; their cut is a partition of `V` into two sets, which is the same as the
subset `Vᵢ` on one side of it. `K` is a natural number: Motwani and Naor's bound is an integer
`k`, and a negative bound has no solution. `K = 0` is allowed (an edgeless graph is covered by
the empty collection).

The instance type, the graph and the well-formedness are GRAPH COLORING's (`GraphColoringWanted`):
a vertex count `n`, an edge list describing a simple graph on `Fin n`, and the bound `K`. The
collection is a family `V : Fin m → Finset (Fin n)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- Some collection of at most `K` vertex subsets `V₀, ..., Vₘ₋₁` cuts every edge: for each edge
`uv`, some `Vⱼ` contains exactly one of `u` and `v`. -/
def CutCoverFeasible (i : GraphColoringInstance) : Prop :=
  ∃ m ≤ i.2.2, ∃ V : Fin m → Finset (Fin i.1), ∀ u v, (Graph i).Adj u v →
    ∃ j, (u ∈ V j ∧ v ∉ V j) ∨ (u ∉ V j ∧ v ∈ V j)

open Classical in
/-- CUT COVER as a decision problem over bitstrings. -/
noncomputable def cutCoverDec : MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ CutCoverFeasible i)
  | none => false

/-- **CUT COVER is NP-complete.** Source: Motwani and Naor (1994), Theorem 2.1; Crescenzi and
Kann, MINIMUM CUT COVER. -/
public theorem_wanted cutCover_npComplete :
    cutCoverDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L cutCoverDec

end MetaMathlibExt.Complexity.NPComplete.CutCover
