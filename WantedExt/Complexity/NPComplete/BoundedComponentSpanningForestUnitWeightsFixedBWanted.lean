/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOUNDED COMPONENT SPANNING FOREST with unit weights and fixed `B ≥ 3` is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [ND10] BOUNDED COMPONENT SPANNING FOREST,
p. 208, comment: "Remains NP-complete even if all weights equal 1 and B is any fixed integer
larger than 2 [Garey and Johnson, ——]" (unpublished);
M. E. Dyer and A. M. Frieze, "On the complexity of partitioning graphs into connected
subgraphs", Discrete Applied Mathematics 10 (1985), 139-153, doi:10.1016/0166-218X(85)90008-3,
Theorem 2.1(a).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.BoundedComponentSpanningForestWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForestUnitWeightsFixedB

open MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForest
  (BoundedComponentSpanningForestInstance BoundedComponentSpanningForestFeasible)

/-!
# BOUNDED COMPONENT SPANNING FOREST with unit weights and fixed `B ≥ 3` is NP-complete

For a fixed integer `B ≥ 3`: INSTANCE: a graph `G = (V, E)`, a weight `w(v) = 1` for each
`v ∈ V`, and a positive integer `K ≤ |V|`. QUESTION: can the vertices in `V` be partitioned
into `k ≤ K` disjoint sets `V₁, V₂, …, V_k` such that, for `1 ≤ i ≤ k`, the subgraph of `G`
induced by `Vᵢ` is connected and the sum of the weights of the vertices in `Vᵢ` (its number of
vertices) does not exceed `B`?

This is BOUNDED COMPONENT SPANNING FOREST (`BoundedComponentSpanningForestWanted`, [ND10]) with
`B` no longer part of the instance. The instance is the graph, the weights and `K`, and
`withBound i B` appends the fixed `B` to obtain an instance of that problem, whose `WellFormed`
(simple edge list, one weight per vertex, `0 < K ≤ |V|`, `0 < B`) and question are reused
unchanged; `WellFormed` here adds that every weight equals `1`. The problem is polynomial for
unit weights and `B = 2` (Hadlock, by matching), so `3` is where hardness starts.

Hardness: Dyer and Frieze, Theorem 2.1(a), prove that deciding whether the vertices of a planar
bipartite graph can be partitioned into sets of exactly `k` vertices, each inducing a connected
subgraph, is NP-complete for every fixed `k ≥ 3`. With unit weights, `B = k` and `K = |V| / k`
(when `k` divides `|V|`), a partition into at most `K` connected sets of at most `B` vertices
must consist of exactly `K` sets of exactly `k` vertices, so their problem reduces to this one.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance for a fixed bound `B`: vertex count `n` (vertices `Fin n`), edge list, vertex
weights `[w 0, …, w (n - 1)]`, and the bound `K` on the number of parts. -/
abbrev FixedBoundInstance := ℕ × List (ℕ × ℕ) × List ℕ × ℕ

/-- The BOUNDED COMPONENT SPANNING FOREST instance given by `i` and the weight bound `B`. -/
abbrev withBound (i : FixedBoundInstance) (B : ℕ) : BoundedComponentSpanningForestInstance :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2, B)

/-- Well-formedness of an instance for the bound `B`: the BOUNDED COMPONENT SPANNING FOREST
instance `withBound i B` is well-formed, and every vertex weight is `1`. -/
def WellFormed (B : ℕ) (i : FixedBoundInstance) : Prop :=
  BoundedComponentSpanningForest.WellFormed (withBound i B) ∧ ∀ x ∈ i.2.2.1, x = 1

open Classical in
/-- BOUNDED COMPONENT SPANNING FOREST with unit weights and the weight bound fixed to `B`, as a
decision problem over bitstrings. -/
noncomputable def boundedComponentSpanningForestUnitWeightsDec (B : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := FixedBoundInstance) x with
  | some i => decide (WellFormed B i ∧ BoundedComponentSpanningForestFeasible (withBound i B))
  | none => false

/-- **BOUNDED COMPONENT SPANNING FOREST with unit weights is NP-complete for every fixed
`B ≥ 3`.** Source: Garey and Johnson (1979), [ND10], comment; Dyer and Frieze (1985),
Theorem 2.1(a). -/
public theorem_wanted boundedComponentSpanningForestUnitWeightsFixedB_npComplete (B : ℕ)
    (hB : 3 ≤ B) :
    boundedComponentSpanningForestUnitWeightsDec B ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (boundedComponentSpanningForestUnitWeightsDec B)

end MetaMathlibExt.Complexity.NPComplete.BoundedComponentSpanningForestUnitWeightsFixedB
