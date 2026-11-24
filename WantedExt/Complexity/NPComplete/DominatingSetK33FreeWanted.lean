/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for K₃,₃-free graphs is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET, comment:
remains NP-complete for planar graphs with maximum vertex degree 3;
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6 (1985),
434-451, doi:10.1016/0196-6774(85)90012-4, Table 1 (row "K3,3-free", column DOMINATING SET);
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200,
doi:10.1016/j.dam.2021.05.021, Table 1 (row K3,3-FREE*, column DOM SET: "N [GJ]").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import WantedExt.Complexity.NPComplete.DominatingSetWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free

open MetaMathlibExt.Complexity.NPComplete.DominatingSet
  (DominatingSetInstance Graph DominatingSetFeasible)

/-!
# DOMINATING SET for K₃,₃-free graphs is NP-complete

INSTANCE: a graph `G = (V, E)` with no subgraph homeomorphic to `K₃,₃`, and a positive integer
`K ≤ |V|`. QUESTION: is there a dominating set of size `K` or less for `G`, i.e., a subset
`V' ⊆ V` with `|V'| ≤ K` such that for all `u ∈ V - V'` there is a `v ∈ V'` for which
`{u, v} ∈ E`?

This is the restriction of DOMINATING SET (`WantedExt.Complexity.NPComplete.DominatingSetWanted`,
[GT2]) to the class that Johnson's 1985 table calls "K3,3-free" and de Figueiredo et al. call
K3,3-FREE*: "the class of graphs that contain no subgraphs homeomorphic to K3,3; in other words,
the class of graphs that do not contain K3,3 as a topological minor". The instance, the graph,
the parent well-formedness condition (a simple edge list) and the question are that module's; the
restriction and the bound `0 < K ≤ |V|` ([GT2]) are added to `WellFormed`. Every planar graph is
K3,3-free (Kuratowski), so the class contains the planar graphs of maximum degree 3, on which
[GT2] records the problem NP-complete; de Figueiredo et al. derive the K3,3-free entries from the
planar ones in this way.

Since `K₃,₃` has no vertex of degree 2, a graph is homeomorphic to `K₃,₃` exactly when it is a
subdivision of `K₃,₃`. `HasK33Subdivision G` says that `G` contains one: six distinct branch
vertices `a₀, a₁, a₂, b₀, b₁, b₂` and, for all `i, j`, a path from `aᵢ` to `bⱼ`, where two
different paths share no vertex other than a common endpoint (a vertex on two different paths is
an endpoint of each, hence a branch vertex they share).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- `G` has a subgraph homeomorphic to `K₃,₃` (a subdivision of `K₃,₃`): distinct branch vertices
`a₀, a₁, a₂, b₀, b₁, b₂` and paths `P i j` from `aᵢ` to `bⱼ` such that a vertex on two different
paths `P i j` and `P k l` is an endpoint of `P i j` (and, symmetrically, of `P k l`). -/
def HasK33Subdivision {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ (a b : Fin 3 → V) (P : ∀ i j, G.Walk (a i) (b j)),
    Function.Injective (Sum.elim a b) ∧ (∀ i j, (P i j).IsPath) ∧
      ∀ i j k l, (i, j) ≠ (k, l) → ∀ v ∈ (P i j).support, v ∈ (P k l).support →
        v = a i ∨ v = b j

/-- Well-formedness of an instance: a well-formed DOMINATING SET instance (simple edge list) whose
graph has no subgraph homeomorphic to `K₃,₃`, with `0 < K ≤ |V|`. -/
def WellFormed (i : DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ ¬ HasK33Subdivision (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET for K₃,₃-free graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetK33FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSetFeasible i)
  | none => false

/-- **DOMINATING SET is NP-complete for K₃,₃-free graphs.** Source: Garey and Johnson (1979),
[GT2], comment; Johnson (1985), Table 1; de Figueiredo, de Melo, Sasaki and Silva (2022),
Table 1. -/
public theorem_wanted dominatingSetK33Free_npComplete :
    dominatingSetK33FreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L dominatingSetK33FreeDec

end MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free
