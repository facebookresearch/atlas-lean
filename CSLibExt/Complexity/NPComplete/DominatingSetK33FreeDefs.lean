/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for K₃,₃-free graphs: definitions

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

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free

open MetaMathlibExt.Complexity.NPComplete.DominatingSet
  (DominatingSetInstance Graph DominatingSetFeasible)

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

end MetaMathlibExt.Complexity.NPComplete.DominatingSetK33Free
