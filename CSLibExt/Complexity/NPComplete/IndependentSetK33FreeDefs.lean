/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INDEPENDENT SET on K_3,3-free graphs: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 6(3)
(1985), 434-451, doi:10.1016/0196-6774(85)90012-4 (Table 1, column "K3,3-free": INDEPENDENT SET
NP-complete, citing Garey and Johnson (1979));
C. M. H. de Figueiredo, A. A. de Melo, D. Sasaki and A. Silva, "Revising Johnson's table for the
21st century", Discrete Applied Mathematics 323 (2022), 184-200, doi:10.1016/j.dam.2021.05.021
(the same entry, unchanged);
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT20] INDEPENDENT SET (comment: remains
NP-complete for cubic planar graphs);
K. Kuratowski, "Sur le problème des courbes gauches en topologie", Fundamenta Mathematicae 15
(1930), 271-283 (a planar graph has no subgraph homeomorphic to `K_3,3`).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Combinatorics.SimpleGraph.Connectivity
public import CSLibExt.Complexity.NPComplete.TriangleFreeIndependentSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IndependentSetK33Free

open TriangleFreeIndependentSet (TriangleFreeIndependentSetInstance Graph
  TriangleFreeIndependentSetFeasible)

/-- `G` has a subgraph homeomorphic to `K_3,3`: injective branch vertices `f (inl i)` and
`f (inr j)` (`i, j : Fin 3`) and paths `p i j` from `f (inl i)` to `f (inr j)` such that no inner
vertex of a path (its support without the two ends) is a branch vertex and two different paths
are internally disjoint. -/
def HasK33Subdivision {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ f : Fin 3 ⊕ Fin 3 → V, Function.Injective f ∧
    ∃ p : ∀ i j : Fin 3, G.Walk (f (Sum.inl i)) (f (Sum.inr j)),
      (∀ i j, (p i j).IsPath) ∧
      (∀ i j, ∀ v ∈ (p i j).support.tail.dropLast, ∀ x, v ≠ f x) ∧
      ∀ i j i' j', (i, j) ≠ (i', j') → SimpleGraph.InternallyDisjoint (p i j) (p i' j')

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range) with no subgraph
homeomorphic to `K_3,3`, and `0 < K ≤ |V|`. -/
def WellFormed (i : TriangleFreeIndependentSetInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    ¬ HasK33Subdivision (Graph i) ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- INDEPENDENT SET on `K_3,3`-free graphs as a decision problem over bitstrings. -/
noncomputable def independentSetK33FreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TriangleFreeIndependentSetInstance) x with
  | some i => decide (WellFormed i ∧ TriangleFreeIndependentSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IndependentSetK33Free
