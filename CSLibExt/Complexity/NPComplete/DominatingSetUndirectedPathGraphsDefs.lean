/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DOMINATING SET for undirected path graphs: definitions

Source:
K. S. Booth and J. H. Johnson, "Dominating sets in chordal graphs", SIAM Journal on Computing
11(1) (1982), 191-199, doi:10.1137/0211015 (finding a minimum dominating set is NP-complete for
chordal graphs, "even when restricted to undirected path graphs");
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT2] DOMINATING SET.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import CSLibExt.Complexity.NPComplete.DominatingSetDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphs

/-- `G` is an undirected path graph: for some tree `T` on `Fin m`, each vertex `v` of `G` has
the vertex set `P v` of a path in `T`, and distinct vertices are adjacent in `G` exactly when
their paths share a vertex. -/
def IsUndirectedPathGraph {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)), T.IsTree ∧
    ∃ P : Fin n → Finset (Fin m),
      (∀ v, ∃ (a b : Fin m) (p : T.Walk a b), p.IsPath ∧ p.support.toFinset = P v) ∧
        ∀ u v, u ≠ v → (G.Adj u v ↔ (P u ∩ P v).Nonempty)

/-- Well-formedness of an instance: the parent's (a simple edge list on `Fin n`), the graph is
an undirected path graph, and `0 < K ≤ n`. -/
def WellFormed (i : DominatingSet.DominatingSetInstance) : Prop :=
  DominatingSet.WellFormed i ∧ IsUndirectedPathGraph (DominatingSet.Graph i) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.1

open Classical in
/-- DOMINATING SET for undirected path graphs as a decision problem over bitstrings. -/
noncomputable def dominatingSetUndirectedPathGraphsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DominatingSet.DominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ DominatingSet.DominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.DominatingSetUndirectedPathGraphs
