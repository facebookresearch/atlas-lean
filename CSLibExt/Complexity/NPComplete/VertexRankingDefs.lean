/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VERTEX RANKING (TREE-DEPTH): definitions

Source:
H. L. Bodlaender, J. S. Deogun, K. Jansen, T. Kloks, D. Kratsch, H. Müller and Zs. Tuza,
"Rankings of graphs", SIAM Journal on Discrete Mathematics 11(1) (1998), 168-181,
doi:10.1137/S0895480195282550;
A. Pothen, "The complexity of optimal elimination trees", Technical Report CS-88-13, Department
of Computer Science, Pennsylvania State University (1988);
I. Karpas, O. Neiman and S. Smorodinsky, "On vertex rankings of graphs and its relatives",
Discrete Mathematics 338(8) (2015), 1460-1467, doi:10.1016/j.disc.2015.03.008, arXiv:1609.06111
(definition, Section 1).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.VertexRanking

open MetaMathlibExt.Complexity.NPComplete.GraphColoring (GraphColoringInstance Graph)

/-- `c` is a vertex ranking of `G`: any path between two distinct vertices of the same color
contains a vertex of larger color. -/
def IsVertexRanking {V : Type*} (G : SimpleGraph V) {k : ℕ} (c : V → Fin k) : Prop :=
  ∀ ⦃u v : V⦄ (p : G.Walk u v), p.IsPath → u ≠ v → c u = c v → ∃ w ∈ p.support, c u < c w

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n`
(`GraphColoring.WellFormed`), and `0 < K ≤ n`. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2 ∧ i.2.2 ≤ i.1

/-- The graph has a vertex ranking with `K` colors. -/
def VertexRankingFeasible (i : GraphColoringInstance) : Prop :=
  ∃ c : Fin i.1 → Fin i.2.2, IsVertexRanking (Graph i) c

open Classical in
/-- VERTEX RANKING as a decision problem over bitstrings. -/
noncomputable def vertexRankingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ VertexRankingFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.VertexRanking
