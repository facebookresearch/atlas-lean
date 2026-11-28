/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GRUNDY NUMBER: definitions

Source:
M. Zaker, "Results on the Grundy chromatic number of graphs", Discrete Mathematics 306 (2006),
3166-3173, doi:10.1016/j.disc.2005.06.044 (Grundy colorings and `Γ(G)`; deciding `Γ(G) ≥ k` is
NP-complete, even for complements of bipartite graphs).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.GraphColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GrundyNumber

open GraphColoring (GraphColoringInstance Graph)

/-- A Grundy `k`-coloring: a proper coloring `c` whose colors are `1, …, k`, each used by some
vertex, such that for colors `i < j` every vertex of color `j` has a neighbor of color `i`. -/
def IsGrundyColoring {V : Type} {G : SimpleGraph V} (k : ℕ) (c : G.Coloring ℕ) : Prop :=
  (∀ v, 1 ≤ c v ∧ c v ≤ k) ∧ (∀ j ≤ k, 1 ≤ j → ∃ v, c v = j) ∧
    ∀ v, ∀ i < c v, 1 ≤ i → ∃ u, G.Adj v u ∧ c u = i

/-- Well-formedness of an instance: the GRAPH K-COLORABILITY well-formedness (a simple edge list
on vertices below `n`), and `K` is positive. -/
def WellFormed (i : GraphColoringInstance) : Prop :=
  GraphColoring.WellFormed i ∧ 0 < i.2.2

/-- `Γ(G) ≥ K`: some Grundy `k`-coloring of the graph has `k ≥ K`. -/
def GrundyNumberFeasible (i : GraphColoringInstance) : Prop :=
  ∃ k ≥ i.2.2, ∃ c : (Graph i).Coloring ℕ, IsGrundyColoring k c

open Classical in
/-- GRUNDY NUMBER as a decision problem over bitstrings. -/
noncomputable def grundyNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GraphColoringInstance) x with
  | some i => decide (WellFormed i ∧ GrundyNumberFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GrundyNumber
