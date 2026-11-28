/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LOCATING-DOMINATING SET: definitions

Source:
I. Charon, O. Hudry and A. Lobstein, "Minimizing the size of an identifying or
locating-dominating code in a graph is NP-hard", Theoretical Computer Science 290(3) (2003),
2109-2120, doi:10.1016/S0304-3975(02)00536-4;
M. R. Cappelle, G. C. M. Gomes and V. F. dos Santos, "Parameterized algorithms for
locating-dominating sets", arXiv:2011.14849 (2020), Section 1 (the problem as stated here, and
its NP-completeness, already for bipartite graphs, credited to Charon, Hudry and Lobstein).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Combinatorics.SimpleGraph.Domination
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LocatingDominatingSet

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the bound `d`. -/
abbrev LocatingDominatingSetInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : LocatingDominatingSetInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: a simple edge list on `Fin n` (no repeated edge, no loop,
no reversed copy). -/
def WellFormed (i : LocatingDominatingSetInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- `S` is a locating-dominating set of `G`: it dominates `G`, and distinct vertices outside
`S` have distinct neighborhoods in `S`. -/
def IsLocatingDominating {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) : Prop :=
  G.IsDominating ↑S ∧ ∀ u v, u ∉ S → v ∉ S → u ≠ v → G.neighborSet u ∩ ↑S ≠ G.neighborSet v ∩ ↑S

/-- Some locating-dominating set has at most `d` vertices. -/
def LocatingDominatingSetFeasible (i : LocatingDominatingSetInstance) : Prop :=
  ∃ S : Finset (Fin i.1), S.card ≤ i.2.2 ∧ IsLocatingDominating (Graph i) S

open Classical in
/-- LOCATING-DOMINATING SET as a decision problem over bitstrings. -/
noncomputable def locatingDominatingSetDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := LocatingDominatingSetInstance) x with
  | some i => decide (WellFormed i ∧ LocatingDominatingSetFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.LocatingDominatingSet
