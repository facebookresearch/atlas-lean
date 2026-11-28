/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ROOTED TREE ARRANGEMENT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT45] ROOTED TREE
ARRANGEMENT (transformation from OPTIMAL LINEAR ARRANGEMENT);
F. Gavril, "Some NP-complete problems on graphs", Proceedings of the 11th
Conference on Information Sciences and Systems, Johns Hopkins University,
Baltimore (1977), 91-95.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Metric

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RootedTreeArrangement

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the bound `K`. -/
abbrev RootedTreeArrangementInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : RootedTreeArrangementInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `K` is
positive. -/
def WellFormed (i : RootedTreeArrangementInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

/-- The cost `∑_{{u, v} ∈ E} d(f(u), f(v))` of placing the vertices of `G` on the tree `T`
by `f`, with `d = T.dist`. -/
noncomputable def arrangementCost {n : ℕ} (G T : SimpleGraph (Fin n)) (f : Fin n → Fin n) : ℕ :=
  ∑ᶠ e ∈ G.edgeSet, Sym2.lift ⟨fun a b => T.dist (f a) (f b), fun _ _ => SimpleGraph.dist_comm⟩ e

/-- A tree `T` on `Fin n` with root `r` and a one-to-one `f` such that the images of the ends
of every edge lie on one simple path from `r`, and the total tree distance is at most `K`. -/
def RootedTreeArrangementFeasible (i : RootedTreeArrangementInstance) : Prop :=
  ∃ T : SimpleGraph (Fin i.1), T.IsTree ∧ ∃ r : Fin i.1, ∃ f : Fin i.1 → Fin i.1,
    Function.Injective f ∧
      (∀ u v, (Graph i).Adj u v →
        ∃ x, ∃ p : T.Walk r x, p.IsPath ∧ f u ∈ p.support ∧ f v ∈ p.support) ∧
      arrangementCost (Graph i) T f ≤ i.2.2

open Classical in
/-- ROOTED TREE ARRANGEMENT as a decision problem over bitstrings. -/
noncomputable def rootedTreeArrangementDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RootedTreeArrangementInstance) x with
  | some i => decide (WellFormed i ∧ RootedTreeArrangementFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.RootedTreeArrangement
