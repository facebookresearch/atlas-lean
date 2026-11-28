/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BRANCHWIDTH: definitions

Source:
P. D. Seymour and R. Thomas, "Call routing and the ratcatcher", Combinatorica 14 (1994),
217-241, doi:10.1007/BF01215352 (branchwidth "is NP-hard for general graphs"; definitions in
Section 1, (1.1)).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Branchwidth

/-- An instance: vertex count `n` (vertices `0, …, n - 1`), edge list, bound `K`. -/
abbrev BranchwidthInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: the edge list describes a simple graph on `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BranchwidthInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

open Classical in
/-- `(T, τ)` is a branch decomposition of the edge list `es` (on vertices `0, …, n - 1`) of
width at most `K`: `T` is a tree whose vertices all have valency `1` or `3`, `τ` is a bijection
from the edges onto the leaves of `T`, and for every edge `xy` of `T`, with `A` the edges whose
leaves are reachable from `x` once `xy` is removed, at most `K` vertices are incident both with
an edge in `A` and with an edge not in `A`. -/
def IsBranchDecompositionOfWidth (n : ℕ) (es : List (ℕ × ℕ)) (K : ℕ) {m : ℕ}
    (T : SimpleGraph (Fin m)) (τ : Fin es.length → Fin m) : Prop :=
  T.IsTree ∧ (∀ x, T.degree x = 1 ∨ T.degree x = 3) ∧ Function.Injective τ ∧
    (∀ x, T.degree x = 1 ↔ x ∈ Set.range τ) ∧
    ∀ x y, T.Adj x y →
      ((Finset.range n).filter fun v =>
        (∃ j, (T.deleteEdges {s(x, y)}).Reachable x (τ j) ∧
          (v = (es.get j).1 ∨ v = (es.get j).2)) ∧
        (∃ j, ¬ (T.deleteEdges {s(x, y)}).Reachable x (τ j) ∧
          (v = (es.get j).1 ∨ v = (es.get j).2))).card ≤ K

/-- The branchwidth is at most `K`: the graph has at most one edge, or some branch decomposition
has width at most `K`. -/
def BranchwidthFeasible (i : BranchwidthInstance) : Prop :=
  i.2.1.length ≤ 1 ∨ ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (τ : Fin i.2.1.length → Fin m),
    IsBranchDecompositionOfWidth i.1 i.2.1 i.2.2 T τ

open Classical in
/-- BRANCHWIDTH as a decision problem over bitstrings. -/
noncomputable def branchwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BranchwidthInstance) x with
  | some i => decide (WellFormed i ∧ BranchwidthFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Branchwidth
