/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON SUBTREE: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM COMMON SUBTREE;
T. Akutsu and M. M. Halldórsson, "On the approximation of largest common subtrees and largest
common point sets", Theoretical Computer Science 233 (2000), 33-50,
doi:10.1016/S0304-3975(97)00278-8 (conference version: Proc. ISAAC 1994, LNCS 834, 405-413,
doi:10.1007/3-540-58325-4_205).
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonSubtree

/-- An instance: the trees `T₁, …, T_n` (each a vertex count and an edge list) and the bound
`K`. -/
abbrev CommonSubtreeInstance := List (ℕ × List (ℕ × ℕ)) × ℕ

/-- The graph on `Fin t.1` with edge list `t.2`. -/
def Graph (t : ℕ × List (ℕ × ℕ)) : SimpleGraph (Fin t.1) :=
  Cslib.Complexity.Karp.edgeGraph t.1 t.2

/-- Well-formedness of an instance: the collection is nonempty, every edge list is simple and
every graph is a tree, and `K` is positive. -/
def WellFormed (i : CommonSubtreeInstance) : Prop :=
  i.1 ≠ [] ∧
    (∀ t ∈ i.1, t.2.Nodup ∧
      (∀ e ∈ t.2, e.1 < t.1 ∧ e.2 < t.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ t.2) ∧ (Graph t).IsTree) ∧
    0 < i.2

/-- Some tree `T'` with at least `K` vertices embeds as an induced subgraph into every `Tᵢ`. -/
def CommonSubtreeFeasible (i : CommonSubtreeInstance) : Prop :=
  ∃ m, i.2 ≤ m ∧ ∃ T' : SimpleGraph (Fin m), T'.IsTree ∧ ∀ t ∈ i.1, Nonempty (T' ↪g Graph t)

open Classical in
/-- COMMON SUBTREE as a decision problem over bitstrings. -/
noncomputable def commonSubtreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CommonSubtreeInstance) x with
  | some i => decide (WellFormed i ∧ CommonSubtreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CommonSubtree
