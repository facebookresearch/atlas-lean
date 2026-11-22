/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON SUBTREE is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition, 2000),
entry MAXIMUM COMMON SUBTREE;
T. Akutsu and M. M. Halldórsson, "On the approximation of largest common subtrees and largest
common point sets", Theoretical Computer Science 233 (2000), 33-50,
doi:10.1016/S0304-3975(97)00278-8 (conference version: Proc. ISAAC 1994, LNCS 834, 405-413,
doi:10.1007/3-540-58325-4_205).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonSubtree

/-!
# COMMON SUBTREE is NP-complete

INSTANCE: a collection `T₁, …, T_n` of trees and a positive integer `K`. QUESTION: is there a
tree `T'` with at least `K` vertices that is isomorphic to a subtree (an induced connected
subgraph) of each `Tᵢ`?

This is the decision version of MAXIMUM COMMON SUBTREE in the compendium of Crescenzi and Kann,
whose measure is the number of vertices of `T'`. The trees are unlabeled and unrooted.

Each tree is a vertex count `n` and an edge list on `Fin n` (`Cslib.Complexity.Karp.edgeGraph`),
a simple edge list (no duplicates, loops or reversed copies) whose graph is a tree
(`SimpleGraph.IsTree`: connected and acyclic). `T'` is a tree on `Fin m` with `K ≤ m`, and
"`T'` is isomorphic to a subtree of `Tᵢ`" is a graph embedding `T' ↪g Tᵢ`
(`SimpleGraph.Embedding`: an injective map that preserves and reflects adjacency). Its image is a
vertex set whose induced subgraph of `Tᵢ` is isomorphic to `T'`, hence connected; conversely an
induced connected subgraph of a tree is a tree. The collection is nonempty (`n ≥ 1`); with no
trees every `K` would be a yes-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **COMMON SUBTREE is NP-complete.** Source: Crescenzi and Kann, MAXIMUM COMMON SUBTREE;
Akutsu and Halldórsson (2000). -/
public theorem_wanted commonSubtree_npComplete :
    commonSubtreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L commonSubtreeDec

end MetaMathlibExt.Complexity.NPComplete.CommonSubtree
