/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# UNORDERED TREE EDIT DISTANCE is NP-complete

Source:
K. Zhang, R. Statman and D. Shasha, "On the editing distance between unordered labeled trees",
Information Processing Letters 42(3) (1992), 133-139, doi:10.1016/0020-0190(92)90136-J
(NP-complete even for binary trees over a two-letter label alphabet);
R. D. M. Page and G. Valiente, "An edit script for taxonomic classifications", BMC
Bioinformatics 6 (2005), 208, doi:10.1186/1471-2105-6-208 (records the result for the least
number of operations);
R. Sridharamurthy, T. B. Masood, A. Kamakshidasan and V. Natarajan, "Edit distance between merge
trees", IEEE Transactions on Visualization and Computer Graphics 26(3) (2020), 1518-1531,
doi:10.1109/TVCG.2018.2873612, arXiv:2207.08511 (Section 2.3 and Section 3.1: the edit
operations, and the edit distance as the cost of a cheapest one-to-one, ancestor-preserving
mapping).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.UnorderedTreeEditDistance

/-!
# UNORDERED TREE EDIT DISTANCE is NP-complete

INSTANCE: two rooted unordered node-labeled trees `T₁`, `T₂` and an integer `K`; the edit
operations, each of unit cost, are: relabel a node; delete a node `v` (the children of `v` become
children of the parent of `v`); insert a node (the inverse of a deletion).
QUESTION: can `T₁` be transformed into `T₂` with at most `K` edit operations?

A tree on `n` nodes is given by a list of `n` pairs `(parent code, label)`: code `0` marks the
root and code `k + 1` names node `k` as the parent; labels are natural numbers. Trees are
unordered: the children of a node form a set, so trees, and the forests met along an edit
sequence, are compared up to renaming of nodes (`Iso`), and each edit step relates two
forests up to renaming. Deleting the root makes its children roots, so an edit sequence may
pass through forests; this is the model in which the edit distance equals the cost of a
cheapest one-to-one, ancestor-preserving mapping between the node sets, with no condition on
the roots (Zhang, Statman and Shasha; Sridharamurthy et al., Section 3.1). Inserting a node
`v` under a node `w` (or as a new root) makes `v` the parent of any subset of the children of
`w` (of the roots).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the trees `T₁` and `T₂`, each a list of `(parent code, label)` pairs (code `0`
for the root, `k + 1` for parent `k`), and the bound `K`. -/
abbrev UnorderedTreeEditDistanceInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- A finite node-labeled forest: nodes `Fin n`, each with an optional parent and a label. -/
structure LabeledForest where
  /-- The number of nodes. -/
  n : ℕ
  /-- The parent of each node (`none` for a root). -/
  parent : Fin n → Option (Fin n)
  /-- The label of each node. -/
  label : Fin n → ℕ

namespace LabeledForest

/-- No node is its own proper ancestor. -/
def Acyclic (F : LabeledForest) : Prop :=
  ∀ x, ¬ Relation.TransGen (fun a b => F.parent a = some b) x x

/-- A rooted tree: an acyclic forest with exactly one root. -/
def IsTree (F : LabeledForest) : Prop :=
  F.Acyclic ∧ ∃! r, F.parent r = none

end LabeledForest

/-- The forest given by a list of `(parent code, label)` pairs: node `j` has the label `t[j].2`
and, when `t[j].1 = k + 1` with `k` a node, the parent `k`. -/
def ofList (t : List (ℕ × ℕ)) : LabeledForest where
  n := t.length
  parent j := match t[j].1 with
    | 0 => none
    | k + 1 => if h : k < t.length then some ⟨k, h⟩ else none
  label j := t[j].2

/-- `F` and `G` are the same unordered labeled forest: a renaming `e` of the nodes of `G` onto
those of `F` preserves parents and labels. -/
def Iso (F G : LabeledForest) : Prop :=
  ∃ e : Fin G.n ≃ Fin F.n,
    (∀ x, (G.parent x).map e = F.parent (e x)) ∧ ∀ x, G.label x = F.label (e x)

/-- `G` is obtained from `F` by relabeling one node `v` (up to renaming of nodes). -/
def Relabels (F G : LabeledForest) : Prop :=
  ∃ e : Fin G.n ≃ Fin F.n, ∃ v : Fin G.n,
    (∀ x, (G.parent x).map e = F.parent (e x)) ∧ ∀ x, x ≠ v → G.label x = F.label (e x)

/-- `G` is obtained from `F` by deleting the node `v` (up to renaming of nodes): the nodes of
`G` are those of `F` other than `v`, via the embedding `e`, with their labels, and the children
of `v` become children of the parent of `v` (roots, when `v` is a root). -/
def Deletes (F G : LabeledForest) : Prop :=
  ∃ v : Fin F.n, ∃ e : Fin G.n → Fin F.n, Function.Injective e ∧ (∀ x, e x ≠ v) ∧
    (∀ y, y ≠ v → ∃ x, e x = y) ∧ (∀ x, G.label x = F.label (e x)) ∧
    ∀ x, (G.parent x).map e =
      if F.parent (e x) = some v then F.parent v else F.parent (e x)

/-- One edit operation: a relabeling, a deletion, or an insertion (`F` is `G` with a node
deleted). -/
def EditStep (F G : LabeledForest) : Prop :=
  Relabels F G ∨ Deletes F G ∨ Deletes G F

/-- Well-formedness of an instance: every parent code names a node (or the root), and both
lists describe rooted trees. -/
def WellFormed (i : UnorderedTreeEditDistanceInstance) : Prop :=
  (∀ p ∈ i.1, p.1 ≤ i.1.length) ∧ (∀ p ∈ i.2.1, p.1 ≤ i.2.1.length) ∧
    (ofList i.1).IsTree ∧ (ofList i.2.1).IsTree

/-- Some sequence of `k ≤ K` edit operations, through forests `P 0, …, P k`, starts at `T₁` and
ends at a forest that is `T₂` up to renaming of nodes. -/
def UnorderedTreeEditDistanceFeasible (i : UnorderedTreeEditDistanceInstance) : Prop :=
  ∃ k ≤ i.2.2, ∃ P : Fin (k + 1) → LabeledForest,
    P 0 = ofList i.1 ∧ Iso (P (Fin.last k)) (ofList i.2.1) ∧ (∀ j, (P j).Acyclic) ∧
      ∀ j : Fin k, EditStep (P j.castSucc) (P j.succ)

open Classical in
/-- UNORDERED TREE EDIT DISTANCE as a decision problem over bitstrings. -/
noncomputable def unorderedTreeEditDistanceDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := UnorderedTreeEditDistanceInstance) x with
  | some i => decide (WellFormed i ∧ UnorderedTreeEditDistanceFeasible i)
  | none => false

/-- **UNORDERED TREE EDIT DISTANCE is NP-complete.** Source: Zhang, Statman and Shasha (1992). -/
public theorem_wanted unorderedTreeEditDistance_npComplete :
    unorderedTreeEditDistanceDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L unorderedTreeEditDistanceDec

end MetaMathlibExt.Complexity.NPComplete.UnorderedTreeEditDistance
