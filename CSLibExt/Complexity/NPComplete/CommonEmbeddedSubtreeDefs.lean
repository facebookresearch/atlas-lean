/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON EMBEDDED SUBTREE: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM COMMON EMBEDDED SUB-TREE;
K. Zhang and T. Jiang, "Some MAX SNP-hard results concerning unordered labeled trees",
Information Processing Letters 49 (1994), 249-254, doi:10.1016/0020-0190(94)90062-0;
P. Kilpeläinen and H. Mannila, "Ordered and unordered tree inclusion", SIAM Journal on
Computing 24(2) (1995), 340-356, doi:10.1137/S0097539791218202 (unordered tree inclusion,
the case `K = |T₁|`, is NP-complete).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.UnorderedTreeEditDistanceDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonEmbeddedSubtree

/-- An instance: the trees `T₁` and `T₂`, each a list of `(parent code, label)` pairs (code `0`
for the root, `k + 1` for parent `k`), and the bound `K`. -/
abbrev CommonEmbeddedSubtreeInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ

/-- `x` is a proper ancestor of `y` in `F`: following parents from `y` reaches `x` in one or
more steps. -/
def IsAncestor (F : UnorderedTreeEditDistance.LabeledForest) (x y : Fin F.n) : Prop :=
  Relation.TransGen (fun a b => F.parent a = some b) y x

/-- An embedding of `S` into `T`: an injective map of the nodes that preserves labels and
ancestorship. -/
def Embeds (S T : UnorderedTreeEditDistance.LabeledForest) : Prop :=
  ∃ f : Fin S.n → Fin T.n, Function.Injective f ∧ (∀ x, S.label x = T.label (f x)) ∧
    ∀ x y, IsAncestor S x y ↔ IsAncestor T (f x) (f y)

/-- Well-formedness of an instance: both lists describe rooted trees (as in
`UnorderedTreeEditDistance.WellFormed`), and `0 < K`. -/
def WellFormed (i : CommonEmbeddedSubtreeInstance) : Prop :=
  UnorderedTreeEditDistance.WellFormed i ∧ 0 < i.2.2

/-- Some labeled tree with at least `K` nodes embeds into both `T₁` and `T₂`. -/
def CommonEmbeddedSubtreeFeasible (i : CommonEmbeddedSubtreeInstance) : Prop :=
  ∃ T' : UnorderedTreeEditDistance.LabeledForest, T'.IsTree ∧ i.2.2 ≤ T'.n ∧
    Embeds T' (UnorderedTreeEditDistance.ofList i.1) ∧
    Embeds T' (UnorderedTreeEditDistance.ofList i.2.1)

open Classical in
/-- COMMON EMBEDDED SUBTREE as a decision problem over bitstrings. -/
noncomputable def commonEmbeddedSubtreeDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CommonEmbeddedSubtreeInstance) x with
  | some i => decide (WellFormed i ∧ CommonEmbeddedSubtreeFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.CommonEmbeddedSubtree
