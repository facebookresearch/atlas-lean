/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMMON EMBEDDED SUBTREE is NP-complete

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

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.UnorderedTreeEditDistanceWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CommonEmbeddedSubtree

/-!
# COMMON EMBEDDED SUBTREE is NP-complete

INSTANCE: rooted trees `T₁` and `T₂` with labels on the nodes, and a positive integer `K`.
QUESTION: is there a common embedded subtree of size at least `K`, i.e. a labeled tree `T'`
with `|T'| ≥ K` that can be embedded into both `T₁` and `T₂`? An embedding of `T'` into `T`
is an injective function from the nodes of `T'` to the nodes of `T` that preserves labels and
ancestorship. Since fathership need not be preserved, `T'` need not be an ordinary subtree.

Trees are unordered and given as in
`WantedExt.Complexity.NPComplete.UnorderedTreeEditDistanceWanted`: a list of
`(parent code, label)` pairs, code `0` for the root and `k + 1` for parent `k`. Preserving
ancestorship means that `x` is a proper ancestor of `y` in `T'` exactly when `f x` is a proper
ancestor of `f y` in `T`, as in the tree-inclusion embeddings of Kilpeläinen and Mannila.

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

/-- **COMMON EMBEDDED SUBTREE is NP-complete.** Source: Crescenzi and Kann, MAXIMUM COMMON EMBEDDED
SUB-TREE; Zhang and Jiang (1994); Kilpeläinen and Mannila (1995). -/
public theorem_wanted commonEmbeddedSubtree_npComplete :
    commonEmbeddedSubtreeDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L commonEmbeddedSubtreeDec

end MetaMathlibExt.Complexity.NPComplete.CommonEmbeddedSubtree
