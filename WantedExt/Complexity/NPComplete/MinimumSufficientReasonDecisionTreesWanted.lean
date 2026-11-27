/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUFFICIENT REASON for decision trees is NP-complete

Source:
P. Barceló, M. Monet, J. Pérez and B. Subercaseaux, "Model interpretability through the lens
of computational complexity", Advances in Neural Information Processing Systems 33
(NeurIPS 2020), Proposition 6 (1) and Lemma 18; arXiv:2010.12265.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.BooleanFunctions.OSSS
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSufficientReasonDecisionTrees

open StatMech.OSSS

/-!
# MINIMUM SUFFICIENT REASON for decision trees is NP-complete

INSTANCE: a decision tree `T` over the Boolean features `1, ..., n`, an instance
`x ∈ {0, 1}ⁿ`, and `k ∈ ℕ`. QUESTION: is there a sufficient reason `y` for `x` with respect to
`T` with `‖y‖ ≤ k`?

Following Barceló, Monet, Pérez and Subercaseaux (2020), Section 3: a partial instance is a
vector `y ∈ {0, 1, ⊥}ⁿ`, and `x` is a completion of `y` when `xᵢ = yᵢ` wherever `yᵢ ≠ ⊥`. A
sufficient reason for `x` is a partial instance `y` of which `x` is a completion and such that
`T(x') = T(x)` for every completion `x'` of `y`; `‖y‖` is the number of components of `y` other
than `⊥`. A partial instance of which `x` is a completion is determined by the set `S` of its
defined components (its values there are those of `x`), so the question asks for a set `S` of
at most `k` features such that every `x'` agreeing with `x` on `S` has `T(x') = T(x)`. A
decision tree is a free binary decision diagram (no two nodes on a root-to-leaf path carry the
same feature) whose underlying graph is a tree; the source proves NP-completeness for free
binary decision diagrams and hardness already for decision trees.

Representation: features are `Fin n`, with `n` the length of the listed instance `x`; the tree
is `StatMech.OSSS.DecisionTree (Fin n)`, whose node `node e t f` continues in `t` when feature
`e` is `1` and in `f` when it is `0`. The instance lists the tree in preorder: the token
`(true, e)` is a node querying feature `e`, followed by its `1`-subtree and then its
`0`-subtree; `(false, 1)` and `(false, 0)` are leaves labelled true and false. Each token is
one node, so the token list has the size of the tree.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the decision tree as a preorder token list, the instance `x` as a list of
Booleans (its length is the number `n` of features), and the bound `k`. -/
abbrev MinimumSufficientReasonDecisionTreesInstance := List (Bool × ℕ) × List Bool × ℕ

/-- `parse n fuel ts` reads one tree over the features `Fin n` from the front of the preorder
token list `ts` and returns it with the unread tokens; `none` if `ts` does not start with a
tree, a node names a feature `≥ n`, a leaf token is not `(false, 0)` or `(false, 1)`, or the
fuel runs out. Every call reads one token, so fuel equal to the token count is enough. -/
def parse (n : ℕ) : ℕ → List (Bool × ℕ) → Option (DecisionTree (Fin n) × List (Bool × ℕ))
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, (false, 0) :: rest => some (.leaf false, rest)
  | _ + 1, (false, 1) :: rest => some (.leaf true, rest)
  | _ + 1, (false, _ + 2) :: _ => none
  | fuel + 1, (true, e) :: rest =>
    if he : e < n then
      match parse n fuel rest with
      | some (t, rest₁) =>
        match parse n fuel rest₁ with
        | some (f, rest₂) => some (.node ⟨e, he⟩ t f, rest₂)
        | none => none
      | none => none
    else none

/-- The number of features of an instance: the length of `x`. -/
abbrev numFeatures (i : MinimumSufficientReasonDecisionTreesInstance) : ℕ := i.2.1.length

/-- The decision tree of an instance (a leaf labelled false when the tokens are not exactly
one tree; `WellFormed` excludes that case). -/
def tree (i : MinimumSufficientReasonDecisionTreesInstance) :
    DecisionTree (Fin (numFeatures i)) :=
  match parse (numFeatures i) i.1.length i.1 with
  | some (t, []) => t
  | _ => .leaf false

/-- The features queried at some node of a tree. -/
def features {n : ℕ} : DecisionTree (Fin n) → Finset (Fin n)
  | .leaf _ => ∅
  | .node e t f => insert e (features t ∪ features f)

/-- A tree is free when no feature is queried twice on a root-to-leaf path: the feature of
each node is queried nowhere below it. -/
def IsFree {n : ℕ} : DecisionTree (Fin n) → Prop
  | .leaf _ => True
  | .node e t f => e ∉ features t ∧ e ∉ features f ∧ IsFree t ∧ IsFree f

/-- Well-formedness of an instance: the token list is exactly one decision tree over the
features `Fin n` in preorder, and that tree is free (a decision tree in the source's sense). -/
def WellFormed (i : MinimumSufficientReasonDecisionTreesInstance) : Prop :=
  (parse (numFeatures i) i.1.length i.1).map Prod.snd = some [] ∧ IsFree (tree i)

/-- A sufficient reason with at most `k` defined components exists: a set `S` of at most `k`
features such that every `x'` that agrees with `x` on `S` is classified as `x` is. -/
def MinimumSufficientReasonDecisionTreesFeasible
    (i : MinimumSufficientReasonDecisionTreesInstance) : Prop :=
  ∃ S : Finset (Fin (numFeatures i)), S.card ≤ i.2.2 ∧
    ∀ x' : Fin (numFeatures i) → Bool, (∀ j ∈ S, x' j = i.2.1.get j) →
      (tree i).eval x' = (tree i).eval i.2.1.get

open Classical in
/-- MINIMUM SUFFICIENT REASON for decision trees as a decision problem over bitstrings. -/
noncomputable def minimumSufficientReasonDecisionTreesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MinimumSufficientReasonDecisionTreesInstance) x with
  | some i => decide (WellFormed i ∧ MinimumSufficientReasonDecisionTreesFeasible i)
  | none => false

/-- **MINIMUM SUFFICIENT REASON for decision trees is NP-complete.** Source: Barceló, Monet,
Pérez and Subercaseaux (2020), Proposition 6 (1) and Lemma 18. -/
public theorem_wanted minimumSufficientReasonDecisionTrees_npComplete :
    minimumSufficientReasonDecisionTreesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L minimumSufficientReasonDecisionTreesDec

end MetaMathlibExt.Complexity.NPComplete.MinimumSufficientReasonDecisionTrees
