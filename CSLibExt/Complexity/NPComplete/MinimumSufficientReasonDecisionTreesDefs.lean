/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MINIMUM SUFFICIENT REASON for decision trees: definitions

Source:
P. Barceló, M. Monet, J. Pérez and B. Subercaseaux, "Model interpretability through the lens
of computational complexity", Advances in Neural Information Processing Systems 33
(NeurIPS 2020), Proposition 6 (1) and Lemma 18; arXiv:2010.12265.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.OSSS
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MinimumSufficientReasonDecisionTrees

open StatMech.OSSS

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

end MetaMathlibExt.Complexity.NPComplete.MinimumSufficientReasonDecisionTrees
