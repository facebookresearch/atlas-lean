/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.BDD.Basic
public meta import CSLibExt.Logics.Propositional.BDD.Basic

@[expose] public section

/-!
# Tests for reduced ordered binary decision diagrams

ROBDDs of small propositions computed by `apply` (`#guard`, since `apply` is defined by
well-founded recursion), canonicity used at the proof level, and the two hypotheses of
canonicity shown necessary by counterexamples.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.BDD

open Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.BDD

private def p : Proposition Nat := .atom 0
private def q : Proposition Nat := .atom 1
private def r : Proposition Nat := .atom 2

#guard ofProposition p == node 0 (leaf false) (leaf true)
#guard ofProposition (p ∧ q : Proposition Nat) ==
  node 0 (leaf false) (node 1 (leaf false) (leaf true))
-- Commutativity and distributivity show up as equal diagrams.
#guard ofProposition (p ∧ q : Proposition Nat) == ofProposition (q ∧ p : Proposition Nat)
#guard ofProposition (p ∧ (q ∨ r) : Proposition Nat) ==
  ofProposition ((p ∧ q) ∨ (p ∧ r) : Proposition Nat)
-- Tautologies reduce to the leaf `true`.
#guard ofProposition (p → p : Proposition Nat) == leaf true
#guard ofProposition (((p → q) → p) → p : Proposition Nat) == leaf true
-- Non-equivalent formulas get different diagrams.
#guard ofProposition (p → q : Proposition Nat) != ofProposition (q → p : Proposition Nat)

/-- Canonicity at the proof level: the ROBDDs of `p ∧ q` and `q ∧ p` are equal because the
truth tables agree. -/
example : ofProposition (p ∧ q : Proposition Nat) = ofProposition (q ∧ p : Proposition Nat) :=
  ofProposition_eq_iff.mpr fun σ ↦ by
    simp only [Proposition.evalBool_and, Bool.and_comm]

/-- `apply` keeps diagrams reduced and ordered. -/
example : IsROBDD (apply (· && ·) (ofProposition p) (ofProposition q)) :=
  isROBDD_apply _ (isROBDD_ofProposition p) (isROBDD_ofProposition q)

/-- Reducedness is needed: a redundant test has the function of its child. -/
example : node 0 (leaf true) (leaf true) ≠ leaf true ∧
    ∀ σ, (node 0 (leaf true) (leaf true)).eval σ = (leaf true).eval σ :=
  ⟨by decide, fun σ ↦ by simp⟩

example : ¬ Reduced (node 0 (leaf true) (leaf true)) := by simp [Reduced]

/-- Ordering is needed: `x₀ ∨ x₁` tested in the order `x₁, x₀` and in the order `x₀, x₁`
gives two different reduced diagrams with the same function. -/
private def outOfOrder : BDD := node 1 (node 0 (leaf false) (leaf true)) (leaf true)
private def inOrder : BDD := node 0 (node 1 (leaf false) (leaf true)) (leaf true)

example : outOfOrder ≠ inOrder ∧ ∀ σ, outOfOrder.eval σ = inOrder.eval σ :=
  ⟨by decide, fun σ ↦ by
    simp only [outOfOrder, inOrder, eval_node, eval_leaf]
    cases σ 0 <;> cases σ 1 <;> rfl⟩

example : Reduced outOfOrder ∧ ¬ OrderedFrom 0 outOfOrder := by
  simp [outOfOrder, Reduced, OrderedFrom]

example : IsROBDD inOrder := by simp [IsROBDD, inOrder, Reduced, OrderedFrom]

/-- Satisfiability: `p ∧ q` is satisfiable since its ROBDD is not the leaf `false`. -/
example : ∃ σ, (p ∧ q : Proposition Nat).evalBool σ = true :=
  ofProposition_ne_leaf_false_iff.mp (by
    rw [show ofProposition (p ∧ q : Proposition Nat) = apply (· && ·)
      (node 0 (leaf false) (leaf true)) (node 1 (leaf false) (leaf true)) from rfl]
    simp [apply, mk])

end CSLibExtTest.Logics.Propositional.BDD
