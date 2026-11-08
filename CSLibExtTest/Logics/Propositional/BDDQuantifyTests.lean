/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.BDD.Quantify
public meta import CSLibExt.Logics.Propositional.BDD.Quantify

@[expose] public section

/-!
# Tests for BDD restriction, quantification, and satisfying paths

Cofactors and quantifiers computed on small ROBDDs (`#guard`, since `apply` is well-founded),
satisfying paths and the assignments they induce, and the proof-level API.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.BDDQuantify

open Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.BDD

private def p : Proposition Nat := .atom 0
private def q : Proposition Nat := .atom 1

#guard restrict 0 true (ofProposition (p ∧ q : Proposition Nat)) == ofProposition q
#guard restrict 0 false (ofProposition (p ∧ q : Proposition Nat)) == leaf false
#guard restrict 1 false (ofProposition (p → q : Proposition Nat)) ==
  node 0 (leaf true) (leaf false)
#guard existsVar 0 (ofProposition (p ∧ q : Proposition Nat)) == ofProposition q
#guard forallVar 0 (ofProposition (p ∨ q : Proposition Nat)) == ofProposition q
#guard forallVar 0 (ofProposition (p ∧ q : Proposition Nat)) == leaf false
#guard satPath (ofProposition (p ∧ q : Proposition Nat)) == some [(0, true), (1, true)]
#guard satPath (ofProposition (p → q : Proposition Nat)) == some [(0, true), (1, true)]
#guard satPath (leaf false) == none
#guard ofPath [(0, true), (3, false)] 0 == true && ofPath [(0, true), (3, false)] 3 == false &&
  ofPath [(0, true), (3, false)] 7 == false

-- `restrict` reduces even an unreduced input.
#guard restrict 5 true (node 0 (leaf true) (leaf true)) == leaf true
example : Reduced (restrict 5 true (node 0 (leaf true) (leaf true))) := reduced_restrict _ _ _

/-- Quantification at the proof level: `∃x₀. x₀ ∧ x₁` holds exactly when `x₁` does. -/
example (σ : Nat → Bool) (h : σ 1 = true) :
    (existsVar 0 (ofProposition (p ∧ q : Proposition Nat))).eval σ = true :=
  (eval_existsVar 0 _ σ).mpr ⟨true, by simp [eval_ofProposition, p, q, h]⟩

/-- A satisfying assignment, computed from the ROBDD of `x₀ ∧ x₁`. -/
example : ∃ path, satPath (ofProposition (p ∧ q : Proposition Nat)) = some path ∧
    (p ∧ q : Proposition Nat).evalBool (ofPath path) = true :=
  ofProposition_satPath _

/-- A model of `x₀ → x₁` with `x₀` false, from the cofactor's satisfying path. -/
example : ∃ path, satPath (restrict 0 false (ofProposition (p → q : Proposition Nat))) =
      some path ∧
    (p → q : Proposition Nat).evalBool (Function.update (ofPath path) 0 false) = true :=
  satPath_restrict_ofProposition 0 ⟨fun _ ↦ false, rfl, by simp [p, q]⟩

#guard satPath (restrict 0 false (ofProposition (p → q : Proposition Nat))) == some []
#guard satPath (restrict 1 false (ofProposition (p ∨ q : Proposition Nat))) == some [(0, true)]

-- With variable `0` fixed to false (`exists_evalBool_eq_false_at_iff`), `x₀ ∧ x₁` has no
-- model and `x₀ → x₁` has one.
#guard restrict 0 false (ofProposition (p ∧ q : Proposition Nat)) == leaf false
#guard restrict 0 false (ofProposition (p → q : Proposition Nat)) != leaf false

end CSLibExtTest.Logics.Propositional.BDDQuantify
