/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.BDD.Count
public meta import CSLibExt.Logics.Propositional.BDD.Count

@[expose] public section

/-!
# Tests for BDD satisfy-count

Counts of small ROBDDs against the enumeration `countModels`, free variables above and
between the tested ones, constant diagrams, and the correctness theorem at a concrete
diagram.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.BDDCount

open Cslib.Logic Cslib.Logic.PL Cslib.Logic.PL.BDD

private def p : Proposition Nat := .atom 0
private def q : Proposition Nat := .atom 1
private def r : Proposition Nat := .atom 2

#guard satCount 2 (ofProposition (p ∧ q : Proposition Nat)) == 1
#guard satCount 2 (ofProposition (p ∨ q : Proposition Nat)) == 3
#guard satCount 2 (ofProposition (p → q : Proposition Nat)) == 3
-- a free variable above the tested ones doubles the count
#guard satCount 3 (ofProposition (p ∧ q : Proposition Nat)) == 2
-- a free variable between tested ones (`x₁` in `x₀ ∧ x₂`)
#guard satCount 3 (ofProposition (p ∧ r : Proposition Nat)) == 2
#guard satCount 3 (ofProposition (p ∨ r : Proposition Nat)) == 6
#guard satCount 0 (leaf true) == 1
#guard satCount 4 (leaf false) == 0
#guard satCount 64 (leaf true) == 2 ^ 64
-- agreement with the enumeration
#guard satCount 3 (ofProposition (p ∨ r : Proposition Nat)) ==
  countModels (List.range 3) (fun τ ↦ (ofProposition (p ∨ r : Proposition Nat)).eval τ)
    (fun _ ↦ false)
#guard satCount 3 (ofProposition ((p → q) ∧ (q → r) : Proposition Nat)) ==
  countModels (List.range 3)
    (fun τ ↦ (ofProposition ((p → q) ∧ (q → r) : Proposition Nat)).eval τ) (fun _ ↦ true)

/-- The correctness theorem at the diagram of `x₀ ∧ x₂`. -/
example (σ : Nat → Bool) :
    satCount 3 (node 0 (leaf false) (node 2 (leaf false) (leaf true))) =
      countModels (List.range 3)
        (fun τ ↦ (node 0 (leaf false) (node 2 (leaf false) (leaf true))).eval τ) σ :=
  satCount_eq_countModels (by simp [OrderedFrom]) (by simp [VarsLT]) σ

end CSLibExtTest.Logics.Propositional.BDDCount
