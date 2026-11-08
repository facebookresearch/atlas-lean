/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

@[expose] public section

/-!
# Tests for truth-table semantics and soundness of natural deduction

Concrete truth-table values, soundness applied to explicit derivations, and
non-derivability results obtained from countervaluations, including the
minimal-logic boundary where `⊥` is an ordinary atom.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.NaturalDeductionSemantics

open Cslib.Logic Cslib.Logic.PL Proposition Theory InferenceSystem

/-- Two ordinary atoms plus a separate falsum atom `⊥`. -/
inductive At where
  | falsum
  | x
  | y
  deriving DecidableEq

instance : Bot At := ⟨.falsum⟩

private def p : Proposition At := .atom .x
private def q : Proposition At := .atom .y

/-- The valuation making `p` true and everything else, including `⊥`, false. -/
private def onlyP : At → Bool := fun a ↦ decide (a = .x)

example : (p ∧ q : Proposition At).evalBool onlyP = false := by decide
example : (p ∨ q : Proposition At).evalBool onlyP = true := by decide
example : (q → p : Proposition At).evalBool onlyP = true := by decide
example : (p → q : Proposition At).evalBool onlyP = false := by decide
example : (¬q : Proposition At).evalBool onlyP = true := by decide
example : (⊥ : Proposition At).evalBool onlyP = false := by decide

/-- `p ∧ q ⊢ q ∧ p` in minimal logic, then read off its truth-table consequence. -/
private def swapAnd : (MPL At).Derivation {p ∧ q} (q ∧ p) :=
  .andI (.andE₂ (.ass (Finset.mem_singleton_self _)))
    (.andE₁ (.ass (Finset.mem_singleton_self _)))

example (v : At → Bool) (h : (p ∧ q : Proposition At).evalBool v = true) :
    (q ∧ p : Proposition At).evalBool v = true :=
  swapAnd.boolSound v (by simp) (by simpa using h)

/-- Soundness refutes a derivation: `p ⊢ q` is not derivable in minimal logic. -/
example : ¬ DerivableIn (MPL At) ({p} ⊢ q) := by
  intro h
  have := DerivableIn.boolSound h onlyP (by simp) (by simp [p, onlyP])
  simp [q, onlyP] at this

/-- Without an ex falso axiom, `⊥` is an ordinary atom: the theory `{⊥}` does not derive `p`.
The countervaluation makes `⊥` true and `p` false. -/
example : ¬ DerivableIn ({⊥} : Theory At) p := by
  intro h
  have := DerivableIn.boolSound h (fun a ↦ decide (a = ⊥)) (by simp) (by simp)
  simp at this

/-- With ex falso, the same theory does derive `p`. -/
example : DerivableIn (IPL At ∪ {⊥} : Theory At) p :=
  ⟨.implE (.ax (Set.mem_union_left _ (efq_mem_ipl p)))
    (.ax (Set.mem_union_right _ rfl))⟩

/-- Peirce's law, derived in `CPL`, is a tautology. -/
example (v : At → Bool) (hv : v ⊥ = false) :
    (((p → q) → p) → p : Proposition At).evalBool v = true :=
  DerivableIn.evalBool_of_cpl (Atom := At) ⟨IsClassical.pierce p q⟩ hv (by simp)

example : ¬ DerivableIn (CPL At) (⊥ : Proposition At) := not_derivableIn_cpl_bot
example : ¬ DerivableIn (CPL At) p := not_derivableIn_cpl_atom _

/-- `IPL` is consistent too. -/
example : ¬ DerivableIn (IPL At) (⊥ : Proposition At) := by
  intro h
  have := DerivableIn.evalBool_of_ipl (v := fun _ ↦ false) h rfl (by simp)
  simp at this

end CSLibExtTest.Logics.Propositional.NaturalDeductionSemantics
