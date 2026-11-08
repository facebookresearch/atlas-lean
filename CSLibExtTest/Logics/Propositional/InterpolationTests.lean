/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.NaturalDeduction.Interpolation

@[expose] public section

/-!
# Tests for Craig interpolation

Concrete atom sets and substitutions, Boolean quantification evaluated through
`evalBool_elimAtoms`, and interpolants obtained from the semantic and the `CPL`
forms, including the boundary case of formulas with no common atom.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.Interpolation

open Cslib.Logic Cslib.Logic.PL Proposition Theory InferenceSystem

/-- Three ordinary atoms plus a separate falsum atom `⊥`. -/
inductive At where
  | falsum
  | x
  | y
  | z
  deriving DecidableEq

instance : Bot At := ⟨.falsum⟩

private def p : Proposition At := .atom .x
private def q : Proposition At := .atom .y
private def r : Proposition At := .atom .z

example : (p ∧ q : Proposition At).atoms = {.x, .y} := by decide
example : (p ∧ q : Proposition At).fixAtom .x true = ((⊥ → ⊥) ∧ q : Proposition At) := by decide
example : (p ∧ q : Proposition At).fixAtom .x false = (⊥ ∧ q : Proposition At) := by decide

/-- Quantifying `x` out of `x ∧ y` leaves `y`. -/
example (v : At → Bool) (hv : v ⊥ = false) :
    (elimAtoms [.x] (p ∧ q : Proposition At)).evalBool v = v .y := by
  have h := evalBool_elimAtoms (ps := [.x]) (by decide) (p ∧ q : Proposition At) hv
  cases hy : v .y
  · rw [Bool.eq_false_iff]
    intro hI
    obtain ⟨w, hw, hA⟩ := h.mp hI
    have : w .y = v .y := hw .y (by decide)
    simp [p, q, this, hy] at hA
  · refine h.mpr ⟨Function.update v .x true, fun a ha ↦ ?_, ?_⟩
    · rw [Function.update_of_ne (by simpa using ha)]
    · simp [p, q, hy]

/-- Eliminating the atom `⊥` itself is allowed: `∃⊥. ⊥` holds (take `⊥ := true`). -/
example (v : At → Bool) (hv : v ⊥ = false) :
    (elimAtom ⊥ (⊥ : Proposition At)).evalBool v = true :=
  (evalBool_elimAtom ⊥ _ hv).mpr ⟨true, by simp⟩

/-- `x ∧ y → y ∨ z` has an interpolant over the common atom `y` (and `⊥`). -/
example : ∃ I : Proposition At, I.atoms ⊆ {⊥, .y} ∧
    DerivableIn (CPL At) (p ∧ q → I : Proposition At) ∧
    DerivableIn (CPL At) (I → q ∨ r : Proposition At) := by
  have h : DerivableIn (CPL At) (p ∧ q → q ∨ r : Proposition At) := by
    rw [DerivableIn.iff_derivableIn_empty, derivableIn_cpl_iff]
    intro v _ _
    simp only [p, q, r, evalBool_imp, evalBool_and, evalBool_or, evalBool_atom]
    cases v .x <;> cases v .y <;> simp
  obtain ⟨I, hI, hAI, hIB⟩ := exists_interpolant_cpl h
  refine ⟨I, fun a ha ↦ ?_, hAI, hIB⟩
  have := hI ha
  simp only [Finset.mem_insert, Finset.mem_inter] at this
  rcases this with rfl | ⟨ha₁, ha₂⟩
  · simp
  · revert ha₁ ha₂
    cases a <;> decide

/-- No common atom: a contradiction implies anything, and its interpolant mentions only
`⊥`. -/
example : ∃ I : Proposition At, I.atoms ⊆ {⊥} ∧
    (∀ v : At → Bool, v ⊥ = false → (p ∧ ¬p : Proposition At).evalBool v = true →
      I.evalBool v = true) ∧
    (∀ v : At → Bool, v ⊥ = false → I.evalBool v = true → q.evalBool v = true) := by
  obtain ⟨I, hI, hAI, hIB⟩ := exists_interpolant (A := (p ∧ ¬p : Proposition At)) (B := q)
    fun v hv hA ↦ by
      rw [evalBool_and, evalBool_neg hv] at hA
      simp at hA
  refine ⟨I, fun a ha ↦ ?_, hAI, hIB⟩
  have := hI ha
  simp only [Finset.mem_insert, Finset.mem_inter] at this
  rcases this with rfl | ⟨ha₁, ha₂⟩
  · simp
  · revert ha₁ ha₂
    cases a <;> decide

end CSLibExtTest.Logics.Propositional.Interpolation
