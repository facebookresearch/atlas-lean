/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Propositional.NaturalDeduction.FunctionalCompleteness

@[expose] public section

/-!
# Tests for functional completeness

The Shannon expansion of exclusive or, its translation to `→` and `⊥`, exact shapes of the
translation, a classical theorem transported through it, and the role of the
finite-support hypothesis.
-/

set_option autoImplicit false

namespace CSLibExtTest.Logics.Propositional.FunctionalCompleteness

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

/-- Exclusive or of `x` and `y`, as a Boolean function of valuations. -/
private def xor' (v : At → Bool) : Bool := v .x != v .y

private theorem xor'_support (v w : At → Bool) (h : ∀ a ∈ [At.x, At.y], v a = w a) :
    xor' v = xor' w := by
  simp only [xor', h .x (by simp), h .y (by simp)]

/-- The Shannon expansion of exclusive or has exclusive or as its truth table. -/
example (v : At → Bool) (hv : v ⊥ = false) :
    (shannon [At.x, .y] xor').evalBool v = (v .x != v .y) :=
  evalBool_shannon xor'_support hv

/-- Exclusive or with `→` and `⊥` only. -/
example : ∃ A : Proposition At, A.IsImpBot ∧
    ∀ v : At → Bool, v ⊥ = false → A.evalBool v = (v .x != v .y) :=
  exists_isImpBot_evalBool_eq [.x, .y] xor' xor'_support

example : toImpBot (p ∧ q : Proposition At) = (((p → (q → ⊥)) → ⊥) : Proposition At) := by
  decide
example : toImpBot (p ∨ q : Proposition At) = (((p → ⊥) → q) : Proposition At) := by decide
example : toImpBot (p → q : Proposition At) = (p → q : Proposition At) := by decide

/-- Excluded middle, rewritten with `→` and `⊥`, is still a `CPL` theorem. -/
example : DerivableIn (CPL At) (toImpBot (p ∨ ¬p : Proposition At)) := by
  rw [derivableIn_cpl_toImpBot_iff, DerivableIn.iff_derivableIn_empty, derivableIn_cpl_iff]
  intro v hv _
  rw [evalBool_or, evalBool_neg hv]
  cases v .x <;> simp [p]

/-- Without the finite-support hypothesis the expansion is wrong: over no atoms, the function
`v ↦ v x` expands to `⊥`, which is false where `x` is true. -/
example : shannon ([] : List At) (fun v ↦ v .x) = (⊥ : Proposition At) := by decide

end CSLibExtTest.Logics.Propositional.FunctionalCompleteness
