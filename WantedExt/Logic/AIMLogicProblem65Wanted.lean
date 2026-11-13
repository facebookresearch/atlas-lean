/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AIM Logic Problem 65
-/
module

public import Mathlib.RingTheory.Algebraic.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Logic.AIMLogicProblem65Wanted

/-! Source record `UM-20002289-Q001`. -/
/-- Terms of the language of rings: variables indexed by `ℕ`, `0`, `1`, sums, products and
negations. -/
inductive RingTerm : Type where
  | var : Nat → RingTerm
  | zero : RingTerm
  | one : RingTerm
  | add : RingTerm → RingTerm → RingTerm
  | mul : RingTerm → RingTerm → RingTerm
  | neg : RingTerm → RingTerm

/-- First-order formulas of the language of rings, quantifying over variables indexed by `ℕ`. -/
inductive RingFormula : Type where
  | equal : RingTerm → RingTerm → RingFormula
  | not : RingFormula → RingFormula
  | and : RingFormula → RingFormula → RingFormula
  | or : RingFormula → RingFormula → RingFormula
  | imp : RingFormula → RingFormula → RingFormula
  | forall_ : Nat → RingFormula → RingFormula
  | exists_ : Nat → RingFormula → RingFormula

/-- The value of a term in a field under the variable assignment `v`. -/
def RingTerm.eval {F : Type} [Field F] (v : Nat → F) : RingTerm → F
  | .var n => v n
  | .zero => 0
  | .one => 1
  | .add t₁ t₂ => (eval v t₁) + (eval v t₂)
  | .mul t₁ t₂ => (eval v t₁) * (eval v t₂)
  | .neg t => - (eval v t)

/-- Satisfaction of a formula in a field under the variable assignment `v`. -/
def RingFormula.satisfies {F : Type} [Field F] (v : Nat → F) : RingFormula → Prop
  | .equal t₁ t₂ => t₁.eval v = t₂.eval v
  | .not φ => ¬ φ.satisfies v
  | .and φ₁ φ₂ => φ₁.satisfies v ∧ φ₂.satisfies v
  | .or φ₁ φ₂ => φ₁.satisfies v ∨ φ₂.satisfies v
  | .imp φ₁ φ₂ => φ₁.satisfies v → φ₂.satisfies v
  | .forall_ n φ => ∀ x : F, φ.satisfies (Function.update v n x)
  | .exists_ n φ => ∃ x : F, φ.satisfies (Function.update v n x)

/-- `F` is elementarily equivalent to `ℚ` in the language of rings: a formula holds under every
assignment in `ℚ` exactly when it holds under every assignment in `F`. -/
def ElementarilyEquivalentToRat (F : Type) [Field F] : Prop :=
  ∀ φ : RingFormula, (∀ v : Nat → ℚ, φ.satisfies v) ↔ (∀ v : Nat → F, φ.satisfies v)

/-- Koenigsmann's question: if `ℚ* ⊆ ℚ**` are both elementarily equivalent to `ℚ`, then `ℚ*` is
relatively algebraically closed in `ℚ**`. -/
def conjecture : Prop :=
  ∀ (Qstar : Type) (QstarStar : Type) [Field Qstar] [Field QstarStar] [Algebra Qstar QstarStar],
    ElementarilyEquivalentToRat Qstar → ElementarilyEquivalentToRat QstarStar →
      ∀ x : QstarStar, IsAlgebraic Qstar x → ∃ y : Qstar, algebraMap Qstar QstarStar y = x

-- Carried source audit `UM-20002289-Q001` (see the Moved/ record).

/--
Resolved true: Resolved true: Dittmann (Irreducibility of polynomials over global fields is
diophantine, arXiv:1601.07829, Corollary 5.3) proves that if K** ⊇ K* are elementary extensions
of a global field K then K* is relatively algebraically closed in K**; with K = Q, whose
elements are all definable, this answers Koenigsmann's question. Source: P. Dittmann,
Irreducibility of polynomials over global fields is diophantine, arXiv:1601.07829,
https://arxiv.org/abs/1601.07829. Moved from `OpenConjectures/Logic/AIMLogicProblem65`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Logic.AIMLogicProblem65Wanted
