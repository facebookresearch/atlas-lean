/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `7f0f951227ee766bba21a6d5a5e56d9065fe85aa`.
Original formalization by Zeina Migeed (@migeed-z); ported with permission.
-/

module

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Semantics
public import Mathlib.CategoryTheory.Category.Basic

@[expose] public section

/-!
# Client tests for intrinsically typed STLC

The examples exercise weakening, beta substitution, progress, determinism, and
the normal-form characterization through the public API.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.Tests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def identity : Tm [] (O ⇒ O) := .lam (.var .zero)

def constant : Tm [] (O ⇒ O ⇒ O) :=
  .lam (.lam (.var (.succ .zero)))

def higherIdentity : Tm [] ((O ⇒ O) ⇒ (O ⇒ O)) :=
  .lam (.var .zero)

def openProjection : Tm [O] (O ⇒ O) :=
  .lam (.var (.succ .zero))

def openIdentitySub : Sub [O] [O]
  | _, .zero => .var .zero

example : Tm.instantiate (.var (.zero : Var [O ⇒ O] (O ⇒ O))) identity = identity := by
  rfl

/-- Substitution crosses a binder, weakening the open replacement so that its
free variable is not captured by the lambda. -/
example : Tm.subst openIdentitySub openProjection = openProjection := by
  rfl

example : Step (.app higherIdentity identity) identity := by
  exact .beta (.lam _)

example : Steps (.app higherIdentity identity) identity := by
  exact Relation.ReflTransGen.single (.beta (.lam _))

example : Value identity := by exact .lam _

example : Step.NormalForm identity := by
  exact Step.closed_normalForm_iff_value identity |>.mpr (.lam _)

example : Value constant ∨ ∃ t', Step constant t' := Step.progress constant

example {t t₁ t₂ : Tm [] (O ⇒ O)} (h₁ : Step t t₁) (h₂ : Step t t₂) : t₁ = t₂ := by
  exact Step.deterministic h₁ h₂

/-! The scoped STLC arrow coexists with Mathlib's categorical arrow notation. -/

example {C : Type} [CategoryTheory.Category C] (X Y : C) : Type := X ⟶ Y

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.rename_comp
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.subst_id
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Tm.subst_ofRen
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Step.progress
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Step.deterministic
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Step.closed_normalForm_iff_value

/-- A lambda whose body is a beta-redex is normal for upstream `Relation.Normal Step`:
call-by-value does not reduce under a binder. -/
example : Relation.Normal Step (.lam (.app (.lam (.var .zero)) (.var .zero)) : Tm [] (O ⇒ O)) :=
  Step.normalForm_iff_normal.mp fun _ h => Step.value_irreducible (Value.lam _) h

/-- A redex is not upstream-normal for `Step`. -/
example : ¬Relation.Normal Step
    (.app (.lam (.var .zero) : Tm [] ((O ⇒ O) ⇒ O ⇒ O)) identity) :=
  fun h => Step.normalForm_iff_normal.mpr h _ (.beta (.lam _))

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Step.normalForm_iff_normal

end Cslib.Languages.LambdaCalculus.Stlc.Tests
