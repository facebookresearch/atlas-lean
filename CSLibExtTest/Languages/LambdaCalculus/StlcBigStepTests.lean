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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.BigStep

@[expose] public section

/-!
# Client tests for STLC big-step semantics

The nested application below forces both application premises and the beta
body premise of big-step evaluation.  The examples compare that derivation
with the existing small-step normalization interface.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.BigStepTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def identity (A : Ty Unit) : Tm [] (A ⇒ A) := .lam (.var .zero)

def nestedIdentity : Tm [] (O ⇒ O) :=
  .app (identity (O ⇒ O)) (.app (identity (O ⇒ O)) (identity O))

example : nestedIdentity ⇓ identity O := by
  apply Eval.app (Eval.lam _)
  · exact Eval.app (Eval.lam _) (Eval.lam _) (Eval.lam _)
  · exact Eval.lam _

example : Steps nestedIdentity (identity O) := by
  exact Eval.to_steps (by
    apply Eval.app (Eval.lam _)
    · exact Eval.app (Eval.lam _) (Eval.lam _) (Eval.lam _)
    · exact Eval.lam _)

example : nestedIdentity ⇓ identity O ↔
    Steps nestedIdentity (identity O) ∧ Value (identity O) := Eval.iff_steps_value

example : ∃ v, nestedIdentity ⇓ v := Eval.exists_closed nestedIdentity

example {v w : Tm [] (O ⇒ O)} (hv : nestedIdentity ⇓ v) (hw : nestedIdentity ⇓ w) :
    v = w := Eval.deterministic hv hw

example {t v w : Tm [O ⇒ O] (O ⇒ O)} (hv : t ⇓ v) (hw : t ⇓ w) : v = w :=
  Eval.deterministic hv hw

example : Terminates nestedIdentity ↔ ∃ v, nestedIdentity ⇓ v := terminates_iff_eval

#print axioms Cslib.Languages.LambdaCalculus.Stlc.Eval.to_steps
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Eval.anti_step
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Eval.iff_steps_value
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Eval.deterministic
#print axioms Cslib.Languages.LambdaCalculus.Stlc.Eval.exists_closed

end Cslib.Languages.LambdaCalculus.Stlc.BigStepTests
