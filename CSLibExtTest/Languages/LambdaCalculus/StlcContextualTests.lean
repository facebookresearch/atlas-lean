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

public import CSLibExt.Languages.LambdaCalculus.DeBruijn.Stlc.Contextual

@[expose] public section

/-!
# Client tests for typed STLC contexts

These examples exercise plugging, context composition, semantic congruence, and
beta and eta equations below nontrivial contexts through the public API.
-/

namespace Cslib.Languages.LambdaCalculus.Stlc.ContextualTests

open Cslib.Languages.LambdaCalculus.Stlc
open scoped CslibStlc

abbrev O : Ty Unit := .base ()

def identity : Tm [] (O ⇒ O) := .lam (.var .zero)

/-- Apply the function in the hole to the open base variable. -/
def applyVariable : TmCtx [O] (O ⇒ O) [O] O :=
  .appFun .hole (.var .zero)

/-- Apply the weakened identity function to the term in the hole. -/
def applyIdentity : TmCtx [O] O [O] O :=
  .appArg (Tm.weaken identity) .hole

/-- Bind the open variable around the term in the hole. -/
def abstract : TmCtx [O] O [] (O ⇒ O) := .lam .hole

example (t : Tm [O] O) :
    (TmCtx.comp abstract applyIdentity).plug t = abstract.plug (applyIdentity.plug t) :=
  TmCtx.plug_comp abstract applyIdentity t

example : TmCtx.comp applyIdentity (.hole : TmCtx [O] O [O] O) = applyIdentity :=
  TmCtx.comp_hole applyIdentity

example {I : Unit → Type} {t u : Tm [O] O} (h : SemEq I t u) :
    SemEq I (abstract.plug t) (abstract.plug u) := abstract.semEq h

example (body : Tm (O :: [O]) O) (a : Tm [O] O) :
    ModelEq (applyIdentity.plug (.app (.lam body) a))
      (applyIdentity.plug (Tm.instantiate body a)) :=
  ModelEq.context_beta applyIdentity body a

example (f : Tm [O] (O ⇒ O)) :
    ModelEq (applyVariable.plug (.lam (.app (Tm.weaken f) (.var .zero))))
      (applyVariable.plug f) :=
  ModelEq.context_eta applyVariable f

/-- The upstream hole-filling notation `C<[t]` is plugging. -/
example (t : Tm [O] O) : (applyIdentity<[t] : Tm [O] O) = .app (Tm.weaken identity) t := rfl

example (t : Tm [O] (O ⇒ O)) :
    HasHContext.fill (α := Tm [O] O) (β := Tm [O] (O ⇒ O)) applyVariable t =
      .app t (.var .zero) := by
  simp [applyVariable]

#print axioms Cslib.Languages.LambdaCalculus.Stlc.TmCtx.fill_eq_plug
#print axioms Cslib.Languages.LambdaCalculus.Stlc.TmCtx.plug_comp
#print axioms Cslib.Languages.LambdaCalculus.Stlc.TmCtx.comp_assoc
#print axioms Cslib.Languages.LambdaCalculus.Stlc.TmCtx.semEq
#print axioms Cslib.Languages.LambdaCalculus.Stlc.ModelEq.context_beta
#print axioms Cslib.Languages.LambdaCalculus.Stlc.ModelEq.context_eta

end Cslib.Languages.LambdaCalculus.Stlc.ContextualTests
