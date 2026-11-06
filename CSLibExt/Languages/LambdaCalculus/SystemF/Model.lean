/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Cslib.Languages.LambdaCalculus.LocallyNameless.Untyped.FullBeta

/-!
# The existing untyped beta-conversion term model

The carrier is CSLib's locally closed untyped syntax over symbolic Nat atoms.
No new untyped syntax or reduction relation is introduced. This fixed syntactic
model is not a set-valued interpretation of all Lean universes.
-/

@[expose] public section

namespace Cslib.Languages.LambdaCalculus.SystemF

open Cslib.LambdaCalculus.LocallyNameless.Untyped

/-- **Untyped locally closed term model.**
Locally closed terms in the pinned CSLib untyped calculus. -/
abbrev Model : Type := {t : Term Nat // t.LcAt 0}

/-- **Beta equivalence in the untyped term model.**
Equivalence closure of the existing full-beta reduction. -/
abbrev BetaEq (f g : Model) : Prop :=
  Relation.EqvGen Term.FullBeta f.val g.val

namespace Model

/-- **Application in the untyped term model.**
Application in the existing untyped term model preserves local closure. -/
def app (f a : Model) : Model :=
  ⟨.app f.val a.val, by
    simpa only [Term.LcAt, Bool.and_eq_true] using
      And.intro f.property a.property⟩

/-- **Model terms are locally closed.**
The Boolean carrier invariant implies CSLib's cofinite local closure. -/
theorem lc (t : Model) : t.val.LC :=
  (Term.lcAt_iff_LC t.val).mp t.property

/-- **Symbolic atoms of the untyped term model.**
A symbolic atom is locally closed; it is not a new System F constant. -/
def atom (i : Nat) : Model := ⟨.fvar i, rfl⟩

end Model

namespace BetaEq

/-- **Reflexivity of beta equivalence.** Upstream beta equivalence is reflexive. -/
@[refl] theorem refl (f : Model) : BetaEq f f := Relation.EqvGen.refl f.val

/-- **Symmetry of beta equivalence.** Upstream beta equivalence is symmetric. -/
@[symm] theorem symm {f g : Model} (h : BetaEq f g) : BetaEq g f :=
  Relation.EqvGen.symm f.val g.val h

/-- **Transitivity of beta equivalence.** Upstream beta equivalence is transitive. -/
@[trans] theorem trans {f g h : Model} (hfg : BetaEq f g)
    (hgh : BetaEq g h) : BetaEq f h :=
  Relation.EqvGen.trans f.val g.val h.val hfg hgh

/-- **Beta equivalence is a congruence in function position.**
Application preserves beta equivalence in its function position. -/
theorem appFun {f g : Model} (h : BetaEq f g) (a : Model) :
    BetaEq (Model.app f a) (Model.app g a) := by
  change Relation.EqvGen Term.FullBeta
    (.app f.val a.val) (.app g.val a.val)
  change Relation.EqvGen Term.FullBeta f.val g.val at h
  generalize f.val = F at h ⊢
  generalize g.val = G at h ⊢
  induction h with
  | rel f g hs => exact Relation.EqvGen.rel _ _ (Term.Xi.appR a.lc hs)
  | refl => exact Relation.EqvGen.refl _
  | symm f g h ih => exact Relation.EqvGen.symm _ _ ih
  | trans f g h hfg hgh ihfg ihgh =>
    exact Relation.EqvGen.trans _ _ _ ihfg ihgh

/-- **Beta equivalence is a congruence in argument position.**
Application preserves beta equivalence in its argument position. -/
theorem appArg (f : Model) {a b : Model} (h : BetaEq a b) :
    BetaEq (Model.app f a) (Model.app f b) := by
  change Relation.EqvGen Term.FullBeta
    (.app f.val a.val) (.app f.val b.val)
  change Relation.EqvGen Term.FullBeta a.val b.val at h
  generalize a.val = A at h ⊢
  generalize b.val = B at h ⊢
  induction h with
  | rel a b hs => exact Relation.EqvGen.rel _ _ (Term.Xi.appL f.lc hs)
  | refl => exact Relation.EqvGen.refl _
  | symm a b h ih => exact Relation.EqvGen.symm _ _ ih
  | trans a b c hab hbc ihab ihbc =>
    exact Relation.EqvGen.trans _ _ _ ihab ihbc

end BetaEq

end Cslib.Languages.LambdaCalculus.SystemF
