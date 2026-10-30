/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.FirstOrder.PropositionalBridge

/-!
# Consumer tests for the propositional-to-first-order bridge

The atoms are the two Boolean values, interpreted by the identity valuation.
Expected truth values are the literal truth-table entries, including the false
antecedent cases of implication and a nested formula using every connective.
-/

set_option autoImplicit false

open Cslib.Logic.FOL (propLanguage)
open Cslib.Logic.FOL.Proposition (embed boolStructure realize_embed_iff_evalBool)

namespace CSLibExtTest.Logics.FirstOrder.PropositionalBridge

private def realizes (A : Cslib.Logic.PL.Proposition Bool) : Prop :=
  @FirstOrder.Language.Formula.Realize (propLanguage Bool) Bool (boolStructure id)
    Empty (embed A) Empty.elim

example : realizes (.atom true) :=
  (realize_embed_iff_evalBool id (.atom true)).mpr rfl

example : ¬ realizes (.atom false) := by
  intro h
  exact Bool.false_ne_true ((realize_embed_iff_evalBool id (.atom false)).mp h)

example : realizes (.and (.atom true) (.atom true)) :=
  (realize_embed_iff_evalBool id (.and (.atom true) (.atom true))).mpr rfl

example : ¬ realizes (.and (.atom true) (.atom false)) := by
  intro h
  exact Bool.false_ne_true
    ((realize_embed_iff_evalBool id (.and (.atom true) (.atom false))).mp h)

example : ¬ realizes (.and (.atom false) (.atom true)) := by
  intro h
  exact Bool.false_ne_true
    ((realize_embed_iff_evalBool id (.and (.atom false) (.atom true))).mp h)

example : realizes (.or (.atom false) (.atom true)) :=
  (realize_embed_iff_evalBool id (.or (.atom false) (.atom true))).mpr rfl

example : realizes (.or (.atom true) (.atom false)) :=
  (realize_embed_iff_evalBool id (.or (.atom true) (.atom false))).mpr rfl

example : ¬ realizes (.or (.atom false) (.atom false)) := by
  intro h
  exact Bool.false_ne_true
    ((realize_embed_iff_evalBool id (.or (.atom false) (.atom false))).mp h)

example : ¬ realizes (.imp (.atom true) (.atom false)) := by
  intro h
  exact Bool.false_ne_true
    ((realize_embed_iff_evalBool id (.imp (.atom true) (.atom false))).mp h)

example : realizes (.imp (.atom false) (.atom true)) :=
  (realize_embed_iff_evalBool id (.imp (.atom false) (.atom true))).mpr rfl

example : realizes (.imp (.atom false) (.atom false)) :=
  (realize_embed_iff_evalBool id (.imp (.atom false) (.atom false))).mpr rfl

example : realizes (.imp (.atom true) (.atom true)) :=
  (realize_embed_iff_evalBool id (.imp (.atom true) (.atom true))).mpr rfl

example : realizes (.and (.or (.atom false) (.atom true))
    (.imp (.atom false) (.atom false))) :=
  (realize_embed_iff_evalBool id (.and (.or (.atom false) (.atom true))
    (.imp (.atom false) (.atom false)))).mpr rfl

end CSLibExtTest.Logics.FirstOrder.PropositionalBridge
