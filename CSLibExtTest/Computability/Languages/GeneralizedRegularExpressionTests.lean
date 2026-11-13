/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Languages.GeneralizedRegularExpression

@[expose] public section

/-!
# Client tests for generalized regular expressions

Smoke tests for `regularStarHeight`, `GenRegExp.denote` / `starHeight`,
and `HasGenHeightLe`, and the theorems: generalized expressions denote
regular languages; single words and `Σ*` have height zero; a star raises the
height bound by at most one; and over `Bool`, `true*` has height zero.
-/

open scoped Computability

namespace Cslib.Language

example : regularStarHeight (RegularExpression.char 'a') = 0 := rfl

example : regularStarHeight (RegularExpression.star (RegularExpression.char 'a')) = 1 := rfl

example :
    regularStarHeight
      (RegularExpression.plus (RegularExpression.char 'a')
        (RegularExpression.star (RegularExpression.char 'b'))) = 1 := rfl

example : GenRegExp.starHeight (GenRegExp.ofReg (RegularExpression.char 'a')) = 0 := rfl

example :
    GenRegExp.starHeight
      (GenRegExp.star (GenRegExp.compl (GenRegExp.ofReg (RegularExpression.char 'a')))) = 1 := rfl

example :
    (GenRegExp.ofReg (RegularExpression.char 'a')).denote = {['a']} := rfl

example : HasGenHeightLe (α := Char) {['a']} 0 :=
  ⟨GenRegExp.ofReg (RegularExpression.char 'a'), rfl, le_refl 0⟩

example (e : GenRegExp Char) : e.denote.IsRegular := e.denote_isRegular

example : HasGenHeightLe ({['a', 'b']} : Language Char) 0 := hasGenHeightLe_zero_singleton _

example : HasGenHeightLe (⊤ : Language Char) 0 := hasGenHeightLe_zero_top

example : HasGenHeightLe (({['a']} : Language Char)∗) 1 :=
  (hasGenHeightLe_zero_singleton ['a']).kstar

example : HasGenHeightLe (({[true]} : Language Bool)∗) 0 := hasGenHeightLe_zero_kstar_true

example : (({[true]} : Language Bool)∗).IsRegular := hasGenHeightLe_zero_kstar_true.isRegular

example : [true, true] ∈ ({[true]} : Language Bool)∗ := mem_kstar_true.2 (by decide)

example : [true, false] ∉ ({[true]} : Language Bool)∗ := fun h => by
  have := mem_kstar_true.1 h false (by decide)
  exact Bool.false_ne_true this

-- Basic generalized-expression clients must not import the higher congruence theories.
run_cmd do
  let env ← Lean.getEnv
  for name in [`CSLibExt.Computability.Languages.Congruences.Varieties,
      `CSLibExt.Computability.Languages.Congruences.Regularity,
      `CSLibExt.Computability.Languages.Congruences.Recognition,
      `CSLibExt.Computability.Languages.Congruences.WordMorphisms,
      `CSLibExt.Computability.Languages.Congruences.Moore,
      `CSLibExt.Computability.Languages.Congruences.StarFreeHeight] do
    if (env.getModuleIdx? name).isSome then
      throwError "Basic generalized expressions unexpectedly import {name}"

end Cslib.Language
