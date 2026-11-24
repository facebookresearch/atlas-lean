/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.SmallObject.TerminalIteration

/-!
# Tests for the terminal restriction of the native small-object iteration
-/

@[expose] public section

noncomputable section

universe v u w vJ uJ μU

open CategoryTheory Limits

namespace CategoryTheory.SmallObject.TerminalIterationTest

variable {C : Type u} [Category.{v} C] [HasTerminal C]
variable (I : MorphismProperty C) (κ : Cardinal.{w})
  [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

example :
    let t := terminal.fromNatTrans C
    let d := SmallObject.functorialFactorizationData I κ
    let r := (d.functorCategory C).factorizationData t
    r.Z = SmallObject.terminalIteration I κ :=
  SmallObject.canonical_terminal_middle_eq_terminalIteration I κ

example (X : C) :
    let t := terminal.fromNatTrans C
    let d := SmallObject.functorialFactorizationData I κ
    let r := (d.functorCategory C).factorizationData t
    r.i.app X = SmallObject.ιObj I κ (terminal.from X) ∧
      r.p.app X = SmallObject.πObj I κ (terminal.from X) ∧
      r.i.app X ≫ r.p.app X = terminal.from X ∧
      r.p.app X ≫
          ((SmallObject.ιIteration I κ).app ((terminal.arrowFunctor C).obj X)).right =
        ((SmallObject.iteration I κ).obj ((terminal.arrowFunctor C).obj X)).hom := by
  let t := terminal.fromNatTrans C
  let d := SmallObject.functorialFactorizationData I κ
  let r := (d.functorCategory C).factorizationData t
  refine ⟨SmallObject.canonical_terminal_middle_unit_app I κ X,
    SmallObject.canonical_terminal_middle_factor_app I κ X, ?_, ?_⟩
  · simpa only [NatTrans.comp_app, t, terminal.fromNatTrans_app] using
      congr_app r.fac X
  · exact SmallObject.canonical_terminal_middle_factor_app_ιIteration_right I κ X

variable (J : Type uJ) [Category.{vJ} J] [HasLimitsOfShape J C]
  [PreservesLimitsOfShape J (SmallObject.iteration I κ)]

example : PreservesLimitsOfShape J (SmallObject.terminalIteration I κ) :=
  SmallObject.terminalIteration_preservesLimitsOfShape I κ J

example [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan (SmallObject.iteration I κ)] :
    (SmallObject.terminalIteration I κ).PreservesMonomorphisms :=
  SmallObject.terminalIteration_preservesMonomorphisms I κ

example (μ : Cardinal.{μU}) [Fact μ.IsRegular]
    [HasCardinalFilteredColimits C μ]
    [(SmallObject.iteration I κ).IsCardinalAccessible μ] :
    (SmallObject.terminalIteration I κ).IsCardinalAccessible μ :=
  SmallObject.terminalIteration_isCardinalAccessible I κ μ

end CategoryTheory.SmallObject.TerminalIterationTest
