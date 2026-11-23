/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Limits.Arrow
public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.MorphismProperty.Factorization
public import Mathlib.CategoryTheory.Presentable.Basic
public import Mathlib.CategoryTheory.SmallObject.IsCardinalForSmallObjectArgument

/-!
# Terminal restriction of the native small-object iteration

For an eligible family `I` and regular cardinal `κ`, the canonical
factorization of the terminal natural transformation has exactly the terminal
restriction of `SmallObject.iteration I κ` as its middle functor. This is an
equality of whole functors, hence retains every object and map.

The two native factor maps and the inverse-right-unit normalization are exposed
separately. Preservation of limits, monomorphisms, and cardinal-filtered
colimits then transfers without selecting another replacement.
-/

@[expose] public section

noncomputable section

universe v u w vJ uJ μU

open CategoryTheory Limits

namespace CategoryTheory.SmallObject

variable {C : Type u} [Category.{v} C] [HasTerminal C]
variable (I : MorphismProperty C) (κ : Cardinal.{w})
  [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  [I.IsCardinalForSmallObjectArgument κ]

/-- The exact terminal-arrow restriction of the native `κ`-iteration. -/
def terminalIteration : C ⥤ C :=
  (terminal.arrowFunctor C ⋙ SmallObject.iteration I κ) ⋙ Arrow.leftFunc

/-- The canonical functor-category factorization middle is exactly the terminal
restriction of the same native iteration, including every object and map. -/
theorem canonical_terminal_middle_eq_terminalIteration :
    let t := terminal.fromNatTrans C
    let d := SmallObject.functorialFactorizationData I κ
    let r := (d.functorCategory C).factorizationData t
    r.Z = terminalIteration I κ := by
  rfl

/-- The canonical terminal-factorization unit is the left component of the
native iteration unit. -/
theorem canonical_terminal_middle_unit_app (X : C) :
    let t := terminal.fromNatTrans C
    let d := SmallObject.functorialFactorizationData I κ
    let r := (d.functorCategory C).factorizationData t
    r.i.app X = SmallObject.ιObj I κ (terminal.from X) := by
  rfl

/-- The canonical terminal-factorization right map is the native
`SmallObject.πObj`, including its inverse right-unit component. -/
theorem canonical_terminal_middle_factor_app (X : C) :
    let t := terminal.fromNatTrans C
    let d := SmallObject.functorialFactorizationData I κ
    let r := (d.functorCategory C).factorizationData t
    r.p.app X = SmallObject.πObj I κ (terminal.from X) := by
  rfl

/-- The same canonical right factor normalizes against the original right
component of `ιIteration`. -/
theorem canonical_terminal_middle_factor_app_ιIteration_right (X : C) :
    let t := terminal.fromNatTrans C
    let d := SmallObject.functorialFactorizationData I κ
    let r := (d.functorCategory C).factorizationData t
    r.p.app X ≫
        ((SmallObject.ιIteration I κ).app ((terminal.arrowFunctor C).obj X)).right =
      ((SmallObject.iteration I κ).obj ((terminal.arrowFunctor C).obj X)).hom := by
  dsimp only
  exact SmallObject.πObj_ιIteration_app_right I κ (terminal.from X)

/-- Terminal restriction and the left Arrow projection transfer preservation of
any limit shape available in the base category. -/
theorem terminalIteration_preservesLimitsOfShape
    (J : Type uJ) [Category.{vJ} J] [HasLimitsOfShape J C]
    [PreservesLimitsOfShape J (SmallObject.iteration I κ)] :
    PreservesLimitsOfShape J (terminalIteration I κ) := by
  let _ : PreservesLimitsOfShape J (terminal.arrowFunctor C) :=
    terminal.arrowFunctor_preservesLimitsOfShape C J
  change PreservesLimitsOfShape J
    ((terminal.arrowFunctor C ⋙ SmallObject.iteration I κ) ⋙ Arrow.leftFunc)
  infer_instance

/-- Pullback preservation of the same terminal iteration implies preservation of
monomorphisms, without a second transfinite induction. -/
theorem terminalIteration_preservesMonomorphisms
    [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan (SmallObject.iteration I κ)] :
    (terminalIteration I κ).PreservesMonomorphisms := by
  let _ : PreservesLimitsOfShape WalkingCospan (terminalIteration I κ) :=
    terminalIteration_preservesLimitsOfShape I κ WalkingCospan
  infer_instance

/-- Cardinal accessibility transfers to the exact terminal restriction of the
same native iteration. -/
theorem terminalIteration_isCardinalAccessible
    (μ : Cardinal.{μU}) [Fact μ.IsRegular]
    [HasCardinalFilteredColimits C μ]
    [(SmallObject.iteration I κ).IsCardinalAccessible μ] :
    (terminalIteration I κ).IsCardinalAccessible μ where
  preservesColimitOfShape J _ _ := by
    have := HasCardinalFilteredColimits.hasColimitsOfShape C μ J
    let _ : PreservesColimitsOfShape J (terminal.arrowFunctor C) :=
      (terminal.arrowFunctor_isCardinalAccessible C μ).preservesColimitOfShape J
    let _ : PreservesColimitsOfShape J (SmallObject.iteration I κ) :=
      Functor.preservesColimitsOfShape_of_isCardinalAccessible
        (SmallObject.iteration I κ) μ J
    change PreservesColimitsOfShape J
      ((terminal.arrowFunctor C ⋙ SmallObject.iteration I κ) ⋙ Arrow.leftFunc)
    infer_instance

end CategoryTheory.SmallObject
