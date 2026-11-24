/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.MorphismProperty.Factorization
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import MathlibExt.CategoryTheory.NatTrans.PointwiseArrowPreservation

/-!
# The same native functorial factorization on original terminal arrows

Factor the supplied original terminal map functorially. The original
middle objects and left factor maps form the replacement functor and its
unit. The same right factor gives its original terminal lifting property.
This is a category-neutral application of actual factorization data;
no model category or weak-class conclusion is assumed.
-/

noncomputable section
universe w v u
open CategoryTheory Limits

namespace CategoryTheory.Arrow

/-- Original terminal maps form a functor with the same source maps and identity terminal
component. -/
private def toIsTerminalFunctor {C : Type u} [Category.{v} C] {T : C} (hT : IsTerminal T) :
  C ⥤ Arrow C := by
  let t : 𝟭 C ⟶ (Functor.const C).obj T :=
    { app X := hT.from X
      naturality X Y f := hT.hom_ext _ _ }
  exact NatTrans.arrow t

/-- The actual terminal-arrow functor preserves cardinal-filtered colimits without a bound
on the terminal object. -/
private theorem toIsTerminalFunctor_isCardinalAccessible {C : Type u} [Category.{v} C]
    {T : C} (hT : IsTerminal T) (κ : Cardinal.{w}) [Fact κ.IsRegular]
    : (toIsTerminalFunctor hT).IsCardinalAccessible κ := by
  let t : 𝟭 C ⟶ (Functor.const C).obj T :=
    { app X := hT.from X
      naturality X Y f := hT.hom_ext _ _ }
  let _ : ((Functor.const C).obj T).IsCardinalAccessible κ := inferInstance
  change (NatTrans.arrow t).IsCardinalAccessible κ
  exact NatTrans.arrow_isCardinalAccessible t κ

end CategoryTheory.Arrow

namespace CategoryTheory.MorphismProperty.FunctorialFactorizationData

variable {C : Type u} [Category.{v} C] {L R : MorphismProperty C}
    (d : FunctorialFactorizationData L R) {T : C} (hT : IsTerminal T)

/-- The actual replacement functor is the original middle factor on the same terminal arrows. -/
def terminalReplacementFunctor : C ⥤ C := Arrow.toIsTerminalFunctor hT ⋙ d.Z

/-- The original native left factor components form the same replacement unit. -/
def terminalReplacementUnit : 𝟭 C ⟶ d.terminalReplacementFunctor hT where
  app X := d.i.app ((Arrow.toIsTerminalFunctor hT).obj X)
  naturality _ _ f := d.i.naturality ((Arrow.toIsTerminalFunctor hT).map f)

/-- The actual native replacement unit belongs to the same proved left class. -/
theorem terminalReplacementUnit_mem_left (X : C) : L ((d.terminalReplacementUnit hT).app X) :=
  d.hi ((Arrow.toIsTerminalFunctor hT).obj X)

/-- The actual native replacement target has the original terminal map in the same proved
right class. -/
theorem terminalReplacement_mem_right (X : C) :
    R (hT.from ((d.terminalReplacementFunctor hT).obj X)) := by
  have h : d.p.app ((Arrow.toIsTerminalFunctor hT).obj X) =
      hT.from ((d.terminalReplacementFunctor hT).obj X) := hT.hom_ext _ _
  exact h ▸ d.hp ((Arrow.toIsTerminalFunctor hT).obj X)

/-- Accessibility of the same native middle factor gives accessibility of its actual
terminal replacement functor. -/
theorem terminalReplacementFunctor_isCardinalAccessible (κ : Cardinal.{w}) [Fact κ.IsRegular]
    [d.Z.IsCardinalAccessible κ] :
    (d.terminalReplacementFunctor hT).IsCardinalAccessible κ := by
  let _ : (Arrow.toIsTerminalFunctor hT).IsCardinalAccessible κ :=
    Arrow.toIsTerminalFunctor_isCardinalAccessible hT κ
  dsimp only [terminalReplacementFunctor]
  infer_instance

end CategoryTheory.MorphismProperty.FunctorialFactorizationData
