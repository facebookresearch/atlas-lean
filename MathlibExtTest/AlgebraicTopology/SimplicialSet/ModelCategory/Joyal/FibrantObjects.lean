/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.FibrantObjects

/-!
# Public consumers of the categorical fibrant-object criterion

These clients use the explicit genuine lifting class to extend maps into
quasicategories. Their statements require no model-category instance.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits SSet
open scoped Simplicial

namespace MathlibExtTest.Joyal.FibrantObjects

/-- A monic categorical equivalence admits strict extension into every quasicategory. -/
theorem strictExtension
    {A B C : SSet.{u}} (i : A ⟶ B) [Mono i] [Quasicategory C]
    (hi : categoricalEquivalences i) (f : A ⟶ C) :
    ∃ g : B ⟶ C, i ≫ g = f := by
  have hC : categoricalFibrations (terminal.from C) :=
    (categoricalFibrations.terminalFrom_iff_quasicategory C).mpr inferInstance
  let _ : HasLiftingProperty i (terminal.from C) :=
    (categoricalFibrations.mem_iff _).mp hC i inferInstance hi
  let sq : CommSq f i (terminal.from C) (terminal.from B) :=
    ⟨terminalIsTerminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- The reverse public criterion recovers quasicategory structure from genuine terminal RLP. -/
theorem quasicategoryOfTerminalRLP
    (X : SSet.{u}) (hX : categoricalFibrations (terminal.from X)) :
    Quasicategory X :=
  (categoricalFibrations.terminalFrom_iff_quasicategory X).mp hX

/-- The strict-extension API works with the standard one-simplex as target. -/
theorem deltaOneStrictExtension
    {A B : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : categoricalEquivalences i) (f : A ⟶ (Δ[1] : SSet.{u})) :
    ∃ g : B ⟶ (Δ[1] : SSet.{u}), i ≫ g = f :=
  strictExtension i hi f

end MathlibExtTest.Joyal.FibrantObjects
