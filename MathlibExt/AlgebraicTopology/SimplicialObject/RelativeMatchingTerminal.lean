/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module
public import MathlibExt.AlgebraicTopology.SimplicialObject.RelativeMatchingIso
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Relative matching arrows over the terminal simplicial object

The existing terminal matching comparison and all its public source,
target, inverse and morphism-property readbacks live in this neutral
module. The supplied coefficient category and original matching arrows
are retained, including degree zero.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialObject
variable {C : Type u} [Category.{v} C]

private def terminalSimplicialObjectObjIsTerminal
    [HasTerminal C] (d : SimplexCategoryᵒᵖ) :
    IsTerminal ((⊤_ (SimplicialObject C)).obj d) :=
  terminalIsTerminal.isTerminalObj
    ((evaluation SimplexCategoryᵒᵖ C).obj d) _

private def terminalMatchingCone
    [HasTerminal C] (n : ℕ) (Z : C) :
    Cone (matchingDiagram (⊤_ (SimplicialObject C)) n) where
  pt := Z
  π :=
    { app := fun a =>
        (terminalSimplicialObjectObjIsTerminal a.obj.right).from Z
      naturality := by
        intro a b f
        apply (terminalSimplicialObjectObjIsTerminal b.obj.right).hom_ext }

private def terminalMatchingObjectIsTerminal
    [HasTerminal C] (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    IsTerminal (matchingObject (⊤_ (SimplicialObject C)) n) :=
  IsTerminal.ofUniqueHom
    (fun Z => limit.lift _ (terminalMatchingCone n Z))
    (fun _ f => by
      apply limit.hom_ext
      intro a
      apply (terminalSimplicialObjectObjIsTerminal a.obj.right).hom_ext)

theorem terminalMatchingMapIsIso
    [HasTerminal C] (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    IsIso (matchingMap (⊤_ (SimplicialObject C)) n) :=
  isIso_of_isTerminal
    (terminalSimplicialObjectObjIsTerminal (op ⦋n⦌))
    (terminalMatchingObjectIsTerminal n) _

/-- The relative matching arrow of the literal terminal map is isomorphic to the
absolute matching arrow. Its target isomorphism is the SAME pullback second projection. -/
def relativeMatchingMapTerminalArrowIso
    [HasTerminal C] [HasPullbacks C] (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    Arrow.mk (relativeMatchingMap (terminal.from X) n) ≅
      Arrow.mk (matchingMap X n) := by
  let _ : IsIso (matchingMap (⊤_ (SimplicialObject C)) n) :=
    terminalMatchingMapIsIso n
  refine Arrow.isoMk (Iso.refl _)
    (asIso (pullback.snd
      (matchingMap (⊤_ (SimplicialObject C)) n)
      ((matchingObjectFunctor n).map (terminal.from X)))) ?_
  change 𝟙 _ ≫ matchingMap X n =
    relativeMatchingMap (terminal.from X) n ≫
      pullback.snd (matchingMap (⊤_ (SimplicialObject C)) n)
        ((matchingObjectFunctor n).map (terminal.from X))
  rw [Category.id_comp, relativeMatchingMap_snd]

/-- The forward source leg is literally the identity of the same degree component. -/
@[simp] theorem relativeMatchingMapTerminalArrowIso_hom_left
    [HasTerminal C] [HasPullbacks C] (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    (relativeMatchingMapTerminalArrowIso X n).hom.left = 𝟙 (X.obj (op ⦋n⦌)) :=
  rfl

/-- The forward target leg is the original pullback second projection. -/
@[simp] theorem relativeMatchingMapTerminalArrowIso_hom_right
    [HasTerminal C] [HasPullbacks C] (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    (relativeMatchingMapTerminalArrowIso X n).hom.right =
      pullback.snd (matchingMap (⊤_ (SimplicialObject C)) n)
        ((matchingObjectFunctor n).map (terminal.from X)) :=
  rfl

/-- The inverse retains the same degree-component identity. -/
@[simp] theorem relativeMatchingMapTerminalArrowIso_inv_left
    [HasTerminal C] [HasPullbacks C] (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    (relativeMatchingMapTerminalArrowIso X n).inv.left = 𝟙 (X.obj (op ⦋n⦌)) :=
  rfl

/-- The inverse square recovers the complete original relative matching map. -/
theorem relativeMatchingMapTerminalArrowIso_inv_square
    [HasTerminal C] [HasPullbacks C] (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    matchingMap X n ≫ (relativeMatchingMapTerminalArrowIso X n).inv.right =
      relativeMatchingMap (terminal.from X) n := by
  have h : matchingMap X n ≫ (relativeMatchingMapTerminalArrowIso X n).inv.right =
      𝟙 (X.obj (op ⦋n⦌)) ≫ relativeMatchingMap (terminal.from X) n :=
    (relativeMatchingMapTerminalArrowIso X n).inv.w.symm
  exact h.trans (CategoryTheory.Category.id_comp _)


/-- Any isomorphism-respecting class tests exactly the same absolute and relative
terminal matching arrows; no fibrancy or model existence is supplied. -/
theorem relativeMatchingMap_terminal_mem_iff
    [HasTerminal C] [HasPullbacks C] (P : MorphismProperty C) [P.RespectsIso]
    (X : SimplicialObject C) (n : ℕ)
    [HasLimitsOfShape (matchingIndex n) C] :
    P (relativeMatchingMap (terminal.from X) n) ↔ P (matchingMap X n) :=
  P.arrow_mk_iso_iff (relativeMatchingMapTerminalArrowIso X n)

end CategoryTheory.SimplicialObject
