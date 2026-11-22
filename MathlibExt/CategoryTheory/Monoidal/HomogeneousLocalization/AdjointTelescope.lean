/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex
module

public import MathlibExt.CategoryTheory.Functor.CoaugmentationIteration
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# The actual beta adjoint and its current-stage telescope diagram

For the actual tensor/internal-Hom adjunction `L ⊣ R` and multiplication
`b : L ⟶ 𝟭 C`, the transition is the original adjunct `X ⟶ R.obj X`.
This construction requires no strict point-set inverse for the tensor
coordinate.  The current-stage diagram retains every original adjunct and
every original input arrow, without identifying the two differently ordered
coaugmentation iterations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory
open CategoryTheory.Functor.Iteration

namespace CategoryTheory.HomogeneousLocalization.AdjointTelescope

variable {C : Type u} [Category.{v} C] {L R : C ⥤ C}
  (a : L ⊣ R) (b : L ⟶ 𝟭 C)

/-- The actual beta adjunct retains the original tensor-Hom unit and the original beta map. -/
def coaugmentation : 𝟭 C ⟶ R :=
  a.unit ≫ Functor.whiskerRight b R ≫ R.leftUnitor.hom

theorem coaugmentation_app (X : C) :
    (coaugmentation a b).app X = a.unit.app X ≫ R.map (b.app X) := by
  simp only [coaugmentation, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.leftUnitor_hom_app, Functor.id_obj]
  exact congrArg (fun q => a.unit.app X ≫ q) (Category.comp_id (R.map (b.app X)))

/-- The entire transition is the original adjunction function at the actual coefficient action. -/
theorem coaugmentation_adjunct (X : C) :
    (coaugmentation a b).app X = a.homEquiv X X (b.app X) := by
  rw [coaugmentation_app, a.homEquiv_unit]

/-- Every original input arrow retains the whole beta-adjoint square. -/
theorem coaugmentation_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (coaugmentation a b).app Y = (coaugmentation a b).app X ≫ R.map f :=
  (coaugmentation a b).naturality f

section CurrentDiagram

variable {H : C ⥤ C} (η : 𝟭 C ⟶ H)

/-- The transition is the actual coaugmentation on the unchanged current stage. -/
def transition (n : ℕ) : iterate H n ⟶ iterate H (n + 1) := currentTransition η n

/-- The complete current-stage diagram keeps all original transition maps. -/
def diagram (X : C) : ℕ ⥤ C := currentDiagram η X

theorem diagram_obj (X : C) (n : ℕ) : (diagram η X).obj n = (iterate H n).obj X := rfl

theorem diagram_map_succ (X : C) (n : ℕ) :
    (diagram η X).map (homOfLE (Nat.le_succ n)) = η.app ((iterate H n).obj X) :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- Every original input arrow is kept at every actual current stage. -/
def diagramMap {X Y : C} (f : X ⟶ Y) : diagram η X ⟶ diagram η Y := currentDiagramMap η f

/-- All original identities and compositions remain in the actual diagram functor. -/
def diagramFunctor : C ⥤ (ℕ ⥤ C) := currentDiagramFunctor η

theorem diagramMap_app {X Y : C} (f : X ⟶ Y) (n : ℕ) :
    (diagramMap η f).app n = (iterate H n).map f := rfl

/-- The nonadjacent source maps retain their whole original naturality equations. -/
theorem diagramMap_naturality {X Y : C} (f : X ⟶ Y) {n m : ℕ} (q : n ⟶ m) :
    (diagram η X).map q ≫ (iterate H m).map f =
      (iterate H n).map f ≫ (diagram η Y).map q := (diagramMap η f).naturality q

end CurrentDiagram

/-- The actual beta diagram uses the actual tensor-Hom adjunct at each current stage. -/
def betaDiagramFunctor : C ⥤ (ℕ ⥤ C) := diagramFunctor (coaugmentation a b)

end CategoryTheory.HomogeneousLocalization.AdjointTelescope
