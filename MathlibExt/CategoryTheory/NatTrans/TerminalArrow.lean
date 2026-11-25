/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
public import MathlibExt.CategoryTheory.NatTrans.PointwiseArrow

/-!
# Canonical terminal and initial arrow functors

The unique maps to a chosen terminal object form a natural transformation from
the identity functor to the constant terminal functor. Dually, the unique maps
from a chosen initial object form a natural transformation in the other direction.
Their pointwise arrows give canonical functors to the arrow category. A functor
preserving the chosen limit or colimit carries these arrow functors to canonically
isomorphic arrow functors.
-/

@[expose] public section

noncomputable section

namespace CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace terminal

variable (C : Type u₁) [Category.{v₁} C]

/-- The canonical natural transformation from the identity to the constant chosen terminal
object. -/
def fromNatTrans [HasTerminal C] :
    𝟭 C ⟶ (Functor.const C).obj (⊤_ C) where
  app X := terminal.from X
  naturality := by
    intro X Y f
    exact terminalIsTerminal.hom_ext _ _

@[simp]
theorem fromNatTrans_app [HasTerminal C] (X : C) :
    (fromNatTrans C).app X = terminal.from X := rfl

/-- The functor sending `X` to its canonical morphism `X ⟶ ⊤_ C`. -/
def arrowFunctor [HasTerminal C] : C ⥤ Arrow C :=
  NatTrans.arrow (fromNatTrans C)

@[simp] theorem arrowFunctor_obj_left [HasTerminal C] (X : C) :
    ((arrowFunctor C).obj X).left = X := rfl

@[simp] theorem arrowFunctor_obj_right [HasTerminal C] (X : C) :
    ((arrowFunctor C).obj X).right = ⊤_ C := rfl

@[simp] theorem arrowFunctor_obj_hom [HasTerminal C] (X : C) :
    ((arrowFunctor C).obj X).hom = terminal.from X := rfl

@[simp] theorem arrowFunctor_map_left [HasTerminal C] {X Y : C} (f : X ⟶ Y) :
    ((arrowFunctor C).map f).left = f := rfl

@[simp] theorem arrowFunctor_map_right [HasTerminal C] {X Y : C} (f : X ⟶ Y) :
    ((arrowFunctor C).map f).right = 𝟙 (⊤_ C) := rfl

end terminal

namespace initial

variable (C : Type u₁) [Category.{v₁} C]

/-- The canonical natural transformation from the constant chosen initial object to the identity. -/
def toNatTrans [HasInitial C] :
    (Functor.const C).obj (⊥_ C) ⟶ 𝟭 C where
  app X := initial.to X
  naturality := by
    intro X Y f
    exact initialIsInitial.hom_ext _ _

@[simp]
theorem toNatTrans_app [HasInitial C] (X : C) :
    (toNatTrans C).app X = initial.to X := rfl

/-- The functor sending `X` to its canonical morphism `⊥_ C ⟶ X`. -/
def arrowFunctor [HasInitial C] : C ⥤ Arrow C :=
  NatTrans.arrow (toNatTrans C)

@[simp] theorem arrowFunctor_obj_left [HasInitial C] (X : C) :
    ((arrowFunctor C).obj X).left = ⊥_ C := rfl

@[simp] theorem arrowFunctor_obj_right [HasInitial C] (X : C) :
    ((arrowFunctor C).obj X).right = X := rfl

@[simp] theorem arrowFunctor_obj_hom [HasInitial C] (X : C) :
    ((arrowFunctor C).obj X).hom = initial.to X := rfl

@[simp] theorem arrowFunctor_map_left [HasInitial C] {X Y : C} (f : X ⟶ Y) :
    ((arrowFunctor C).map f).left = 𝟙 (⊥_ C) := rfl

@[simp] theorem arrowFunctor_map_right [HasInitial C] {X Y : C} (f : X ⟶ Y) :
    ((arrowFunctor C).map f).right = f := rfl

end initial

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/-- The canonical comparison from mapped terminal arrows to terminal arrows of mapped objects. -/
def terminal.arrowFunctorComparisonNatTrans (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D] :
    terminal.arrowFunctor C ⋙ F.mapArrow ⟶ F ⋙ terminal.arrowFunctor D where
  app X := Arrow.homMk (𝟙 _) (terminalComparison F)
    (terminalIsTerminal.hom_ext _ _)
  naturality X Y f := by
    apply Arrow.hom_ext
    · change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
      simp
    · change F.map (𝟙 (⊤_ C)) ≫ terminalComparison F =
        terminalComparison F ≫ 𝟙 _
      simp

@[simp] theorem terminal.arrowFunctorComparisonNatTrans_app_left (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D] (X : C) :
    ((terminal.arrowFunctorComparisonNatTrans F).app X).left = 𝟙 (F.obj X) := rfl

@[simp] theorem terminal.arrowFunctorComparisonNatTrans_app_right (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D] (X : C) :
    ((terminal.arrowFunctorComparisonNatTrans F).app X).right = terminalComparison F := rfl

/-- For a terminal-preserving functor, the canonical terminal-arrow comparison is an isomorphism. -/
def terminal.arrowFunctorComparisonNatIso (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D]
    [PreservesLimit (Functor.empty.{0} C) F] :
    terminal.arrowFunctor C ⋙ F.mapArrow ≅ F ⋙ terminal.arrowFunctor D :=
  NatIso.ofComponents
    (fun X => Arrow.isoMk' (F.map (terminal.from X))
      (terminal.from (F.obj X)) (Iso.refl _) (PreservesTerminal.iso F)
      (terminalIsTerminal.hom_ext _ _))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
        simp
      · change F.map (𝟙 (⊤_ C)) ≫ (PreservesTerminal.iso F).hom =
          (PreservesTerminal.iso F).hom ≫ 𝟙 _
        simp)

@[simp] theorem terminal.arrowFunctorComparisonNatIso_hom (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D]
    [PreservesLimit (Functor.empty.{0} C) F] :
    (terminal.arrowFunctorComparisonNatIso F).hom =
      terminal.arrowFunctorComparisonNatTrans F := by
  apply NatTrans.ext
  funext X
  apply Arrow.hom_ext <;> rfl

@[simp] theorem terminal.arrowFunctorComparisonNatIso_hom_app_left (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D]
    [PreservesLimit (Functor.empty.{0} C) F] (X : C) :
    ((terminal.arrowFunctorComparisonNatIso F).hom.app X).left = 𝟙 (F.obj X) := rfl

@[simp] theorem terminal.arrowFunctorComparisonNatIso_hom_app_right (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D]
    [PreservesLimit (Functor.empty.{0} C) F] (X : C) :
    ((terminal.arrowFunctorComparisonNatIso F).hom.app X).right =
      (PreservesTerminal.iso F).hom := rfl

@[simp] theorem terminal.arrowFunctorComparisonNatIso_inv_app_left (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D]
    [PreservesLimit (Functor.empty.{0} C) F] (X : C) :
    ((terminal.arrowFunctorComparisonNatIso F).inv.app X).left = 𝟙 (F.obj X) := rfl

@[simp] theorem terminal.arrowFunctorComparisonNatIso_inv_app_right (F : C ⥤ D)
    [HasTerminal C] [HasTerminal D]
    [PreservesLimit (Functor.empty.{0} C) F] (X : C) :
    ((terminal.arrowFunctorComparisonNatIso F).inv.app X).right =
      (PreservesTerminal.iso F).inv := rfl

/-- The canonical comparison from initial arrows of mapped objects to mapped initial arrows. -/
def initial.arrowFunctorComparisonNatTrans (F : C ⥤ D)
    [HasInitial C] [HasInitial D] :
    F ⋙ initial.arrowFunctor D ⟶ initial.arrowFunctor C ⋙ F.mapArrow where
  app X := Arrow.homMk (initialComparison F) (𝟙 _)
    (initialIsInitial.hom_ext _ _)
  naturality X Y f := by
    apply Arrow.hom_ext
    · change 𝟙 _ ≫ initialComparison F =
        initialComparison F ≫ F.map (𝟙 (⊥_ C))
      simp
    · change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
      simp

@[simp] theorem initial.arrowFunctorComparisonNatTrans_app_left (F : C ⥤ D)
    [HasInitial C] [HasInitial D] (X : C) :
    ((initial.arrowFunctorComparisonNatTrans F).app X).left = initialComparison F := rfl

@[simp] theorem initial.arrowFunctorComparisonNatTrans_app_right (F : C ⥤ D)
    [HasInitial C] [HasInitial D] (X : C) :
    ((initial.arrowFunctorComparisonNatTrans F).app X).right = 𝟙 (F.obj X) := rfl

/-- For an initial-preserving functor, the canonical initial-arrow comparison is an isomorphism. -/
def initial.arrowFunctorComparisonNatIso (F : C ⥤ D)
    [HasInitial C] [HasInitial D]
    [PreservesColimit (Functor.empty.{0} C) F] :
    F ⋙ initial.arrowFunctor D ≅ initial.arrowFunctor C ⋙ F.mapArrow :=
  NatIso.ofComponents
    (fun X => Arrow.isoMk' (initial.to (F.obj X)) (F.map (initial.to X))
      (PreservesInitial.iso F).symm (Iso.refl _)
      (initialIsInitial.hom_ext _ _))
    (by
      intro X Y f
      apply Arrow.hom_ext
      · change 𝟙 _ ≫ (PreservesInitial.iso F).inv =
          (PreservesInitial.iso F).inv ≫ F.map (𝟙 (⊥_ C))
        simp
      · change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f
        simp)

@[simp] theorem initial.arrowFunctorComparisonNatIso_hom (F : C ⥤ D)
    [HasInitial C] [HasInitial D]
    [PreservesColimit (Functor.empty.{0} C) F] :
    (initial.arrowFunctorComparisonNatIso F).hom =
      initial.arrowFunctorComparisonNatTrans F := by
  apply NatTrans.ext
  funext X
  apply Arrow.hom_ext <;> rfl

@[simp] theorem initial.arrowFunctorComparisonNatIso_hom_app_left (F : C ⥤ D)
    [HasInitial C] [HasInitial D]
    [PreservesColimit (Functor.empty.{0} C) F] (X : C) :
    ((initial.arrowFunctorComparisonNatIso F).hom.app X).left =
      (PreservesInitial.iso F).inv := rfl

@[simp] theorem initial.arrowFunctorComparisonNatIso_hom_app_right (F : C ⥤ D)
    [HasInitial C] [HasInitial D]
    [PreservesColimit (Functor.empty.{0} C) F] (X : C) :
    ((initial.arrowFunctorComparisonNatIso F).hom.app X).right = 𝟙 (F.obj X) := rfl

@[simp] theorem initial.arrowFunctorComparisonNatIso_inv_app_left (F : C ⥤ D)
    [HasInitial C] [HasInitial D]
    [PreservesColimit (Functor.empty.{0} C) F] (X : C) :
    ((initial.arrowFunctorComparisonNatIso F).inv.app X).left =
      (PreservesInitial.iso F).hom := rfl

@[simp] theorem initial.arrowFunctorComparisonNatIso_inv_app_right (F : C ⥤ D)
    [HasInitial C] [HasInitial D]
    [PreservesColimit (Functor.empty.{0} C) F] (X : C) :
    ((initial.arrowFunctorComparisonNatIso F).inv.app X).right = 𝟙 (F.obj X) := rfl

end CategoryTheory.Limits
