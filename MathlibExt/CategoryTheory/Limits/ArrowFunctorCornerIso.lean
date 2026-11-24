/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Limits.ChosenPullbackArrowIso

/-!
# Whole corners of naturally isomorphic Arrow functors

An actual natural isomorphism of Arrow functors retains both scalar
endpoint functions and both original naturality squares. These give
the whole Arrow isomorphism between the caller's two chosen corners.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe uC uD vC vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ArrowFunctorCornerIso

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {F G : C ⥤ Arrow D} (e : F ≅ G)
  {X Y : C} (f : X ⟶ Y)

/-- The actual full source endpoint isomorphism of the Arrow comparison. -/
def leftIso (X : C) : (F.obj X).left ≅ (G.obj X).left :=
  (Arrow.leftFunc : Arrow D ⥤ D).mapIso (e.app X)

/-- The actual full target endpoint isomorphism of the Arrow comparison. -/
def rightIso (X : C) : (F.obj X).right ≅ (G.obj X).right :=
  (Arrow.rightFunc : Arrow D ⥤ D).mapIso (e.app X)

theorem leftIso_hom (X : C) : (leftIso e X).hom = (e.hom.app X).left := by
  change (e.app X).hom.left = (e.hom.app X).left
  exact congrArg Arrow.Hom.left (Iso.app_hom e X)

theorem rightIso_hom (X : C) : (rightIso e X).hom = (e.hom.app X).right := by
  change (e.app X).hom.right = (e.hom.app X).right
  exact congrArg Arrow.Hom.right (Iso.app_hom e X)

theorem left_naturality :
    (F.map f).left ≫ (leftIso e Y).hom = (leftIso e X).hom ≫ (G.map f).left := by
  have h := congrArg Arrow.Hom.left (e.hom.naturality f)
  simpa only [Arrow.comp_left, leftIso_hom] using h

theorem right_naturality :
    (F.map f).right ≫ (rightIso e Y).hom = (rightIso e X).hom ≫ (G.map f).right := by
  have h := congrArg Arrow.Hom.right (e.hom.naturality f)
  simpa only [Arrow.comp_right, rightIso_hom] using h

/-- Each actual original Arrow component retains the entire
source-to-target comparison equation. -/
theorem component_square (X : C) :
    (F.obj X).hom ≫ (rightIso e X).hom = (leftIso e X).hom ≫ (G.obj X).hom :=
  (e.hom.app X).w.symm

section Chosen

variable {P Q : D}
  (fst : P ⟶ (F.obj X).right) (snd : P ⟶ (F.obj Y).left)
  (fst' : Q ⟶ (G.obj X).right) (snd' : Q ⟶ (G.obj Y).left)
  (pb : IsPullback fst snd (F.map f).right (F.obj Y).hom)
  (pb' : IsPullback fst' snd' (G.map f).right (G.obj Y).hom)

/-- The full given-corner point comparison follows from both actual
Arrow-functor endpoint naturalities and the original component square. -/
def pointIso : P ≅ Q :=
  ChosenPullbackArrowIso.pointIso fst snd (F.map f).right (F.obj Y).hom
    fst' snd' (G.map f).right (G.obj Y).hom pb pb'
    (rightIso e X) (leftIso e Y) (rightIso e Y)
    (right_naturality e f) (component_square e Y)

theorem pointIso_hom_first :
    (pointIso e f fst snd fst' snd' pb pb').hom ≫ fst' = fst ≫ (rightIso e X).hom :=
  ChosenPullbackArrowIso.pointIso_hom_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem pointIso_hom_second :
    (pointIso e f fst snd fst' snd' pb pb').hom ≫ snd' = snd ≫ (leftIso e Y).hom :=
  ChosenPullbackArrowIso.pointIso_hom_snd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem pointIso_inv_first :
    (pointIso e f fst snd fst' snd' pb pb').inv ≫ fst = fst' ≫ (rightIso e X).inv :=
  ChosenPullbackArrowIso.pointIso_inv_fst _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem pointIso_inv_second :
    (pointIso e f fst snd fst' snd' pb pb').inv ≫ snd = snd' ≫ (leftIso e Y).inv :=
  ChosenPullbackArrowIso.pointIso_inv_snd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

variable (φ : (F.obj X).left ⟶ P) (ψ : (G.obj X).left ⟶ Q)
  (hφ₁ : φ ≫ fst = (F.obj X).hom) (hφ₂ : φ ≫ snd = (F.map f).left)
  (hψ₁ : ψ ≫ fst' = (G.obj X).hom) (hψ₂ : ψ ≫ snd' = (G.map f).left)

include hφ₁ hψ₁ in
theorem firstEquation :
    (φ ≫ fst) ≫ (rightIso e X).hom = ((leftIso e X).hom ≫ ψ) ≫ fst' := by
  rw [hφ₁, Category.assoc, hψ₁]
  exact component_square e X

include hφ₂ hψ₂ in
theorem secondEquation :
    (φ ≫ snd) ≫ (leftIso e Y).hom = ((leftIso e X).hom ≫ ψ) ≫ snd' := by
  rw [hφ₂, Category.assoc, hψ₂]
  exact left_naturality e f

/-- The entire Arrow comparison retains both caller-selected corner
maps and both entire source/target functions of the original NatIso. -/
def arrowIso : Arrow.mk φ ≅ Arrow.mk ψ :=
  ChosenPullbackArrowIso.arrowIso fst snd (F.map f).right (F.obj Y).hom
    fst' snd' (G.map f).right (G.obj Y).hom pb pb'
    (rightIso e X) (leftIso e Y) (rightIso e Y)
    (right_naturality e f) (component_square e Y)
    φ ψ (leftIso e X)
    (firstEquation e fst fst' φ ψ hφ₁ hψ₁)
    (secondEquation e f snd snd' φ ψ hφ₂ hψ₂)

theorem arrowIso_hom_source :
    (arrowIso e f fst snd fst' snd' pb pb' φ ψ hφ₁ hφ₂ hψ₁ hψ₂).hom.left =
      (leftIso e X).hom := rfl

theorem arrowIso_inv_source :
    (arrowIso e f fst snd fst' snd' pb pb' φ ψ hφ₁ hφ₂ hψ₁ hψ₂).inv.left =
      (leftIso e X).inv := rfl

theorem arrowIso_hom_target :
    (arrowIso e f fst snd fst' snd' pb pb' φ ψ hφ₁ hφ₂ hψ₁ hψ₂).hom.right =
      (pointIso e f fst snd fst' snd' pb pb').hom := rfl

theorem arrowIso_inv_target :
    (arrowIso e f fst snd fst' snd' pb pb' φ ψ hφ₁ hφ₂ hψ₁ hψ₂).inv.right =
      (pointIso e f fst snd fst' snd' pb pb').inv := rfl

end Chosen

end CategoryTheory.ArrowFunctorCornerIso
