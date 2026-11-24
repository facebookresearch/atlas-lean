/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomSuspensionGenerators
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentVertices

/-!
# Actual original unit and empty Hom objects of the simplicial suspension

The original free suspension has only its empty paths on either
individual object label and no reverse path. Its two whole diagonal
Hom objects are the actual tensor unit. The given simplicial generating
Hom is not quotiented or replaced by an assumed model.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite

namespace CategoryTheory.CoherentRealization.HomSuspensionUnits
open SimplicialQuiver HomSuspensionGenerators
variable (K : SSet.{u})

/-- Every original reverse free path would force the two distinct original suspension labels
to coincide. -/
theorem no_reverse {n : SimplexCategoryᵒᵖ}
    (p : SimplicialQuiver.Path (quiver K) n right left) : False :=
  left_ne_right (path_to_left K p).symm

/-- Every original free path beginning at the right label has no generator and ends at that
same original label. -/
theorem path_from_right {n : SimplexCategoryᵒᵖ} {a : Objects.{u}}
    (p : SimplicialQuiver.Path (quiver K) n right a) : a = right := by
  let _ : Quiver Objects.{u} := quiverAt (quiver K) n
  induction p with
  | nil => rfl
  | @cons b c p a ih =>
    subst b
    exact False.elim (no_generator_from_right K a)

/-- An actual free path on the right label is the original empty path. -/
theorem path_right_right {n : SimplexCategoryᵒᵖ}
    (p : SimplicialQuiver.Path (quiver K) n right right) :
    p = @Quiver.Path.nil Objects.{u} (quiverAt (quiver K) n) right := by
  let _ : Quiver Objects.{u} := quiverAt (quiver K) n
  cases p with
  | nil => rfl
  | @cons b c p a =>
    have hb := path_from_right K p
    subst b
    exact False.elim (no_generator_from_right K a)

/-- The whole actual free left diagonal Hom is the original simplicial tensor unit. -/
def leftUnitIso : 𝟙_ SSet.{u} ≅ freeHom (quiver K) left left where
  hom := freeId (quiver K) left
  inv := SimplicialEnrichment.toUnit _
  hom_inv_id := by ext n p; rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    exact (path_left_left K p).symm

/-- The whole actual free right diagonal Hom is the original simplicial tensor unit. -/
def rightUnitIso : 𝟙_ SSet.{u} ≅ freeHom (quiver K) right right where
  hom := freeId (quiver K) right
  inv := SimplicialEnrichment.toUnit _
  hom_inv_id := by ext n p; rfl
  inv_hom_id := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro p
    exact (path_right_right K p).symm

/-- The actual original reverse Hom is empty in every scalar degree. -/
def reverseEmptyIso : freeHom (quiver K) right left ≅ empty.{u} where
  hom := {
    app n := ↾fun p => False.elim (no_reverse K p)
    naturality n m f := by ext p; exact False.elim (no_reverse K p) }
  inv := {
    app n := ↾fun p => p.elim
    naturality n m f := by ext p; exact p.elim }
  hom_inv_id := by ext n p; exact False.elim (no_reverse K p)
  inv_hom_id := by ext n p; exact p.elim

end CategoryTheory.CoherentRealization.HomSuspensionUnits
