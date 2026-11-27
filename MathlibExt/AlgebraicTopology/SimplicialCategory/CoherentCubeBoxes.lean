/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMappingCube
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentOpenBox

/-!
# Actual distinguished-coordinate coherent open boxes

A supplied original coordinate is split off from the actual scalar cube
by explicit inverse maps. An upper open box in those actual coordinates
has an anodyne inclusion into the whole original cube and an actual Kan
extension retaining its entire original restriction. No enriched model,
fixed-face principle, or lifting outcome is an assumption.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.CubeBoxes
open MappingCube
variable {I : Type u} (j : I)

/-- The other supplied original cube coordinates, excluding exactly the distinguished label. -/
abbrev Remaining := {i : I // i ≠ j}

/-- The actual coordinate splitting map to the original other-coordinate cube and
distinguished interval. -/
def splitHom : cube I ⟶ cube (Remaining j) ⊗ Δ[1] :=
  CartesianMonoidalCategory.lift
    (Limits.Pi.lift (fun i : Remaining j => Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i.val))
    (Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) j)

/-- The actual inverse coordinate assembly, retaining every original label. -/
def assembleHom : cube (Remaining j) ⊗ Δ[1] ⟶ cube I := by
  classical
  exact Limits.Pi.lift (fun i : I => if hi : i = j then
    CartesianMonoidalCategory.snd _ _ else
      CartesianMonoidalCategory.fst _ _ ≫ Limits.Pi.π (fun _ : Remaining j =>
        (Δ[1] : SSet.{u})) ⟨i, hi⟩)

/-- The actual assembled distinguished coordinate is the original interval projection. -/
theorem assembleHom_self :
    assembleHom j ≫ Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) j =
      CartesianMonoidalCategory.snd _ _ := by
  classical
  simp [assembleHom]

/-- Every other assembled coordinate is the actual supplied original other-coordinate projection. -/
theorem assembleHom_other (i : Remaining j) :
    assembleHom j ≫ Limits.Pi.π (fun _ : I => (Δ[1] : SSet.{u})) i.val =
      CartesianMonoidalCategory.fst _ _ ≫ Limits.Pi.π (fun _ : Remaining j =>
        (Δ[1] : SSet.{u})) i := by
  classical
  simp [assembleHom, i.property]

/-- The actual full cube and its distinguished-coordinate scalar product are strictly isomorphic. -/
def splitIso : cube I ≅ cube (Remaining j) ⊗ Δ[1] where
  hom := splitHom j
  inv := assembleHom j
  hom_inv_id := by
    classical
    apply Limits.Pi.hom_ext
    intro i
    by_cases hi : i = j
    · subst i
      simp only [Category.assoc, assembleHom_self, splitHom,
        CartesianMonoidalCategory.lift_snd, Category.id_comp]
    · have ho := assembleHom_other j (⟨i, hi⟩ : Remaining j)
      rw [Category.assoc, ho, ← Category.assoc]
      simp only [splitHom, CartesianMonoidalCategory.lift_fst, Limits.Pi.lift_comp_π,
        Category.id_comp]
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, splitHom, CartesianMonoidalCategory.lift_fst]
      apply Limits.Pi.hom_ext
      intro i
      simp only [Category.assoc, Limits.Pi.lift_comp_π, assembleHom_other, Category.id_comp]
    · simp only [Category.assoc, splitHom, CartesianMonoidalCategory.lift_snd, assembleHom_self,
        Category.id_comp]

/-- The actual distinguished-coordinate open-box domain in its concrete scalar product chart. -/
abbrev boxDomain (A : (cube (Remaining j)).Subcomplex) : SSet.{u} := OpenBox.upper A

/-- Its actual inclusion into the whole original cube, through the proved inverse coordinate
chart. -/
def boxι (A : (cube (Remaining j)).Subcomplex) : boxDomain j A ⟶ cube I :=
  (OpenBox.upper A).ι ≫ (splitIso j).inv

/-- This actual coherent cube inclusion is an anodyne extension by genuine scalar
pushout-product geometry. -/
theorem boxι_anodyne (A : (cube (Remaining j)).Subcomplex) : SSet.anodyneExtensions (boxι j A) :=
  MorphismProperty.comp_mem SSet.anodyneExtensions _ _ (OpenBox.upper_anodyne A)
    (SSet.anodyneExtensions.of_isIso _)

/-- An actual distinguished-coordinate box map into a Kan complex extends on the whole
original coherent cube. -/
theorem exists_fill {Y : SSet.{u}} [SSet.KanComplex Y]
    (A : (cube (Remaining j)).Subcomplex) (f : boxDomain j A ⟶ Y) :
    ∃ g : cube I ⟶ Y, boxι j A ≫ g = f := by
  refine ⟨(splitIso j).hom ≫ OpenBox.fill A f, ?_⟩
  change ((OpenBox.upper A).ι ≫ (splitIso j).inv) ≫ ((splitIso j).hom ≫ OpenBox.fill A f) = f
  rw [Category.assoc, ← Category.assoc (splitIso j).inv (splitIso j).hom,
    Iso.inv_hom_id, Category.id_comp, OpenBox.fill_restrict]

end CategoryTheory.CoherentRealization.CubeBoxes
