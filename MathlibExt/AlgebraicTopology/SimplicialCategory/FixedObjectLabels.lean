/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjects
import Mathlib.CategoryTheory.MorphismProperty.Basic

/-!
# Individual label and original-Hom readback in the fixed-object fiber

The fiber equality gives inverse maps between individual labels and
original vertices. Every fiber arrow is consequently bijective on
objects. Its evaluated Hom map differs from the original Hom map only
by the actual target equality isomorphism.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.FixedObjects

variable {O : Type u}

/-- Read the supplied individual label of an original vertex. -/
def label (C : FixedObjects O) (a : C.val) : O := (eqToHom C.property) a

/-- Reading and restoring a label returns exactly the original vertex. -/
@[simp]
theorem vertex_label (C : FixedObjects O) (a : C.val) : vertex C (label C a) = a := by
  have h : eqToHom C.property ≫ eqToHom C.property.symm =
      𝟙 (forgetObjects.obj C.val) := by simp
  exact congrArg (fun k => k a) h

/-- Restoring and reading a label returns exactly that same label. -/
@[simp]
theorem label_vertex (C : FixedObjects O) (x : O) : label C (vertex C x) = x := by
  have h : eqToHom C.property.symm ≫ eqToHom C.property = 𝟙 O := by simp
  exact congrArg (fun k => k x) h

/-- The actual equivalence of individual labels with original vertices, without a quotient. -/
def verticesEquiv (C : FixedObjects O) : O ≃ C.val where
  toFun := vertex C
  invFun := label C
  left_inv := label_vertex C
  right_inv := vertex_label C

/-- The original object function preserves its supplied label exactly. -/
theorem map_label {C D : FixedObjects O} (F : C ⟶ D) (a : C.val) :
    label D (F.val.obj a) = label C a := by
  have h := congrArg (label D) (map_vertex F (label C a))
  simpa only [vertex_label, label_vertex] using h

/-- Identity-on-label maps are actually bijective on the original object types. -/
theorem objects_bijective {C D : FixedObjects O} (F : C ⟶ D) :
    Function.Bijective F.val.obj := by
  constructor
  · intro a b h
    apply (verticesEquiv C).symm.injective
    change label C a = label C b
    exact (map_label F a).symm.trans ((congrArg (label D) h).trans (map_label F b))
  · intro b
    refine ⟨vertex C (label D b), ?_⟩
    exact (map_vertex F (label D b)).trans (vertex_label D b)

/-- Any isomorphism-invariant scalar property is unchanged by the actual Hom endpoint transport. -/
theorem homMap_property_iff (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    {C D : FixedObjects O} (F : C ⟶ D) (x y : O) :
    P (homMap F x y) ↔ P (F.val.map (vertex C x) (vertex C y)) :=
  P.cancel_right_of_respectsIso (F.val.map (vertex C x) (vertex C y))
    (eqToHom (by rw [map_vertex F x, map_vertex F y]))

/-- Evaluation tests every original Hom, not only selected representatives or object classes. -/
theorem all_homMap_property_iff (P : MorphismProperty SSet.{u}) [P.RespectsIso]
    {C D : FixedObjects O} (F : C ⟶ D) :
    (∀ x y : O, P (homMap F x y)) ↔ ∀ a b : C.val, P (F.val.map a b) := by
  constructor
  · intro h a b
    obtain ⟨x, hx⟩ := (verticesEquiv C).surjective a
    obtain ⟨y, hy⟩ := (verticesEquiv C).surjective b
    subst a
    subst b
    exact (homMap_property_iff P F x y).mp (h x y)
  · intro h x y
    exact (homMap_property_iff P F x y).mpr (h (vertex C x) (vertex C y))

end CategoryTheory.SimplicialEnrichment.FixedObjects
