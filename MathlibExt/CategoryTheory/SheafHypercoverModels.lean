/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-!
# Actual boundary matching maps of sheaf hypercovers

The base is a specified native sheaf on a specified site. Every degree's
matching object is its actual relative limit over all boundary simplices.
The matching comparison is the native lift of the original simplex maps.
A hypercover requires these actual maps to be epimorphisms in every
degree. No extra object labelled a matching space is selected.

References: Stacks Project, Tag 01GZ; Scholze, arXiv:1709.07343v4,
Proposition 17.3; Anschuetz--Mann, arXiv:2403.01951v2, Theorem 1.1.
-/

@[expose] public noncomputable section

namespace MathlibExt.CategoryTheory.SheafHypercoverModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite

universe u v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (F : Sheaf J (Type 1))

/-- Actual simplicial sheaves augmented to the specified native base sheaf. -/
abbrev Diagram := SimplicialObject (Over F)

variable {F}

/-- Every actual simplex of the native boundary indexes the matching diagram. -/
def boundaryDiagram (H : Diagram F) (n : ℕ) :
    (SSet.boundary.{0} n).toSSet.Elements ⥤ Over F :=
  Functor.Elements.π (SSet.boundary.{0} n).toSSet ⋙ H

/-- The actual cone from the degree-n sheaf, with the original simplex maps. -/
def boundaryCone (H : Diagram F) (n : ℕ) : Cone (boundaryDiagram H n) where
  pt := H.obj (op (SimplexCategory.mk n))
  π.app x := H.map (((SSet.boundary.{0} n).ι.app x.obj x.val).down.op)
  π.naturality x y f := by
    change (𝟙 _) ≫ H.map (((SSet.boundary.{0} n).ι.app y.obj y.val).down.op) =
      H.map (((SSet.boundary.{0} n).ι.app x.obj x.val).down.op) ≫ H.map f.hom
    rw [Category.id_comp]
    symm
    rw [← H.map_comp]
    congr 1
    apply Quiver.Hom.unop_inj
    have h := congrArg (fun q ↦ q x.val) ((SSet.boundary.{0} n).ι.naturality f.hom)
    simp only [types_comp_apply, f.map_val] at h
    exact (congrArg ULift.down h).symm

/-- The actual relative boundary-matching object. -/
abbrev matchingObject (H : Diagram F) (n : ℕ) := limit (boundaryDiagram H n)

/-- The native matching comparison map, including degree zero. -/
def matchingMap (H : Diagram F) (n : ℕ) :
    H.obj (op (SimplexCategory.mk n)) ⟶ matchingObject H n :=
  limit.lift _ (boundaryCone H n)

/-- Its every boundary projection is the original actual simplex map. -/
theorem matchingMap_projection (H : Diagram F) (n : ℕ)
    (x : (SSet.boundary.{0} n).toSSet.Elements) :
    matchingMap H n ≫ limit.π (boundaryDiagram H n) x =
      H.map (((SSet.boundary.{0} n).ι.app x.obj x.val).down.op) := limit.lift_π _ _

/-- A hypercover by actual sheaves, with all native matching epimorphisms. -/
structure Hypercover (F : Sheaf J (Type 1)) where
  diagram : Diagram F
  covers : ∀ n : ℕ, Epi (matchingMap diagram n).left

end MathlibExt.CategoryTheory.SheafHypercoverModels
