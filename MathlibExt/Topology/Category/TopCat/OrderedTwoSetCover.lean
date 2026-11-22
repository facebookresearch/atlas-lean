/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.Subspace

/-!
# Ordered two-set covers

Coefficient-independent ordered two-set covers extracted from singular homology.
This is the topology-layer API used for abstract Mayer–Vietoris.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicTopology

universe w

/-- An ordered cover of a space by two subsets whose interiors cover. -/
structure OrderedTwoSetCover where
  X : TopCat.{w}
  left : Set X
  right : Set X
  interior_cover : (Set.univ : Set X) ⊆ interior left ∪ interior right

namespace OrderedTwoSetCover

/-- Morphisms of ordered two-set covers, given by an ambient map preserving each side. -/
structure Hom (C D : OrderedTwoSetCover.{w}) where
  f : C.X ⟶ D.X
  left_maps : Set.MapsTo f C.left D.left
  right_maps : Set.MapsTo f C.right D.right

@[ext]
theorem Hom.ext {C D : OrderedTwoSetCover.{w}} {f g : Hom C D} (h : f.f = g.f) : f = g := by
  rcases f with ⟨f, hf1, hf2⟩
  rcases g with ⟨g, hg1, hg2⟩
  simp_all

instance : Category (OrderedTwoSetCover.{w}) where
  Hom := Hom
  id C :=
    { f := 𝟙 C.X
      left_maps := fun _ hx => hx
      right_maps := fun _ hx => hx }
  comp f g :=
    { f := f.f ≫ g.f
      left_maps := fun _ hx => g.left_maps (f.left_maps hx)
      right_maps := fun _ hx => g.right_maps (f.right_maps hx) }
  id_comp f := Hom.ext (by simp)
  comp_id f := Hom.ext (by simp)
  assoc f g h := Hom.ext (by simp)

theorem interMaps {C D : OrderedTwoSetCover.{w}} (f : Hom C D) :
    Set.MapsTo f.f (C.left ∩ C.right) (D.left ∩ D.right) :=
  fun _ hx => ⟨f.left_maps hx.1, f.right_maps hx.2⟩

def spaceFunctor : OrderedTwoSetCover.{w} ⥤ TopCat.{w} where
  obj C := C.X
  map f := f.f
  map_id _ := rfl
  map_comp _ _ := rfl

noncomputable def leftFunctor : OrderedTwoSetCover.{w} ⥤ TopCat.{w} where
  obj C := TopCat.of C.left
  map f := subspaceMap f.f f.left_maps
  map_id _ := subspaceMap_id _
  map_comp _ _ := subspaceMap_comp

noncomputable def rightFunctor : OrderedTwoSetCover.{w} ⥤ TopCat.{w} where
  obj C := TopCat.of C.right
  map f := subspaceMap f.f f.right_maps
  map_id _ := subspaceMap_id _
  map_comp _ _ := subspaceMap_comp

noncomputable def interFunctor : OrderedTwoSetCover.{w} ⥤ TopCat.{w} where
  obj C := TopCat.of (C.left ∩ C.right : Set C.X)
  map f := subspaceMap f.f (interMaps f)
  map_id _ := subspaceMap_id _
  map_comp _ _ := subspaceMap_comp

@[simp]
lemma spaceFunctor_obj (C : OrderedTwoSetCover.{w}) : spaceFunctor.obj C = C.X :=
  rfl

@[simp]
lemma spaceFunctor_map {C D : OrderedTwoSetCover.{w}} (f : C ⟶ D) :
    spaceFunctor.map f = f.f :=
  rfl

@[simp]
lemma leftFunctor_obj (C : OrderedTwoSetCover.{w}) : leftFunctor.obj C = TopCat.of C.left :=
  rfl

@[simp]
lemma leftFunctor_map {C D : OrderedTwoSetCover.{w}} (f : C ⟶ D) :
    leftFunctor.map f = subspaceMap f.f f.left_maps :=
  rfl

@[simp]
lemma rightFunctor_obj (C : OrderedTwoSetCover.{w}) : rightFunctor.obj C = TopCat.of C.right :=
  rfl

@[simp]
lemma rightFunctor_map {C D : OrderedTwoSetCover.{w}} (f : C ⟶ D) :
    rightFunctor.map f = subspaceMap f.f f.right_maps :=
  rfl

@[simp]
lemma interFunctor_obj (C : OrderedTwoSetCover.{w}) :
    interFunctor.obj C = TopCat.of (C.left ∩ C.right : Set C.X) :=
  rfl

@[simp]
lemma interFunctor_map {C D : OrderedTwoSetCover.{w}} (f : C ⟶ D) :
    interFunctor.map f = subspaceMap f.f (interMaps f) :=
  rfl

noncomputable def interToLeft : interFunctor.{w} ⟶ leftFunctor.{w} where
  app C := subspaceInclOfSubset Set.inter_subset_left
  naturality _ _ _ := by
    apply TopCat.hom_ext
    ext x
    rfl

noncomputable def interToRight : interFunctor.{w} ⟶ rightFunctor.{w} where
  app C := subspaceInclOfSubset Set.inter_subset_right
  naturality _ _ _ := by
    apply TopCat.hom_ext
    ext x
    rfl

noncomputable def leftToSpace : leftFunctor.{w} ⟶ spaceFunctor.{w} where
  app C := subspaceIncl C.left
  naturality _ _ f := (subspaceMap_comp_subspaceIncl f.f f.left_maps).symm

noncomputable def rightToSpace : rightFunctor.{w} ⟶ spaceFunctor.{w} where
  app C := subspaceIncl C.right
  naturality _ _ f := (subspaceMap_comp_subspaceIncl f.f f.right_maps).symm

@[simp]
lemma interToLeft_app (C : OrderedTwoSetCover.{w}) :
    interToLeft.app C = subspaceInclOfSubset Set.inter_subset_left :=
  rfl

@[simp]
lemma interToRight_app (C : OrderedTwoSetCover.{w}) :
    interToRight.app C = subspaceInclOfSubset Set.inter_subset_right :=
  rfl

@[simp]
lemma leftToSpace_app (C : OrderedTwoSetCover.{w}) :
    leftToSpace.app C = subspaceIncl C.left :=
  rfl

@[simp]
lemma rightToSpace_app (C : OrderedTwoSetCover.{w}) :
    rightToSpace.app C = subspaceIncl C.right :=
  rfl

end OrderedTwoSetCover

end AlgebraicTopology
