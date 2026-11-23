/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.ClassifyingSpace.CGWH
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.Topology.Category.PointedCGWH.Basic

/-!
# Chosen-object pointed classifying spaces in CGWH

An object of a category determines a realized vertex of its native CGWH
classifying space. Functors preserve these chosen vertices strictly, giving
the exact basepoint equation needed for pointed morphisms.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory

variable {C D : Type u}
variable [Category.{v} C] [Category.{v} D]

/-- The point of the native classifying space represented by `c`. -/
noncomputable def classifyingSpaceCGWHPoint (c : C) :
    classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) :=
  SSet.realizedVertex (ComposableArrows.mk₀ c)

/-- The underlying-Top comparison sends the native point to the existing
realized vertex. -/
theorem classifyingSpaceCGWHPoint_toTop (c : C) :
    (classifyingSpaceCGWHToTopIso.{w, v, u}.app (Cat.of C)).hom
        (classifyingSpaceCGWHPoint.{w} c) =
      SSet.realizedVertex (ComposableArrows.mk₀ c) := by
  rfl

/-- Constant map from the native CGWH point. -/
noncomputable def classifyingSpaceCGWHBasepointMap (c : C) :
    CGWH.point.{w, max u v} ⟶
      classifyingSpaceCGWH.{w, v, u}.obj (Cat.of C) :=
  ConcreteCategory.ofHom
    (ContinuousMap.const _ (classifyingSpaceCGWHPoint.{w} c))

/-- The classifying space pointed at the object `c`. -/
noncomputable def classifyingSpaceCGWHPointed (c : C) :
    PointedCGWH.{w, max u v} :=
  Under.mk (classifyingSpaceCGWHBasepointMap.{w} c)

/-- The classifying-space map sends the chosen realized vertex to the
chosen realized vertex of the image object. -/
@[simp]
theorem classifyingSpaceCGWH_map_point (F : C ⥤ D) (c : C) :
    (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)
        (classifyingSpaceCGWHPoint.{w} c) =
      classifyingSpaceCGWHPoint.{w} (F.obj c) := by
  change SSet.toTop.map (CategoryTheory.nerveMap F)
      (SSet.realizedVertex (ComposableArrows.mk₀ c)) =
    SSet.realizedVertex (ComposableArrows.mk₀ (F.obj c))
  simpa only [CategoryTheory.nerveMap_app_mk₀] using
    (SSet.realizedVertex_naturality
      (CategoryTheory.nerveMap F) (ComposableArrows.mk₀ c)).symm

/-- The native basepoint map is strictly natural under a category
functor. -/
@[simp, reassoc]
theorem classifyingSpaceCGWH_basepointMap_naturality
    (F : C ⥤ D) (c : C) :
    classifyingSpaceCGWHBasepointMap.{w} c ≫
        classifyingSpaceCGWH.{w, v, u}.map F.toCatHom =
      classifyingSpaceCGWHBasepointMap.{w} (F.obj c) := by
  apply ConcreteCategory.hom_ext
  intro p
  change (classifyingSpaceCGWH.{w, v, u}.map F.toCatHom)
      (classifyingSpaceCGWHPoint.{w} c) =
    classifyingSpaceCGWHPoint.{w} (F.obj c)
  exact classifyingSpaceCGWH_map_point F c

end CategoryTheory
