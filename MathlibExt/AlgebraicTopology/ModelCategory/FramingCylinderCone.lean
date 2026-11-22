/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedOrdinaryCone
import MathlibExt.AlgebraicTopology.ModelCategory.PointedFramingAction

/-!
# Cones from the actual original good framing cylinder

Collapse the first endpoint of the original good cylinder on QX. The
remaining insertion retains the original second endpoint. Its weak
contraction is earned from the pushed-out trivial cofibration at the
first endpoint. The whole two-end boundary supplies the cofibration of
the remaining insertion, with its actual original pushout maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u v

open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace HomotopicalAlgebra.FramingCylinderCone

open OrdinaryHoChosenPuppe

attribute [local implicit_reducible] PointedFramingAction.leftCylinder

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (d : GeneratedFunctorialReplacements.Data (C := C)) (Z : C) (hZ : IsZero Z)

/-- The cylinder carrier is the same original first frame degree in every variable. -/
def cylinderFunctor : C ⥤ C :=
  PointedFramingAction.leftFrame d ⋙ (evaluation SimplexCategory C).obj ⦋1⦌

/-- The first original cylinder endpoint retains the complete Q and frame maps. -/
def first : d.Q ⟶ cylinderFunctor d where
  app X := (PointedFramingAction.leftCylinder d X).i₀
  naturality _ _ f := PointedFramingAction.leftCylinder_i₀_naturality d f

/-- The second original cylinder endpoint retains those same complete maps. -/
def second : d.Q ⟶ cylinderFunctor d where
  app X := (PointedFramingAction.leftCylinder d X).i₁
  naturality _ _ f := PointedFramingAction.leftCylinder_i₁_naturality d f

/-- The actual cone collapses only the first endpoint to the unchanged caller zero. -/
def cone : C ⥤ C where
  obj X := pushout ((first d).app X) (toZero Z hZ (d.Q.obj X))
  map {X Y} f := pushout.map ((first d).app X) (toZero Z hZ (d.Q.obj X))
    ((first d).app Y) (toZero Z hZ (d.Q.obj Y))
    ((cylinderFunctor d).map f) (𝟙 Z) (d.Q.map f)
    ((first d).naturality f).symm (hZ.isTerminal.hom_ext _ _)
  map_id X := by
    apply pushout.hom_ext
    · rw [pushout.inl_desc]
      exact (congrArg (fun a => a ≫ pushout.inl ((first d).app X)
          (toZero Z hZ (d.Q.obj X))) ((cylinderFunctor d).map_id X)).trans
        ((Category.id_comp _).trans (Category.comp_id _).symm)
    · rw [pushout.inr_desc]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  map_comp f g := by
    simp only [Functor.map_comp]
    rw [pushout.map_comp]
    simp only [Category.comp_id]

/-- The full original cylinder injects by the first chosen pushout leg. -/
def cylinderLeg (X : C) : (cylinderFunctor d).obj X ⟶ (cone d Z hZ).obj X :=
  pushout.inl _ _

/-- The actual zero object injects by the other original chosen pushout leg. -/
def zeroLeg (X : C) : Z ⟶ (cone d Z hZ).obj X := pushout.inr _ _

/-- The entire cone map retains every original cylinder map on its first leg. -/
theorem coneMap_cylinder {X Y : C} (f : X ⟶ Y) :
    cylinderLeg d Z hZ X ≫ (cone d Z hZ).map f =
      (cylinderFunctor d).map f ≫ cylinderLeg d Z hZ Y :=
  pushout.inl_desc _ _ _

/-- The entire cone map retains the unchanged original zero leg. -/
theorem coneMap_zero {X Y : C} (f : X ⟶ Y) :
    zeroLeg d Z hZ X ≫ (cone d Z hZ).map f = zeroLeg d Z hZ Y :=
  (pushout.inr_desc _ _ _).trans (Category.id_comp _)

/-- The remaining insertion is precisely the original second cylinder endpoint. -/
def inclusion : d.Q ⟶ cone d Z hZ where
  app X := (second d).app X ≫ cylinderLeg d Z hZ X
  naturality X Y f := by
    calc
      d.Q.map f ≫ ((second d).app Y ≫ cylinderLeg d Z hZ Y) =
          (d.Q.map f ≫ (second d).app Y) ≫ cylinderLeg d Z hZ Y :=
        (Category.assoc _ _ _).symm
      _ = ((second d).app X ≫ (cylinderFunctor d).map f) ≫ cylinderLeg d Z hZ Y :=
        congrArg (fun a => a ≫ cylinderLeg d Z hZ Y) ((second d).naturality f)
      _ = (second d).app X ≫ ((cylinderFunctor d).map f ≫ cylinderLeg d Z hZ Y) :=
        Category.assoc _ _ _
      _ = (second d).app X ≫ (cylinderLeg d Z hZ X ≫ (cone d Z hZ).map f) :=
        congrArg (fun a => (second d).app X ≫ a) (coneMap_cylinder d Z hZ f).symm
      _ = ((second d).app X ≫ cylinderLeg d Z hZ X) ≫ (cone d Z hZ).map f :=
        (Category.assoc _ _ _).symm

/-- The actual cone contracts to the unchanged original zero object. -/
def contraction : cone d Z hZ ⟶ (Functor.const C).obj Z where
  app X := toZero Z hZ ((cone d Z hZ).obj X)
  naturality _ _ _ := hZ.isTerminal.hom_ext _ _

/-- Collapsing the first cylinder endpoint gives an actual trivial-cofibration zero leg. -/
theorem zeroLeg_trivialCofibration (X : C) : trivialCofibrations C (zeroLeg d Z hZ X) := by
  let _ : IsCofibrant (d.Q.obj X) := d.q_cofibrant X
  let _ : Cofibration ((first d).app X) :=
    inferInstanceAs (Cofibration (PointedFramingAction.leftCylinder d X).i₀)
  let _ : WeakEquivalence ((first d).app X) :=
    inferInstanceAs (WeakEquivalence (PointedFramingAction.leftCylinder d X).i₀)
  exact (trivialCofibrations C).of_isPushout
    (IsPushout.of_hasPushout ((first d).app X) (toZero Z hZ (d.Q.obj X))).flip
    (mem_trivialCofibrations ((first d).app X))

/-- The weak contraction is earned from that same original pushed-out cylinder endpoint. -/
theorem contraction_weak (X : C) :
    weakEquivalences C ((contraction d Z hZ).app X) := by
  have h : zeroLeg d Z hZ X ≫ (contraction d Z hZ).app X = 𝟙 Z :=
    hZ.isTerminal.hom_ext _ _
  exact (weakEquivalences C).of_precomp _ _
    (zeroLeg_trivialCofibration d Z hZ X).2 (h.symm ▸ mem_weakEquivalences (𝟙 Z))

/-- Every original framed cone is cofibrant through its actual zero-source leg. -/
theorem cone_isCofibrant (X : C) : IsCofibrant ((cone d Z hZ).obj X) := by
  let _ : IsCofibrant Z :=
    (isCofibrant_iff_of_isInitial (𝟙 Z) hZ.isInitial).mpr (by infer_instance)
  let _ : Cofibration (zeroLeg d Z hZ X) :=
    (cofibration_iff _).mpr (zeroLeg_trivialCofibration d Z hZ X).1
  exact isCofibrant_of_cofibration (zeroLeg d Z hZ X)

/-- The full original good-cylinder boundary retains both original endpoint inclusions. -/
def boundary (X : C) : d.Q.obj X ⨿ d.Q.obj X ⟶ (cylinderFunctor d).obj X :=
  coprod.desc ((first d).app X) ((second d).app X)

/-- Collapse the first source copy through the actual zero and keep the second source copy. -/
def collapseBoundary (X : C) : d.Q.obj X ⨿ d.Q.obj X ⟶ d.Q.obj X :=
  coprod.desc (nullMap Z hZ (d.Q.obj X) (d.Q.obj X)) (𝟙 (d.Q.obj X))

/-- The whole original cylinder boundary and remaining inclusion form the actual cone square. -/
theorem boundary_square (X : C) :
    boundary d X ≫ cylinderLeg d Z hZ X =
      collapseBoundary d Z hZ X ≫ (inclusion d Z hZ).app X := by
  apply coprod.hom_ext
  · simp only [boundary, collapseBoundary, coprod.inl_desc_assoc]
    have hZero : fromZero Z hZ (d.Q.obj X) ≫ (inclusion d Z hZ).app X =
        zeroLeg d Z hZ X := hZ.isInitial.hom_ext _ _
    change (first d).app X ≫ cylinderLeg d Z hZ X =
      (toZero Z hZ (d.Q.obj X) ≫ fromZero Z hZ (d.Q.obj X)) ≫ (inclusion d Z hZ).app X
    rw [Category.assoc, hZero]
    exact pushout.condition
  · simp only [boundary, collapseBoundary, coprod.inr_desc_assoc, Category.id_comp]
    rfl

/-- Both original cylinder maps give the whole boundary pushout cocone. -/
def boundaryCocone (X : C) : PushoutCocone (boundary d X) (collapseBoundary d Z hZ X) :=
  PushoutCocone.mk (cylinderLeg d Z hZ X) ((inclusion d Z hZ).app X) (boundary_square d Z hZ X)

/-- The first original source copy in any full boundary cocone factors through the actual zero. -/
theorem boundaryCocone_first (X : C)
    (s : PushoutCocone (boundary d X) (collapseBoundary d Z hZ X)) :
    (first d).app X ≫ s.inl = toZero Z hZ (d.Q.obj X) ≫ fromZero Z hZ s.pt := by
  have h := congrArg (fun a => coprod.inl (X := d.Q.obj X) (Y := d.Q.obj X) ≫ a) s.condition
  have hFirst : (first d).app X ≫ s.inl = nullMap Z hZ (d.Q.obj X) (d.Q.obj X) ≫ s.inr := by
    simpa only [boundary, collapseBoundary, Category.assoc, coprod.inl_desc_assoc] using h
  exact hFirst.trans ((Category.assoc _ _ _).trans
    (congrArg (fun a => toZero Z hZ (d.Q.obj X) ≫ a) (fromZero_comp Z hZ s.inr)))

/-- The second original source copy in every full boundary cocone is unchanged. -/
theorem boundaryCocone_second (X : C)
    (s : PushoutCocone (boundary d X) (collapseBoundary d Z hZ X)) :
    (second d).app X ≫ s.inl = s.inr := by
  have h := congrArg (fun a => coprod.inr (X := d.Q.obj X) (Y := d.Q.obj X) ≫ a) s.condition
  simpa only [boundary, collapseBoundary, Category.assoc, coprod.inr_desc_assoc, Category.id_comp] using h

/-- The full boundary descent is the original first-endpoint pushout descent. -/
def boundaryDesc (X : C)
    (s : PushoutCocone (boundary d X) (collapseBoundary d Z hZ X)) :
    (cone d Z hZ).obj X ⟶ s.pt :=
  pushout.desc (f := (first d).app X) (g := toZero Z hZ (d.Q.obj X))
    s.inl (fromZero Z hZ s.pt) (boundaryCocone_first d Z hZ X s)

/-- The whole boundary descent retains the original cylinder leg. -/
theorem boundaryDesc_cylinder (X : C)
    (s : PushoutCocone (boundary d X) (collapseBoundary d Z hZ X)) :
    cylinderLeg d Z hZ X ≫ boundaryDesc d Z hZ X s = s.inl := pushout.inl_desc _ _ _

/-- The whole boundary descent retains the original remaining insertion leg. -/
theorem boundaryDesc_inclusion (X : C)
    (s : PushoutCocone (boundary d X) (collapseBoundary d Z hZ X)) :
    (inclusion d Z hZ).app X ≫ boundaryDesc d Z hZ X s = s.inr := by
  change ((second d).app X ≫ cylinderLeg d Z hZ X) ≫ boundaryDesc d Z hZ X s = s.inr
  rw [Category.assoc, boundaryDesc_cylinder]
  exact boundaryCocone_second d Z hZ X s

/-- The original cylinder restriction determines a full descent because the other source is zero. -/
theorem boundaryDesc_unique (X : C)
    (s : PushoutCocone (boundary d X) (collapseBoundary d Z hZ X))
    (m : (cone d Z hZ).obj X ⟶ s.pt)
    (hm : cylinderLeg d Z hZ X ≫ m = s.inl) : m = boundaryDesc d Z hZ X s := by
  apply pushout.hom_ext
  · exact hm.trans (boundaryDesc_cylinder d Z hZ X s).symm
  · exact hZ.isInitial.hom_ext _ _

/-- The full boundary pushout universal property is earned from the original first-endpoint pushout. -/
def boundaryIsColimit (X : C) : IsColimit (boundaryCocone d Z hZ X) :=
  PushoutCocone.IsColimit.mk (boundary_square d Z hZ X) (boundaryDesc d Z hZ X)
    (boundaryDesc_cylinder d Z hZ X) (boundaryDesc_inclusion d Z hZ X)
    (fun s m hm _ => boundaryDesc_unique d Z hZ X s m hm)

/-- The original whole good-cylinder boundary is a cofibration. -/
theorem boundary_cofibration (X : C) : cofibrations C (boundary d X) := by
  change cofibrations C (PointedFramingAction.leftCylinder d X).i
  exact mem_cofibrations _

/-- The remaining insertion is a cofibration by the constructed full boundary pushout. -/
theorem inclusion_cofibration (X : C) : cofibrations C ((inclusion d Z hZ).app X) :=
  (cofibrations C).of_isPushout (IsPushout.of_isColimit (boundaryIsColimit d Z hZ X)).flip
    (boundary_cofibration d X)

/-- The actual remaining insertion and contraction recover the original Q collapse. -/
theorem inclusion_contraction (X : C) :
    (inclusion d Z hZ).app X ≫ (contraction d Z hZ).app X = toZero Z hZ (d.Q.obj X) :=
  hZ.isTerminal.hom_ext _ _

end HomotopicalAlgebra.FramingCylinderCone
