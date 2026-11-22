/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.Basic

/-!
# Repointing native pointed CGWH spaces

The selected point and the carrier map with its given point equation define
repointing directly in the undercategory of the native point. The original
constant-point map, carrier functions and pointed identity and composition
formulas are retained.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Topology
open scoped ContinuousMap

namespace PointedCGWH

/-- The selected point of a pointed CGWH space. -/
def basepoint (X : PointedCGWH.{u, v}) : X.right :=
  X.hom (show CGWH.point.{u, v} from PUnit.unit)

/-- A pointed morphism carries the selected point to the selected point. -/
@[simp]
theorem map_basepoint {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    f.right (basepoint X) = basepoint Y := by
  change f.right (X.hom PUnit.unit) = Y.hom PUnit.unit
  exact ConcreteCategory.congr_hom (Under.w f)
    (show CGWH.point.{u, v} from PUnit.unit)

private def pointMap (B : CGWH.{u, v}) (b : B) :
    CGWH.point.{u, v} ⟶ B :=
  ConcreteCategory.ofHom (ContinuousMap.const _ b)

/-- A native CGWH space pointed at a specified element. -/
noncomputable abbrev pointedAt (B : CGWH.{u, v}) (b : B) :
    PointedCGWH.{u, v} :=
  Under.mk (pointMap B b)

/-- The selected point of a repointed object is the specified element. -/
@[simp]
theorem pointedAt_basepoint (B : CGWH.{u, v}) (b : B) :
    basepoint (pointedAt B b) = b :=
  rfl

/-- The whole repointed carrier family is the supplied native space. -/
theorem pointedAt_right_whole (B : CGWH.{u, v}) :
    (fun b : B => (pointedAt B b).right) = (fun _ => B) := rfl

/-- The selected point map is the actual inverse of the native point equivalence. -/
theorem pointedAt_hom_eq_pointHomEquiv_symm (B : CGWH.{u, v}) (b : B) :
    (pointedAt B b).hom = (CGWH.pointHomEquiv B).symm b := by
  apply ConcreteCategory.hom_ext
  intro p
  exact (CGWH.pointHomEquiv_symm_apply_apply B b p).symm

/-- The entire canonical repointing function retains the native point-equivalence formula. -/
theorem pointedAt_whole_value :
    (fun (B : CGWH.{u, v}) (b : B) => pointedAt B b) =
      (fun B b => Under.mk ((CGWH.pointHomEquiv B).symm b)) := by
  funext B b
  exact congrArg (fun f : CGWH.point.{u, v} ⟶ B => Under.mk f)
    (pointedAt_hom_eq_pointHomEquiv_symm B b)

/-- Repointing a pointed object at its selected point recovers it. -/
noncomputable def pointedAtBasepointIso (X : PointedCGWH.{u, v}) :
    pointedAt X.right (basepoint X) ≅ X :=
  Under.isoMk (Iso.refl X.right) (by
    change pointMap X.right (basepoint X) ≫ 𝟙 X.right = X.hom
    rw [Category.comp_id]
    apply ConcreteCategory.hom_ext
    intro p
    change basepoint X = X.hom p
    change X.hom PUnit.unit = X.hom p
    cases p
    rfl)

/-- A carrier map with a specified point equation gives the canonical pointed morphism. -/
def pointedAtMap {B C : CGWH.{u, v}} (f : B ⟶ C) (b : B) (c : C) (h : f b = c) :
    pointedAt B b ⟶ pointedAt C c :=
  Under.homMk f (by
    apply ConcreteCategory.hom_ext
    intro p
    exact h)

/-- The complete pointed-map family retains its original carrier map. -/
theorem pointedAtMap_right_whole {B C : CGWH.{u, v}} (f : B ⟶ C) :
    (fun (b : B) (c : C) (h : f b = c) => (pointedAtMap f b c h).right) =
      (fun _ _ _ => f) := rfl

/-- The canonical pointed identity retains the actual given point. -/
theorem pointedAtMap_id (B : CGWH.{u, v}) (b : B) :
    pointedAtMap (𝟙 B) b b rfl = 𝟙 (pointedAt B b) := by
  apply (Under.forget CGWH.point.{u, v}).map_injective
  rfl

/-- Pointed composition retains both complete carrier maps and the supplied point equations. -/
theorem pointedAtMap_comp {B C D : CGWH.{u, v}} (f : B ⟶ C) (g : C ⟶ D)
    (b : B) (c : C) (d : D) (hf : f b = c) (hg : g c = d) :
    pointedAtMap f b c hf ≫ pointedAtMap g c d hg =
      pointedAtMap (f ≫ g) b d ((congrArg g hf).trans hg) := by
  apply (Under.forget CGWH.point.{u, v}).map_injective
  rfl

end PointedCGWH
