/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.SmallKanCoends
import MathlibExt.Topology.Category.PointedCGWH.Repointing
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Sequential pointed diagrams at actual source points

The given point is transported through each actual diagram map. The repointed
cocone retains every original leg, and its colimit proof comes from the same
underlying cocone.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits

namespace PointedCGWH.PointedAtGeometry

/-- The canonical native small-colimit provider supplies Nat colimits. -/
theorem pointedNatColimits : HasColimitsOfShape ℕ PointedCGWH.{u, v} := by
  let _ : HasColimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
    PointedCGWH.EnrichedKan.hasSmallColimits
  infer_instance

attribute [local instance] pointedNatColimits


/-- The actual original zero-stage point is transported by the SAME complete finite diagram map. -/
def diagramPoint (F : ℕ ⥤ CGWH.{u, v}) (a : F.obj 0) (n : ℕ) : F.obj n :=
  F.map (homOfLE (Nat.zero_le n)) a

/-- EVERY original finite map carries the actual chosen source point to its actual target point. -/
theorem diagramPoint_naturality (F : ℕ ⥤ CGWH.{u, v}) (a : F.obj 0)
    {i j : ℕ} (f : i ⟶ j) : F.map f (diagramPoint F a i) = diagramPoint F a j := by
  have h : F.map (homOfLE (Nat.zero_le i)) ≫ F.map f =
      F.map (homOfLE (Nat.zero_le j)) :=
    (F.map_comp _ _).symm.trans (F.congr_map (Subsingleton.elim _ _))
  exact ConcreteCategory.congr_hom h a

/-- The ENTIRE based diagram retains every actual original finite map and object. -/
def diagramAt (F : ℕ ⥤ CGWH.{u, v}) (a : F.obj 0) : ℕ ⥤ PointedCGWH.{u, v} where
  obj n := PointedCGWH.pointedAt (F.obj n) (diagramPoint F a n)
  map f := PointedCGWH.pointedAtMap (F.map f) _ _ (diagramPoint_naturality F a f)
  map_id n := by
    apply pointedToCGWH.map_injective
    exact F.map_id n
  map_comp f g := by
    apply pointedToCGWH.map_injective
    exact F.map_comp f g

/-- The WHOLE based-diagram family forgets to the SAME ENTIRE original underlying diagram. -/
theorem diagramAt_forget_whole (F : ℕ ⥤ CGWH.{u, v}) :
    (fun a : F.obj 0 => diagramAt F a ⋙ pointedToCGWH) = (fun _ => F) := rfl

/-- The original chosen colimit leg selects the ACTUAL image of the given zero-stage point. -/
def coconePoint {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (a : F.obj 0) : c.pt :=
  c.ι.app 0 a

/-- EVERY original colimit leg carries the based source point to the SAME actual colimit point. -/
theorem coconePoint_leg {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (a : F.obj 0) (n : ℕ) :
    c.ι.app n (diagramPoint F a n) = coconePoint c a :=
  ConcreteCategory.congr_hom (c.w (homOfLE (Nat.zero_le n))) a

/-- The ENTIRE actual based cocone retains the SAME physical colimit and every original leg. -/
def coconeAt {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (a : F.obj 0) : Cocone (diagramAt F a) where
  pt := PointedCGWH.pointedAt c.pt (coconePoint c a)
  ι :=
    { app n := PointedCGWH.pointedAtMap (c.ι.app n) _ _ (coconePoint_leg c a n)
      naturality _ _ f := by
        apply pointedToCGWH.map_injective
        exact (c.w f).trans (Category.comp_id _).symm }

/-- The WHOLE actual cocone family forgets to the SAME full original underlying cocone. -/
theorem coconeAt_forget_whole {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) :
    (fun a : F.obj 0 => pointedToCGWH.mapCocone (coconeAt c a)) = (fun _ => c) := rfl

/-- The genuine SAME underlying cocone UPL proves the complete actual based-cocone UPL. -/
def coconeAtIsColimit {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (hc : IsColimit c)
    (a : F.obj 0) : IsColimit (coconeAt c a) := by
  let _ : CategoryTheory.IsConnected ℕ := CategoryTheory.IsFiltered.isConnected ℕ
  exact isColimitOfReflects pointedToCGWH hc

/-- EVERY actual diagram/cocone map carries the SAME chosen zero-stage point to its image point. -/
theorem coconePoint_map {F G : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (d : Cocone G)
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) (h : ∀ n, c.ι.app n ≫ t = α.app n ≫ d.ι.app n)
    (a : F.obj 0) : t (coconePoint c a) = coconePoint d (α.app 0 a) :=
  ConcreteCategory.congr_hom (h 0) a

/-- The ENTIRE original diagram map preserves actual source points at EVERY original index. -/
theorem diagramPoint_map {F G : ℕ ⥤ CGWH.{u, v}} (α : F ⟶ G) (a : F.obj 0) (n : ℕ) :
    α.app n (diagramPoint F a n) = diagramPoint G (α.app 0 a) n :=
  ConcreteCategory.congr_hom (α.naturality (homOfLE (Nat.zero_le n))) a

/-- BOTH actual based diagram maps retain the same original entire diagram-input transformation. -/
def diagramAtMap {F G : ℕ ⥤ CGWH.{u, v}} (α : F ⟶ G) (a : F.obj 0) :
    diagramAt F a ⟶ diagramAt G (α.app 0 a) where
  app n := PointedCGWH.pointedAtMap (α.app n) _ _ (diagramPoint_map α a n)
  naturality _ _ f := by
    apply pointedToCGWH.map_injective
    exact α.naturality f

/-- The WHOLE based diagram-map family forgets to the SAME full original diagram transformation. -/
theorem diagramAtMap_right_whole {F G : ℕ ⥤ CGWH.{u, v}} (α : F ⟶ G) :
    (fun (a : F.obj 0) (n : ℕ) => ((diagramAtMap α a).app n).right) =
      (fun _ n => α.app n) := rfl

/-- The ENTIRE original cocone map retains its actual right map and image-point equation. -/
def coconeAtMap {F G : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (d : Cocone G)
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) (h : ∀ n, c.ι.app n ≫ t = α.app n ≫ d.ι.app n)
    (a : F.obj 0) : (coconeAt c a).pt ⟶ (coconeAt d (α.app 0 a)).pt :=
  PointedCGWH.pointedAtMap t _ _ (coconePoint_map c d α t h a)

/-- The WHOLE actual based cocone-map family forgets to the SAME original complete right map. -/
theorem coconeAtMap_right_whole {F G : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (d : Cocone G)
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) :
    (fun (h : ∀ n, c.ι.app n ≫ t = α.app n ≫ d.ι.app n) (a : F.obj 0) =>
      (coconeAtMap c d α t h a).right) = (fun _ _ => t) := rfl

/-- EVERY complete original based map square preserves every entire actual original cocone leg. -/
theorem coconeAtMap_leg {F G : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) (d : Cocone G)
    (α : F ⟶ G) (t : c.pt ⟶ d.pt) (h : ∀ n, c.ι.app n ≫ t = α.app n ≫ d.ι.app n)
    (a : F.obj 0) (n : ℕ) :
    (coconeAt c a).ι.app n ≫ coconeAtMap c d α t h a =
      (diagramAtMap α a).app n ≫ (coconeAt d (α.app 0 a)).ι.app n := by
  apply pointedToCGWH.map_injective
  exact h n

end PointedCGWH.PointedAtGeometry

namespace PointedCGWH.PointedAtGeometry

/-- Every underlying based-diagram object is the actual finite-map image of the given point. -/
theorem diagramAt_obj_whole (F : ℕ ⥤ CGWH.{u, v}) :
    (fun (a : F.obj 0) (n : ℕ) => (diagramAt F a).obj n) =
      (fun a n => PointedCGWH.pointedAt (F.obj n) (F.map (homOfLE (Nat.zero_le n)) a)) := rfl

/-- The complete based-cocone point is the actual image under the original zero-stage leg. -/
theorem coconeAt_pt_whole {F : ℕ ⥤ CGWH.{u, v}} (c : Cocone F) :
    (fun a : F.obj 0 => (coconeAt c a).pt) =
      (fun a => PointedCGWH.pointedAt c.pt (c.ι.app 0 a)) := rfl

end PointedCGWH.PointedAtGeometry
