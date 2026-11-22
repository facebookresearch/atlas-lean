/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.BasedFiber
import MathlibExt.Topology.Category.PointedCGWH.Zero
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The literal pointed native strict fiber, with its full universal property

The fiber object is exactly the supplied native CGWH pullback, pointed by
the original total-space basepoint. Both projections and every map of
pointed arrows retain the original CGWH projections and chosen points.
The complete pointed pullback universal property is proved from the native
CGWH pullback, rather than postulated as fiber comparison data.

This is the level endpoint for evaluating a chosen original spectrum fiber.
The literal point object is retained explicitly, without identifying a
different chosen zero object by definitional equality.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits

namespace PointedCGWH.StrictFiberGeometry

/-- The literal pointed native point, with its identity basepoint. -/
abbrev pointObject : PointedCGWH.{u, v} := Under.mk (𝟙 CGWH.point.{u, v})

/-- The original pointed point is initial, by the undercategory construction. -/
def pointObjectIsInitial : IsInitial pointObject.{u, v} := Under.mkIdInitial

/-- The same literal pointed point is terminal. -/
def pointObjectIsTerminal : IsTerminal pointObject.{u, v} :=
  IsTerminal.ofUniqueHom
    (fun X => Under.homMk (CGWH.point_isTerminal.from X.right)
      (CGWH.point_isTerminal.hom_ext _ _))
    (fun _ f => Under.UnderMorphism.ext (CGWH.point_isTerminal.hom_ext f.right _))

/-- The map from the literal point has exactly the target's chosen basepoint. -/
def fromPoint (X : PointedCGWH.{u, v}) : pointObject ⟶ X :=
  Under.homMk X.hom (Category.id_comp _)

/-- The collapse to the literal point is its unique pointed map. -/
def toPoint (X : PointedCGWH.{u, v}) : X ⟶ pointObject :=
  pointObjectIsTerminal.from X

/-- The original basepoint is preserved by every pointed morphism. -/
theorem fromPoint_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    fromPoint X ≫ f = fromPoint Y :=
  pointObjectIsInitial.hom_ext _ _

/-- The actual point collapse is natural for every pointed morphism. -/
theorem toPoint_naturality {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    f ≫ toPoint Y = toPoint X := pointObjectIsTerminal.hom_ext _ _

/-- The literal chosen fiber of a pointed arrow. -/
abbrev fiber {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) : PointedCGWH.{u, v} :=
  Under.mk (CGWH.strictFiberPoint f.right Y.hom X.hom (Under.w f))

/-- The full fiber projection retains the native total-space leg. -/
def fiberToTotal {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) : fiber f ⟶ X :=
  Under.homMk (CGWH.strictFiberToTotal f.right Y.hom)
    (CGWH.strictFiberPoint_toTotal f.right Y.hom X.hom (Under.w f))

/-- The full fiber collapse retains the native point leg. -/
def fiberToPoint {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) : fiber f ⟶ pointObject :=
  Under.homMk (CGWH.strictFiberToPoint f.right Y.hom)
    (CGWH.strictFiberPoint_toPoint f.right Y.hom X.hom (Under.w f))

/-- The forward total projection is the entire original native map. -/
theorem fiberToTotal_right {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (fiberToTotal f).right = CGWH.strictFiberToTotal f.right Y.hom := rfl

/-- The forward point projection is the entire original native collapse. -/
theorem fiberToPoint_right {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (fiberToPoint f).right = CGWH.strictFiberToPoint f.right Y.hom := rfl

/-- The chosen point of the pointed fiber is exactly the original native lift. -/
theorem fiber_hom {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    (fiber f).hom = CGWH.strictFiberPoint f.right Y.hom X.hom (Under.w f) := rfl

/-- The two original pointed projections satisfy the actual pullback equation. -/
theorem fiber_condition {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    fiberToTotal f ≫ f = fiberToPoint f ≫ fromPoint Y := by
  apply Under.UnderMorphism.ext
  exact CGWH.strictFiber_condition f.right Y.hom

/-- The native pointed fiber and its two actual projections form a pullback cone. -/
def fiberCone {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    PullbackCone f (fromPoint Y) :=
  PullbackCone.mk (fiberToTotal f) (fiberToPoint f) (fiber_condition f)

/-- The original CGWH lift of the whole underlying pointed cone. -/
def fiberLiftRight {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (s : PullbackCone f (fromPoint Y)) : s.pt.right ⟶ CGWH.strictFiber f.right Y.hom :=
  pullback.lift s.fst.right s.snd.right (by
    simpa only [Under.comp_right, fromPoint, Under.homMk_right] using
      congrArg (fun (q : s.pt ⟶ Y) => q.right) s.condition)

/-- The entire underlying native lift retains the original total projection. -/
theorem fiberLiftRight_fst {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (s : PullbackCone f (fromPoint Y)) :
    fiberLiftRight f s ≫ CGWH.strictFiberToTotal f.right Y.hom = s.fst.right :=
  pullback.lift_fst _ _ _

/-- The entire underlying native lift retains the original point projection. -/
theorem fiberLiftRight_snd {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (s : PullbackCone f (fromPoint Y)) :
    fiberLiftRight f s ≫ CGWH.strictFiberToPoint f.right Y.hom = s.snd.right :=
  pullback.lift_snd _ _ _

/-- Lift an arbitrary pointed cone by the original CGWH pullback lift. -/
def fiberLift {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (s : PullbackCone f (fromPoint Y)) : s.pt ⟶ fiber f :=
  Under.homMk (fiberLiftRight f s) (by
      rw [fiber_hom]
      apply pullback.hom_ext
      · rw [Category.assoc, fiberLiftRight_fst, CGWH.strictFiberPoint_toTotal]
        exact Under.w s.fst
      · rw [Category.assoc, fiberLiftRight_snd, CGWH.strictFiberPoint_toPoint]
        exact Under.w s.snd)

/-- The complete native lift preserves the actual total-space cone leg. -/
theorem fiberLift_fst {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (s : PullbackCone f (fromPoint Y)) :
    fiberLift f s ≫ fiberToTotal f = s.fst := by
  apply Under.UnderMorphism.ext
  exact fiberLiftRight_fst f s

/-- The complete native lift preserves the actual point cone leg. -/
theorem fiberLift_snd {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (s : PullbackCone f (fromPoint Y)) :
    fiberLift f s ≫ fiberToPoint f = s.snd := by
  apply Under.UnderMorphism.ext
  exact fiberLiftRight_snd f s

/-- The literal pointed native strict fiber has the full universal property. -/
def fiberConeIsLimit {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y) :
    IsLimit (fiberCone f) := by
  apply PullbackCone.IsLimit.mk (fiber_condition f)
  case lift => exact fiberLift f
  case fac_left => exact fiberLift_fst f
  case fac_right => exact fiberLift_snd f
  case uniq =>
    intro s m hm hn
    apply Under.UnderMorphism.ext
    apply pullback.hom_ext
    · exact (congrArg (fun (q : s.pt ⟶ X) => q.right) hm).trans
        (fiberLiftRight_fst f s).symm
    · exact (congrArg (fun (q : s.pt ⟶ pointObject) => q.right) hn).trans
        (fiberLiftRight_snd f s).symm

/-- A full pointed Arrow square gives the original pointed strict-fiber map. -/
def fiberMap {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiber F.hom ⟶ fiber G.hom :=
  PointedCGWH.strictFiberPointedMap (Under.w F.hom) (Under.w G.hom)
    q.left.right q.right.right
    (by simpa only [Under.comp_right] using
      congrArg (fun (p : F.left ⟶ G.right) => p.right) (Arrow.w q))
    (Under.w q.right) (Under.w q.left)

/-- Every fiber map retains the entire original total projection square. -/
theorem fiberMap_fst {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberMap q ≫ fiberToTotal G.hom = fiberToTotal F.hom ≫ q.left := by
  apply Under.UnderMorphism.ext
  exact CGWH.strictFiberMap_toTotal _ _ _ _

/-- Every fiber map retains the entire original point projection square. -/
theorem fiberMap_snd {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberMap q ≫ fiberToPoint G.hom = fiberToPoint F.hom := by
  apply Under.UnderMorphism.ext
  exact CGWH.strictFiberMap_toPoint _ _ _ _

/-- The full original chosen-basepoint native fiber construction is a functor. -/
def fiberFunctor : Arrow PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} where
  obj F := fiber F.hom
  map q := fiberMap q
  map_id F := by
    apply PullbackCone.IsLimit.hom_ext (fiberConeIsLimit F.hom)
    · change fiberMap (𝟙 F) ≫ fiberToTotal F.hom = 𝟙 _ ≫ fiberToTotal F.hom
      rw [fiberMap_fst, Category.id_comp]
      exact Category.comp_id _
    · change fiberMap (𝟙 F) ≫ fiberToPoint F.hom = 𝟙 _ ≫ fiberToPoint F.hom
      rw [fiberMap_snd, Category.id_comp]
  map_comp {F G H} q r := by
    apply PullbackCone.IsLimit.hom_ext (fiberConeIsLimit H.hom)
    · change fiberMap (q ≫ r) ≫ fiberToTotal H.hom =
        (fiberMap q ≫ fiberMap r) ≫ fiberToTotal H.hom
      rw [fiberMap_fst, Category.assoc, fiberMap_fst,
        ← Category.assoc, fiberMap_fst]
      rfl
    · change fiberMap (q ≫ r) ≫ fiberToPoint H.hom =
        (fiberMap q ≫ fiberMap r) ≫ fiberToPoint H.hom
      rw [fiberMap_snd, Category.assoc, fiberMap_snd, fiberMap_snd]

/-- The functor retains exactly the literal native pointed fiber object. -/
theorem fiberFunctor_obj (F : Arrow PointedCGWH.{u, v}) :
    fiberFunctor.obj F = PointedCGWH.strictFiberPointed
      F.hom.right F.right.hom F.left.hom (Under.w F.hom) := rfl

/-- The functor retains the original chosen-point native fiber map. -/
theorem fiberFunctor_map {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberFunctor.map q = fiberMap q := rfl

/-- The original native total projections form a complete natural transformation. -/
def fiberToTotalNatTrans : fiberFunctor.{u, v} ⟶ Arrow.leftFunc where
  app F := fiberToTotal F.hom
  naturality {F G} q := by
    change fiberMap q ≫ fiberToTotal G.hom = fiberToTotal F.hom ≫ q.left
    exact fiberMap_fst q

/-- The original native point projections form a complete natural transformation. -/
def fiberToPointNatTrans : fiberFunctor.{u, v} ⟶
    (Functor.const (Arrow PointedCGWH.{u, v})).obj pointObject where
  app F := fiberToPoint F.hom
  naturality {F G} q := by
    change fiberMap q ≫ fiberToPoint G.hom = fiberToPoint F.hom ≫ 𝟙 pointObject
    rw [Category.comp_id]
    exact fiberMap_snd q

/-- The entire total-projection Arrow construction preserves both square components. -/
def fiberToTotalArrowFunctor : Arrow PointedCGWH.{u, v} ⥤ Arrow PointedCGWH.{u, v} where
  obj F := Arrow.mk (fiberToTotal F.hom)
  map q := Arrow.homMk (fiberFunctor.map q) q.left (fiberMap_fst q)
  map_id F := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (𝟙 F) = 𝟙 (fiberFunctor.obj F)
      exact fiberFunctor.map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (q ≫ r) = fiberFunctor.map q ≫ fiberFunctor.map r
      exact fiberFunctor.map_comp q r
    · rfl

/-- The entire point-projection Arrow construction retains the literal point endpoint. -/
def fiberToPointArrowFunctor : Arrow PointedCGWH.{u, v} ⥤ Arrow PointedCGWH.{u, v} where
  obj F := Arrow.mk (fiberToPoint F.hom)
  map {F G} q := Arrow.homMk (fiberFunctor.map q) (𝟙 pointObject)
    (by
      change fiberMap q ≫ fiberToPoint G.hom = fiberToPoint F.hom ≫ 𝟙 pointObject
      rw [Category.comp_id]
      exact fiberMap_snd q)
  map_id F := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (𝟙 F) = 𝟙 (fiberFunctor.obj F)
      exact fiberFunctor.map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · change fiberFunctor.map (q ≫ r) = fiberFunctor.map q ≫ fiberFunctor.map r
      exact fiberFunctor.map_comp q r
    · exact (Category.comp_id _).symm

/-- Every total-projection Arrow map has exactly the original fiber map on its source. -/
theorem fiberToTotalArrowFunctor_map_left
    {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (fiberToTotalArrowFunctor.map q).left = fiberFunctor.map q := rfl

/-- Every total-projection Arrow map has exactly the original total-space map on its target. -/
theorem fiberToTotalArrowFunctor_map_right
    {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (fiberToTotalArrowFunctor.map q).right = q.left := rfl

/-- Every collapse Arrow map has exactly the original fiber map on its source. -/
theorem fiberToPointArrowFunctor_map_left
    {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (fiberToPointArrowFunctor.map q).left = fiberFunctor.map q := rfl

/-- Every collapse Arrow map has the actual identity of the literal point on its target. -/
theorem fiberToPointArrowFunctor_map_right
    {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    (fiberToPointArrowFunctor.map q).right = 𝟙 pointObject := rfl

end PointedCGWH.StrictFiberGeometry

namespace PointedCGWH.StrictFiberGeometry

/-- A full native pointed Arrow square constructs the cone for the chosen fiber map. -/
abbrev nativeChosenMapCone {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right)) :
    PullbackCone G.hom (fromPoint G.right) :=
  PullbackCone.mk (c.fst ≫ q.left) c.snd (by
    calc
      (c.fst ≫ q.left) ≫ G.hom = (c.fst ≫ F.hom) ≫ q.right := by
        rw [Category.assoc, Arrow.w q, ← Category.assoc]
      _ = (c.snd ≫ fromPoint F.right) ≫ q.right := by rw [c.condition]
      _ = c.snd ≫ fromPoint G.right := by
        rw [Category.assoc, PointedCGWH.StrictFiberGeometry.fromPoint_naturality])

/-- The target's actual universal property constructs the full chosen native fiber map. -/
def nativeChosenFiberMap {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right))
    (d : PullbackCone G.hom (fromPoint G.right)) (hd : IsLimit d) : c.pt ⟶ d.pt :=
  hd.lift (nativeChosenMapCone q c)

/-- The full chosen native map preserves the caller's actual total projection. -/
theorem nativeChosenFiberMap_fst {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right))
    (d : PullbackCone G.hom (fromPoint G.right)) (hd : IsLimit d) :
    nativeChosenFiberMap q c d hd ≫ d.fst = c.fst ≫ q.left :=
  hd.fac (nativeChosenMapCone q c) WalkingCospan.left

/-- The full chosen native map preserves the caller's actual point projection. -/
theorem nativeChosenFiberMap_snd {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right))
    (d : PullbackCone G.hom (fromPoint G.right)) (hd : IsLimit d) :
    nativeChosenFiberMap q c d hd ≫ d.snd = c.snd :=
  hd.fac (nativeChosenMapCone q c) WalkingCospan.right

/-- The caller's chosen native pointed fiber is compared with the literal CGWH fiber. -/
def nativeChosenFiberIso (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    c.pt ≅ PointedCGWH.StrictFiberGeometry.fiber F.hom :=
  hc.conePointUniqueUpToIso (t := PointedCGWH.StrictFiberGeometry.fiberCone F.hom)
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit F.hom)

/-- The whole forward native comparison retains the actual total projection. -/
theorem nativeChosenFiberIso_hom_fst (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    (nativeChosenFiberIso F c hc).hom ≫
      PointedCGWH.StrictFiberGeometry.fiberToTotal F.hom = c.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp hc
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit F.hom) WalkingCospan.left

/-- The whole forward native comparison retains the actual point projection. -/
theorem nativeChosenFiberIso_hom_snd (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    (nativeChosenFiberIso F c hc).hom ≫
      PointedCGWH.StrictFiberGeometry.fiberToPoint F.hom = c.snd :=
  IsLimit.conePointUniqueUpToIso_hom_comp hc
    (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit F.hom) WalkingCospan.right

/-- The whole inverse native comparison retains the same actual total projection. -/
theorem nativeChosenFiberIso_inv_fst (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    (nativeChosenFiberIso F c hc).inv ≫ c.fst =
      PointedCGWH.StrictFiberGeometry.fiberToTotal F.hom := by
  rw [← nativeChosenFiberIso_hom_fst F c hc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The whole inverse native comparison retains the same actual point projection. -/
theorem nativeChosenFiberIso_inv_snd (F : Arrow PointedCGWH.{u, v})
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c) :
    (nativeChosenFiberIso F c hc).inv ≫ c.snd =
      PointedCGWH.StrictFiberGeometry.fiberToPoint F.hom := by
  rw [← nativeChosenFiberIso_hom_snd F c hc, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- The entire native comparison is natural for every actual nonidentity pointed square. -/
theorem nativeChosenFiberIso_naturality {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (fromPoint F.right)) (hc : IsLimit c)
    (d : PullbackCone G.hom (fromPoint G.right)) (hd : IsLimit d) :
    nativeChosenFiberMap q c d hd ≫ (nativeChosenFiberIso G d hd).hom =
      (nativeChosenFiberIso F c hc).hom ≫ PointedCGWH.StrictFiberGeometry.fiberFunctor.map q := by
  change nativeChosenFiberMap q c d hd ≫ (nativeChosenFiberIso G d hd).hom =
    (nativeChosenFiberIso F c hc).hom ≫ PointedCGWH.StrictFiberGeometry.fiberMap q
  apply PullbackCone.IsLimit.hom_ext (PointedCGWH.StrictFiberGeometry.fiberConeIsLimit G.hom)
  · change (_ ≫ (nativeChosenFiberIso G d hd).hom) ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal G.hom =
      (_ ≫ PointedCGWH.StrictFiberGeometry.fiberMap q) ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal G.hom
    rw [Category.assoc, nativeChosenFiberIso_hom_fst, nativeChosenFiberMap_fst,
      Category.assoc, PointedCGWH.StrictFiberGeometry.fiberMap_fst,
      ← Category.assoc, nativeChosenFiberIso_hom_fst]
  · change (_ ≫ (nativeChosenFiberIso G d hd).hom) ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint G.hom =
      (_ ≫ PointedCGWH.StrictFiberGeometry.fiberMap q) ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint G.hom
    rw [Category.assoc, nativeChosenFiberIso_hom_snd, nativeChosenFiberMap_snd,
      Category.assoc, PointedCGWH.StrictFiberGeometry.fiberMap_snd,
      nativeChosenFiberIso_hom_snd]

variable
  (c : ∀ F : Arrow PointedCGWH.{u, v}, PullbackCone F.hom (fromPoint F.right))
  (hc : ∀ F, IsLimit (c F))

/-- Every actual family of caller-chosen native fibers forms its full pointed functor. -/
def nativeChosenFiberFunctor : Arrow PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} where
  obj F := (c F).pt
  map {F G} q := nativeChosenFiberMap q (c F) (c G) (hc G)
  map_id F := by
    apply PullbackCone.IsLimit.hom_ext (hc F)
    · rw [nativeChosenFiberMap_fst, Category.id_comp]
      exact Category.comp_id _
    · rw [nativeChosenFiberMap_snd, Category.id_comp]
  map_comp {F G H} q r := by
    apply PullbackCone.IsLimit.hom_ext (hc H)
    · rw [nativeChosenFiberMap_fst, Category.assoc, nativeChosenFiberMap_fst,
        ← Category.assoc, nativeChosenFiberMap_fst, Arrow.comp_left, Category.assoc]
    · rw [nativeChosenFiberMap_snd, Category.assoc,
        nativeChosenFiberMap_snd, nativeChosenFiberMap_snd]

/-- The whole caller-chosen native fiber functor has its full literal CGWH fiber NatIso. -/
def nativeChosenFiberNatIso :
    nativeChosenFiberFunctor c hc ≅ PointedCGWH.StrictFiberGeometry.fiberFunctor :=
  NatIso.ofComponents (fun F => nativeChosenFiberIso F (c F) (hc F)) (by
    intro F G q
    exact nativeChosenFiberIso_naturality q (c F) (hc F) (c G) (hc G))

/-- The caller's native total-projection Arrow functor retains its whole original squares. -/
def nativeChosenTotalArrowFunctor : Arrow PointedCGWH.{u, v} ⥤ Arrow PointedCGWH.{u, v} where
  obj F := Arrow.mk (c F).fst
  map {F G} q := Arrow.homMk ((nativeChosenFiberFunctor c hc).map q) q.left (by
    change nativeChosenFiberMap q (c F) (c G) (hc G) ≫ (c G).fst = (c F).fst ≫ q.left
    exact nativeChosenFiberMap_fst q _ _ _)
  map_id F := by
    apply Arrow.hom_ext
    · change (nativeChosenFiberFunctor c hc).map (𝟙 F) = 𝟙 ((nativeChosenFiberFunctor c hc).obj F)
      exact (nativeChosenFiberFunctor c hc).map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · change (nativeChosenFiberFunctor c hc).map (q ≫ r) =
        (nativeChosenFiberFunctor c hc).map q ≫ (nativeChosenFiberFunctor c hc).map r
      exact (nativeChosenFiberFunctor c hc).map_comp q r
    · rfl

/-- The caller's native point-projection Arrow functor retains the literal point endpoint. -/
def nativeChosenPointArrowFunctor : Arrow PointedCGWH.{u, v} ⥤ Arrow PointedCGWH.{u, v} where
  obj F := Arrow.mk (c F).snd
  map {F G} q := Arrow.homMk ((nativeChosenFiberFunctor c hc).map q) (𝟙 pointObject) (by
    change nativeChosenFiberMap q (c F) (c G) (hc G) ≫ (c G).snd = (c F).snd ≫ 𝟙 pointObject
    rw [Category.comp_id]
    exact nativeChosenFiberMap_snd q _ _ _)
  map_id F := by
    apply Arrow.hom_ext
    · change (nativeChosenFiberFunctor c hc).map (𝟙 F) = 𝟙 ((nativeChosenFiberFunctor c hc).obj F)
      exact (nativeChosenFiberFunctor c hc).map_id F
    · rfl
  map_comp q r := by
    apply Arrow.hom_ext
    · change (nativeChosenFiberFunctor c hc).map (q ≫ r) =
        (nativeChosenFiberFunctor c hc).map q ≫ (nativeChosenFiberFunctor c hc).map r
      exact (nativeChosenFiberFunctor c hc).map_comp q r
    · exact (Category.comp_id _).symm

/-- The complete native total-projection Arrow comparison is natural on the whole category. -/
def nativeChosenTotalArrowNatIso :
    nativeChosenTotalArrowFunctor c hc ≅ PointedCGWH.StrictFiberGeometry.fiberToTotalArrowFunctor :=
  NatIso.ofComponents (fun F => Arrow.isoMk' _ _ (nativeChosenFiberIso F (c F) (hc F))
    (Iso.refl F.left) (by
      rw [Iso.refl_hom, Category.comp_id]
      exact nativeChosenFiberIso_hom_fst F _ _)) (by
    intro F G q
    apply Arrow.hom_ext
    · change (nativeChosenFiberFunctor c hc).map q ≫ (nativeChosenFiberIso G (c G) (hc G)).hom =
        (nativeChosenFiberIso F (c F) (hc F)).hom ≫
          PointedCGWH.StrictFiberGeometry.fiberFunctor.map q
      exact (nativeChosenFiberNatIso c hc).hom.naturality q
    · change q.left ≫ 𝟙 _ = 𝟙 _ ≫ q.left
      rw [Category.comp_id, Category.id_comp])

/-- The complete native point-projection Arrow comparison is natural on the whole category. -/
def nativeChosenPointArrowNatIso :
    nativeChosenPointArrowFunctor c hc ≅ PointedCGWH.StrictFiberGeometry.fiberToPointArrowFunctor :=
  NatIso.ofComponents (fun F => Arrow.isoMk' _ _ (nativeChosenFiberIso F (c F) (hc F))
    (Iso.refl pointObject) (by
      rw [Iso.refl_hom, Category.comp_id]
      exact nativeChosenFiberIso_hom_snd F _ _)) (by
    intro F G q
    apply Arrow.hom_ext
    · change (nativeChosenFiberFunctor c hc).map q ≫ (nativeChosenFiberIso G (c G) (hc G)).hom =
        (nativeChosenFiberIso F (c F) (hc F)).hom ≫
          PointedCGWH.StrictFiberGeometry.fiberFunctor.map q
      exact (nativeChosenFiberNatIso c hc).hom.naturality q
    · change 𝟙 pointObject ≫ 𝟙 pointObject = 𝟙 pointObject ≫ 𝟙 pointObject
      rfl)

end PointedCGWH.StrictFiberGeometry
