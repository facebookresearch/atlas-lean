/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.StrictFiber
import MathlibExt.Topology.Category.PointedCGWH.SuspensionLoop
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks

/-!
# Whole original loop/fiber functors and all actual original Arrow maps

The actual native strict-fiber functor, one-sphere loop functor and all
original pointed Arrow maps retain their literal carriers and projections.
The entire original loop/fiber comparison is natural in both directions.
Arbitrary actual native chosen-fiber families also have their whole natural
comparison, constructed from their original limit universal properties.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits
open scoped CGWH.limits MonoidalClosed

namespace PointedCGWH.LoopFiberGeometry

open PointedCGWH.StrictFiberGeometry
  (pointObject pointObjectIsTerminal pointObjectIsInitial fromPoint fiberCone fiberConeIsLimit)

/-- The same original native one-sphere loop sends the literal point
to an actual terminal object. -/
def loopPointIsTerminal : IsTerminal (PointedCGWH.loop.{u, v}.obj pointObject) := by
  letI := PointedCGWH.suspensionLoopAdjunction.{u, v}.rightAdjoint_preservesLimits
  exact IsTerminal.isTerminalObj PointedCGWH.loop pointObject pointObjectIsTerminal

/-- Both actual original pointed point objects are compared
by their terminal universal properties. -/
def loopPointIso : PointedCGWH.loop.{u, v}.obj pointObject ≅ pointObject :=
  loopPointIsTerminal.uniqueUpToIso pointObjectIsTerminal

/-- The inverse original point comparison retains the actual looped basepoint map. -/
theorem loopFromPoint_inverse_characteristic (X : PointedCGWH.{u, v}) :
    loopPointIso.inv ≫ PointedCGWH.loop.map (fromPoint X) =
      fromPoint (PointedCGWH.loop.obj X) :=
  pointObjectIsInitial.hom_ext _ _

/-- The forward original point comparison retains the same actual looped basepoint map. -/
theorem loopFromPoint_characteristic (X : PointedCGWH.{u, v}) :
    PointedCGWH.loop.map (fromPoint X) =
      loopPointIso.hom ≫ fromPoint (PointedCGWH.loop.obj X) := by
  exact (Category.id_comp _).symm.trans
    ((congrArg (fun r => r ≫ PointedCGWH.loop.map (fromPoint X))
        loopPointIso.hom_inv_id.symm).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun r => loopPointIso.hom ≫ r) (loopFromPoint_inverse_characteristic X))))

/-- The whole caller-chosen fiber cone is mapped by the actual original loop functor. -/
def mappedChosenCone {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) :
    PullbackCone (PointedCGWH.loop.map f) (PointedCGWH.loop.map (fromPoint Y)) :=
  c.map PointedCGWH.loop

/-- The original mapped chosen cone has its genuine loop-preserved limit universal property. -/
def mappedChosenConeIsLimit {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) : IsLimit (mappedChosenCone f c) := by
  letI := PointedCGWH.suspensionLoopAdjunction.{u, v}.rightAdjoint_preservesLimits
  exact (PullbackCone.isLimitMapConeEquiv c PointedCGWH.loop).1
    (isLimitOfPreserves PointedCGWH.loop hc)

/-- The actual original looped legs satisfy the same pointed fiber square through the point Iso. -/
theorem loopedChosen_point_condition {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) :
    PointedCGWH.loop.map c.fst ≫ PointedCGWH.loop.map f =
      (PointedCGWH.loop.map c.snd ≫ loopPointIso.hom) ≫ fromPoint (PointedCGWH.loop.obj Y) := by
  have h := (mappedChosenCone f c).condition
  change PointedCGWH.loop.map c.fst ≫ PointedCGWH.loop.map f =
    PointedCGWH.loop.map c.snd ≫ PointedCGWH.loop.map (fromPoint Y) at h
  exact h.trans
    ((congrArg (fun r => PointedCGWH.loop.map c.snd ≫ r) (loopFromPoint_characteristic Y)).trans
      (Category.assoc _ _ _).symm)

/-- The caller's same original looped fiber carrier and total leg form the literal point cone. -/
def loopedChosenPointCone {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) :
    PullbackCone (PointedCGWH.loop.map f) (fromPoint (PointedCGWH.loop.obj Y)) :=
  PullbackCone.mk (PointedCGWH.loop.map c.fst)
    (PointedCGWH.loop.map c.snd ≫ loopPointIso.hom) (loopedChosen_point_condition f c)

/-- The whole literal-point cone is converted to the original looped point endpoint. -/
def pointConeToLoopPoint {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (d : PullbackCone (PointedCGWH.loop.map f) (fromPoint (PointedCGWH.loop.obj Y))) :
    PullbackCone (PointedCGWH.loop.map f) (PointedCGWH.loop.map (fromPoint Y)) :=
  PullbackCone.mk d.fst (d.snd ≫ loopPointIso.inv) (by
    exact d.condition.trans
      ((congrArg (fun r => d.snd ≫ r) (loopFromPoint_inverse_characteristic Y).symm).trans
        (Category.assoc _ _ _).symm))

/-- The actual preserved original limit constructs the whole lift of every literal-point cone. -/
def loopedChosenPointLift {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c)
    (d : PullbackCone (PointedCGWH.loop.map f) (fromPoint (PointedCGWH.loop.obj Y))) :
    d.pt ⟶ PointedCGWH.loop.obj c.pt :=
  (mappedChosenConeIsLimit f c hc).lift (pointConeToLoopPoint f d)

/-- Every whole lift retains the caller's actual original looped total projection. -/
theorem loopedChosenPointLift_fst {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c)
    (d : PullbackCone (PointedCGWH.loop.map f) (fromPoint (PointedCGWH.loop.obj Y))) :
    loopedChosenPointLift f c hc d ≫ PointedCGWH.loop.map c.fst = d.fst :=
  (mappedChosenConeIsLimit f c hc).fac (pointConeToLoopPoint f d) WalkingCospan.left

/-- Every whole lift retains the caller's actual original looped point projection. -/
theorem loopedChosenPointLift_original_snd {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c)
    (d : PullbackCone (PointedCGWH.loop.map f) (fromPoint (PointedCGWH.loop.obj Y))) :
    loopedChosenPointLift f c hc d ≫ PointedCGWH.loop.map c.snd = d.snd ≫ loopPointIso.inv :=
  (mappedChosenConeIsLimit f c hc).fac (pointConeToLoopPoint f d) WalkingCospan.right

/-- Every whole lift retains the same original point leg through the constructed point Iso. -/
theorem loopedChosenPointLift_snd {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c)
    (d : PullbackCone (PointedCGWH.loop.map f) (fromPoint (PointedCGWH.loop.obj Y))) :
    loopedChosenPointLift f c hc d ≫ (PointedCGWH.loop.map c.snd ≫ loopPointIso.hom) =
      d.snd := by
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun r => r ≫ loopPointIso.hom) (loopedChosenPointLift_original_snd f c hc d)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun r => d.snd ≫ r) loopPointIso.inv_hom_id).trans (Category.comp_id d.snd))))

/-- The caller's same original looped chosen fiber has the complete literal-point limit property. -/
def loopedChosenPointConeIsLimit {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    IsLimit (loopedChosenPointCone f c) := by
  apply PullbackCone.IsLimit.mk (loopedChosen_point_condition f c)
  case lift => exact loopedChosenPointLift f c hc
  case fac_left => exact loopedChosenPointLift_fst f c hc
  case fac_right => exact loopedChosenPointLift_snd f c hc
  case uniq =>
    intro d m hm hn
    apply PullbackCone.IsLimit.hom_ext (mappedChosenConeIsLimit f c hc)
    · exact hm.trans (loopedChosenPointLift_fst f c hc d).symm
    · apply (cancel_mono loopPointIso.hom).mp
      exact (Category.assoc _ _ _).trans
        (hn.trans ((loopedChosenPointLift_snd f c hc d).symm.trans (Category.assoc _ _ _).symm))

/-- The entire loop of the same caller-chosen original fiber has its full
native looped-fiber Iso. -/
def loopedChosenFiberIso {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    PointedCGWH.loop.obj c.pt ≅ PointedCGWH.StrictFiberGeometry.fiber (PointedCGWH.loop.map f) :=
  (loopedChosenPointConeIsLimit f c hc).conePointUniqueUpToIso
    (t := fiberCone (PointedCGWH.loop.map f)) (fiberConeIsLimit (PointedCGWH.loop.map f))

/-- The full forward Iso retains the same actual original chosen looped total leg. -/
theorem loopedChosenFiberIso_hom_fst {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    (loopedChosenFiberIso f c hc).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal (PointedCGWH.loop.map f) =
      PointedCGWH.loop.map c.fst :=
  IsLimit.conePointUniqueUpToIso_hom_comp (loopedChosenPointConeIsLimit f c hc)
    (fiberConeIsLimit (PointedCGWH.loop.map f)) WalkingCospan.left

/-- The full forward Iso retains the same actual original chosen looped point leg and point Iso. -/
theorem loopedChosenFiberIso_hom_snd {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    (loopedChosenFiberIso f c hc).hom ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint (PointedCGWH.loop.map f) =
      PointedCGWH.loop.map c.snd ≫ loopPointIso.hom :=
  IsLimit.conePointUniqueUpToIso_hom_comp (loopedChosenPointConeIsLimit f c hc)
    (fiberConeIsLimit (PointedCGWH.loop.map f)) WalkingCospan.right

/-- The full inverse Iso retains the same actual original chosen looped total leg. -/
theorem loopedChosenFiberIso_inv_fst {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    (loopedChosenFiberIso f c hc).inv ≫ PointedCGWH.loop.map c.fst =
      PointedCGWH.StrictFiberGeometry.fiberToTotal (PointedCGWH.loop.map f) := by
  let e := loopedChosenFiberIso f c hc
  let j := PointedCGWH.StrictFiberGeometry.fiberToTotal (PointedCGWH.loop.map f)
  exact (congrArg (fun r => e.inv ≫ r) (loopedChosenFiberIso_hom_fst f c hc).symm).trans
    ((Category.assoc e.inv e.hom j).symm.trans
      ((congrArg (fun r => r ≫ j) e.inv_hom_id).trans (Category.id_comp j)))

/-- The full inverse Iso retains the actual original looped point leg with its inverse point Iso. -/
theorem loopedChosenFiberIso_inv_snd {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    (loopedChosenFiberIso f c hc).inv ≫ PointedCGWH.loop.map c.snd =
      PointedCGWH.StrictFiberGeometry.fiberToPoint (PointedCGWH.loop.map f) ≫ loopPointIso.inv := by
  let e := loopedChosenFiberIso f c hc
  let j := PointedCGWH.StrictFiberGeometry.fiberToPoint (PointedCGWH.loop.map f)
  apply (cancel_mono loopPointIso.hom).mp
  have hLeft : (e.inv ≫ PointedCGWH.loop.map c.snd) ≫ loopPointIso.hom = j :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun r => e.inv ≫ r) (loopedChosenFiberIso_hom_snd f c hc).symm).trans
        ((Category.assoc e.inv e.hom j).symm.trans
          ((congrArg (fun r => r ≫ j) e.inv_hom_id).trans (Category.id_comp j))))
  have hRight : (j ≫ loopPointIso.inv) ≫ loopPointIso.hom = j :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun r => j ≫ r) loopPointIso.inv_hom_id).trans (Category.comp_id j))
  exact hLeft.trans hRight.symm

/-- The full forward comparison preserves the same original chosen pointed loop-fiber point. -/
theorem loopedChosenFiberIso_hom_point {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    (PointedCGWH.loop.obj c.pt).hom ≫ (loopedChosenFiberIso f c hc).hom.right =
      (PointedCGWH.StrictFiberGeometry.fiber (PointedCGWH.loop.map f)).hom :=
  Under.w (loopedChosenFiberIso f c hc).hom

/-- The full inverse comparison preserves the caller's same original chosen pointed loop point. -/
theorem loopedChosenFiberIso_inv_point {X Y : PointedCGWH.{u, v}} (f : X ⟶ Y)
    (c : PullbackCone f (fromPoint Y)) (hc : IsLimit c) :
    (PointedCGWH.StrictFiberGeometry.fiber (PointedCGWH.loop.map f)).hom ≫
        (loopedChosenFiberIso f c hc).inv.right = (PointedCGWH.loop.obj c.pt).hom :=
  Under.w (loopedChosenFiberIso f c hc).inv

end PointedCGWH.LoopFiberGeometry

namespace PointedCGWH.LoopFiberGeometry

open PointedCGWH.StrictFiberGeometry
  (fiberCone fiberConeIsLimit fiberToTotal fiberToPoint fiberMap fiberMap_fst fiberMap_snd)
open PointedCGWH.StrictFiberGeometry
  (nativeChosenFiberMap nativeChosenFiberMap_fst nativeChosenFiberMap_snd
    nativeChosenFiberFunctor)

/-- Every entire original square commutes with the full looped chosen-fiber comparison. -/
theorem loopedChosenFiberIso_naturality {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G)
    (c : PullbackCone F.hom (PointedCGWH.StrictFiberGeometry.fromPoint F.right)) (hc : IsLimit c)
    (d : PullbackCone G.hom (PointedCGWH.StrictFiberGeometry.fromPoint G.right)) (hd : IsLimit d) :
    PointedCGWH.loop.map (nativeChosenFiberMap q c d hd) ≫
        (loopedChosenFiberIso G.hom d hd).hom =
      (loopedChosenFiberIso F.hom c hc).hom ≫
        fiberMap (PointedCGWH.loop.mapArrow.map q) := by
  apply PullbackCone.IsLimit.hom_ext (fiberConeIsLimit (PointedCGWH.loop.map G.hom))
  · have hLeft : (PointedCGWH.loop.map (nativeChosenFiberMap q c d hd) ≫
        (loopedChosenFiberIso G.hom d hd).hom) ≫
          fiberToTotal (PointedCGWH.loop.map G.hom) =
      PointedCGWH.loop.map c.fst ≫ PointedCGWH.loop.map q.left :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun r => PointedCGWH.loop.map (nativeChosenFiberMap q c d hd) ≫ r)
          (loopedChosenFiberIso_hom_fst G.hom d hd)).trans
            ((PointedCGWH.loop.map_comp _ _).symm.trans
              ((congrArg PointedCGWH.loop.map (nativeChosenFiberMap_fst q c d hd)).trans
                (PointedCGWH.loop.map_comp _ _))))
    have hRight : ((loopedChosenFiberIso F.hom c hc).hom ≫
        fiberMap (PointedCGWH.loop.mapArrow.map q)) ≫
          fiberToTotal (PointedCGWH.loop.map G.hom) =
      PointedCGWH.loop.map c.fst ≫ PointedCGWH.loop.map q.left :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun r => (loopedChosenFiberIso F.hom c hc).hom ≫ r)
          (fiberMap_fst (PointedCGWH.loop.mapArrow.map q))).trans
            ((Category.assoc _ _ _).symm.trans
              (congrArg (fun r => r ≫ PointedCGWH.loop.map q.left)
                (loopedChosenFiberIso_hom_fst F.hom c hc))))
    exact hLeft.trans hRight.symm
  · have hLeft : (PointedCGWH.loop.map (nativeChosenFiberMap q c d hd) ≫
        (loopedChosenFiberIso G.hom d hd).hom) ≫
          fiberToPoint (PointedCGWH.loop.map G.hom) =
      PointedCGWH.loop.map c.snd ≫ loopPointIso.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun r => PointedCGWH.loop.map (nativeChosenFiberMap q c d hd) ≫ r)
          (loopedChosenFiberIso_hom_snd G.hom d hd)).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun r => r ≫ loopPointIso.hom)
                ((PointedCGWH.loop.map_comp _ _).symm.trans
                  (congrArg PointedCGWH.loop.map (nativeChosenFiberMap_snd q c d hd)))))))
    have hRight : ((loopedChosenFiberIso F.hom c hc).hom ≫
        fiberMap (PointedCGWH.loop.mapArrow.map q)) ≫
          fiberToPoint (PointedCGWH.loop.map G.hom) =
      PointedCGWH.loop.map c.snd ≫ loopPointIso.hom :=
      (Category.assoc _ _ _).trans
        ((congrArg (fun r => (loopedChosenFiberIso F.hom c hc).hom ≫ r)
          (fiberMap_snd (PointedCGWH.loop.mapArrow.map q))).trans
            (loopedChosenFiberIso_hom_snd F.hom c hc))
    exact hLeft.trans hRight.symm

/-- The original native chosen map of the actual strict cones is the same
original strict-fiber map. -/
theorem nativeChosenActualMap_eq_fiberMap {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    nativeChosenFiberMap q (fiberCone F.hom) (fiberCone G.hom) (fiberConeIsLimit G.hom) =
      fiberMap q := by
  apply PullbackCone.IsLimit.hom_ext (fiberConeIsLimit G.hom)
  · exact (nativeChosenFiberMap_fst q _ _ _).trans (fiberMap_fst q).symm
  · exact (nativeChosenFiberMap_snd q _ _ _).trans (fiberMap_snd q).symm

/-- The complete original native strict-fiber functor is followed
by the same one-sphere loop functor. -/
def loopFiberFunctor : Arrow PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.StrictFiberGeometry.fiberFunctor ⋙ PointedCGWH.loop

/-- The complete original looped Arrow functor is followed
by the same native strict-fiber functor. -/
def fiberLoopFunctor : Arrow PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  PointedCGWH.loop.mapArrow ⋙ PointedCGWH.StrictFiberGeometry.fiberFunctor

/-- The complete native loop/fiber Iso uses the original actual strict cone and limit proof. -/
def nativeLoopFiberIso (F : Arrow PointedCGWH.{u, v}) :
    loopFiberFunctor.obj F ≅ fiberLoopFunctor.obj F :=
  loopedChosenFiberIso F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)

/-- Every full forward native comparison keeps the entire original looped total projection. -/
theorem nativeLoopFiberIso_hom_fst (F : Arrow PointedCGWH.{u, v}) :
    (nativeLoopFiberIso F).hom ≫ fiberToTotal (PointedCGWH.loop.map F.hom) =
      PointedCGWH.loop.map (fiberToTotal F.hom) :=
  loopedChosenFiberIso_hom_fst F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)

/-- Every full forward native comparison keeps the entire original looped point projection. -/
theorem nativeLoopFiberIso_hom_snd (F : Arrow PointedCGWH.{u, v}) :
    (nativeLoopFiberIso F).hom ≫ fiberToPoint (PointedCGWH.loop.map F.hom) =
      PointedCGWH.loop.map (fiberToPoint F.hom) ≫ loopPointIso.hom :=
  loopedChosenFiberIso_hom_snd F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)

/-- Every full inverse native comparison keeps the entire original looped total projection. -/
theorem nativeLoopFiberIso_inv_fst (F : Arrow PointedCGWH.{u, v}) :
    (nativeLoopFiberIso F).inv ≫ PointedCGWH.loop.map (fiberToTotal F.hom) =
      fiberToTotal (PointedCGWH.loop.map F.hom) :=
  loopedChosenFiberIso_inv_fst F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)

/-- Every full inverse native comparison keeps the entire original looped point projection. -/
theorem nativeLoopFiberIso_inv_snd (F : Arrow PointedCGWH.{u, v}) :
    (nativeLoopFiberIso F).inv ≫ PointedCGWH.loop.map (fiberToPoint F.hom) =
      fiberToPoint (PointedCGWH.loop.map F.hom) ≫ loopPointIso.inv :=
  loopedChosenFiberIso_inv_snd F.hom (fiberCone F.hom) (fiberConeIsLimit F.hom)

/-- The entire native forward Iso preserves the same actual original chosen pointed loop point. -/
theorem nativeLoopFiberIso_hom_point (F : Arrow PointedCGWH.{u, v}) :
    (loopFiberFunctor.obj F).hom ≫ (nativeLoopFiberIso F).hom.right =
      (fiberLoopFunctor.obj F).hom :=
  Under.w (nativeLoopFiberIso F).hom

/-- The entire native inverse Iso preserves the same actual original chosen pointed loop point. -/
theorem nativeLoopFiberIso_inv_point (F : Arrow PointedCGWH.{u, v}) :
    (fiberLoopFunctor.obj F).hom ≫ (nativeLoopFiberIso F).inv.right =
      (loopFiberFunctor.obj F).hom :=
  Under.w (nativeLoopFiberIso F).inv

/-- Every actual entire original Arrow map commutes with the full native loop/fiber Iso. -/
theorem nativeLoopFiberIso_naturality {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    loopFiberFunctor.map q ≫ (nativeLoopFiberIso G).hom =
      (nativeLoopFiberIso F).hom ≫ fiberLoopFunctor.map q :=
  (congrArg (fun r => PointedCGWH.loop.map r ≫ (nativeLoopFiberIso G).hom)
      (nativeChosenActualMap_eq_fiberMap q).symm).trans
    (loopedChosenFiberIso_naturality q (fiberCone F.hom) (fiberConeIsLimit F.hom)
      (fiberCone G.hom) (fiberConeIsLimit G.hom))

/-- All full original native loop/fiber functors have their entire original natural Iso. -/
def nativeLoopFiberNatIso : loopFiberFunctor.{u, v} ≅ fiberLoopFunctor :=
  NatIso.ofComponents nativeLoopFiberIso (by
    intro F G q
    exact nativeLoopFiberIso_naturality q)

/-- The complete forward natural component is the actual original
constructed native loop/fiber map. -/
theorem nativeLoopFiberNatIso_hom_app (F : Arrow PointedCGWH.{u, v}) :
    nativeLoopFiberNatIso.hom.app F = (nativeLoopFiberIso F).hom := rfl

/-- The complete inverse natural component is the actual original constructed inverse map. -/
theorem nativeLoopFiberNatIso_inv_app (F : Arrow PointedCGWH.{u, v}) :
    nativeLoopFiberNatIso.inv.app F = (nativeLoopFiberIso F).inv := rfl

/-- All complete original inverse native comparisons retain the full original Arrow naturality. -/
theorem nativeLoopFiberNatIso_inv_naturality {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberLoopFunctor.map q ≫ nativeLoopFiberNatIso.inv.app G =
      nativeLoopFiberNatIso.inv.app F ≫ loopFiberFunctor.map q :=
  nativeLoopFiberNatIso.inv.naturality q

variable
  (c : ∀ F : Arrow PointedCGWH.{u, v},
    PullbackCone F.hom (PointedCGWH.StrictFiberGeometry.fromPoint F.right))
  (hc : ∀ F, IsLimit (c F))

/-- The full actual caller-chosen native fiber functor is followed
by the same original loop functor. -/
def loopChosenFiberFunctor : Arrow PointedCGWH.{u, v} ⥤ PointedCGWH.{u, v} :=
  nativeChosenFiberFunctor c hc ⋙ PointedCGWH.loop

/-- Every actual native choice family has its complete original loop/fiber natural Iso. -/
def loopChosenFiberNatIso : loopChosenFiberFunctor c hc ≅ fiberLoopFunctor.{u, v} :=
  NatIso.ofComponents (fun F => loopedChosenFiberIso F.hom (c F) (hc F)) (by
    intro F G q
    exact loopedChosenFiberIso_naturality q (c F) (hc F) (c G) (hc G))

/-- Every full forward chosen component is the same original universal-property comparison. -/
theorem loopChosenFiberNatIso_hom_app (F : Arrow PointedCGWH.{u, v}) :
    (loopChosenFiberNatIso c hc).hom.app F = (loopedChosenFiberIso F.hom (c F) (hc F)).hom := rfl

/-- Every full inverse chosen component is the actual inverse of that same comparison. -/
theorem loopChosenFiberNatIso_inv_app (F : Arrow PointedCGWH.{u, v}) :
    (loopChosenFiberNatIso c hc).inv.app F = (loopedChosenFiberIso F.hom (c F) (hc F)).inv := rfl

/-- Every entire chosen forward component preserves the original
caller-chosen pointed loop point. -/
theorem loopChosenFiberNatIso_hom_point (F : Arrow PointedCGWH.{u, v}) :
    ((loopChosenFiberFunctor c hc).obj F).hom ≫ ((loopChosenFiberNatIso c hc).hom.app F).right =
      (fiberLoopFunctor.obj F).hom :=
  Under.w ((loopChosenFiberNatIso c hc).hom.app F)

/-- Every entire chosen inverse component preserves the original
caller-chosen pointed loop point. -/
theorem loopChosenFiberNatIso_inv_point (F : Arrow PointedCGWH.{u, v}) :
    (fiberLoopFunctor.obj F).hom ≫ ((loopChosenFiberNatIso c hc).inv.app F).right =
      ((loopChosenFiberFunctor c hc).obj F).hom :=
  Under.w ((loopChosenFiberNatIso c hc).inv.app F)

/-- Every entire original inverse chosen comparison retains all actual
original choice-family maps. -/
theorem loopChosenFiberNatIso_inv_naturality {F G : Arrow PointedCGWH.{u, v}} (q : F ⟶ G) :
    fiberLoopFunctor.map q ≫ (loopChosenFiberNatIso c hc).inv.app G =
      (loopChosenFiberNatIso c hc).inv.app F ≫ (loopChosenFiberFunctor c hc).map q :=
  (loopChosenFiberNatIso c hc).inv.naturality q

end PointedCGWH.LoopFiberGeometry
