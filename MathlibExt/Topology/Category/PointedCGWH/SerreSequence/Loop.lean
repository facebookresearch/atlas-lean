/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.SerreSequence.LoopFiberArrow
import MathlibExt.Topology.Category.PointedCGWH.Singular.HomotopyFunctor
import MathlibExt.Topology.Category.PointedCGWH.SerreSequence.FiberSingular
import MathlibExt.AlgebraicTopology.Spectra.Sequential.OrderedLoop.Iteration

/-!
# Original native loop fibrations and their complete singular sequences

The actual one-sphere loop Arrow functor lifts to the full subcategory of
the original native pointed fibrations. All entire original squares and
chosen points are retained. The same original singular sequence functor
then gives the looped sequence, including its original strict fiber map.
The genuine native loop/fiber comparison and singular comparison compose
to a full natural Iso with both original component maps.
-/

set_option autoImplicit false
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed Simplicial

namespace PointedCGWH.SerreSequenceGeometry

open PointedCGWH.LoopFiberGeometry
open PointedCGWH.SingularHomotopyGeometry (singularFunctor singularPoint)

/-- The same original loop Arrow functor retains the actual native fibration property. -/
def loopFibrationArrowFunctor : FibrationArrow.{u, v} ⥤ FibrationArrow.{u, v} :=
  fibrationArrowProperty.lift (arrowFunctor ⋙ PointedCGWH.loop.mapArrow)
    (fun F => by
      let _ : IsCofibrant PointedCGWH.sphereOne.{u, v} :=
        PointedCGWH.modelCategory.sphereOne_isCofibrant
      let _ := ihomAdjunction_isQuillenAdjunction_of_isCofibrant
        PointedCGWH.sphereOne.{u, v}
      exact Adjunction.IsQuillenAdjunction.preservesFibrations
        (adj := ihom.adjunction PointedCGWH.sphereOne) F.obj.hom F.property)

/-- The full lifted Arrow has the literal original one-sphere looped map. -/
theorem loopFibrationArrowFunctor_obj_hom (F : FibrationArrow.{u, v}) :
    (loopFibrationArrowFunctor.obj F).obj.hom = PointedCGWH.loop.map F.obj.hom := rfl

/-- The entire lifted square is the original loop Arrow functor on the whole original square. -/
theorem loopFibrationArrowFunctor_map {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopFibrationArrowFunctor.map q).hom = PointedCGWH.loop.mapArrow.map q.hom := rfl

/-- The whole total component is the actual original looped total map. -/
theorem loopFibrationArrowFunctor_map_left {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopFibrationArrowFunctor.map q).hom.left = PointedCGWH.loop.map q.hom.left := rfl

/-- The whole base component is the actual original looped base map. -/
theorem loopFibrationArrowFunctor_map_right {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopFibrationArrowFunctor.map q).hom.right = PointedCGWH.loop.map q.hom.right := rfl

/-- Both original looped square maps commute with the entire original looped fibration. -/
theorem loopFibrationArrowFunctor_map_square {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    PointedCGWH.loop.map q.hom.left ≫ PointedCGWH.loop.map G.obj.hom =
      PointedCGWH.loop.map F.obj.hom ≫ PointedCGWH.loop.map q.hom.right :=
  Arrow.w (loopFibrationArrowFunctor.map q).hom

/-- The complete lifted total map preserves the actual original loop point. -/
theorem loopFibrationArrowFunctor_map_left_point {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (PointedCGWH.loop.obj F.obj.left).hom ≫ (PointedCGWH.loop.map q.hom.left).right =
      (PointedCGWH.loop.obj G.obj.left).hom :=
  Under.w (PointedCGWH.loop.map q.hom.left)

/-- The complete lifted base map preserves the actual original loop point. -/
theorem loopFibrationArrowFunctor_map_right_point {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (PointedCGWH.loop.obj F.obj.right).hom ≫ (PointedCGWH.loop.map q.hom.right).right =
      (PointedCGWH.loop.obj G.obj.right).hom :=
  Under.w (PointedCGWH.loop.map q.hom.right)

/-- The same original native sequence construction is applied
to the lifted loop fibrations. -/
def loopedSequenceFunctor : FibrationArrow.{u, v} ⥤ SSet.FibrationSequence.{v} :=
  loopFibrationArrowFunctor ⋙ sequenceFunctor

/-- The looped sequence has the original whole singular projection of the same native loop map. -/
theorem loopedSequenceFunctor_projection (F : FibrationArrow.{u, v}) :
    (loopedSequenceFunctor.obj F).p =
      underlyingSingularFunctor.map (PointedCGWH.loop.map F.obj.hom).right := rfl

/-- Each full looped sequence square retains the original whole singular total component. -/
theorem loopedSequenceFunctor_map_total {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopedSequenceFunctor.map q).totalMap =
      underlyingSingularFunctor.map (PointedCGWH.loop.map q.hom.left).right := rfl

/-- Each full looped sequence square retains the original whole singular base component. -/
theorem loopedSequenceFunctor_map_base {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopedSequenceFunctor.map q).baseMap =
      underlyingSingularFunctor.map (PointedCGWH.loop.map q.hom.right).right := rfl

/-- Every entire original looped square retains the original total singular point equation. -/
theorem loopedSequenceFunctor_map_total_point {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopedSequenceFunctor.map q).totalMap.app _ (loopedSequenceFunctor.obj F).e =
      (loopedSequenceFunctor.obj G).e :=
  (loopedSequenceFunctor.map q).total_pt

/-- Every entire original looped square retains the original base singular point equation. -/
theorem loopedSequenceFunctor_map_base_point {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopedSequenceFunctor.map q).baseMap.app _ (loopedSequenceFunctor.obj F).b =
      (loopedSequenceFunctor.obj G).b :=
  (loopedSequenceFunctor.map q).base_pt

/-- The full original native strict fiber is looped using its same original map functions. -/
def loopedNativeFiberFunctor : FibrationArrow.{u, v} ⥤ PointedCGWH.{u, v} :=
  arrowFunctor ⋙ PointedCGWH.StrictFiberGeometry.fiberFunctor ⋙ PointedCGWH.loop

/-- The whole original native strict fiber of the actual lifted looped fibration. -/
def nativeLoopedFibrationFiberFunctor : FibrationArrow.{u, v} ⥤ PointedCGWH.{u, v} :=
  loopFibrationArrowFunctor ⋙ arrowFunctor ⋙ PointedCGWH.StrictFiberGeometry.fiberFunctor

/-- Restricting the original complete native loop/fiber comparison
preserves every original square. -/
def loopFibrationFiberNatIso :
    loopedNativeFiberFunctor.{u, v} ≅ nativeLoopedFibrationFiberFunctor :=
  NatIso.ofComponents (fun F => nativeLoopFiberIso F.obj) (by
    intro F G q
    exact nativeLoopFiberIso_naturality q.hom)

/-- The complete forward restricted comparison is the same original native loop/fiber map. -/
theorem loopFibrationFiberNatIso_hom_app (F : FibrationArrow.{u, v}) :
    loopFibrationFiberNatIso.hom.app F = (nativeLoopFiberIso F.obj).hom := rfl

/-- The complete inverse restricted comparison is the same original native loop/fiber inverse. -/
theorem loopFibrationFiberNatIso_inv_app (F : FibrationArrow.{u, v}) :
    loopFibrationFiberNatIso.inv.app F = (nativeLoopFiberIso F.obj).inv := rfl

/-- The complete forward comparison retains the actual original total projection. -/
theorem loopFibrationFiberNatIso_hom_fst (F : FibrationArrow.{u, v}) :
    loopFibrationFiberNatIso.hom.app F ≫
        PointedCGWH.StrictFiberGeometry.fiberToTotal (PointedCGWH.loop.map F.obj.hom) =
      PointedCGWH.loop.map (PointedCGWH.StrictFiberGeometry.fiberToTotal F.obj.hom) :=
  nativeLoopFiberIso_hom_fst F.obj

/-- The complete forward comparison retains the original point projection and loop-point Iso. -/
theorem loopFibrationFiberNatIso_hom_snd (F : FibrationArrow.{u, v}) :
    loopFibrationFiberNatIso.hom.app F ≫
        PointedCGWH.StrictFiberGeometry.fiberToPoint (PointedCGWH.loop.map F.obj.hom) =
      PointedCGWH.loop.map (PointedCGWH.StrictFiberGeometry.fiberToPoint F.obj.hom) ≫
        loopPointIso.hom :=
  nativeLoopFiberIso_hom_snd F.obj

/-- The original native loop/fiber and singular comparisons
give the entire original sequence fiber. -/
def loopFibrationFiberSingularNatIso :
    loopedNativeFiberFunctor.{u, v} ⋙ singularFunctor ≅
      loopedSequenceFunctor ⋙ SSet.FibrationSequence.Geometry.fiberFunctor :=
  Functor.isoWhiskerRight loopFibrationFiberNatIso singularFunctor ≪≫
    Functor.isoWhiskerLeft loopFibrationArrowFunctor nativeFiberSingularNatIso

/-- Every complete original square commutes with the full forward singular loop/fiber map. -/
theorem loopFibrationFiberSingularNatIso_hom_naturality
    {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopedNativeFiberFunctor ⋙ singularFunctor).map q ≫
        loopFibrationFiberSingularNatIso.hom.app G =
      loopFibrationFiberSingularNatIso.hom.app F ≫ (loopedSequenceFunctor.map q).fiberMap :=
  loopFibrationFiberSingularNatIso.hom.naturality q

/-- Every complete original square commutes with the full inverse singular loop/fiber map. -/
theorem loopFibrationFiberSingularNatIso_inv_naturality
    {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (loopedSequenceFunctor.map q).fiberMap ≫ loopFibrationFiberSingularNatIso.inv.app G =
      loopFibrationFiberSingularNatIso.inv.app F ≫
        (loopedNativeFiberFunctor ⋙ singularFunctor).map q :=
  loopFibrationFiberSingularNatIso.inv.naturality q

end PointedCGWH.SerreSequenceGeometry
