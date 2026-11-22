/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.SerreSequence.Category
import MathlibExt.Topology.Category.PointedCGWH.StrictFiber

/-!
# Whole native strict-fiber singular comparison and all original square maps

The actual original pointed strict-fiber functor is followed by the original
CGWH inclusion and singular functor. Its full Iso to the original singular
Serre fiber keeps the entire total projection and the exact original point.
Every actual original Arrow square commutes with both whole Iso directions.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CGWH.modelCategory Simplicial

namespace PointedCGWH.SerreSequenceGeometry

/-- The whole singular native strict-fiber functor uses the exact original pointed fiber. -/
def nativeFiberSingularFunctor : FibrationArrow.{u, v} ⥤ SSet.{v} :=
  arrowFunctor ⋙ PointedCGWH.StrictFiberGeometry.fiberFunctor ⋙
    Under.forget CGWH.point ⋙ underlyingSingularFunctor

/-- The same original strict native fiber has its full original singular strict-fiber Iso. -/
def nativeFiberSingularIso (F : FibrationArrow.{u, v}) :
    nativeFiberSingularFunctor.obj F ≅ (sequence F).fiber :=
  PointedCGWH.FiberGeometry.strictFiberSingularIso F.obj.hom.right F.obj.right.hom

/-- The entire raw original point-fiber Iso keeps its actual total-space projection. -/
theorem strictFiberRawIso_hom_projection
    {E B : CGWH.{u, v}} (p : E ⟶ B) (b : CGWH.point.{u, v} ⟶ B) :
    (CGWH.strictFiberPointFiberIso p b).hom ≫
        AlgebraicTopology.subspaceIncl
          (X := CGWH.cgwhToTop.obj E)
          (Set.ofPred fun x => (CGWH.cgwhToTop.map p) x = CGWH.pointHomEquiv B b) =
      CGWH.cgwhToTop.map (CGWH.strictFiberToTotal p b) := by
  apply ConcreteCategory.hom_ext
  intro x
  exact CGWH.strictFiberPointFiberIso_hom_val p b x

/-- The entire forward native singular-fiber Iso keeps the original total projection map. -/
theorem nativeFiberSingularIso_hom_projection (F : FibrationArrow.{u, v}) :
    (nativeFiberSingularIso F).hom ≫ (sequence F).fiberIncl =
      underlyingSingularFunctor.map
        (CGWH.strictFiberToTotal F.obj.hom.right F.obj.right.hom) := by
  change (TopCat.toSSet.map
      (CGWH.strictFiberPointFiberIso F.obj.hom.right F.obj.right.hom).hom ≫
        (SSet.singularFiberIso (CGWH.cgwhToTop.map F.obj.hom.right).hom
          (CGWH.pointHomEquiv F.obj.right.right F.obj.right.hom)).hom) ≫ _ = _
  let a := (CGWH.strictFiberPointFiberIso
    F.obj.hom.right F.obj.right.hom).hom
  let b := (SSet.singularFiberIso (CGWH.cgwhToTop.map F.obj.hom.right).hom
    (CGWH.pointHomEquiv F.obj.right.right F.obj.right.hom)).hom
  let j := AlgebraicTopology.subspaceIncl
    (X := CGWH.cgwhToTop.obj F.obj.left.right)
    (Set.ofPred fun x => (CGWH.cgwhToTop.map F.obj.hom.right) x =
      CGWH.pointHomEquiv F.obj.right.right F.obj.right.hom)
  have hSing : b ≫ (sequence F).fiberIncl = TopCat.toSSet.map j :=
    SSet.singularFiberIso_hom_ι (CGWH.cgwhToTop.map F.obj.hom.right).hom
      (CGWH.pointHomEquiv F.obj.right.right F.obj.right.hom)
  have hRaw : a ≫ j = CGWH.cgwhToTop.map
      (CGWH.strictFiberToTotal F.obj.hom.right F.obj.right.hom) :=
    strictFiberRawIso_hom_projection F.obj.hom.right F.obj.right.hom
  exact (Category.assoc (TopCat.toSSet.map a) b (sequence F).fiberIncl).trans
    ((congrArg (fun r => TopCat.toSSet.map a ≫ r) hSing).trans
      ((TopCat.toSSet.map_comp a j).symm.trans (congrArg TopCat.toSSet.map hRaw)))

/-- The full forward Iso preserves the same original native strict-fiber chosen point. -/
theorem nativeFiberSingularIso_hom_point (F : FibrationArrow.{u, v}) :
    (nativeFiberSingularIso F).hom.app _
      (TopCat.toSSetObj₀Equiv.symm
        (CGWH.pointHomEquiv
          (CGWH.strictFiber F.obj.hom.right F.obj.right.hom)
          (CGWH.strictFiberPoint F.obj.hom.right F.obj.right.hom F.obj.left.hom
            (Under.w F.obj.hom)))) = (sequence F).fiberPoint :=
  PointedCGWH.FiberGeometry.strictFiberSingularIso_hom_point
    F.obj.hom.right F.obj.right.hom F.obj.left.hom (Under.w F.obj.hom)

/-- The full native singular-fiber map has the original total square after singular inclusion. -/
theorem nativeFiberSingularFunctor_map_projection
    {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    nativeFiberSingularFunctor.map q ≫
        underlyingSingularFunctor.map
          (CGWH.strictFiberToTotal G.obj.hom.right G.obj.right.hom) =
      underlyingSingularFunctor.map
          (CGWH.strictFiberToTotal F.obj.hom.right F.obj.right.hom) ≫
        underlyingSingularFunctor.map q.hom.left.right := by
  have h := PointedCGWH.StrictFiberGeometry.fiberMap_fst q.hom
  have hRaw := congrArg (fun (r :
      PointedCGWH.StrictFiberGeometry.fiber F.obj.hom ⟶ G.obj.left) => r.right) h
  change underlyingSingularFunctor.map
      (PointedCGWH.StrictFiberGeometry.fiberMap q.hom).right ≫ _ = _
  have w : (PointedCGWH.StrictFiberGeometry.fiberMap q.hom).right ≫
      CGWH.strictFiberToTotal G.obj.hom.right G.obj.right.hom =
    CGWH.strictFiberToTotal F.obj.hom.right F.obj.right.hom ≫ q.hom.left.right := by
    simpa only [Under.comp_right, PointedCGWH.StrictFiberGeometry.fiberToTotal_right] using hRaw
  exact (underlyingSingularFunctor.map_comp _ _).symm.trans
    ((congrArg underlyingSingularFunctor.map w).trans (underlyingSingularFunctor.map_comp _ _))

/-- Every entire original pointed Arrow square commutes with the full native fiber singular Iso. -/
theorem nativeFiberSingularIso_naturality
    {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    nativeFiberSingularFunctor.map q ≫ (nativeFiberSingularIso G).hom =
      (nativeFiberSingularIso F).hom ≫ (sequenceMap q).fiberMap := by
  let _ : Mono (sequence G).fiberIncl := inferInstance
  apply (cancel_mono (sequence G).fiberIncl).mp
  have hLeft : (nativeFiberSingularFunctor.map q ≫ (nativeFiberSingularIso G).hom) ≫
      (sequence G).fiberIncl = nativeFiberSingularFunctor.map q ≫
        underlyingSingularFunctor.map
          (CGWH.strictFiberToTotal G.obj.hom.right G.obj.right.hom) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun r => nativeFiberSingularFunctor.map q ≫ r)
        (nativeFiberSingularIso_hom_projection G))
  have hRight : ((nativeFiberSingularIso F).hom ≫ (sequenceMap q).fiberMap) ≫
      (sequence G).fiberIncl =
        underlyingSingularFunctor.map
          (CGWH.strictFiberToTotal F.obj.hom.right F.obj.right.hom) ≫
            underlyingSingularFunctor.map q.hom.left.right :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun r => (nativeFiberSingularIso F).hom ≫ r)
        (SSet.FibrationSequenceHom.fiberMap_ι (sequenceMap q))).trans
          ((Category.assoc _ _ _).symm.trans
            ((congrArg (fun r => r ≫ (sequenceMap q).totalMap)
              (nativeFiberSingularIso_hom_projection F)).trans
                (congrArg (fun r => underlyingSingularFunctor.map
                  (CGWH.strictFiberToTotal F.obj.hom.right F.obj.right.hom) ≫ r)
                    (sequenceMap_total q)))))
  exact hLeft.trans ((nativeFiberSingularFunctor_map_projection q).trans hRight.symm)

/-- The entire original native singular-fiber functor is naturally the
genuine sequence fiber functor. -/
def nativeFiberSingularNatIso : nativeFiberSingularFunctor.{u, v} ≅
    sequenceFunctor ⋙ SSet.FibrationSequence.Geometry.fiberFunctor :=
  NatIso.ofComponents nativeFiberSingularIso (by
    intro F G q
    exact nativeFiberSingularIso_naturality q)

/-- The whole comparison keeps the exact original forward Iso map at every source object. -/
theorem nativeFiberSingularNatIso_hom_app (F : FibrationArrow.{u, v}) :
    nativeFiberSingularNatIso.hom.app F = (nativeFiberSingularIso F).hom := rfl

/-- The whole comparison keeps the exact original inverse Iso map at every source object. -/
theorem nativeFiberSingularNatIso_inv_app (F : FibrationArrow.{u, v}) :
    nativeFiberSingularNatIso.inv.app F = (nativeFiberSingularIso F).inv := rfl

/-- Every whole inverse comparison retains the complete original native Arrow naturality. -/
theorem nativeFiberSingularNatIso_inv_naturality
    {F G : FibrationArrow.{u, v}} (q : F ⟶ G) :
    (sequenceFunctor ⋙ SSet.FibrationSequence.Geometry.fiberFunctor).map q ≫
        nativeFiberSingularNatIso.inv.app G =
      nativeFiberSingularNatIso.inv.app F ≫ nativeFiberSingularFunctor.map q :=
  nativeFiberSingularNatIso.inv.naturality q

end PointedCGWH.SerreSequenceGeometry
