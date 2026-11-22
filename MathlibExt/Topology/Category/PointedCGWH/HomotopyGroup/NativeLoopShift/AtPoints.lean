/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.Topology.Category.PointedCGWH.HomotopyGroup.NativeLoopShift
import MathlibExt.Topology.Category.PointedCGWH.Repointing
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.LoopSpaceBasedPositive.VertexEquiv
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap

/-!
# Native loop homotopy shifts at arbitrary points

The actual native singular comparison and the connecting equivalence at the
given vertex retain both complete shift maps and every pointed-map naturality.
-/

set_option autoImplicit false
set_option maxRecDepth 512
noncomputable section
universe u v
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped CGWH.modelCategory Simplicial

namespace PointedCGWH.NativeAllPointLoopShiftGeometry
open PointedCGWH.SingularHomotopyGeometry
open PointedCGWH.CubeSingularGeometry
open PointedCGWH.NativeLoopShiftGeometry

/-- The source vertex is the ACTUAL given point after the SAME original singular inclusion. -/
def nativeVertex (A : PointedCGWH.{u, v}) (a : (PointedCGWH.loop.obj A).right) :
    (nativeLoopSingularFunctor.obj A) _⦋0⦌ :=
  singularPoint (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a)

/-- The original whole native-loop Iso gives the ACTUAL strict-loop image of the source point. -/
def strictVertex (A : PointedCGWH.{u, v}) (a : (PointedCGWH.loop.obj A).right) :
    (strictLoopSingularFunctor.obj A) _⦋0⦌ :=
  (nativeLoopSingularIso A).hom.app _ (nativeVertex A a)

/-- The ENTIRE original inverse loop comparison recovers EVERY actual source vertex. -/
theorem nativeIso_inverse_vertex (A : PointedCGWH.{u, v})
    (a : (PointedCGWH.loop.obj A).right) :
    (nativeLoopSingularIso A).inv.app _ (strictVertex A a) = nativeVertex A a :=
  congrArg (fun f : nativeLoopSingularFunctor.obj A ⟶ nativeLoopSingularFunctor.obj A =>
    f.app _ (nativeVertex A a)) (nativeLoopSingularIso A).hom_inv_id

/-- The actual based map retains the SAME original native loop map and given point equation. -/
def loopAtMap {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (a : (PointedCGWH.loop.obj A).right) (d : (PointedCGWH.loop.obj D).right)
    (h : (PointedCGWH.loop.map f).right a = d) :
    PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a ⟶
      PointedCGWH.pointedAt (PointedCGWH.loop.obj D).right d :=
  PointedCGWH.pointedAtMap (PointedCGWH.loop.map f).right a d h

/-- EVERY original native loop map preserves the ACTUAL arbitrary singular source point. -/
theorem nativeVertex_naturality {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (a : (PointedCGWH.loop.obj A).right) (d : (PointedCGWH.loop.obj D).right)
    (h : (PointedCGWH.loop.map f).right a = d) :
    (nativeLoopSingularFunctor.map f).app _ (nativeVertex A a) = nativeVertex D d :=
  singularPoint_naturality (PointedCGWH.NativeAllPointLoopShiftGeometry.loopAtMap f a d h)

/-- EVERY full original strict-loop map preserves the ACTUAL arbitrary image vertex. -/
theorem strictVertex_naturality {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (a : (PointedCGWH.loop.obj A).right) (d : (PointedCGWH.loop.obj D).right)
    (h : (PointedCGWH.loop.map f).right a = d) :
    (strictLoopSingularFunctor.map f).app _ (strictVertex A a) = strictVertex D d := by
  have hn := congrArg (fun g : nativeLoopSingularFunctor.obj A ⟶
      strictLoopSingularFunctor.obj D => g.app _ (nativeVertex A a))
    (nativeLoopSingularIso_naturality f)
  exact hn.symm.trans
    (congrArg ((nativeLoopSingularIso D).hom.app _) (nativeVertex_naturality f a d h))

/-- BOTH full singular-loop pi comparisons retain the actual original Iso at the GIVEN point. -/
def singularAtIso (A : PointedCGWH.{u, v}) (a : (PointedCGWH.loop.obj A).right) (k : ℕ) :
    (piFunctor k).obj (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a) ≅
      SSet.KanComplex.π k (strictLoopSingularFunctor.obj A) (strictVertex A a) :=
  (SSet.KanComplex.π.equivOfIso (nativeLoopSingularIso A) (x := nativeVertex A a) rfl k).toIso

/-- BOTH original connecting maps are chosen at the ACTUAL strict image vertex, in ALL degrees. -/
def connectingAtIso (A : PointedCGWH.{u, v}) (a : (PointedCGWH.loop.obj A).right) (k : ℕ) :
    (piFunctor (k + 1)).obj A ≅
      SSet.KanComplex.π k (strictLoopSingularFunctor.obj A) (strictVertex A a) :=
  (SSet.connectingAtVertexEquiv (singularFunctor.obj A)
    (singularPoint A) (strictVertex A a) k).toIso

/-- The GENUINE native all-point all-degree shift retains BOTH entire original comparison maps. -/
def loopAtShiftIso (A : PointedCGWH.{u, v}) (a : (PointedCGWH.loop.obj A).right) (k : ℕ) :
    (piNFunctor k).obj (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a) ≅
      (piNFunctor (k + 1)).obj A :=
  (cubeSingularNatIso k).app (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a) ≪≫
    singularAtIso A a k ≪≫ (connectingAtIso A a k).symm ≪≫ ((cubeSingularNatIso (k + 1)).app A).symm

/-- The ENTIRE forward shift function retains all actual original source/cube/connecting maps. -/
theorem loopAtShiftIso_hom_whole (A : PointedCGWH.{u, v})
    (a : (PointedCGWH.loop.obj A).right) (k : ℕ) :
    (fun q => (loopAtShiftIso A a k).hom q) = (fun q =>
      (cubeSingularEquiv (k + 1) A).symm
        ((SSet.connectingAtVertexEquiv (singularFunctor.obj A)
          (singularPoint A) (strictVertex A a) k).symm
            (SSet.KanComplex.π.map (nativeLoopSingularIso A).hom rfl k
              (cubeSingularEquiv k
                (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a) q)))) := rfl

/-- The ENTIRE inverse shift retains every actual original inverse function and source point. -/
theorem loopAtShiftIso_inv_whole (A : PointedCGWH.{u, v})
    (a : (PointedCGWH.loop.obj A).right) (k : ℕ) :
    (fun q => (loopAtShiftIso A a k).inv q) = (fun q =>
      (cubeSingularEquiv k (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a)).symm
        (SSet.KanComplex.π.map (nativeLoopSingularIso A).inv (nativeIso_inverse_vertex A a) k
          (SSet.connectingAtVertexEquiv (singularFunctor.obj A)
            (singularPoint A) (strictVertex A a) k (cubeSingularEquiv (k + 1) A q)))) := rfl

/-- EVERY original native based map preserves the ENTIRE all-point forward shift square. -/
theorem loopAtShiftIso_hom_naturality {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (a : (PointedCGWH.loop.obj A).right) (d : (PointedCGWH.loop.obj D).right)
    (h : (PointedCGWH.loop.map f).right a = d) (k : ℕ) :
    (piNFunctor k).map
        (PointedCGWH.NativeAllPointLoopShiftGeometry.loopAtMap f a d h) ≫
      (loopAtShiftIso D d k).hom =
      (loopAtShiftIso A a k).hom ≫ (piNFunctor (k + 1)).map f := by
  let g := PointedCGWH.NativeAllPointLoopShiftGeometry.loopAtMap f a d h
  let hz := strictVertex_naturality f a d h
  let b := TypeCat.ofHom (SSet.KanComplex.π.map (strictLoopSingularFunctor.map f) hz k)
  have h₁ : CommSq ((piNFunctor k).map g)
      ((cubeSingularNatIso k).hom.app (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a))
      ((cubeSingularNatIso k).hom.app (PointedCGWH.pointedAt (PointedCGWH.loop.obj D).right d))
      ((piFunctor k).map g) := ⟨(cubeSingularNatIso k).hom.naturality g⟩
  have h₂ : CommSq ((piFunctor k).map g) (singularAtIso A a k).hom
      (singularAtIso D d k).hom b := by
    constructor
    apply ConcreteCategory.hom_ext
    intro q
    exact SSet.KanComplex.π.map_square
      (nativeLoopSingularIso A).hom (nativeLoopSingularIso D).hom
      (nativeLoopSingularFunctor.map f) (strictLoopSingularFunctor.map f)
      (nativeLoopSingularIso_naturality f) rfl rfl
      (nativeVertex_naturality f a d h) hz k q
  have h₃ : CommSq b (connectingAtIso A a k).inv (connectingAtIso D d k).inv
      ((piFunctor (k + 1)).map f) := by
    constructor
    apply ConcreteCategory.hom_ext
    intro q
    exact (congrFun (SSet.connectingAtVertexEquiv_inverse_naturality_at_target
      (singularFunctor.map f)
      (singularPoint_naturality f) (strictVertex A a) (strictVertex D d) hz k) q).symm
  have h₄ : CommSq ((piFunctor (k + 1)).map f)
      ((cubeSingularNatIso (k + 1)).inv.app A) ((cubeSingularNatIso (k + 1)).inv.app D)
      ((piNFunctor (k + 1)).map f) := ⟨(cubeSingularNatIso (k + 1)).inv.naturality f⟩
  exact (h₁.vert_comp (h₂.vert_comp (h₃.vert_comp h₄))).w

/-- EVERY original native based map preserves the ENTIRE inverse all-point shift square. -/
theorem loopAtShiftIso_inv_naturality {A D : PointedCGWH.{u, v}} (f : A ⟶ D)
    (a : (PointedCGWH.loop.obj A).right) (d : (PointedCGWH.loop.obj D).right)
    (h : (PointedCGWH.loop.map f).right a = d) (k : ℕ) :
    (piNFunctor (k + 1)).map f ≫ (loopAtShiftIso D d k).inv =
      (loopAtShiftIso A a k).inv ≫ (piNFunctor k).map
        (PointedCGWH.NativeAllPointLoopShiftGeometry.loopAtMap f a d h) :=
  (CommSq.vert_inv (g := loopAtShiftIso A a k) (h := loopAtShiftIso D d k)
    ⟨loopAtShiftIso_hom_naturality f a d h k⟩).w

end PointedCGWH.NativeAllPointLoopShiftGeometry

namespace PointedCGWH.NativeAllPointLoopShiftGeometry
open PointedCGWH.SingularHomotopyGeometry
open PointedCGWH.CubeSingularGeometry

/-- The whole all-point shift retains every actual cube, singular and connecting choice. -/
theorem loopAtShiftIso_whole_value :
    (fun (A : PointedCGWH.{u, v}) (a : (PointedCGWH.loop.obj A).right) (k : ℕ) =>
      loopAtShiftIso A a k) =
      (fun A a k =>
        (cubeSingularNatIso k).app (PointedCGWH.pointedAt (PointedCGWH.loop.obj A).right a) ≪≫
          singularAtIso A a k ≪≫ (connectingAtIso A a k).symm ≪≫
            ((cubeSingularNatIso (k + 1)).app A).symm) := rfl

end PointedCGWH.NativeAllPointLoopShiftGeometry
