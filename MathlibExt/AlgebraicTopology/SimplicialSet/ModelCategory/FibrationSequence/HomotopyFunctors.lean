/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.Category
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.HomotopyGroupMap
import Mathlib.CategoryTheory.Types.Basic

/-!
# Whole homotopy functors and actual natural exact segments

Every literal degree, including zero, has complete total/base/fiber homotopy
functors on the actual original pointed Kan sequence category. The original
projection, inclusion and connecting functions are full natural
transformations. Their three adjacent exactness statements are proved from
the actual original fibration sequence. No exactness or group-action
dictionary is an input.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Simplicial
open scoped Simplicial

namespace SSet.FibrationSequence.Geometry

/-- All original total-space homotopy maps form a full functor in every literal degree. -/
def totalPiFunctor (n : ℕ) : SSet.FibrationSequence.{u} ⥤ Type u where
  obj S := KanComplex.π n S.E S.e
  map f := TypeCat.ofHom (KanComplex.π.map f.totalMap f.total_pt n)
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro q
    exact KanComplex.π.map_id_apply (X := S.E) (x := S.e) q
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    exact KanComplex.π.map_comp_apply f.totalMap g.totalMap f.total_pt g.total_pt
      (SSet.FibrationSequenceHom.comp f g).total_pt q

/-- All original base-space homotopy maps form a full functor in every literal degree. -/
def basePiFunctor (n : ℕ) : SSet.FibrationSequence.{u} ⥤ Type u where
  obj S := KanComplex.π n S.B S.b
  map f := TypeCat.ofHom (KanComplex.π.map f.baseMap f.base_pt n)
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro q
    exact KanComplex.π.map_id_apply (X := S.B) (x := S.b) q
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    exact KanComplex.π.map_comp_apply f.baseMap g.baseMap f.base_pt g.base_pt
      (SSet.FibrationSequenceHom.comp f g).base_pt q

/-- All classes of the original strict fiber, including all components, form a full functor. -/
def fiberPiFunctor (n : ℕ) : SSet.FibrationSequence.{u} ⥤ Type u where
  obj S := KanComplex.π n S.fiber S.fiberPoint
  map f := TypeCat.ofHom (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n)
  map_id S := by
    apply ConcreteCategory.hom_ext
    intro q
    change KanComplex.π.map (SSet.FibrationSequenceHom.id S).fiberMap _ n q = q
    exact (congrFun (KanComplex.π.map_congr (SSet.FibrationSequenceHom.id_fiberMap S)
      _ rfl n) q).trans (KanComplex.π.map_id_apply q)
  map_comp {S T U} f g := by
    apply ConcreteCategory.hom_ext
    intro q
    change KanComplex.π.map (SSet.FibrationSequenceHom.comp f g).fiberMap _ n q =
      KanComplex.π.map g.fiberMap g.fiberMap_app_basePoint n
        (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n q)
    have hPoint : (f.fiberMap ≫ g.fiberMap).app _ S.fiberPoint = U.fiberPoint := by
      change g.fiberMap.app _ (f.fiberMap.app _ S.fiberPoint) = U.fiberPoint
      rw [f.fiberMap_app_basePoint, g.fiberMap_app_basePoint]
    exact (congrFun (KanComplex.π.map_congr (SSet.FibrationSequenceHom.comp_fiberMap f g)
      _ hPoint n) q).trans (KanComplex.π.map_comp_apply f.fiberMap g.fiberMap
        f.fiberMap_app_basePoint g.fiberMap_app_basePoint hPoint q)

/-- The whole total homotopy object retains the actual original constant class. -/
instance totalPiFunctorOne (n : ℕ) (S : SSet.FibrationSequence.{u}) :
    One ((totalPiFunctor n).obj S) :=
  inferInstanceAs (One (KanComplex.π n S.E S.e))

/-- The whole base homotopy object retains the actual original constant class. -/
instance basePiFunctorOne (n : ℕ) (S : SSet.FibrationSequence.{u}) :
    One ((basePiFunctor n).obj S) :=
  inferInstanceAs (One (KanComplex.π n S.B S.b))

/-- The whole fiber homotopy object retains the same original chosen-point constant class. -/
instance fiberPiFunctorOne (n : ℕ) (S : SSet.FibrationSequence.{u}) :
    One ((fiberPiFunctor n).obj S) :=
  inferInstanceAs (One (KanComplex.π n S.fiber S.fiberPoint))

/-- Every whole total functor map is the exact original pointed homotopy function. -/
theorem totalPiFunctor_map (n : ℕ) {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T) :
    (totalPiFunctor n).map f = TypeCat.ofHom (KanComplex.π.map f.totalMap f.total_pt n) := rfl

/-- Every whole base functor map is the exact original pointed homotopy function. -/
theorem basePiFunctor_map (n : ℕ) {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T) :
    (basePiFunctor n).map f = TypeCat.ofHom (KanComplex.π.map f.baseMap f.base_pt n) := rfl

/-- Every whole fiber functor map is the exact original pointed strict-fiber homotopy function. -/
theorem fiberPiFunctor_map (n : ℕ) {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T) :
    (fiberPiFunctor n).map f =
      TypeCat.ofHom (KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint n) := rfl

/-- The entire original projection function is natural in every actual pointed source square. -/
def projectionPiNatTrans (n : ℕ) : totalPiFunctor.{u} n ⟶ basePiFunctor n where
  app S := TypeCat.ofHom (KanComplex.π.map S.p S.hb n)
  naturality {S T} f := by
    apply ConcreteCategory.hom_ext
    intro q
    exact KanComplex.π.map_square S.p T.p f.totalMap f.baseMap f.comm
      S.hb T.hb f.total_pt f.base_pt n q

/-- The entire original fiber inclusion function is natural on all original homotopy types. -/
def inclusionPiNatTrans (n : ℕ) : fiberPiFunctor.{u} n ⟶ totalPiFunctor n where
  app S := TypeCat.ofHom (KanComplex.π.map S.fiberIncl rfl n)
  naturality {S T} f := by
    apply ConcreteCategory.hom_ext
    intro q
    exact KanComplex.π.map_square S.fiberIncl T.fiberIncl f.fiberMap f.totalMap f.fiberMap_ι
      rfl rfl f.fiberMap_app_basePoint f.total_pt n q

/-- The actual connecting function is fully natural, including its action
on all fiber components. -/
def connectingPiNatTrans (n : ℕ) : basePiFunctor.{u} (n + 1) ⟶ fiberPiFunctor n where
  app S := TypeCat.ofHom (S.connectingMap (n := n))
  naturality {S T} f := by
    apply ConcreteCategory.hom_ext
    intro q
    exact (SSet.FibrationSequence.connectingMap_naturality (S := S) (T := T) f q).symm

/-- The complete actual natural sequence is exact at the original base homotopy object. -/
theorem exact_at_base (S : SSet.FibrationSequence.{u}) (n : ℕ) :
    Function.MulExact ((projectionPiNatTrans (n + 1)).app S)
      ((connectingPiNatTrans n).app S) :=
  S.mulExact_at_B

/-- The complete actual natural sequence is exact at the same original strict-fiber object. -/
theorem exact_at_fiber (S : SSet.FibrationSequence.{u}) (n : ℕ) :
    Function.MulExact ((connectingPiNatTrans n).app S)
      ((inclusionPiNatTrans n).app S) :=
  S.mulExact_at_fiber

/-- The complete actual natural sequence is exact at the original total homotopy object. -/
theorem exact_at_total (S : SSet.FibrationSequence.{u}) (n : ℕ) :
    Function.MulExact ((inclusionPiNatTrans n).app S) ((projectionPiNatTrans n).app S) :=
  S.mulExact_at_E

end SSet.FibrationSequence.Geometry
