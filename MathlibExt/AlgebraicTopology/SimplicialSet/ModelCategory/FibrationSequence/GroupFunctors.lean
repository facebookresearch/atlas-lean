/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequence.HomotopyFunctors
import Mathlib.Algebra.Category.Grp.Basic
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FibrationSequenceContractible

/-!
# Whole genuine group functors and group maps of the original Kan sequences

Every positive homotopy degree of the actual pointed Kan fibration sequence
has its complete total, base and fiber group functor. The actual projection,
inclusion and connecting functions form complete group natural
transformations. Their original three adjacent exactness statements hold
for these actual group maps. No connecting multiplication or exactness law
is supplied as a dictionary.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory Simplicial
open scoped Simplicial

namespace SSet.FibrationSequence.Geometry

/-- The original positive connecting map is a genuine group homomorphism. -/
def sequenceConnectingGroupHom (S : SSet.FibrationSequence.{u}) (n : ℕ) :
    SSet.KanComplex.π (n + 2) S.B S.b →*
      SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint where
  toFun := S.connectingMap (n + 1)
  map_mul' := S.connectingMap_mul n
  map_one' := by
    have h := S.connectingMap_map_eq_one (n := n + 1)
      (1 : SSet.KanComplex.π (n + 2) S.E S.e)
    exact (congrArg (S.connectingMap (n + 1))
      (SSet.KanComplex.π.map_one S.p S.hb (n + 2))).symm.trans h

/-- The full original connecting group map has its exact original connecting function. -/
theorem sequenceConnectingGroupHom_apply (S : SSet.FibrationSequence.{u}) (n : ℕ)
    (x : SSet.KanComplex.π (n + 2) S.B S.b) :
    sequenceConnectingGroupHom S n x = S.connectingMap (n + 1) x := rfl

/-- The complete original total positive homotopy group functor. -/
def totalGroupFunctor (n : ℕ) : SSet.FibrationSequence.{u} ⥤ GrpCat.{u} where
  obj S := GrpCat.of (SSet.KanComplex.π (n + 1) S.E S.e)
  map f := GrpCat.ofHom
    { toFun := SSet.KanComplex.π.map f.totalMap f.total_pt (n + 1)
      map_one' := SSet.KanComplex.π.map_one f.totalMap f.total_pt (n + 1)
      map_mul' := SSet.KanComplex.π.map_mul f.totalMap f.total_pt n }
  map_id S := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((totalPiFunctor (n + 1)).map_id S) q)
  map_comp f g := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((totalPiFunctor (n + 1)).map_comp f g) q)

/-- The complete original base positive homotopy group functor. -/
def baseGroupFunctor (n : ℕ) : SSet.FibrationSequence.{u} ⥤ GrpCat.{u} where
  obj S := GrpCat.of (SSet.KanComplex.π (n + 1) S.B S.b)
  map f := GrpCat.ofHom
    { toFun := SSet.KanComplex.π.map f.baseMap f.base_pt (n + 1)
      map_one' := SSet.KanComplex.π.map_one f.baseMap f.base_pt (n + 1)
      map_mul' := SSet.KanComplex.π.map_mul f.baseMap f.base_pt n }
  map_id S := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((basePiFunctor (n + 1)).map_id S) q)
  map_comp f g := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((basePiFunctor (n + 1)).map_comp f g) q)

/-- The complete original fiber positive homotopy group functor. -/
def fiberGroupFunctor (n : ℕ) : SSet.FibrationSequence.{u} ⥤ GrpCat.{u} where
  obj S := GrpCat.of (SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint)
  map f := GrpCat.ofHom
    { toFun := SSet.KanComplex.π.map f.fiberMap f.fiberMap_app_basePoint (n + 1)
      map_one' := SSet.KanComplex.π.map_one f.fiberMap f.fiberMap_app_basePoint (n + 1)
      map_mul' := SSet.KanComplex.π.map_mul f.fiberMap f.fiberMap_app_basePoint n }
  map_id S := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((fiberPiFunctor (n + 1)).map_id S) q)
  map_comp f g := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((fiberPiFunctor (n + 1)).map_comp f g) q)

/-- Every full total group map is the exact original total homotopy function. -/
theorem totalGroupFunctor_map (n : ℕ) {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T)
    (q : SSet.KanComplex.π (n + 1) S.E S.e) :
    ((totalGroupFunctor n).map f).hom q = (totalPiFunctor (n + 1)).map f q := rfl

/-- Every full base group map is the exact original base homotopy function. -/
theorem baseGroupFunctor_map (n : ℕ) {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T)
    (q : SSet.KanComplex.π (n + 1) S.B S.b) :
    ((baseGroupFunctor n).map f).hom q = (basePiFunctor (n + 1)).map f q := rfl

/-- Every full fiber group map is the exact original fiber homotopy function. -/
theorem fiberGroupFunctor_map (n : ℕ) {S T : SSet.FibrationSequence.{u}} (f : S ⟶ T)
    (q : SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint) :
    ((fiberGroupFunctor n).map f).hom q = (fiberPiFunctor (n + 1)).map f q := rfl

/-- The whole actual original projection is a full natural group map. -/
def projectionGroupNatTrans (n : ℕ) : totalGroupFunctor.{u} n ⟶ baseGroupFunctor n where
  app S := GrpCat.ofHom
    { toFun := SSet.KanComplex.π.map S.p S.hb (n + 1)
      map_one' := SSet.KanComplex.π.map_one S.p S.hb (n + 1)
      map_mul' := SSet.KanComplex.π.map_mul S.p S.hb n }
  naturality {S T} f := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((projectionPiNatTrans (n + 1)).naturality f) q)

/-- The whole actual original inclusion is a full natural group map. -/
def inclusionGroupNatTrans (n : ℕ) : fiberGroupFunctor.{u} n ⟶ totalGroupFunctor n where
  app S := GrpCat.ofHom
    { toFun := SSet.KanComplex.π.map S.fiberIncl rfl (n + 1)
      map_one' := SSet.KanComplex.π.map_one S.fiberIncl rfl (n + 1)
      map_mul' := SSet.KanComplex.π.map_mul S.fiberIncl rfl n }
  naturality {S T} f := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q => ConcreteCategory.congr_hom
      ((inclusionPiNatTrans (n + 1)).naturality f) q)

/-- The whole actual original connecting function is a full natural group map. -/
def connectingGroupNatTrans (n : ℕ) : baseGroupFunctor.{u} (n + 1) ⟶ fiberGroupFunctor n where
  app S := GrpCat.ofHom (sequenceConnectingGroupHom S n)
  naturality {S T} f := by
    apply GrpCat.hom_ext
    exact MonoidHom.ext (fun q =>
      (SSet.FibrationSequence.connectingMap_naturality (n := n + 1) f q).symm)

/-- The original group projection component keeps its exact entire original function. -/
theorem projectionGroupNatTrans_apply (n : ℕ) (S : SSet.FibrationSequence.{u})
    (q : SSet.KanComplex.π (n + 1) S.E S.e) :
    ((projectionGroupNatTrans n).app S).hom q = (projectionPiNatTrans (n + 1)).app S q := rfl

/-- The original group inclusion component keeps its exact entire original function. -/
theorem inclusionGroupNatTrans_apply (n : ℕ) (S : SSet.FibrationSequence.{u})
    (q : SSet.KanComplex.π (n + 1) S.fiber S.fiberPoint) :
    ((inclusionGroupNatTrans n).app S).hom q = (inclusionPiNatTrans (n + 1)).app S q := rfl

/-- The original connecting group component keeps its exact entire original function. -/
theorem connectingGroupNatTrans_apply (n : ℕ) (S : SSet.FibrationSequence.{u})
    (q : SSet.KanComplex.π (n + 2) S.B S.b) :
    ((connectingGroupNatTrans n).app S).hom q = (connectingPiNatTrans (n + 1)).app S q := rfl

/-- The genuine complete group sequence is exact at the unchanged original base group. -/
theorem groupExact_at_base (n : ℕ) (S : SSet.FibrationSequence.{u}) :
    Function.MulExact ((projectionGroupNatTrans (n + 1)).app S).hom
      ((connectingGroupNatTrans n).app S).hom :=
  exact_at_base S (n + 1)

/-- The genuine complete group sequence is exact at the unchanged original fiber group. -/
theorem groupExact_at_fiber (n : ℕ) (S : SSet.FibrationSequence.{u}) :
    Function.MulExact ((connectingGroupNatTrans n).app S).hom
      ((inclusionGroupNatTrans n).app S).hom :=
  exact_at_fiber S (n + 1)

/-- The genuine complete group sequence is exact at the unchanged original total group. -/
theorem groupExact_at_total (n : ℕ) (S : SSet.FibrationSequence.{u}) :
    Function.MulExact ((inclusionGroupNatTrans n).app S).hom
      ((projectionGroupNatTrans n).app S).hom :=
  exact_at_total S (n + 1)

end SSet.FibrationSequence.Geometry
