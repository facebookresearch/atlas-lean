/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Exact.Quillen.QuillenStageGridMapReindex
public import MathlibExt.KTheory.Exact.Quillen.QuillenQSZigzagWeaklyPointed
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift

/-!
# Actual mixed original Stage-grid diagonal realization map

The original independent-role Stage-grid functor/reindex laws map every
original diagonal chain. The SAME original two simplicial carrier lifts and
realization lift charts give the actual map between unchanged original spaces.
Every original vertex is recovered as its actual image vertex. The original
Q/Stage map squares and three-edge root calibration remain further work.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen.SConstruction
open scoped Simplicial Topology

universe uC vC uD vD

namespace AlgebraicKTheory

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- Standard Waldhausen structure selected locally for the source exact category. -/
local instance originalMixedGridWaldhausenC : WaldhausenCategory C :=
  ExactCategory.waldhausenCategory C
/-- Standard Waldhausen structure selected locally for the target exact category. -/
local instance originalMixedGridWaldhausenD : WaldhausenCategory D :=
  ExactCategory.waldhausenCategory D

/-- The actual original independent-role grid chain map in the minimum
common simplicial carrier universe, with both original grid carriers retained. -/
def quillenStageGridDiagonalMixedMap :
    SSet.uliftFunctor.{max uD vD, max uC vC}.obj (quillenStageGridDiagonal C) ⟶
      SSet.uliftFunctor.{max uC vC, max uD vD}.obj (quillenStageGridDiagonal D) where
  app n := ↾fun q => ULift.up (q.down ⋙ quillenStageGridLiftMap F n.unop)
  naturality {a b} f := by
    ext q
    apply ULift.ext
    change ((f.unop.toOrderHom.toFunctor ⋙ q.down) ⋙
      reindexQuillenStageGridLift (C := C) f.unop) ⋙ quillenStageGridLiftMap F b.unop =
        (f.unop.toOrderHom.toFunctor ⋙ (q.down ⋙ quillenStageGridLiftMap F a.unop)) ⋙
          reindexQuillenStageGridLift (C := D) f.unop
    exact congrArg (fun G => f.unop.toOrderHom.toFunctor ⋙ q.down ⋙ G)
      (quillenStageGridLiftMap_reindex F f.unop)

private theorem originalMixedGridDiagonalAppComputed (n : SimplexCategoryᵒᵖ)
    (q : (SSet.uliftFunctor.{max uD vD, max uC vC}.obj (quillenStageGridDiagonal C)).obj n) :
    (quillenStageGridDiagonalMixedMap F).app n q =
      (ULift.up (q.down ⋙ quillenStageGridLiftMap F n.unop) :
        (SSet.uliftFunctor.{max uC vC, max uD vD}.obj (quillenStageGridDiagonal D)).obj n) := rfl

/-- Every original degree and whole grid chain retains the actual original functor image. -/
theorem quillenStageGridDiagonalMixedMap_app (n : SimplexCategoryᵒᵖ)
    (q : (SSet.uliftFunctor.{max uD vD, max uC vC}.obj (quillenStageGridDiagonal C)).obj n) :
    (quillenStageGridDiagonalMixedMap F).app n q =
      (ULift.up (q.down ⋙ quillenStageGridLiftMap F n.unop) :
        (SSet.uliftFunctor.{max uC vC, max uD vD}.obj (quillenStageGridDiagonal D)).obj n) :=
  originalMixedGridDiagonalAppComputed F n q

/-- The actual map between unchanged original grid realization carriers,
through BOTH original minimum-universe lift charts. -/
def quillenStageGridDiagonalRealMixedMap :
    C(quillenStageGridDiagonalReal C, quillenStageGridDiagonalReal D) := by
  let XC := quillenStageGridDiagonal C
  let XD := quillenStageGridDiagonal D
  let UC := SSet.toTopULiftIso.{max uC vC, max uD vD}.app XC
  let UD := SSet.toTopULiftIso.{max uD vD, max uC vC}.app XD
  let M := SSet.toTop.map (quillenStageGridDiagonalMixedMap F)
  exact
    { toFun := fun x => (UD.hom (M (UC.inv (ULift.up x)))).down
      continuous_toFun := continuous_uliftDown.comp
        (UD.hom.hom.continuous.comp
          (M.hom.continuous.comp (UC.inv.hom.continuous.comp continuous_uliftUp))) }

private theorem originalMixedGridRealValueComputed (x : quillenStageGridDiagonalReal C) :
    quillenStageGridDiagonalRealMixedMap F x =
      ((SSet.toTopULiftIso.{max uD vD, max uC vC}.hom.app (quillenStageGridDiagonal D))
        (SSet.toTop.map (quillenStageGridDiagonalMixedMap F)
          ((SSet.toTopULiftIso.{max uC vC, max uD vD}.inv.app (quillenStageGridDiagonal C))
            (ULift.up x)))).down := rfl

/-- Every actual original realization point uses the SAME source lift/M/target down chart. -/
theorem quillenStageGridDiagonalRealMixedMap_apply (x : quillenStageGridDiagonalReal C) :
    quillenStageGridDiagonalRealMixedMap F x =
      ((SSet.toTopULiftIso.{max uD vD, max uC vC}.hom.app (quillenStageGridDiagonal D))
        (SSet.toTop.map (quillenStageGridDiagonalMixedMap F)
          ((SSet.toTopULiftIso.{max uC vC, max uD vD}.inv.app (quillenStageGridDiagonal C))
            (ULift.up x)))).down :=
  originalMixedGridRealValueComputed F x

/-- Every original grid vertex recovers its actual independent-role image vertex. -/
theorem quillenStageGridDiagonalRealMixedMap_realizedVertex
    (x : (quillenStageGridDiagonal C).obj (op ⦋0⦌)) :
    quillenStageGridDiagonalRealMixedMap F (SSet.realizedVertex x) =
      SSet.realizedVertex
        ((x ⋙ quillenStageGridLiftMap F ⦋0⦌) : (quillenStageGridDiagonal D).obj (op ⦋0⦌)) := by
  let XC := quillenStageGridDiagonal C
  let XD := quillenStageGridDiagonal D
  let UC := SSet.toTopULiftIso.{max uC vC, max uD vD}.app XC
  let UD := SSet.toTopULiftIso.{max uD vD, max uC vC}.app XD
  let M := SSet.toTop.map (quillenStageGridDiagonalMixedMap F)
  have hC := SSet.toTopULiftIso_inv_realizedVertex.{max uC vC, max uD vD} XC x
  have hM : M (SSet.realizedVertex
      (X := SSet.uliftFunctor.{max uD vD, max uC vC}.obj XC) (ULift.up x)) =
      SSet.realizedVertex
        (X := SSet.uliftFunctor.{max uC vC, max uD vD}.obj XD)
          (ULift.up (x ⋙ quillenStageGridLiftMap F ⦋0⦌)) :=
    (SSet.realizedVertex_naturality (quillenStageGridDiagonalMixedMap F) (ULift.up x)).symm.trans
      (congrArg (fun q => SSet.realizedVertex
        (X := SSet.uliftFunctor.{max uC vC, max uD vD}.obj XD) q)
        (quillenStageGridDiagonalMixedMap_app F (op ⦋0⦌) (ULift.up x)))
  have hD := SSet.toTopULiftIso_hom_realizedVertex.{max uD vD, max uC vC} XD
    (x ⋙ quillenStageGridLiftMap F ⦋0⦌)
  rw [quillenStageGridDiagonalRealMixedMap_apply]
  exact congrArg ULift.down
    ((congrArg (fun q => UD.hom (M q)) hC).trans ((congrArg UD.hom hM).trans hD))

end AlgebraicKTheory

end
