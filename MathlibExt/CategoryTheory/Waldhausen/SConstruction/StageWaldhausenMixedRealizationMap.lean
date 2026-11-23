/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenNerveMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift

/-!
# Mixed-universe original Waldhausen diagonal realization maps

Actual mixed-universe weak-stage functors map every original diagonal chain.
The two original simplicial carrier lifts place those chains in their minimum
common carrier universe. Their actual realization lift isomorphisms then
give a continuous map between the unchanged original realization spaces.
The original mapped zero vertex is computed, separately from target zero.
No exact-category, common object/Hom universe, CW or root outcome is assumed.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe uB vB uD vD

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategory D]
variable {F : B ⥤ D}

/-- The actual mixed weak-stage chain map in the minimum common simplicial carrier universe. -/
def stageWeakDiagonalMixedMap (hF : F.IsWaldhausenExact) :
    SSet.uliftFunctor.{max uD vD, max uB vB}.obj (stageWeakDiagonal B) ⟶
      SSet.uliftFunctor.{max uB vB, max uD vD}.obj (stageWeakDiagonal D) where
  app n := ↾fun q => ULift.up (q.down ⋙ hF.mapStageWeak n.unop.len)
  naturality {a b} f := by
    ext q
    apply ULift.ext
    change ((f.unop.toOrderHom.toFunctor ⋙ q.down) ⋙ reindexStageWeak B f.unop) ⋙
        hF.mapStageWeak b.unop.len =
      (f.unop.toOrderHom.toFunctor ⋙ (q.down ⋙ hF.mapStageWeak a.unop.len)) ⋙
        reindexStageWeak D f.unop
    exact congrArg (fun G => f.unop.toOrderHom.toFunctor ⋙ q.down ⋙ G)
      (hF.mapStageWeak_reindex f.unop)

private theorem originalMixedWaldhausenDiagonalMapAppComputed
    (hF : F.IsWaldhausenExact) (n : SimplexCategoryᵒᵖ)
    (q : (SSet.uliftFunctor.{max uD vD, max uB vB}.obj (stageWeakDiagonal B)).obj n) :
    hF.stageWeakDiagonalMixedMap.app n q =
      (ULift.up (q.down ⋙ hF.mapStageWeak n.unop.len) :
        (SSet.uliftFunctor.{max uB vB, max uD vD}.obj (stageWeakDiagonal D)).obj n) := rfl

/-- Every original degree and every whole chain is mapped by SAME actual mixed weak-stage functor. -/
theorem stageWeakDiagonalMixedMap_app
    (hF : F.IsWaldhausenExact) (n : SimplexCategoryᵒᵖ)
    (q : (SSet.uliftFunctor.{max uD vD, max uB vB}.obj (stageWeakDiagonal B)).obj n) :
    hF.stageWeakDiagonalMixedMap.app n q =
      (ULift.up (q.down ⋙ hF.mapStageWeak n.unop.len) :
        (SSet.uliftFunctor.{max uB vB, max uD vD}.obj (stageWeakDiagonal D)).obj n) :=
  originalMixedWaldhausenDiagonalMapAppComputed hF n q

/-- The ACTUAL original mapped-zero weak-stage vertex, with the original source Stage-zero object. -/
def stageWeakDiagonalMixedMappedZeroVertex (hF : F.IsWaldhausenExact) :
    (stageWeakDiagonal D).obj (op ⦋0⦌) :=
  ComposableArrows.mk₀
    ((hF.mapStageWeak 0).obj (⟨stageZero B⟩ : StageWeakCategory B 0))

/-- The actual lifted zero vertex maps to the lift of SAME original mapped-zero vertex. -/
theorem stageWeakDiagonalMixedMap_zeroVertex (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalMixedMap.app (op ⦋0⦌)
        (ULift.up (stageWeakDiagonalZeroVertex B)) =
      ULift.up hF.stageWeakDiagonalMixedMappedZeroVertex := by
  apply ULift.ext
  apply ComposableArrows.ext₀
  rfl

/-- The actual ordinary realization map, through BOTH retained original carrier-lift isomorphisms. -/
def stageWeakDiagonalRealMixedMap (hF : F.IsWaldhausenExact) :
    C(stageWeakDiagonalReal B, stageWeakDiagonalReal D) := by
  let XB := stageWeakDiagonal B
  let XD := stageWeakDiagonal D
  let UB := SSet.toTopULiftIso.{max uB vB, max uD vD}.app XB
  let UD := SSet.toTopULiftIso.{max uD vD, max uB vB}.app XD
  let M := SSet.toTop.map hF.stageWeakDiagonalMixedMap
  exact
    { toFun := fun x => (UD.hom (M (UB.inv (ULift.up x)))).down
      continuous_toFun := continuous_uliftDown.comp
        (UD.hom.hom.continuous.comp
          (M.hom.continuous.comp (UB.inv.hom.continuous.comp continuous_uliftUp))) }

private theorem originalMixedWaldhausenRealizationValueComputed
    (hF : F.IsWaldhausenExact) (x : stageWeakDiagonalReal B) :
    hF.stageWeakDiagonalRealMixedMap x =
      ((SSet.toTopULiftIso.{max uD vD, max uB vB}.hom.app (stageWeakDiagonal D))
        (SSet.toTop.map hF.stageWeakDiagonalMixedMap
          ((SSet.toTopULiftIso.{max uB vB, max uD vD}.inv.app (stageWeakDiagonal B))
            (ULift.up x)))).down := rfl

/-- Every original point uses the same retained source lift, actual M and target down chart. -/
theorem stageWeakDiagonalRealMixedMap_apply
    (hF : F.IsWaldhausenExact) (x : stageWeakDiagonalReal B) :
    hF.stageWeakDiagonalRealMixedMap x =
      ((SSet.toTopULiftIso.{max uD vD, max uB vB}.hom.app (stageWeakDiagonal D))
        (SSet.toTop.map hF.stageWeakDiagonalMixedMap
          ((SSet.toTopULiftIso.{max uB vB, max uD vD}.inv.app (stageWeakDiagonal B))
            (ULift.up x)))).down :=
  originalMixedWaldhausenRealizationValueComputed hF x

/-- Every original vertex maps to the realized vertex of its actual mixed weak-stage chain image. -/
theorem stageWeakDiagonalRealMixedMap_realizedVertex
    (hF : F.IsWaldhausenExact) (x : (stageWeakDiagonal B).obj (op ⦋0⦌)) :
    hF.stageWeakDiagonalRealMixedMap (SSet.realizedVertex x) =
      SSet.realizedVertex
        ((x ⋙ hF.mapStageWeak 0) : (stageWeakDiagonal D).obj (op ⦋0⦌)) := by
  let XB := stageWeakDiagonal B
  let XD := stageWeakDiagonal D
  let UB := SSet.toTopULiftIso.{max uB vB, max uD vD}.app XB
  let UD := SSet.toTopULiftIso.{max uD vD, max uB vB}.app XD
  let M := SSet.toTop.map hF.stageWeakDiagonalMixedMap
  have hB := SSet.toTopULiftIso_inv_realizedVertex.{max uB vB, max uD vD} XB x
  have hM : M
      (SSet.realizedVertex
        (X := SSet.uliftFunctor.{max uD vD, max uB vB}.obj XB) (ULift.up x)) =
      SSet.realizedVertex
        (X := SSet.uliftFunctor.{max uB vB, max uD vD}.obj XD)
          (ULift.up (x ⋙ hF.mapStageWeak 0)) :=
    (SSet.realizedVertex_naturality hF.stageWeakDiagonalMixedMap (ULift.up x)).symm.trans
      (congrArg (fun q => SSet.realizedVertex
        (X := SSet.uliftFunctor.{max uB vB, max uD vD}.obj XD) q)
        (stageWeakDiagonalMixedMap_app hF (op ⦋0⦌) (ULift.up x)))
  have hD := SSet.toTopULiftIso_hom_realizedVertex.{max uD vD, max uB vB} XD
    (x ⋙ hF.mapStageWeak 0)
  rw [stageWeakDiagonalRealMixedMap_apply]
  exact congrArg ULift.down
    ((congrArg (fun q => UD.hom (M q)) hB).trans
      ((congrArg UD.hom hM).trans hD))

/-- The ORIGINAL source realization point maps to the ACTUAL F(Bzero) vertex;
it is kept separate from the selected target zero point. -/
theorem stageWeakDiagonalRealMixedMap_basepoint
    (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalRealMixedMap (stageWeakDiagonalReal.basepoint B) =
      SSet.realizedVertex hF.stageWeakDiagonalMixedMappedZeroVertex := by
  have hBase : stageWeakDiagonalReal.basepoint B =
      SSet.realizedVertex (stageWeakDiagonalZeroVertex B) := by
    simpa [stageWeakDiagonalReal.basepoint, stageWeakDiagonalZeroInclusion] using
      (SSet.realizedVertex_eq_const (stageWeakDiagonalZeroVertex B)).symm
  rw [hBase, stageWeakDiagonalRealMixedMap_realizedVertex]
  apply congrArg SSet.realizedVertex
  apply ComposableArrows.ext₀
  rfl

end CategoryTheory.Functor.IsWaldhausenExact

universe u v

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {B D : Type u} [Category.{v} B] [Category.{v} D]
  [HasZeroObject B] [HasZeroObject D] [WaldhausenCategory B] [WaldhausenCategory D]
variable {F : B ⥤ D}

/-- The original same-universe general diagonal map is recovered by the actual whole carrier lift. -/
theorem stageWeakDiagonalMixedMap_sameUniverses (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalMixedMap =
      SSet.uliftFunctor.{max u v, max u v}.map hF.stageWeakDiagonalMap := by
  apply NatTrans.ext
  funext n
  ext q
  apply ULift.ext
  rfl

/-- The actual mixed realization specializes to the ORIGINAL general same-universe
SSet realization map, by naturality of the SAME retained lift isomorphism. -/
theorem stageWeakDiagonalRealMixedMap_sameUniverses (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalRealMixedMap = (SSet.toTop.map hF.stageWeakDiagonalMap).hom := by
  let X := stageWeakDiagonal B
  let Y := stageWeakDiagonal D
  let U := SSet.toTopULiftIso.{max u v, max u v}
  let M := SSet.toTop.map hF.stageWeakDiagonalMap
  apply ContinuousMap.ext
  intro x
  rw [stageWeakDiagonalRealMixedMap_apply, stageWeakDiagonalMixedMap_sameUniverses]
  have hNat := ConcreteCategory.congr_hom (U.hom.naturality hF.stageWeakDiagonalMap)
    (U.inv.app X (ULift.up x))
  have hSource : U.hom.app X (U.inv.app X (ULift.up x)) = ULift.up x :=
    ConcreteCategory.congr_hom (U.app X).inv_hom_id (ULift.up x)
  have hValue : U.hom.app Y
      (SSet.toTop.map
        (SSet.uliftFunctor.{max u v, max u v}.map hF.stageWeakDiagonalMap)
          (U.inv.app X (ULift.up x))) =
      ULift.up (M x) := by
    have hEval : U.hom.app Y
        (SSet.toTop.map
          (SSet.uliftFunctor.{max u v, max u v}.map hF.stageWeakDiagonalMap)
            (U.inv.app X (ULift.up x))) =
        (TopCat.uliftFunctor.{max u v, max u v}.map M)
          (U.hom.app X (U.inv.app X (ULift.up x))) :=
      (CategoryTheory.comp_apply
        (SSet.toTop.map
          (SSet.uliftFunctor.{max u v, max u v}.map hF.stageWeakDiagonalMap))
        (U.hom.app Y) (U.inv.app X (ULift.up x))).symm.trans
          (hNat.trans (CategoryTheory.comp_apply (U.hom.app X)
            (TopCat.uliftFunctor.{max u v, max u v}.map M)
            (U.inv.app X (ULift.up x))))
    rw [hSource] at hEval
    exact hEval
  exact congrArg ULift.down hValue

end CategoryTheory.Functor.IsWaldhausenExact

end


noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial Topology

universe uMappedViewB vMappedViewB uMappedViewD vMappedViewD

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {B : Type uMappedViewB} [Category.{vMappedViewB} B]
  [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uMappedViewD} [Category.{vMappedViewD} D]
  [HasZeroObject D] [WaldhausenCategory D]
variable {F : B ⥤ D}

private theorem originalMixedMappedZeroVertexValueComputed (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalMixedMappedZeroVertex =
      ComposableArrows.mk₀
        ((hF.mapStageWeak 0).obj (⟨stageZero B⟩ : StageWeakCategory B 0)) := rfl

/-- The whole original mixed mapped-zero vertex retains the actual hF image
of SAME original source Stage-zero, in all four independent category roles. -/
public theorem stageWeakDiagonalMixedMappedZeroVertex_eq (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalMixedMappedZeroVertex =
      ComposableArrows.mk₀
        ((hF.mapStageWeak 0).obj (⟨stageZero B⟩ : StageWeakCategory B 0)) :=
  originalMixedMappedZeroVertexValueComputed hF

end CategoryTheory.Functor.IsWaldhausenExact

end
