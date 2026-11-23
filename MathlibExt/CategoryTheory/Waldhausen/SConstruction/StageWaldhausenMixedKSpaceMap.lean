/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenMixedZeroEdge
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceContinuousMap
public import MathlibExt.Topology.Homotopy.SourceConnectorLoopHomotopy

/-!
# Original K-space maps for mixed general Waldhausen functors

The actual mixed diagonal realization map is rooted by the realized ORIGINAL
mapped-to-target degree-one zero edge. Source and target casts come from
its actual mapped-source vertex and the original selected target-zero vertex.
The same root gives the full continuous map of the original ordinary K
carriers and its canonical moving unit path. An exact homogeneous
specialization recovers the original exact map and root recipe.
-/

public section

noncomputable section

open CategoryTheory Limits
open scoped Simplicial Topology

universe uB vB uD vD

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategory D]
variable {F : B ⥤ D}

/-- The ORIGINAL mapped-to-target root, with source/target casts earned from actual vertex values. -/
def stageWeakDiagonalMixedRootPath (hF : F.IsWaldhausenExact) :
    _root_.Path
      (hF.stageWeakDiagonalRealMixedMap (stageWeakDiagonalReal.basepoint B))
      (stageWeakDiagonalReal.basepoint D) :=
  (TopCat.pathEquiv
    (SSet.realizedEdgePath (stageWeakDiagonalMixedZeroEdge F hF))).cast
      (stageWeakDiagonalRealMixedMap_basepoint hF)
      (stageWeakDiagonalReal.basepoint_eq_realizedVertex D)

private theorem originalMixedRootContinuousMapValueComputed (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalMixedRootPath.toContinuousMap =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath (stageWeakDiagonalMixedZeroEdge F hF))).toContinuousMap := rfl

/-- The whole original root map retains the ACTUAL original mapped-to-target edge. -/
theorem stageWeakDiagonalMixedRootPath_toContinuousMap (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalMixedRootPath.toContinuousMap =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath (stageWeakDiagonalMixedZeroEdge F hF))).toContinuousMap :=
  originalMixedRootContinuousMapValueComputed hF

/-- The unchanged mixed realization spaces and original points, weakly pointed by the earned original root. -/
def stageWeakDiagonalRealMixedMapWeaklyPointed (hF : F.IsWaldhausenExact) :
    ContinuousMap.WeaklyPointed (stageWeakDiagonalReal.basepoint B)
      (stageWeakDiagonalReal.basepoint D) :=
  ⟨hF.stageWeakDiagonalRealMixedMap, hF.stageWeakDiagonalMixedRootPath⟩

private theorem originalMixedWeaklyPointedHomValueComputed (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalRealMixedMapWeaklyPointed.hom = hF.stageWeakDiagonalRealMixedMap := rfl

/-- The original weakly pointed map keeps its same actual mixed realization map. -/
theorem stageWeakDiagonalRealMixedMapWeaklyPointed_hom (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalRealMixedMapWeaklyPointed.hom = hF.stageWeakDiagonalRealMixedMap :=
  originalMixedWeaklyPointedHomValueComputed hF

private theorem originalMixedWeaklyPointedRootValueComputed (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalRealMixedMapWeaklyPointed.rootPath =
      hF.stageWeakDiagonalMixedRootPath.cast
        (congrArg (fun f : C(stageWeakDiagonalReal B, stageWeakDiagonalReal D) =>
          f (stageWeakDiagonalReal.basepoint B))
            (stageWeakDiagonalRealMixedMapWeaklyPointed_hom hF)) rfl := rfl

/-- The original weakly pointed map keeps its same actual mapped-zero edge root,
with only the earned stored-hom source cast. -/
theorem stageWeakDiagonalRealMixedMapWeaklyPointed_rootPath (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalRealMixedMapWeaklyPointed.rootPath =
      hF.stageWeakDiagonalMixedRootPath.cast
        (congrArg (fun f : C(stageWeakDiagonalReal B, stageWeakDiagonalReal D) =>
          f (stageWeakDiagonalReal.basepoint B))
            (stageWeakDiagonalRealMixedMapWeaklyPointed_hom hF)) rfl :=
  originalMixedWeaklyPointedRootValueComputed hF

/-- The complete actual general K map on ORIGINAL ordinary K carriers, in four independent roles. -/
def stageWeakDiagonalKSpaceMixedMap (hF : F.IsWaldhausenExact) :
    C(stageWeakDiagonalKSpace B, stageWeakDiagonalKSpace D) :=
  hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap

private theorem originalMixedKMapLoopValueComputed (hF : F.IsWaldhausenExact)
    (gamma : stageWeakDiagonalKSpace B) :
    hF.stageWeakDiagonalKSpaceMixedMap gamma =
      hF.stageWeakDiagonalMixedRootPath.symm.trans
        ((gamma.map hF.stageWeakDiagonalRealMixedMap.continuous).trans
          hF.stageWeakDiagonalMixedRootPath) := rfl

/-- Every original loop is mapped through the SAME actual mixed map and SAME original root. -/
theorem stageWeakDiagonalKSpaceMixedMap_apply (hF : F.IsWaldhausenExact)
    (gamma : stageWeakDiagonalKSpace B) :
    hF.stageWeakDiagonalKSpaceMixedMap gamma =
      hF.stageWeakDiagonalMixedRootPath.symm.trans
        ((gamma.map hF.stageWeakDiagonalRealMixedMap.continuous).trans
          hF.stageWeakDiagonalMixedRootPath) :=
  originalMixedKMapLoopValueComputed hF gamma

/-- The ACTUAL canonical moving unit path of the same general original K map. -/
def stageWeakDiagonalKSpaceMixedMapUnitPath (hF : F.IsWaldhausenExact) :
    _root_.Path
      (hF.stageWeakDiagonalKSpaceMixedMap (_root_.Path.refl (stageWeakDiagonalReal.basepoint B)))
      (_root_.Path.refl (stageWeakDiagonalReal.basepoint D)) :=
  ContinuousMap.WeaklyPointed.loopUnitRootPath hF.stageWeakDiagonalRealMixedMapWeaklyPointed

private theorem originalMixedKMapUnitValueComputed
    (hF : F.IsWaldhausenExact) (u s : unitInterval) :
    ((hF.stageWeakDiagonalKSpaceMixedMapUnitPath.toContinuousMap.toFun u : unitInterval →
      stageWeakDiagonalReal D) s) =
      hF.stageWeakDiagonalMixedRootPath
        (ContinuousMap.HomotopyRel.sourceLoopUnitTemplateContraction (u, s)) := by
  change ContinuousMap.WeaklyPointed.loopUnitRootPath
    hF.stageWeakDiagonalRealMixedMapWeaklyPointed u s = _
  have h := ContinuousMap.WeaklyPointed.loopUnitRootPath_value
    hF.stageWeakDiagonalRealMixedMapWeaklyPointed u s
  have hRoot := congrArg (fun p => p
    (ContinuousMap.HomotopyRel.sourceLoopUnitTemplateContraction (u, s)))
      (stageWeakDiagonalRealMixedMapWeaklyPointed_rootPath hF)
  exact h.trans hRoot

/-- Every original contraction and loop time reads SAME original root on SAME original unit template. -/
theorem stageWeakDiagonalKSpaceMixedMapUnitPath_value
    (hF : F.IsWaldhausenExact) (u s : unitInterval) :
    ((hF.stageWeakDiagonalKSpaceMixedMapUnitPath.toContinuousMap.toFun u : unitInterval →
      stageWeakDiagonalReal D) s) =
      hF.stageWeakDiagonalMixedRootPath
        (ContinuousMap.HomotopyRel.sourceLoopUnitTemplateContraction (u, s)) :=
  originalMixedKMapUnitValueComputed hF u s

end CategoryTheory.Functor.IsWaldhausenExact

universe u v

namespace CategoryTheory.Waldhausen.SConstruction

private theorem originalMixedKMapConjugationCast
    {X : Type u} [TopologicalSpace X] {a a' b : X}
    (q : _root_.Path a b) (gamma : _root_.Path a a) (h : a' = a) :
    (q.cast h rfl).symm.trans ((gamma.cast h h).trans (q.cast h rfl)) =
      q.symm.trans (gamma.trans q) := by
  cases h
  rfl

variable (B D : Type u) [Category.{v} B] [Category.{v} D]
  [Preadditive B] [Preadditive D] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts B] [HasBinaryBiproducts D] [ExactCategory B] [ExactCategory D]
variable (F : B ⥤ D) [F.Additive] [Functor.IsExact F]

private theorem originalMixedExactWeakStageMap_eq
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) (n : ℕ) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    hF.mapStageWeak n = mapStageWeak B D F n := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  apply Functor.hext
  · intro X
    rfl
  · intro X Y f
    rfl

/-- The whole generic diagonal specializes to the ORIGINAL exact diagonal map in homogeneous worlds. -/
theorem stageWeakDiagonalMixedMap_exactHomogeneous
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    hF.stageWeakDiagonalMap = stageWeakDiagonalMap B D F := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  apply NatTrans.ext
  funext n
  ext q
  change q ⋙ hF.mapStageWeak n.unop.len = q ⋙ mapStageWeak B D F n.unop.len
  rw [originalMixedExactWeakStageMap_eq]

/-- The whole generic realization specializes to the ORIGINAL exact realization map. -/
theorem stageWeakDiagonalRealMixedMap_exactHomogeneous
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    hF.stageWeakDiagonalRealMixedMap = (stageWeakDiagonalReal.map B D F).hom := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  rw [Functor.IsWaldhausenExact.stageWeakDiagonalRealMixedMap_sameUniverses,
    stageWeakDiagonalMixedMap_exactHomogeneous]
  rfl

/-- The original generic mapped-to-target root specializes to the ORIGINAL exact
zero-comparison root, with only the earned whole-map source cast. -/
theorem stageWeakDiagonalMixedRootPath_exactHomogeneous
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    hF.stageWeakDiagonalMixedRootPath =
      (stageWeakDiagonalKSpace.zeroComparisonRootPath B D F).cast
        (congrArg (fun f : C(stageWeakDiagonalReal B, stageWeakDiagonalReal D) =>
          f (stageWeakDiagonalReal.basepoint B))
          (stageWeakDiagonalRealMixedMap_exactHomogeneous B D F hF)) rfl := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  have hEdge := stageWeakDiagonalMixedZeroEdge_exactRecipe B D F hF
  have hUnderlying : (stageWeakDiagonalMixedZeroEdge F hF).edge =
      (stageWeakDiagonalLevelZeroEdge B D F).edge :=
    congrArg SSet.Edge.edge hEdge
  have hHom : (SSet.realizedEdgePath (stageWeakDiagonalMixedZeroEdge F hF)).hom =
      (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge B D F)).hom := by
    rw [SSet.realizedEdgePath_hom, SSet.realizedEdgePath_hom, hUnderlying]
  apply _root_.Path.ext
  funext t
  change (SSet.realizedEdgePath (stageWeakDiagonalMixedZeroEdge F hF)).hom.hom
      (TopCat.I.homeomorph.symm t) =
    (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge B D F)).hom.hom
      (TopCat.I.homeomorph.symm t)
  exact congrArg (fun f : TopCat.I ⟶ stageWeakDiagonalReal D =>
    f.hom (TopCat.I.homeomorph.symm t)) hHom

/-- The whole generic continuous K map recovers the ORIGINAL exact facade,
using actual whole-map and original-root equality rather than a new root choice. -/
theorem stageWeakDiagonalKSpaceMixedMap_exactHomogeneous
    (hF : letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      F.IsWaldhausenExact) :
    letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B;
    letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
    hF.stageWeakDiagonalKSpaceMixedMap = stageWeakDiagonalKSpaceContinuousMap B D F := by
  letI : WaldhausenCategory B := ExactCategory.waldhausenCategory B
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let f := hF.stageWeakDiagonalRealMixedMap
  let g := (stageWeakDiagonalReal.map B D F).hom
  let p := hF.stageWeakDiagonalMixedRootPath
  let q := stageWeakDiagonalKSpace.zeroComparisonRootPath B D F
  have hfg : f = g := stageWeakDiagonalRealMixedMap_exactHomogeneous B D F hF
  let hpt := congrArg (fun k : C(stageWeakDiagonalReal B, stageWeakDiagonalReal D) =>
    k (stageWeakDiagonalReal.basepoint B)) hfg
  have hp : p = q.cast hpt rfl :=
    stageWeakDiagonalMixedRootPath_exactHomogeneous B D F hF
  apply ContinuousMap.ext
  intro gamma
  have hSource : hF.stageWeakDiagonalKSpaceMixedMap gamma =
      p.symm.trans ((gamma.map f.continuous).trans p) :=
    Functor.IsWaldhausenExact.stageWeakDiagonalKSpaceMixedMap_apply hF gamma
  have hRootValue : p.symm.trans ((gamma.map f.continuous).trans p) =
      (q.cast hpt rfl).symm.trans
        ((gamma.map f.continuous).trans (q.cast hpt rfl)) :=
    congrArg (fun r : _root_.Path (f (stageWeakDiagonalReal.basepoint B))
      (stageWeakDiagonalReal.basepoint D) =>
      r.symm.trans ((gamma.map f.continuous).trans r)) hp
  refine hSource.trans (hRootValue.trans ?_)
  have hLoop : gamma.map f.continuous =
      (gamma.map g.continuous).cast hpt
        hpt := by
    apply _root_.Path.ext
    funext s
    exact congrArg (fun k : C(stageWeakDiagonalReal B, stageWeakDiagonalReal D) =>
      k (gamma s)) hfg
  change (q.cast _ rfl).symm.trans ((gamma.map f.continuous).trans (q.cast _ rfl)) =
    q.symm.trans ((gamma.map g.continuous).trans q)
  rw [hLoop]
  exact originalMixedKMapConjugationCast q (gamma.map g.continuous)
    hpt

end CategoryTheory.Waldhausen.SConstruction

end

noncomputable section

open CategoryTheory Limits

universe uKValueB vKValueB uKValueD vKValueD

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {B : Type uKValueB} [Category.{vKValueB} B] [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uKValueD} [Category.{vKValueD} D] [HasZeroObject D] [WaldhausenCategory D]
variable {F : B ⥤ D}

private theorem originalMixedKMapWholeValueComputed (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalKSpaceMixedMap = hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap := by
  rfl

/-- The whole original mixed K-map is SAME original rooted ordinary loop map. -/
theorem stageWeakDiagonalKSpaceMixedMap_eq (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalKSpaceMixedMap = hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap :=
  originalMixedKMapWholeValueComputed hF

private theorem originalMixedKUnitWholeValueComputed (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalKSpaceMixedMapUnitPath =
      (ContinuousMap.WeaklyPointed.loopUnitRootPath hF.stageWeakDiagonalRealMixedMapWeaklyPointed).cast
        (congrArg (fun k : C(stageWeakDiagonalKSpace B, stageWeakDiagonalKSpace D) =>
          k.toFun (_root_.Path.refl (stageWeakDiagonalReal.basepoint B)))
            (stageWeakDiagonalKSpaceMixedMap_eq hF)) rfl := by
  rfl

/-- The whole original UnitPath is SAME SourceConnector unit path of the
original weakly pointed realization map, with no unit/root replacement. -/
theorem stageWeakDiagonalKSpaceMixedMapUnitPath_eq (hF : F.IsWaldhausenExact) :
    hF.stageWeakDiagonalKSpaceMixedMapUnitPath =
      (ContinuousMap.WeaklyPointed.loopUnitRootPath hF.stageWeakDiagonalRealMixedMapWeaklyPointed).cast
        (congrArg (fun k : C(stageWeakDiagonalKSpace B, stageWeakDiagonalKSpace D) =>
          k.toFun (_root_.Path.refl (stageWeakDiagonalReal.basepoint B)))
            (stageWeakDiagonalKSpaceMixedMap_eq hF)) rfl :=
  originalMixedKUnitWholeValueComputed hF

end CategoryTheory.Functor.IsWaldhausenExact

end
