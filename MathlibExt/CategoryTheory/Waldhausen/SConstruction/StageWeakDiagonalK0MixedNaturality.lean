/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.ExactCategoryFunctor
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenMixedKSpaceMap
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenMixedSimplexEdgeNaturality
public import
  MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalK0Realization
public import MathlibExt.KTheory.Waldhausen.K0.Functor
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.WeaklyPointedLoopComponentsWeakHomotopy

/-!
# Mixed-universe naturality of the original Waldhausen K-zero comparison

The actual mixed weak-stage realization map carries an object loop to its
mapped object edge, conjugated by the original mapped-zero edge. The two
connector values cancel after the combinatorial K-zero decode. Extensionality
on K-zero generators then gives naturality on every fundamental-group class
and every loop component. The source and target object and morphism universes
remain independent; no group structure is installed on loop components.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial Topology

universe uC vC uD vD uX

namespace CategoryTheory.Waldhausen.SConstruction

private theorem realizedEdgeIntervalValue (X : SSet.{uX})
    {x y : X.obj (op ⦋0⦌)} (e : X.Edge x y) (t : unitInterval) :
    (TopCat.pathEquiv (SSet.realizedEdgePath e)).toContinuousMap.toFun t =
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)
        ((SSet.toTopSimplex.{uX}.inv.app ⦋1⦌)
          (ULift.up (Convexity.StdSimplex.homeomorphI.symm t) :
            SimplexCategory.toTop.{uX}.obj ⦋1⦌)) := by
  have h := congrArg
    (fun f : TopCat.I.{uX} ⟶ SSet.toTop.obj X =>
      f.hom.toFun (TopCat.I.homeomorph.symm t))
    (SSet.realizedEdgePath_hom e)
  have hc := CategoryTheory.comp_apply SSet.stdSimplex.toTopObjIsoI.{uX}.inv
    (SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) (TopCat.I.homeomorph.symm t)
  change (SSet.realizedEdgePath e).hom.hom.toFun (TopCat.I.homeomorph.symm t) = _
  exact h.trans (hc.trans rfl)

private theorem decodeConjugation (E : Type uX) [Category.{vC} E]
    [HasZeroObject E] [WaldhausenCategory E]
    {x y : (stageWeakDiagonal E).obj (op ⦋0⦌)}
    (p : SSet.FundamentalGroupoid.mk x ≅ SSet.FundamentalGroupoid.mk y)
    (h : SSet.FundamentalGroupoid.mk x ⟶ SSet.FundamentalGroupoid.mk x) :
    (stageWeakDiagonalK0Functor E).map (p.inv ≫ h ≫ p.hom) =
      (stageWeakDiagonalK0Functor E).map h := by
  rw [Functor.map_comp, Functor.map_comp]
  simp only [SingleObj.comp_as_mul]
  let qh : Multiplicative (WaldhausenKTheory.K0 E) :=
    (stageWeakDiagonalK0Functor E).map p.hom
  let qi : Multiplicative (WaldhausenKTheory.K0 E) :=
    (stageWeakDiagonalK0Functor E).map p.inv
  let a : Multiplicative (WaldhausenKTheory.K0 E) :=
    (stageWeakDiagonalK0Functor E).map h
  change (qh * a) * qi = a
  have hpCat : (stageWeakDiagonalK0Functor E).map p.inv ≫
      (stageWeakDiagonalK0Functor E).map p.hom = 𝟙 _ := by
    rw [← Functor.map_comp, p.inv_hom_id, Functor.map_id]
  have hp : qh * qi = 1 := by
    dsimp only [qh, qi]
    simpa only [SingleObj.comp_as_mul, SingleObj.id_as_one] using hpCat
  calc
    _ = (qh * qi) * a := by ac_rfl
    _ = a := by rw [hp, one_mul]

variable {C : Type uC} [Category.{vC} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable {D : Type uD} [Category.{vD} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [F.IsExact]

/-- The standard exact-derived Waldhausen structure on the source category. -/
local instance stageWeakDiagonalK0MixedWaldhausenCategoryC : WaldhausenCategory C := ExactCategory.waldhausenCategory C
/-- The standard exact-derived Waldhausen structure on the target category. -/
local instance stageWeakDiagonalK0MixedWaldhausenCategoryD : WaldhausenCategory D := ExactCategory.waldhausenCategory D

private theorem mixedK0Exact : F.IsWaldhausenExact :=
  Functor.IsWaldhausenExact.ofExactCategory F

private theorem mixedObjectSimplexFace (X : C) (i : Fin 2) :
    (stageWeakDiagonal D).δ i
        (ComposableArrows.mk₁ (𝟙 (((mixedK0Exact F).mapStageWeak 1).obj
          (stageOneWeakObj C X)))) =
      (mixedK0Exact F).stageWeakDiagonalMixedMappedZeroVertex := by
  let S := ((mixedK0Exact F).mapStageWeak 1).obj (stageOneWeakObj C X)
  have hstep : (stageWeakDiagonal D).map (SimplexCategory.δ i).op
      (ComposableArrows.mk₁ (𝟙 S)) =
    (CategoryTheory.nerveMap (reindexStageWeak D (SimplexCategory.δ i))).app
      (op ⦋0⦌)
      (((CategoryTheory.nerve (StageWeakCategory D 1)).map
        (SimplexCategory.δ i).op) (ComposableArrows.mk₁ (𝟙 S))) := rfl
  have hinner : ((CategoryTheory.nerve (StageWeakCategory D 1)).map
      (SimplexCategory.δ i).op) (ComposableArrows.mk₁ (𝟙 S)) =
      ComposableArrows.mk₀ S := by
    apply ComposableArrows.ext₀
    fin_cases i <;> rfl
  change (stageWeakDiagonal D).map (SimplexCategory.δ i).op
    (ComposableArrows.mk₁ (𝟙 S)) = _
  rw [hstep, hinner, CategoryTheory.nerveMap_app_mk₀]
  have hReindex := congrArg
    (fun G : StageWeakCategory C 1 ⥤ StageWeakCategory D 0 =>
      G.obj (stageOneWeakObj C X))
    ((mixedK0Exact F).mapStageWeak_reindex (SimplexCategory.δ i))
  change ComposableArrows.mk₀
      ((reindexStageWeak D (SimplexCategory.δ i)).obj
        (((mixedK0Exact F).mapStageWeak 1).obj (stageOneWeakObj C X))) = _
  have hReindex' :
      (reindexStageWeak D (SimplexCategory.δ i)).obj
        (((mixedK0Exact F).mapStageWeak 1).obj (stageOneWeakObj C X)) =
      ((mixedK0Exact F).mapStageWeak 0).obj
        ((reindexStageWeak C (SimplexCategory.δ i)).obj (stageOneWeakObj C X)) :=
    hReindex.symm
  rw [hReindex', stageOneWeakObj_reindex_delta]
  exact ((mixedK0Exact F).stageWeakDiagonalMixedMappedZeroVertex_eq).symm

private def mixedObjectEdge (X : C) :
    (stageWeakDiagonal D).Edge
      (mixedK0Exact F).stageWeakDiagonalMixedMappedZeroVertex
      (mixedK0Exact F).stageWeakDiagonalMixedMappedZeroVertex :=
  SSet.Edge.ofEq (SSet.Edge.mk'
    (ComposableArrows.mk₁ (𝟙 (((mixedK0Exact F).mapStageWeak 1).obj
      (stageOneWeakObj C X)))))
    (mixedObjectSimplexFace F X 1) (mixedObjectSimplexFace F X 0)

private theorem mixedObjectEdgeValue (X : C) :
    (mixedObjectEdge F X).edge =
      ComposableArrows.mk₁ (𝟙 (((mixedK0Exact F).mapStageWeak 1).obj
        (stageOneWeakObj C X))) := rfl

private theorem mixedObjectSimplexImage (X : C) :
    (stageWeakDiagonalObjectEdge C X).edge ⋙ (mixedK0Exact F).mapStageWeak 1 =
      (mixedObjectEdge F X).edge := by
  rw [stageWeakDiagonalObjectEdge_edge, mixedObjectEdgeValue]
  refine ComposableArrows.ext₁ rfl rfl ?_
  change ((mixedK0Exact F).mapStageWeak 1).map (𝟙 (stageOneWeakObj C X)) =
    eqToHom rfl ≫ 𝟙 (((mixedK0Exact F).mapStageWeak 1).obj (stageOneWeakObj C X)) ≫
      eqToHom rfl
  rw [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ((mixedK0Exact F).mapStageWeak 1).map_id _

private theorem mixedObjectLoopImage (X : C) :
    (stageWeakDiagonalObjectLoop C X).map
        (mixedK0Exact F).stageWeakDiagonalRealMixedMap.continuous =
      (TopCat.pathEquiv (SSet.realizedEdgePath (mixedObjectEdge F X))).cast
        ((mixedK0Exact F).stageWeakDiagonalRealMixedMap_basepoint)
        ((mixedK0Exact F).stageWeakDiagonalRealMixedMap_basepoint) := by
  apply Path.ext
  funext t
  have hC := realizedEdgeIntervalValue (stageWeakDiagonal C)
    (stageWeakDiagonalObjectEdge C X) t
  have hD := realizedEdgeIntervalValue (stageWeakDiagonal D) (mixedObjectEdge F X) t
  have hs := (mixedK0Exact F).stageWeakDiagonalRealMixedMap_simplexValue ⦋1⦌
    (stageWeakDiagonalObjectEdge C X).edge (Convexity.StdSimplex.homeomorphI.symm t)
  have he := congrArg
    (fun x : (stageWeakDiagonal D).obj (op ⦋1⦌) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm x)
        ((SSet.toTopSimplex.{max uD vD}.inv.app ⦋1⦌)
          (ULift.up (Convexity.StdSimplex.homeomorphI.symm t) :
            SimplexCategory.toTop.{max uD vD}.obj ⦋1⦌)))
    (mixedObjectSimplexImage F X)
  change (mixedK0Exact F).stageWeakDiagonalRealMixedMap
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalObjectEdge C X))).toContinuousMap.toFun t) =
    (TopCat.pathEquiv (SSet.realizedEdgePath (mixedObjectEdge F X))).toContinuousMap.toFun t
  exact (congrArg (mixedK0Exact F).stageWeakDiagonalRealMixedMap hC).trans
    (hs.trans (he.trans hD.symm))

private theorem mixedObjectDecode (X : C) :
    (stageWeakDiagonalK0Functor D).map
        (SSet.FundamentalGroupoid.homMk (mixedObjectEdge F X)) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk (F.obj X)) := by
  have hEval : (stageOneEval D).obj (ComposableArrows.left (mixedObjectEdge F X).edge).obj =
      F.obj X := by
    rw [mixedObjectEdgeValue]
    change (stageOneEval D).obj
        (((mixedK0Exact F).mapStageWeak 1).obj (stageOneWeakObj C X)).obj = _
    rw [(mixedK0Exact F).mapStageWeak_obj]
    change ((((mixedK0Exact F).mapStage 1).obj
      ((stageOne C).obj X)).obj.obj (interval (0 : Fin 2) 1 (by decide))) = F.obj X
    have hStage := congrArg
      (fun A : Ar 1 ⥤ D => A.obj (interval (0 : Fin 2) 1 (by decide)))
      ((mixedK0Exact F).mapStage_obj 1 ((stageOne C).obj X))
    have hEvalC : F.obj ((stageOneEval C).obj ((stageOne C).obj X)) = F.obj X :=
      congrArg F.obj (by
        simpa only [Functor.comp_obj] using stageOneEval_obj C X)
    exact hStage.trans hEvalC
  exact (stageWeakDiagonalK0Functor_map_homMk D (mixedObjectEdge F X)).trans
    (congrArg (fun Y : D =>
      (Multiplicative.ofAdd (WaldhausenKTheory.K0.mk Y) :
        Multiplicative (WaldhausenKTheory.K0 D))) hEval)

private theorem realizationHomMkTransport (X : SSet.{uX})
    {x y : X.obj (op ⦋0⦌)} (e : X.Edge x y) :
    eqToHom (SSet.realizationFundamentalGroupoidFunctor_obj_mk X x).symm ≫
      (SSet.realizationFundamentalGroupoidFunctor X).map (SSet.FundamentalGroupoid.homMk e) ≫
        eqToHom (SSet.realizationFundamentalGroupoidFunctor_obj_mk X y) =
      Path.Homotopic.Quotient.mk (TopCat.pathEquiv (SSet.realizedEdgePath e)) := by
  have hValue := SSet.realizationFundamentalGroupoidFunctor_map_homMk X e
  exact ((CategoryTheory.conj_eqToHom_iff_heq
    (Path.Homotopic.Quotient.mk (TopCat.pathEquiv (SSet.realizedEdgePath e)))
    ((SSet.realizationFundamentalGroupoidFunctor X).map (SSet.FundamentalGroupoid.homMk e))
    (SSet.realizationFundamentalGroupoidFunctor_obj_mk X x).symm
    (SSet.realizationFundamentalGroupoidFunctor_obj_mk X y).symm).mpr hValue.heq.symm).symm

private abbrev mixedFundamentalMap :=
  basedFundamentalGroupMap (mixedK0Exact F).stageWeakDiagonalRealMixedMap
    (mixedK0Exact F).stageWeakDiagonalMixedRootPath

private theorem realizedMixedConjugate (X : C) :
    let p := asIso (SSet.FundamentalGroupoid.homMk
      (stageWeakDiagonalMixedZeroEdge F (mixedK0Exact F)))
    let g := End.of (p.inv ≫ SSet.FundamentalGroupoid.homMk (mixedObjectEdge F X) ≫ p.hom)
    stageWeakDiagonalRealizationFundamentalMulEquiv D g =
      mixedFundamentalMap F
        (stageWeakDiagonalRealizationFundamentalMulEquiv C
          (stageWeakDiagonalObjectGenerator C X)) := by
  dsimp only
  let e0 := stageWeakDiagonalMixedZeroEdge F (mixedK0Exact F)
  let eX := mixedObjectEdge F X
  let p := asIso (SSet.FundamentalGroupoid.homMk e0)
  let g := End.of (p.inv ≫ SSet.FundamentalGroupoid.homMk eX ≫ p.hom)
  let R := SSet.realizationFundamentalGroupoidFunctor (stageWeakDiagonal D)
  let p0 := TopCat.pathEquiv (SSet.realizedEdgePath e0)
  let pX := TopCat.pathEquiv (SSet.realizedEdgePath eX)
  let hD := stageWeakDiagonalReal.basepoint_eq_realizedVertex D
  let hM := (mixedK0Exact F).stageWeakDiagonalRealMixedMap_basepoint
  have hReal : (stageWeakDiagonalRealizationFundamentalMulEquiv D g).asHom =
      Path.Homotopic.Quotient.mk ((p0.symm.trans (pX.trans p0)).cast hD hD) := by
    let z := stageWeakDiagonalZeroVertex D
    let m := (mixedK0Exact F).stageWeakDiagonalMixedMappedZeroVertex
    let hz := SSet.realizationFundamentalGroupoidFunctor_obj_mk (stageWeakDiagonal D) z
    let hm := SSet.realizationFundamentalGroupoidFunctor_obj_mk (stageWeakDiagonal D) m
    let zTop : _root_.FundamentalGroupoid (SSet.toTop.obj (stageWeakDiagonal D)) :=
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex (X := stageWeakDiagonal D) z)
    let mTop : _root_.FundamentalGroupoid (SSet.toTop.obj (stageWeakDiagonal D)) :=
      _root_.FundamentalGroupoid.mk (SSet.realizedVertex (X := stageWeakDiagonal D) m)
    let q0 : mTop ⟶ zTop := Path.Homotopic.Quotient.mk p0
    let E := SSet.realizationFundamentalGroupoidFunctorEndMulEquiv (stageWeakDiagonal D) z g
    let b := stageWeakDiagonalRealizedVertexBasepointIso D
    have hE := SSet.realizationFundamentalGroupoidFunctor_endMulEquiv_apply
      (stageWeakDiagonal D) z g
    have hOriginal : stageWeakDiagonalRealizationFundamentalMulEquiv D g = b.conj E :=
      (stageWeakDiagonalRealizationFundamentalMulEquiv_apply D g).trans
        (congrArg b.conj hE).symm
    have hEHom : E.asHom = eqToHom hz.symm ≫ R.map g.asHom ≫ eqToHom hz := by
      have hRaw := congrArg
        (fun a : End (_root_.FundamentalGroupoid.mk (SSet.realizedVertex z)) => a.asHom) hE
      exact (CategoryTheory.conj_eqToHom_iff_heq E.asHom (R.map g.asHom)
        hz.symm hz.symm).mpr hRaw.heq
    let i := (eqToIso hm).symm ≪≫ R.mapIso p ≪≫ eqToIso hz
    have hi : i = asIso (Path.Homotopic.Quotient.mk p0) := by
      apply Iso.ext
      change eqToHom hm.symm ≫ R.map p.hom ≫ eqToHom hz =
        (asIso (Path.Homotopic.Quotient.mk p0)).hom
      rw [asIso_hom, asIso_hom]
      exact realizationHomMkTransport (stageWeakDiagonal D) e0
    have hInv : eqToHom hz.symm ≫ R.map p.inv ≫ eqToHom hm =
        (Path.Homotopic.Quotient.mk p0).symm := by
      have hValue : i.inv = eqToHom hz.symm ≫ R.map p.inv ≫ eqToHom hm := by
        dsimp only [i]
        simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
          eqToIso.inv, eqToIso.hom, Category.assoc]
      have hInverse := congrArg Iso.inv hi
      have hPathInverse : (asIso q0).inv =
          ((Path.Homotopic.Quotient.mk p0).symm : zTop ⟶ mTop) := by
        rw [asIso_inv, ← Groupoid.inv_eq_inv]
        rfl
      exact hValue.symm.trans (hInverse.trans hPathInverse)
    have hX : eqToHom hm.symm ≫ R.map (SSet.FundamentalGroupoid.homMk eX) ≫
        eqToHom hm = Path.Homotopic.Quotient.mk pX :=
      realizationHomMkTransport (stageWeakDiagonal D) eX
    have hZero : eqToHom hm.symm ≫ R.map p.hom ≫ eqToHom hz =
        Path.Homotopic.Quotient.mk p0 := by
      rw [asIso_hom]
      exact realizationHomMkTransport (stageWeakDiagonal D) e0
    have hFactor : eqToHom hz.symm ≫ R.map g.asHom ≫ eqToHom hz =
        (eqToHom hz.symm ≫ R.map p.inv ≫ eqToHom hm) ≫
          (eqToHom hm.symm ≫ R.map (SSet.FundamentalGroupoid.homMk eX) ≫ eqToHom hm) ≫
            (eqToHom hm.symm ≫ R.map p.hom ≫ eqToHom hz) := by
      change eqToHom hz.symm ≫
        R.map (p.inv ≫ SSet.FundamentalGroupoid.homMk eX ≫ p.hom) ≫ eqToHom hz = _
      rw [Functor.map_comp, Functor.map_comp]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have hPath : E.asHom = Path.Homotopic.Quotient.mk (p0.symm.trans (pX.trans p0)) := by
      have hInner :
          ((Path.Homotopic.Quotient.mk pX : mTop ⟶ mTop) ≫ q0 : mTop ⟶ zTop) =
            (Path.Homotopic.Quotient.mk (pX.trans p0) : mTop ⟶ zTop) :=
        (_root_.FundamentalGroupoid.comp_eq mTop mTop zTop
          (Path.Homotopic.Quotient.mk pX : mTop ⟶ mTop) q0).trans
          (Path.Homotopic.Quotient.mk_trans pX p0).symm
      have hOuter :
          ((Path.Homotopic.Quotient.mk p0.symm : zTop ⟶ mTop) ≫
            (Path.Homotopic.Quotient.mk (pX.trans p0) : mTop ⟶ zTop) : zTop ⟶ zTop) =
              (Path.Homotopic.Quotient.mk (p0.symm.trans (pX.trans p0)) : zTop ⟶ zTop) :=
        (_root_.FundamentalGroupoid.comp_eq zTop mTop zTop
          (Path.Homotopic.Quotient.mk p0.symm : zTop ⟶ mTop)
          (Path.Homotopic.Quotient.mk (pX.trans p0) : mTop ⟶ zTop)).trans
          (Path.Homotopic.Quotient.mk_trans p0.symm (pX.trans p0)).symm
      calc
        _ = _ := hEHom.trans hFactor
        _ = _ := by
          rw [hInv, hX, hZero]
          rfl
        _ = (Path.Homotopic.Quotient.mk p0).symm ≫
            Path.Homotopic.Quotient.mk (pX.trans p0) :=
          congrArg (fun f : mTop ⟶ zTop =>
            ((Path.Homotopic.Quotient.mk p0).symm : zTop ⟶ mTop) ≫ f) hInner
        _ = Path.Homotopic.Quotient.mk p0.symm ≫
            Path.Homotopic.Quotient.mk (pX.trans p0) :=
          congrArg (fun f : zTop ⟶ mTop =>
            f ≫ (Path.Homotopic.Quotient.mk (pX.trans p0) : mTop ⟶ zTop))
            (Path.Homotopic.Quotient.mk_symm p0).symm
        _ = _ := hOuter
    have hConj : b.inv ≫ E.asHom ≫ b.hom =
        Path.Homotopic.Quotient.mk ((p0.symm.trans (pX.trans p0)).cast hD hD) := by
      rw [hPath]
      change eqToHom (congrArg _root_.FundamentalGroupoid.mk hD) ≫
        Path.Homotopic.Quotient.mk (p0.symm.trans (pX.trans p0)) ≫
          eqToHom (congrArg _root_.FundamentalGroupoid.mk hD.symm) = _
      exact (_root_.FundamentalGroupoid.conj_eqToHom hD hD).trans
        (Path.Homotopic.Quotient.mk_cast _ hD hD).symm
    exact (congrArg End.asHom hOriginal).trans
      ((Iso.conj_apply_asHom b E).trans hConj)
  have hRoot : (mixedK0Exact F).stageWeakDiagonalMixedRootPath = p0.cast hM hD := by
    apply Path.ext
    funext t
    exact congrArg
      (fun f : C(unitInterval, stageWeakDiagonalReal D) => f t)
      ((mixedK0Exact F).stageWeakDiagonalMixedRootPath_toContinuousMap)
  have hLoop :
      ((mixedK0Exact F).stageWeakDiagonalMixedRootPath.symm.trans
        (((stageWeakDiagonalObjectLoop C X).map
          (mixedK0Exact F).stageWeakDiagonalRealMixedMap.continuous).trans
          (mixedK0Exact F).stageWeakDiagonalMixedRootPath)) =
        (p0.symm.trans (pX.trans p0)).cast hD hD := by
    rw [hRoot, mixedObjectLoopImage F X]
    apply Path.ext
    rfl
  rw [stageWeakDiagonalRealizationFundamentalMulEquiv_objectGenerator,
    basedFundamentalGroupMap_mk]
  apply End.ext
  exact hReal.trans (congrArg Path.Homotopic.Quotient.mk hLoop).symm

private theorem mixedFundamentalObjectDecode (X : C) :
    stageWeakDiagonalRealizedFundamentalK0MulEquiv D
        (mixedFundamentalMap F
          (stageWeakDiagonalRealizationFundamentalMulEquiv C
            (stageWeakDiagonalObjectGenerator C X))) =
      Multiplicative.ofAdd (WaldhausenKTheory.K0.mk (F.obj X)) := by
  let p := asIso (SSet.FundamentalGroupoid.homMk
    (stageWeakDiagonalMixedZeroEdge F (mixedK0Exact F)))
  let g := End.of (p.inv ≫ SSet.FundamentalGroupoid.homMk (mixedObjectEdge F X) ≫ p.hom)
  have h := realizedMixedConjugate F X
  change stageWeakDiagonalRealizationFundamentalMulEquiv D g = _ at h
  rw [← h, stageWeakDiagonalRealizedFundamentalK0MulEquiv_realization,
    stageWeakDiagonalFundamentalK0MulEquiv_apply, stageWeakDiagonalFundamentalToK0_apply]
  change (stageWeakDiagonalK0Functor D).map
    (p.inv ≫ SSet.FundamentalGroupoid.homMk (mixedObjectEdge F X) ≫ p.hom) = _
  rw [decodeConjugation, mixedObjectDecode]

/-- The original mixed weak-stage map and original zero edge give the canonical
K-zero square on every fundamental-group class, in independent category universes. -/
theorem stageWeakDiagonalRealizedFundamentalK0MulEquiv_mixed_naturality
    (g : FundamentalGroup (stageWeakDiagonalReal C) (stageWeakDiagonalReal.basepoint C)) :
    stageWeakDiagonalRealizedFundamentalK0MulEquiv D
        (basedFundamentalGroupMap
          (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalRealMixedMap
          (Functor.IsWaldhausenExact.ofExactCategory F).stageWeakDiagonalMixedRootPath g) =
      Multiplicative.ofAdd
        (WaldhausenKTheory.K0.map F
          (Multiplicative.toAdd (stageWeakDiagonalRealizedFundamentalK0MulEquiv C g))) := by
  let kC := stageWeakDiagonalRealizedFundamentalK0MulEquiv C
  let kD := stageWeakDiagonalRealizedFundamentalK0MulEquiv D
  let fPi := mixedFundamentalMap F
  let beta : WaldhausenKTheory.K0 C →+ WaldhausenKTheory.K0 D :=
    kD.toAdditiveLeft.toAddMonoidHom.comp
      ((MonoidHom.toAdditive fPi).comp kC.symm.toAdditiveRight.toAddMonoidHom)
  have hBeta : beta = WaldhausenKTheory.K0.map F := by
    apply WaldhausenKTheory.K0.hom_ext
    intro X
    have hX : kC.symm (Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X)) =
        stageWeakDiagonalRealizationFundamentalMulEquiv C
          (stageWeakDiagonalObjectGenerator C X) := by
      apply kC.injective
      rw [kC.apply_symm_apply]
      exact ((stageWeakDiagonalRealizedFundamentalK0MulEquiv_realization C
        (stageWeakDiagonalObjectGenerator C X)).trans
          (stageWeakDiagonalFundamentalK0MulEquiv_objectGenerator C X)).symm
    change Multiplicative.toAdd
      (kD (fPi (kC.symm (Multiplicative.ofAdd (WaldhausenKTheory.K0.mk X))))) = _
    rw [hX, mixedFundamentalObjectDecode, WaldhausenKTheory.K0.map_mk]
    rfl
  have hAll := DFunLike.congr_fun hBeta (Multiplicative.toAdd (kC g))
  change Multiplicative.toAdd
      (kD (fPi (kC.symm (Multiplicative.ofAdd (Multiplicative.toAdd (kC g)))))) =
        WaldhausenKTheory.K0.map F (Multiplicative.toAdd (kC g)) at hAll
  have hg : kC.symm (Multiplicative.ofAdd (Multiplicative.toAdd (kC g))) = g :=
    kC.symm_apply_apply g
  rw [hg] at hAll
  apply Multiplicative.toAdd.injective
  exact hAll

/-- Every original mixed weak-stage loop component has its canonical K-zero value. -/
theorem stageWeakDiagonalKSpacePiZeroEquivK0_mixed_naturality
    (a : ZerothHomotopy (stageWeakDiagonalKSpace C)) :
    stageWeakDiagonalKSpacePiZeroEquivK0 D
        (ContinuousMap.WeaklyPointed.loopComponentsMap
          (Functor.IsWaldhausenExact.stageWeakDiagonalRealMixedMapWeaklyPointed
            (Functor.IsWaldhausenExact.ofExactCategory F)) a) =
      WaldhausenKTheory.K0.map F (stageWeakDiagonalKSpacePiZeroEquivK0 C a) := by
  induction a using ZerothHomotopy.rec with
  | mk gamma =>
    let gammaRaw : LoopSpace (stageWeakDiagonalReal C) (stageWeakDiagonalReal.basepoint C) := gamma
    let hF := mixedK0Exact F
    let phiC := loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal C)
      (stageWeakDiagonalReal.basepoint C)
    let phiD := loopComponentsEquivFundamentalGroup (stageWeakDiagonalReal D)
      (stageWeakDiagonalReal.basepoint D)
    let zF : ZerothHomotopy
        (LoopSpace (stageWeakDiagonalReal C) (stageWeakDiagonalReal.basepoint C)) →
        ZerothHomotopy
          (LoopSpace (stageWeakDiagonalReal D) (stageWeakDiagonalReal.basepoint D)) :=
      ZerothHomotopy.lift
        (fun x => ZerothHomotopy.mk (hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap x))
        (fun {_ _} p => ZerothHomotopy.sound
          (p.map hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap.continuous))
    have hLiteral : hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopComponentsMap
        (ZerothHomotopy.mk gammaRaw) = zF (ZerothHomotopy.mk gammaRaw) :=
      ContinuousMap.WeaklyPointed.loopComponentsMap_mk
        hF.stageWeakDiagonalRealMixedMapWeaklyPointed gammaRaw
    have hLift : zF (ZerothHomotopy.mk gammaRaw) =
        ZerothHomotopy.mk (hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap gammaRaw) := rfl
    have hLoop : hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap gammaRaw =
        hF.stageWeakDiagonalMixedRootPath.symm.trans
          ((gammaRaw.map hF.stageWeakDiagonalRealMixedMap.continuous).trans
            hF.stageWeakDiagonalMixedRootPath) :=
      (congrArg (fun f : C(stageWeakDiagonalKSpace C, stageWeakDiagonalKSpace D) => f gammaRaw)
        hF.stageWeakDiagonalKSpaceMixedMap_eq).symm.trans
          (hF.stageWeakDiagonalKSpaceMixedMap_apply gammaRaw)
    have hComponents :
        phiD (hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopComponentsMap
          (ZerothHomotopy.mk gammaRaw)) =
        mixedFundamentalMap F (phiC (ZerothHomotopy.mk gammaRaw)) := by
      have hSource := loopComponentsEquivFundamentalGroup_mk gammaRaw
      have hTarget := loopComponentsEquivFundamentalGroup_mk
        (hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopMap gammaRaw)
      have hClassLoop := congrArg
        (fun p : LoopSpace (stageWeakDiagonalReal D) (stageWeakDiagonalReal.basepoint D) =>
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk p)) hLoop
      have hBased := basedFundamentalGroupMap_mk hF.stageWeakDiagonalRealMixedMap
        hF.stageWeakDiagonalMixedRootPath gammaRaw
      exact (congrArg phiD hLiteral).trans
        ((congrArg phiD hLift).trans
          (hTarget.trans (hClassLoop.trans (hBased.symm.trans
            (congrArg (mixedFundamentalMap F) hSource).symm))))
    have hValueD := stageWeakDiagonalKSpacePiZeroEquivK0_apply D
      (hF.stageWeakDiagonalRealMixedMapWeaklyPointed.loopComponentsMap
        (ZerothHomotopy.mk gammaRaw))
    have hValueC := stageWeakDiagonalKSpacePiZeroEquivK0_apply C (ZerothHomotopy.mk gammaRaw)
    have hMapped := congrArg
      (fun g : FundamentalGroup (stageWeakDiagonalReal D) (stageWeakDiagonalReal.basepoint D) =>
        Multiplicative.toAdd (stageWeakDiagonalRealizedFundamentalK0MulEquiv D g)) hComponents
    have hNaturality := congrArg Multiplicative.toAdd
      (stageWeakDiagonalRealizedFundamentalK0MulEquiv_mixed_naturality F
        (phiC (ZerothHomotopy.mk gammaRaw)))
    exact hValueD.trans
      (hMapped.trans (hNaturality.trans (congrArg (WaldhausenKTheory.K0.map F) hValueC).symm))

end CategoryTheory.Waldhausen.SConstruction

end
