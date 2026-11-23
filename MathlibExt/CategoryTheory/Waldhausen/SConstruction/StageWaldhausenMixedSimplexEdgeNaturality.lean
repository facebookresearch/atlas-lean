/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenMixedRealizationMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalZeroContraction
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationUniverseLift

/-!
# Original mixed realization simplex and sigma-edge values

The actual mixed weak-stage map keeps every original simplex and its
barycentric parameter through BOTH retained realization universe-lift
isomorphisms. The degree-one sigma-arrow specialization retains the actual
original stage arrows, endpoint vertices and interval parameter.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite Simplicial
open scoped Simplicial Topology

universe u v

private def originalMixedOrdinarySimplexPoint
    (X : SSet.{u}) (n : SimplexCategory) (x : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) : SSet.toTop.obj X :=
  SSet.toTop.map (SSet.yonedaEquiv.symm x)
    ((SSet.toTopSimplex.{u}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{u}.obj n))

private def originalMixedLiftedStandardSimplexJ (n : SimplexCategory) :
    SSet.stdSimplex.{max u v}.obj n ⟶
      SSet.uliftFunctor.{v, u}.obj (SSet.stdSimplex.{u}.obj n) where
  app a := ↾fun q => ULift.up (ULift.up q.down)
  naturality {a b} f := by ext q; rfl

private theorem originalMixedLiftedYonedaFactor
    (X : SSet.{u}) (n : SimplexCategory) (x : X.obj (op n)) :
    (SSet.yonedaEquiv.symm
      (ULift.up x : (SSet.uliftFunctor.{v, u}.obj X).obj (op n))) =
      originalMixedLiftedStandardSimplexJ.{u, v} n ≫
        SSet.uliftFunctor.{v, u}.map (SSet.yonedaEquiv.symm x) := by
  ext a q
  rfl

private theorem originalMixedLiftIsoSimplexForward
    (X : SSet.{u}) (n : SimplexCategory) (x : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    (SSet.toTopULiftIso.{u, v}.hom.app X)
      (originalMixedOrdinarySimplexPoint
        (SSet.uliftFunctor.{v, u}.obj X) n (ULift.up x) t) =
      (ULift.up (originalMixedOrdinarySimplexPoint X n x t) :
        TopCat.uliftFunctor.{v, u}.obj (SSet.toTop.obj X)) := by
  let S := SSet.stdSimplex.{u}.obj n
  let SL := SSet.stdSimplex.{max u v}.obj n
  let f : S ⟶ X := SSet.yonedaEquiv.symm x
  let J := originalMixedLiftedStandardSimplexJ.{u, v} n
  let K : SL ⟶ SSet.uliftFunctor.{v, u}.obj X :=
    SSet.yonedaEquiv.symm (ULift.up x)
  let U := SSet.toTopULiftIso.{u, v}
  let p : SSet.toTop.obj SL :=
    (SSet.toTopSimplex.{max u v}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max u v}.obj n)
  let jp := SSet.toTop.map J p
  have hK : SSet.toTop.map K =
      SSet.toTop.map J ≫ SSet.toTop.map (SSet.uliftFunctor.{v, u}.map f) :=
    (congrArg SSet.toTop.map (originalMixedLiftedYonedaFactor.{u, v} X n x)).trans
      (SSet.toTop.map_comp J (SSet.uliftFunctor.{v, u}.map f))
  have hKValue : SSet.toTop.map K p =
      SSet.toTop.map (SSet.uliftFunctor.{v, u}.map f) jp :=
    (ConcreteCategory.congr_hom hK p).trans
      (CategoryTheory.comp_apply (SSet.toTop.map J)
        (SSet.toTop.map (SSet.uliftFunctor.{v, u}.map f)) p)
  have hNat := ConcreteCategory.congr_hom (U.hom.naturality f) jp
  have hNatValue : U.hom.app X
      (SSet.toTop.map (SSet.uliftFunctor.{v, u}.map f) jp) =
      (TopCat.uliftFunctor.{v, u}.map (SSet.toTop.map f)) (U.hom.app S jp) :=
    (CategoryTheory.comp_apply
      (SSet.toTop.map (SSet.uliftFunctor.{v, u}.map f)) (U.hom.app X) jp).symm.trans
        (hNat.trans (CategoryTheory.comp_apply (U.hom.app S)
          (TopCat.uliftFunctor.{v, u}.map (SSet.toTop.map f)) jp))
  have hStd : U.hom.app S jp =
      (ULift.up ((SSet.toTopSimplex.{u}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{u}.obj n)) :
          TopCat.uliftFunctor.{v, u}.obj (SSet.toTop.obj S)) :=
    SSet.toTopULiftIso_hom_simplexValue.{u, v} n t
  have hLast : (TopCat.uliftFunctor.{v, u}.map (SSet.toTop.map f))
      (ULift.up ((SSet.toTopSimplex.{u}.inv.app n)
        (ULift.up t : SimplexCategory.toTop.{u}.obj n))) =
      (ULift.up (originalMixedOrdinarySimplexPoint X n x t) :
        TopCat.uliftFunctor.{v, u}.obj (SSet.toTop.obj X)) := by
    rfl
  change U.hom.app X (SSet.toTop.map K p) = _
  exact (congrArg (U.hom.app X) hKValue).trans
    (hNatValue.trans ((congrArg
      (TopCat.uliftFunctor.{v, u}.map (SSet.toTop.map f)) hStd).trans hLast))

private theorem originalMixedLiftIsoSimplexInverse
    (X : SSet.{u}) (n : SimplexCategory) (x : X.obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    (SSet.toTopULiftIso.{u, v}.inv.app X)
      (ULift.up (originalMixedOrdinarySimplexPoint X n x t) :
        TopCat.uliftFunctor.{v, u}.obj (SSet.toTop.obj X)) =
      originalMixedOrdinarySimplexPoint
        (SSet.uliftFunctor.{v, u}.obj X) n (ULift.up x) t := by
  have h := congrArg (SSet.toTopULiftIso.{u, v}.inv.app X)
    (originalMixedLiftIsoSimplexForward.{u, v} X n x t)
  exact h.symm.trans
    (ConcreteCategory.congr_hom (SSet.toTopULiftIso.{u, v}.app X).hom_inv_id
      (originalMixedOrdinarySimplexPoint
        (SSet.uliftFunctor.{v, u}.obj X) n (ULift.up x) t))

private def originalMixedIntervalBarycentricPoint (t : unitInterval) :
    Convexity.StdSimplex ℝ (Fin (⦋1⦌.len + 1)) :=
  Convexity.StdSimplex.homeomorphI.symm t

private theorem originalMixedIntervalSimplexClock (t : unitInterval) :
    SSet.stdSimplex.toTopObjIsoI.{u}.inv (TopCat.I.homeomorph.symm t) =
      (SSet.toTopSimplex.{u}.inv.app ⦋1⦌)
        (ULift.up (originalMixedIntervalBarycentricPoint t) :
          SimplexCategory.toTop.{u}.obj ⦋1⦌) := by
  rfl

private theorem originalMixedRealizedEdgePathSimplexValue
    (X : SSet.{u}) {x₀ x₁ : X.obj (op ⦋0⦌)} (e : X.Edge x₀ x₁)
    (t : unitInterval) :
    (TopCat.pathEquiv (SSet.realizedEdgePath e)).toContinuousMap.toFun t =
      originalMixedOrdinarySimplexPoint X ⦋1⦌ e.edge
        (originalMixedIntervalBarycentricPoint t) := by
  have hHom := congrArg
    (fun q : TopCat.I.{u} ⟶ SSet.toTop.obj X =>
      q.hom.toFun (TopCat.I.homeomorph.symm t))
    (SSet.realizedEdgePath_hom e)
  have hPoint := CategoryTheory.comp_apply SSet.stdSimplex.toTopObjIsoI.{u}.inv
    (SSet.toTop.map (SSet.yonedaEquiv.symm e.edge)) (TopCat.I.homeomorph.symm t)
  have hClock := congrArg
    (fun y : SSet.toTop.obj (SSet.stdSimplex.{u}.obj ⦋1⦌) =>
      SSet.toTop.map (SSet.yonedaEquiv.symm e.edge) y)
    (originalMixedIntervalSimplexClock.{u} t)
  change (SSet.realizedEdgePath e).hom.hom.toFun (TopCat.I.homeomorph.symm t) = _
  exact hHom.trans (hPoint.trans hClock)

universe uB vB uD vD

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {B : Type uB} [Category.{vB} B] [HasZeroObject B] [WaldhausenCategory B]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategory D]
variable {F : B ⥤ D}

private theorem originalMixedRealizationSimplexValueComputed
    (hF : F.IsWaldhausenExact) (n : SimplexCategory)
    (x : (stageWeakDiagonal B).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    hF.stageWeakDiagonalRealMixedMap
      (originalMixedOrdinarySimplexPoint (stageWeakDiagonal B) n x t) =
      originalMixedOrdinarySimplexPoint (stageWeakDiagonal D) n
        (x ⋙ hF.mapStageWeak n.len) t := by
  let XB := stageWeakDiagonal B
  let XD := stageWeakDiagonal D
  let UB := SSet.toTopULiftIso.{max uB vB, max uD vD}.app XB
  let UD := SSet.toTopULiftIso.{max uD vD, max uB vB}.app XD
  let M := SSet.toTop.map hF.stageWeakDiagonalMixedMap
  let y : XD.obj (op n) := x ⋙ hF.mapStageWeak n.len
  let xL : (SSet.uliftFunctor.{max uD vD, max uB vB}.obj XB).obj (op n) := ULift.up x
  let yL : (SSet.uliftFunctor.{max uB vB, max uD vD}.obj XD).obj (op n) := ULift.up y
  let LB : SSet.stdSimplex.{max uB vB uD vD}.obj n ⟶
      SSet.uliftFunctor.{max uD vD, max uB vB}.obj XB :=
    SSet.yonedaEquiv.symm xL
  let LD : SSet.stdSimplex.{max uB vB uD vD}.obj n ⟶
      SSet.uliftFunctor.{max uB vB, max uD vD}.obj XD :=
    SSet.yonedaEquiv.symm yL
  have hMapped : hF.stageWeakDiagonalMixedMap.app (op n) xL = yL :=
    stageWeakDiagonalMixedMap_app hF (op n) xL
  have hYoneda : LB ≫ hF.stageWeakDiagonalMixedMap = LD :=
    (SSet.yonedaEquiv_symm_comp xL hF.stageWeakDiagonalMixedMap).trans
      (congrArg SSet.yonedaEquiv.symm hMapped)
  have hMap : SSet.toTop.map LB ≫ M = SSet.toTop.map LD :=
    (SSet.toTop.map_comp LB hF.stageWeakDiagonalMixedMap).symm.trans
      (congrArg SSet.toTop.map hYoneda)
  let p : SSet.toTop.obj (SSet.stdSimplex.{max uB vB uD vD}.obj n) :=
    (SSet.toTopSimplex.{max uB vB uD vD}.inv.app n)
      (ULift.up t : SimplexCategory.toTop.{max uB vB uD vD}.obj n)
  have hM : M (originalMixedOrdinarySimplexPoint
      (SSet.uliftFunctor.{max uD vD, max uB vB}.obj XB) n (ULift.up x) t) =
      originalMixedOrdinarySimplexPoint
        (SSet.uliftFunctor.{max uB vB, max uD vD}.obj XD) n (ULift.up y) t :=
    (CategoryTheory.comp_apply (SSet.toTop.map LB) M p).symm.trans
      (ConcreteCategory.congr_hom hMap p)
  have hB := originalMixedLiftIsoSimplexInverse.{max uB vB, max uD vD} XB n x t
  have hD := originalMixedLiftIsoSimplexForward.{max uD vD, max uB vB} XD n y t
  rw [stageWeakDiagonalRealMixedMap_apply]
  exact congrArg ULift.down
    ((congrArg (fun q => UD.hom (M q)) hB).trans
      ((congrArg UD.hom hM).trans hD))

/-- Every original simplex and barycentric point is mapped by SAME actual
weak-stage functor through BOTH retained original carrier-lift isomorphisms. -/
theorem stageWeakDiagonalRealMixedMap_simplexValue
    (hF : F.IsWaldhausenExact) (n : SimplexCategory)
    (x : (stageWeakDiagonal B).obj (op n))
    (t : Convexity.StdSimplex ℝ (Fin (n.len + 1))) :
    hF.stageWeakDiagonalRealMixedMap
      (SSet.toTop.map (SSet.yonedaEquiv.symm x)
        ((SSet.toTopSimplex.{max uB vB}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max uB vB}.obj n))) =
      SSet.toTop.map (SSet.yonedaEquiv.symm (x ⋙ hF.mapStageWeak n.len))
        ((SSet.toTopSimplex.{max uD vD}.inv.app n)
          (ULift.up t : SimplexCategory.toTop.{max uD vD}.obj n)) :=
  originalMixedRealizationSimplexValueComputed hF n x t

private theorem originalMixedOneArrowPostcomposition
    {A E : Type*} [Category* A] [Category* E] (G : A ⥤ E)
    {X Y : A} (f : X ⟶ Y) :
    ComposableArrows.mk₁ f ⋙ G = ComposableArrows.mk₁ (G.map f) := by
  refine ComposableArrows.ext₁ (F := ComposableArrows.mk₁ f ⋙ G)
    (G := ComposableArrows.mk₁ (G.map f)) rfl rfl ?_
  simp

private theorem originalMixedSigmaSimplexValueComputed
    (hF : F.IsWaldhausenExact) {S T : StageWeakCategory B 0} (f : S ⟶ T) :
    ((stageWeakDiagonalStageZeroMapEdge B f).edge ⋙ hF.mapStageWeak 1) =
      (stageWeakDiagonalStageZeroMapEdge D ((hF.mapStageWeak 0).map f)).edge := by
  have hFunctor : reindexStageWeak B (SimplexCategory.σ (0 : Fin 1)) ⋙
      hF.mapStageWeak 1 = hF.mapStageWeak 0 ⋙
        reindexStageWeak D (SimplexCategory.σ (0 : Fin 1)) :=
    hF.mapStageWeak_reindex (SimplexCategory.σ (0 : Fin 1))
  have hChain := congrArg
    (fun G : StageWeakCategory B 0 ⥤ StageWeakCategory D 1 =>
      (G.mapComposableArrows 1).obj (ComposableArrows.mk₁ f)) hFunctor
  change (ComposableArrows.mk₁ f ⋙
      (reindexStageWeak B (SimplexCategory.σ (0 : Fin 1)) ⋙ hF.mapStageWeak 1)) =
    (ComposableArrows.mk₁ f ⋙
      (hF.mapStageWeak 0 ⋙ reindexStageWeak D (SimplexCategory.σ (0 : Fin 1)))) at hChain
  have hLeft := originalMixedOneArrowPostcomposition
    (reindexStageWeak B (SimplexCategory.σ (0 : Fin 1))) f
  have hRightFirst := originalMixedOneArrowPostcomposition (hF.mapStageWeak 0) f
  have hRightLast := originalMixedOneArrowPostcomposition
    (reindexStageWeak D (SimplexCategory.σ (0 : Fin 1))) ((hF.mapStageWeak 0).map f)
  rw [stageWeakDiagonalStageZeroMapEdge_edge, stageWeakDiagonalStageZeroMapEdge_edge]
  exact (congrArg (fun X : ComposableArrows (StageWeakCategory B 1) 1 =>
    X ⋙ hF.mapStageWeak 1) hLeft).symm.trans
      (hChain.trans ((congrArg
        (fun X : ComposableArrows (StageWeakCategory D 0) 1 =>
          X ⋙ reindexStageWeak D (SimplexCategory.σ (0 : Fin 1))) hRightFirst).trans hRightLast))

/-- The actual mixed degree1 map carries ORIGINAL sigma0 arrow simplex
into ORIGINAL sigma0 simplex of the actual mapped Stage0 arrow. -/
theorem stageWeakDiagonalMixedMap_sigmaSimplex
    (hF : F.IsWaldhausenExact) {S T : StageWeakCategory B 0} (f : S ⟶ T) :
    hF.stageWeakDiagonalMixedMap.app (op ⦋1⦌)
      (ULift.up (stageWeakDiagonalStageZeroMapEdge B f).edge) =
      ULift.up (stageWeakDiagonalStageZeroMapEdge D ((hF.mapStageWeak 0).map f)).edge :=
  (stageWeakDiagonalMixedMap_app hF (op ⦋1⦌)
    (ULift.up (stageWeakDiagonalStageZeroMapEdge B f).edge)).trans
      (congrArg ULift.up (originalMixedSigmaSimplexValueComputed hF f))

private theorem originalMixedStageZeroVertexValueComputed
    (hF : F.IsWaldhausenExact) (S : StageWeakCategory B 0) :
    hF.stageWeakDiagonalRealMixedMap (SSet.realizedVertex (ComposableArrows.mk₀ S)) =
      SSet.realizedVertex (ComposableArrows.mk₀ ((hF.mapStageWeak 0).obj S)) := by
  have hVertex : (ComposableArrows.mk₀ S ⋙ hF.mapStageWeak 0) =
      ComposableArrows.mk₀ ((hF.mapStageWeak 0).obj S) := by
    apply ComposableArrows.ext₀
    rfl
  exact (stageWeakDiagonalRealMixedMap_realizedVertex hF (ComposableArrows.mk₀ S)).trans
    (congrArg SSet.realizedVertex hVertex)

/-- The actual image of every ORIGINAL Stage0 vertex retains the actual
mixed weak-stage functor value. This earns BOTH sigma-edge endpoint casts. -/
theorem stageWeakDiagonalRealMixedMap_stageZeroVertex
    (hF : F.IsWaldhausenExact) (S : StageWeakCategory B 0) :
    hF.stageWeakDiagonalRealMixedMap (SSet.realizedVertex (ComposableArrows.mk₀ S)) =
      SSet.realizedVertex (ComposableArrows.mk₀ ((hF.mapStageWeak 0).obj S)) :=
  originalMixedStageZeroVertexValueComputed hF S

private theorem originalMixedSigmaPathValueComputed
    (hF : F.IsWaldhausenExact) {S T : StageWeakCategory B 0} (f : S ⟶ T)
    (t : unitInterval) :
    hF.stageWeakDiagonalRealMixedMap
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalStageZeroMapEdge B f))).toContinuousMap.toFun t) =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (stageWeakDiagonalStageZeroMapEdge D ((hF.mapStageWeak 0).map f)))).toContinuousMap.toFun t := by
  let fReal : C(stageWeakDiagonalReal B, stageWeakDiagonalReal D) :=
    hF.stageWeakDiagonalRealMixedMap
  have hSource := originalMixedRealizedEdgePathSimplexValue
    (stageWeakDiagonal B) (stageWeakDiagonalStageZeroMapEdge B f) t
  have hTarget := originalMixedRealizedEdgePathSimplexValue
    (stageWeakDiagonal D)
      (stageWeakDiagonalStageZeroMapEdge D ((hF.mapStageWeak 0).map f)) t
  have hSimplex := originalMixedRealizationSimplexValueComputed hF ⦋1⦌
    (stageWeakDiagonalStageZeroMapEdge B f).edge (originalMixedIntervalBarycentricPoint t)
  have hSigma := congrArg
    (fun x : (stageWeakDiagonal D).obj (op ⦋1⦌) =>
      originalMixedOrdinarySimplexPoint (stageWeakDiagonal D) ⦋1⦌ x
        (originalMixedIntervalBarycentricPoint t))
    (originalMixedSigmaSimplexValueComputed hF f)
  exact (congrArg fReal.toFun hSource).trans
    (hSimplex.trans (hSigma.trans hTarget.symm))

/-- Every actual interval value of the ORIGINAL sigma0 edge is preserved
by the mixed realization map with the SAME original barycentric clock. -/
theorem stageWeakDiagonalRealMixedMap_sigmaPath_apply
    (hF : F.IsWaldhausenExact) {S T : StageWeakCategory B 0} (f : S ⟶ T)
    (t : unitInterval) :
    hF.stageWeakDiagonalRealMixedMap
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalStageZeroMapEdge B f))).toContinuousMap.toFun t) =
      (TopCat.pathEquiv
        (SSet.realizedEdgePath
          (stageWeakDiagonalStageZeroMapEdge D ((hF.mapStageWeak 0).map f)))).toContinuousMap.toFun t :=
  originalMixedSigmaPathValueComputed hF f t

private theorem originalMixedSigmaPathNaturalityComputed
    (hF : F.IsWaldhausenExact) {S T : StageWeakCategory B 0} (f : S ⟶ T) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (stageWeakDiagonalStageZeroMapEdge B f))).map
        hF.stageWeakDiagonalRealMixedMap.continuous =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalStageZeroMapEdge D ((hF.mapStageWeak 0).map f)))).cast
          (stageWeakDiagonalRealMixedMap_stageZeroVertex hF S)
          (stageWeakDiagonalRealMixedMap_stageZeroVertex hF T) := by
  apply _root_.Path.ext
  funext t
  exact originalMixedSigmaPathValueComputed hF f t

/-- The whole ORIGINAL sigma0 edge path maps to the whole ORIGINAL mapped
sigma0 path. BOTH endpoint casts are earned actual mixed-map vertex values. -/
theorem stageWeakDiagonalRealMixedMap_sigmaPath
    (hF : F.IsWaldhausenExact) {S T : StageWeakCategory B 0} (f : S ⟶ T) :
    (TopCat.pathEquiv (SSet.realizedEdgePath
      (stageWeakDiagonalStageZeroMapEdge B f))).map
        hF.stageWeakDiagonalRealMixedMap.continuous =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalStageZeroMapEdge D ((hF.mapStageWeak 0).map f)))).cast
          (stageWeakDiagonalRealMixedMap_stageZeroVertex hF S)
          (stageWeakDiagonalRealMixedMap_stageZeroVertex hF T) :=
  originalMixedSigmaPathNaturalityComputed hF f

end CategoryTheory.Functor.IsWaldhausenExact

end
