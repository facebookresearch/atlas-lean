/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.WeakHomotopyEquivalenceHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaQuillenBComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKan
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointFiberComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanTotalHomotopyNatural
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanSourceWeakEquivalenceCommonUniverse
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberHomotopySquare
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.RightCommaBousfieldKanPrism
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakEquivalence
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopyMapPrecomp
public import MathlibExt.AlgebraicTopology.SimplicialSet.HomotopyComp
public import MathlibExt.Topology.Category.TopCat.ProdMapPointwise
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanSkeletalFiberTheorem
public import MathlibExt.Topology.Category.TopCat.HomotopyFiberConullBase

/-!
# Transfer from the BK point-fiber comparison to the right comma

For a functor `F : C ⥤ D` between categories with small hom sets and an object
`d : D`, this file factors the canonical realized right-comma comparison
through the Bousfield--Kan point-fiber comparison and homotopy-fiber transport.
The transport is a weak homotopy equivalence because the BK source projection
is one. Restriction to constant outer chains identifies its path with the
comma-arrow path followed by a constant pause; endpoint-preserving
reparameterization gives the factorization homotopy.

The public interface is the BK fiber transport, its weak-equivalence theorem,
the total-coordinate identity, the factorization homotopy, and the transfer
from a supplied BK point-fiber equivalence. Cylinder, prism, and interval
computations are private.

The source objects have universe `max u w`, the target objects have
universe `u`, and both Hom types have universe `max v w`. The original
nerves and full compact-open homotopy fibers have their common native
value universe `max u v w`. The selected vertex and original comma arrow
are retained in every comparison and coordinate law.

The final transfer assumes directly that the BK point-fiber comparison is a
weak homotopy equivalence. Deriving that premise from transition-map
hypotheses remains the separate BK fiber theorem.
-/

public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Simplicial
open scoped Simplicial CategoryTheory.Prod unitInterval

attribute [local instance] uliftCategory

universe u v w

namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-! ## The BK target map for the right-comma diagram -/

/-- The generic BK projection to the indexing nerve agrees with the
right-comma total target map. -/
private theorem bkHocolimToNerve_rightCommaNerveDiagram (F : C ⥤ D) :
    bkHocolimToNerve (rightCommaNerveDiagram F) =
      rightCommaTotalToTarget F := by
  unfold bkHocolimToNerve rightCommaTotalToTarget
  have hPoint : bkDiagramToPoint (rightCommaNerveDiagram F) =
      rightCommaToPoint F :=
    rfl
  rw [hPoint]

/-! ## The constant-chain inclusion followed by the source projection -/

/-- Including the constant-chain fiber and projecting to the source nerve
recovers the comma projection. -/
private theorem bkPointInclusion_comp_rightCommaTotalToSource
    (F : C ⥤ D) (d : D) :
    bkPointInclusion (rightCommaNerveDiagram F) d ≫
        rightCommaTotalToSource F =
      nerveMapCommonHom.{max u w, v, w} (rightCommaProjectionFunctor.{u, v, w} F d) := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  rw [NatTrans.comp_app, bkPointInclusion_app_mk]
  have h := ConcreteCategory.congr_hom
    (rightCommaTotalToSource_app_mk_ι F n (bkPointWeightedIndex d n)) x
  change ((rightCommaTotalToSource F).app (op ⦋n⦌))
      ((bkPointOuterComponent (rightCommaNerveDiagram F) d n).app
        (op ⦋n⦌) x) = _
  unfold bkPointOuterComponent at h ⊢
  exact h

end SSet

namespace SSet

variable {C : Type (max u w)} {D : Type u}
  [Category.{max v w} C] [Category.{max v w} D]

/-! ## Fiber transport along the realized total homotopy -/

/-- The realized total homotopy from the source route to the target map. -/
private noncomputable def rightCommaTotalHomotopyRealized (F : C ⥤ D) :
    ContinuousMap.Homotopy
      (SSet.toTop.map (rightCommaTotalToSource F) ≫
        SSet.toTop.map (nerveMapCommonHom.{u, w, v} F)).hom
      (SSet.toTop.map (rightCommaTotalToTarget F)).hom :=
  (SSet.realizeHomotopy _ _ _ _ (rightCommaTotalHomotopy F)).cast
    (by rw [Functor.map_comp]) rfl

/-- Transport along the realized total homotopy, from the homotopy fiber of
the BK target map to the homotopy fiber of the nerve map. -/
noncomputable def rightCommaBKFiberTransport (F : C ⥤ D) (d : D) :
    TopCat.homotopyFiber (SSet.toTop.map (rightCommaTotalToTarget F))
        (SSet.realizedVertex
          (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌)) ⟶
      TopCat.homotopyFiber (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
        (SSet.realizedVertex
          (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌)) :=
  TopCat.homotopyFiberMapOfHomotopy _ _ _ _
    (rightCommaTotalHomotopyRealized F)

/-- The BK target fiber transport is a weak homotopy equivalence, since the
BK source projection is one. -/
theorem rightCommaBKFiberTransport_mem_weakHomotopyEquivalences
    (F : C ⥤ D) (d : D) :
    TopCat.weakHomotopyEquivalences
      (rightCommaBKFiberTransport F d) := by
  unfold rightCommaBKFiberTransport
  apply TopCat.homotopyFiberMapOfHomotopy_mem_weakHomotopyEquivalences
  have hSource := rightCommaTotalToSource_mem_realizationWeakEquivalences_commonUniverse F
  rw [SSet.mem_realizationWeakEquivalences_iff] at hSource
  rw [TopCat.mem_weakHomotopyEquivalences_iff]
  exact hSource

/-! ## The cylinder over the constant chain is the arrow prism -/

/-- Over a constant outer chain, the comma/outer-chain bridge is the
whiskered comma-arrow transformation. -/
private theorem rightCommaChainBridgeLift_constChain (F : C ⥤ D) (d : D) (n : ℕ)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj d) n) :
    rightCommaChainBridgeLift F (SrepBridge.constChain d n) X =
      Functor.whiskerLeft (rightCommaPrismLiftChain X)
        (rightCommaArrowNatTrans F d) := by
  refine NatTrans.ext (funext fun i => ?_)
  have hApp := rightCommaChainBridgeLift_app F
    (SrepBridge.constChain d n) X i
  rw [hApp]
  change (X.obj i.down).hom ≫
      (SrepBridge.constChain d n).map' 0 i.down.val =
    (X.obj i.down).hom
  have hmap : (SrepBridge.constChain d n).map' 0 i.down.val = 𝟙 d := rfl
  rw [hmap]
  exact Category.comp_id _

/-- The total prism over the constant chain at `d` is the comma-arrow
cylinder. -/
private theorem rightCommaPrismSimplex_constChain (F : C ⥤ D) (d : D) (n : ℕ)
    (X : ComposableArrows ((CostructuredArrow.functor F).obj d) n)
    (t : (Δ[1] : SSet.{max u v w}).obj (op ⦋n⦌)) :
    rightCommaPrismSimplex F (SrepBridge.constChain d n) X t =
      (CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTrans F d)).app (op ⦋n⦌) ⟨X, t⟩ := by
  let K : rightCommaPrismIndex.{max u v w} n ⥤ CostructuredArrow F d :=
    rightCommaPrismLiftChain X
  let indexChain := rightCommaPrismIndexSimplex.{max u v w} n
  let T := (SSet.stdSimplex.asOrderHom t).toFunctor
  let α : rightCommaProjectionFunctor.{u, v, w} F d ⋙ F ⟶
      (Functor.const (CostructuredArrow F d)).obj d :=
    rightCommaArrowNatTrans F d
  have hBridge := rightCommaChainBridgeLift_constChain F d n X
  change ((CategoryTheory.NatTrans.nerveCylinderFunctor
      (rightCommaChainBridgeLift F (SrepBridge.constChain d n) X)).mapComposableArrows n).obj
        (indexChain.prod' T) =
    ((CategoryTheory.NatTrans.nerveCylinderFunctor α).mapComposableArrows n).obj (X.prod' T)
  rw [hBridge]
  change ((CategoryTheory.NatTrans.nerveCylinderFunctor
      (Functor.whiskerLeft K α)).mapComposableArrows n).obj (indexChain.prod' T) =
    ((CategoryTheory.NatTrans.nerveCylinderFunctor α).mapComposableArrows n).obj (X.prod' T)
  have hClass :
      CategoryTheory.NatTrans.nerveCylinderFunctor (Functor.whiskerLeft K α) =
        (K.prod (𝟭 (Fin 2))) ⋙ CategoryTheory.NatTrans.nerveCylinderFunctor α :=
    CategoryTheory.NatTrans.nerveCylinderFunctor_whiskerLeft.{
      max u v w, 0, max u v w, max v w, u, max v w} K α
  have hClassInput := congrArg
    (fun L : (rightCommaPrismIndex.{max u v w} n × Fin 2) ⥤ D =>
      (L.mapComposableArrows n).obj (indexChain.prod' T)) hClass
  have hProd : ((K.prod (𝟭 (Fin 2))).mapComposableArrows n).obj (indexChain.prod' T) =
      ((K.mapComposableArrows n).obj indexChain).prod' T := by
    apply CategoryTheory.Functor.hext
    · intro i
      rfl
    · intro i j f
      exact HEq.rfl
  have hChain : (K.mapComposableArrows n).obj indexChain = X :=
    nerveMap_rightCommaPrismLiftChain_indexSimplex X
  have hInput : ((K.prod (𝟭 (Fin 2))).mapComposableArrows n).obj (indexChain.prod' T) =
      X.prod' T :=
    hProd.trans (congrArg
      (fun Y : ComposableArrows (CostructuredArrow F d) n => Y.prod' T) hChain)
  exact hClassInput.trans (congrArg
    (fun Y : ComposableArrows (CostructuredArrow F d × Fin 2) n =>
      ((CategoryTheory.NatTrans.nerveCylinderFunctor α).mapComposableArrows n).obj Y)
    hInput)

/-- Restricting the total cylinder along the constant-chain inclusion
recovers the comma-arrow cylinder. -/
private theorem rightCommaTotalCylinder_bkPointInclusion (F : C ⥤ D) (d : D) :
    (bkPointInclusion (rightCommaNerveDiagram F) d ▷
          (Δ[1] : SSet.{max u v w})) ≫
        (rightCommaTotalHomotopy F).h =
      CategoryTheory.NatTrans.nerveHomotopyMapCommonHom.{u, max v w, 0}
        (rightCommaArrowNatTrans F d) := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  obtain ⟨X, t⟩ := x
  change ((bkPointInclusion (rightCommaNerveDiagram F) d ▷
      (Δ[1] : SSet.{max u v w})) ≫
        (rightCommaTotalHomotopy F).h).app (op ⦋n⦌) ⟨X, t⟩ = _
  change (rightCommaTotalHomotopy F).h.app (op ⦋n⦌)
      ⟨(bkPointInclusion (rightCommaNerveDiagram F) d).app
        (op ⦋n⦌) X, t⟩ = _
  rw [bkPointInclusion_app_mk]
  change (rightCommaTotalHomotopy F).h.app (op ⦋n⦌)
      ⟨(bkPointOuterComponent (rightCommaNerveDiagram F) d n).app
        (op ⦋n⦌) X, t⟩ = _
  change (rightCommaTotalCylinder F).app (op ⦋n⦌)
      ⟨(bkPointOuterComponent (rightCommaNerveDiagram F) d n).app
        (op ⦋n⦌) X, t⟩ = _
  rw [rightCommaTotalCylinder_app_mk]
  change rightCommaTotalCylinderDegree F n
      ⟨(bkPointOuterComponent (rightCommaNerveDiagram F) d n).app
        (op ⦋n⦌) X, t⟩ = _
  have hCyl := rightCommaTotalCylinderDegree_ι F n
    (bkPointWeightedIndex d n) X t
  have hCyl' : rightCommaTotalCylinderDegree F n
      ⟨(bkPointOuterComponent (rightCommaNerveDiagram F) d n).app
        (op ⦋n⦌) X, t⟩ =
      rightCommaPrismSimplex F (bkPointWeightedIndex d n).1 X t := hCyl
  rw [hCyl']
  change rightCommaPrismSimplex F (SrepBridge.constChain d n) X t = _
  have hPrism := rightCommaPrismSimplex_constChain F d n X t
  exact hPrism

/-! ## The realized cylinder restricts to the realized arrow homotopy -/

/-- The precomposed total homotopy has the same cylinder as the arrow
homotopy. -/
private theorem rightCommaTotalHomotopy_precomp_cylinder (F : C ⥤ D) (d : D) :
    ((rightCommaTotalHomotopy F).precomp
          (bkPointInclusion (rightCommaNerveDiagram F) d)).h =
      (rightCommaArrowNerveHomotopy F d).h := by
  rw [SSet.Homotopy.precomp_h, rightCommaTotalCylinder_bkPointInclusion]
  rfl

/-- Realization commutes with restricting the total homotopy along the
constant-chain inclusion: the result is the realized comma-arrow homotopy
map. -/
private theorem rightCommaRealizeHomotopyMap_bkPointInclusion (F : C ⥤ D) (d : D) :
    Limits.prod.map (𝟙 TopCat.I.{max u v w})
          (SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d)) ≫
        SSet.realizeHomotopyMap _ _ _ _
          (rightCommaTotalHomotopy F) =
      SSet.realizeHomotopyMap _ _ _ _
        (rightCommaArrowNerveHomotopy F d) := by
  have hPre := SSet.realizeHomotopyMap_precomp (rightCommaTotalHomotopy F)
    (bkPointInclusion (rightCommaNerveDiagram F) d)
  rw [hPre]
  have hH := rightCommaTotalHomotopy_precomp_cylinder F d
  unfold SSet.realizeHomotopyMap
  rw [hH]
  rfl

/-- The realized total-homotopy segment over a constant-chain point is the
realized comma-arrow segment. -/
private theorem rightCommaTotalHomotopyRealized_segment (F : C ⥤ D) (d : D)
    (s : unitInterval)
    (z : SSet.toTop.obj ((rightCommaNerveDiagram F).obj d)) :
    (rightCommaTotalHomotopyRealized F).toFun
        (s, (SSet.toTop.map
          (bkPointInclusion (rightCommaNerveDiagram F) d)).hom z) =
      (SSet.realizeHomotopy _ _ _ _
        (rightCommaArrowNerveHomotopy F d)).toFun (s, z) := by
  have hMap := rightCommaRealizeHomotopyMap_bkPointInclusion F d
  have hPt := ConcreteCategory.congr_hom hMap
    ((TopCat.prodIsoProd TopCat.I.{max u v w} _).inv
      (TopCat.I.homeomorph.symm s, z))
  simp only [TopCat.comp_app] at hPt
  have hRW : (Limits.prod.map (𝟙 TopCat.I.{max u v w})
          (SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d))).hom
        ((TopCat.prodIsoProd TopCat.I.{max u v w} _).inv
          (TopCat.I.homeomorph.symm s, z)) =
        (TopCat.prodIsoProd TopCat.I.{max u v w} _).inv
          (TopCat.I.homeomorph.symm s, (SSet.toTop.map
            (bkPointInclusion (rightCommaNerveDiagram F) d)).hom z) :=
    TopCat.prodMap_prodIso_inv_apply _ _ _
  rw [hRW] at hPt
  exact hPt

/-! ## The comparison factors through the BK fiber, up to homotopy -/

/-- The trans/refl reparameterization as an interval endomap. -/
private noncomputable def rightCommaTransReflReparam : unitInterval → unitInterval :=
  fun t => ⟨Path.Homotopy.transReflReparamAux t,
    Path.Homotopy.transReflReparamAux_mem_I t⟩

private theorem rightCommaTransReflReparam_continuous :
    Continuous rightCommaTransReflReparam :=
  Continuous.subtype_mk Path.Homotopy.continuous_transReflReparamAux _

private theorem rightCommaTransReflReparam_zero :
    rightCommaTransReflReparam 0 = 0 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_zero

private theorem rightCommaTransReflReparam_one :
    rightCommaTransReflReparam 1 = 1 :=
  Subtype.ext Path.Homotopy.transReflReparamAux_one

/-- The BK point-fiber comparison lands over the BK target map, in
target-map form. -/
private theorem rightCommaBKPointFiber_toTotal_target (F : C ⥤ D) (d : D) :
    bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map (rightCommaTotalToTarget F))
        (bkPointRealizedVertex d) =
      SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d) :=
  bkPointFiberComparison_toTotal (rightCommaNerveDiagram F) d

/-- The BK point-fiber path, in target-map form. -/
private theorem rightCommaBKPointFiber_path_target (F : C ⥤ D) (d : D) :
    bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
      TopCat.homotopyFiberPath
        (SSet.toTop.map (rightCommaTotalToTarget F))
        (bkPointRealizedVertex d) =
      bkPointConstantPath (rightCommaNerveDiagram F) d :=
  bkPointFiberComparison_path (rightCommaNerveDiagram F) d

/-- The BK point-fiber path is constantly the vertex. -/
private theorem rightCommaBKPointFiberPath_const (F : C ⥤ D) (d : D)
    (z : SSet.toTop.obj ((rightCommaNerveDiagram F).obj d))
    (t : TopCat.I.{max u v w}) :
    TopCat.homotopyFiberPath
      (SSet.toTop.map (rightCommaTotalToTarget F))
      (bkPointRealizedVertex d)
      (bkPointFiberComparison (rightCommaNerveDiagram F) d z) t =
      SSet.realizedVertex
        (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌) := by
  have hPath := rightCommaBKPointFiber_path_target F d
  have hApp := congr_arg (fun p : TopCat.pathObject _ => p t)
    (ConcreteCategory.congr_hom hPath z)
  exact hApp

/-- The BK target map sends constant-chain points to the vertex. -/
private theorem rightCommaBKTarget_bkPointInclusion (F : C ⥤ D) (d : D)
    (z : SSet.toTop.obj ((rightCommaNerveDiagram F).obj d)) :
    (SSet.toTop.map (rightCommaTotalToTarget F)).hom
      ((SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d)).hom
        z) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌) := by
  have hProj :=
    bkPointInclusion_realized_projection (rightCommaNerveDiagram F) d
  have hEq := bkHocolimToNerve_rightCommaNerveDiagram F
  rw [hEq] at hProj
  have hPt := ConcreteCategory.congr_hom hProj z
  exact hPt

/-- The factored comparison and the direct comparison agree on total
coordinates. -/
theorem rightCommaHomotopyFiberComparison_bkFactorization_toTotal (F : C ⥤ D) (d : D) :
    (bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
      rightCommaBKFiberTransport F d) ≫
      TopCat.homotopyFiberToTotal _ _ =
    rightCommaHomotopyFiberComparison F d ≫
      TopCat.homotopyFiberToTotal _ _ := by
  have hΦtot : rightCommaBKFiberTransport F d ≫
      TopCat.homotopyFiberToTotal (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F)) _ =
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map (rightCommaTotalToTarget F)) _ ≫
        SSet.toTop.map (rightCommaTotalToSource F) :=
    TopCat.homotopyFiberMapOfHomotopy_toTotal _ _ _ _ _
  have hψtot : bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
      TopCat.homotopyFiberToTotal
        (SSet.toTop.map (rightCommaTotalToTarget F)) _ =
      SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d) :=
    bkPointFiberComparison_toTotal (rightCommaNerveDiagram F) d
  have hJS : SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d) ≫
      SSet.toTop.map (rightCommaTotalToSource F) =
      SSet.toTop.map
        (nerveMapCommonHom.{max u w, v, w} (rightCommaProjectionFunctor.{u, v, w} F d)) := by
    rw [← Functor.map_comp, bkPointInclusion_comp_rightCommaTotalToSource]
    rfl
  exact (Category.assoc _ _ _).trans
    ((congr_arg
        (fun m => bkPointFiberComparison (rightCommaNerveDiagram F) d ≫ m)
        hΦtot).trans
      ((Category.assoc _ _ _).symm.trans
        ((congr_arg
            (fun m => m ≫ SSet.toTop.map (rightCommaTotalToSource F))
            hψtot).trans
          (hJS.trans
            (rightCommaHomotopyFiberComparison_toTotal F d).symm))))

/-- The factored comparison path is the arrow path, up to the
trans/refl reparameterization. -/
private theorem rightCommaComparison_bkFactor_hpath (F : C ⥤ D) (d : D)
    (z : SSet.toTop.obj ((rightCommaNerveDiagram F).obj d))
    (t : TopCat.I.{max u v w}) :
    ((bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
      rightCommaBKFiberTransport F d) ≫
      TopCat.homotopyFiberPath _ _) z t =
    ((rightCommaHomotopyFiberComparison F d ≫
      TopCat.homotopyFiberPath _ _) z)
      (TopCat.I.homeomorph.symm
        (rightCommaTransReflReparam (TopCat.I.homeomorph t))) := by
  have hForm := TopCat.homotopyFiberMapOfHomotopy_path
    (SSet.toTop.map (rightCommaTotalToSource F))
    (SSet.toTop.map (rightCommaTotalToTarget F))
    (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F)) (bkPointRealizedVertex d)
    (rightCommaTotalHomotopyRealized F)
    (bkPointFiberComparison (rightCommaNerveDiagram F) d z) t
  have hTot : TopCat.homotopyFiberToTotal
      (SSet.toTop.map (rightCommaTotalToTarget F))
      (bkPointRealizedVertex d)
      (bkPointFiberComparison (rightCommaNerveDiagram F) d z) =
      (SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d)).hom
        z := by
    have hPt := ConcreteCategory.congr_hom
      (rightCommaBKPointFiber_toTotal_target F d) z
    exact hPt
  have hφ : ∀ t' : TopCat.I.{max u v w},
      ((rightCommaHomotopyFiberComparison F d ≫
        TopCat.homotopyFiberPath _ _) z) t' =
        (SSet.realizeHomotopy _ _ _ _
          (rightCommaArrowNerveHomotopy F d)).toFun
          (TopCat.I.homeomorph t', z) := by
    intro t'
    have hP := rightCommaHomotopyFiberComparison_path F d
    have hPt := congr_arg (fun p : TopCat.pathObject _ => p t')
      (ConcreteCategory.congr_hom hP z)
    exact hPt
  have hSeg : ∀ s : unitInterval,
      (rightCommaTotalHomotopyRealized F).toFun
          (s, (SSet.toTop.map
            (bkPointInclusion (rightCommaNerveDiagram F) d)).hom z) =
        (SSet.realizeHomotopy _ _ _ _
          (rightCommaArrowNerveHomotopy F d)).toFun (s, z) :=
    fun s => rightCommaTotalHomotopyRealized_segment F d s z
  have hOne : (rightCommaTotalHomotopyRealized F).toFun
      (1, (SSet.toTop.map
        (bkPointInclusion (rightCommaNerveDiagram F) d)).hom z) =
      SSet.realizedVertex
        (ComposableArrows.mk₀ d : (nerve D : SSet.{max u v w}) _⦋0⦌) := by
    have h1 := (SSet.realizeHomotopy _ _ _ _
      (rightCommaTotalHomotopy F)).map_one_left
      ((SSet.toTop.map (bkPointInclusion (rightCommaNerveDiagram F) d)).hom
        z)
    have hTgt := rightCommaBKTarget_bkPointInclusion F d z
    exact h1.trans hTgt
  change TopCat.homotopyFiberPath (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F))
      (bkPointRealizedVertex d)
      (TopCat.homotopyFiberMapOfHomotopy
        (SSet.toTop.map (rightCommaTotalToSource F))
        (SSet.toTop.map (rightCommaTotalToTarget F))
        (SSet.toTop.map (nerveMapCommonHom.{u, w, v} F)) (bkPointRealizedVertex d)
        (rightCommaTotalHomotopyRealized F)
        (bkPointFiberComparison (rightCommaNerveDiagram F) d z)) t = _
  rw [hForm]
  rw [hφ]
  by_cases h : ((TopCat.I.homeomorph t : unitInterval) : ℝ) ≤ 1 / 2
  · rw [dite_eq_left h]
    rw [hTot]
    have hSymm : TopCat.I.homeomorph
        (TopCat.I.homeomorph.symm
          (rightCommaTransReflReparam (TopCat.I.homeomorph t))) =
        rightCommaTransReflReparam (TopCat.I.homeomorph t) :=
      TopCat.I.homeomorph.apply_symm_apply _
    rw [hSymm]
    have hAux : Path.Homotopy.transReflReparamAux
        (TopCat.I.homeomorph t) = 2 * TopCat.I.homeomorph t := by
      unfold Path.Homotopy.transReflReparamAux
      rw [ite_eq_left h]
    have hReparam : rightCommaTransReflReparam (TopCat.I.homeomorph t) =
        (⟨2 * TopCat.I.homeomorph t, by
          have hmem := Path.Homotopy.transReflReparamAux_mem_I
            (TopCat.I.homeomorph t)
          rw [hAux] at hmem
          exact hmem⟩ : unitInterval) := by
      apply Subtype.ext
      change Path.Homotopy.transReflReparamAux _ = _
      exact hAux
    rw [hReparam, ← hSeg]
    rfl
  · rw [dite_eq_right h]
    rw [rightCommaBKPointFiberPath_const]
    have hSymm : TopCat.I.homeomorph
        (TopCat.I.homeomorph.symm
          (rightCommaTransReflReparam (TopCat.I.homeomorph t))) =
        rightCommaTransReflReparam (TopCat.I.homeomorph t) :=
      TopCat.I.homeomorph.apply_symm_apply _
    rw [hSymm]
    have hAux : Path.Homotopy.transReflReparamAux
        (TopCat.I.homeomorph t) = 1 := by
      unfold Path.Homotopy.transReflReparamAux
      rw [ite_eq_right h]
    have hReparam : rightCommaTransReflReparam (TopCat.I.homeomorph t) =
        (1 : unitInterval) := by
      apply Subtype.ext
      change Path.Homotopy.transReflReparamAux _ = _
      exact hAux
    rw [hReparam, ← hSeg]
    exact hOne.symm

/-- The comparison is homotopic to the BK-fiber factorization. -/
noncomputable def rightCommaBKFactorizationHomotopy (F : C ⥤ D)
    (d : D) :
    ContinuousMap.Homotopy
      (bkPointFiberComparison (rightCommaNerveDiagram F) d ≫
        rightCommaBKFiberTransport F d).hom
      (rightCommaHomotopyFiberComparison F d).hom :=
  TopCat.homotopyFiberReparamHomotopy _ _ _ _
    rightCommaTransReflReparam rightCommaTransReflReparam_continuous
    rightCommaTransReflReparam_zero rightCommaTransReflReparam_one
    (rightCommaHomotopyFiberComparison_bkFactorization_toTotal F d)
    (rightCommaComparison_bkFactor_hpath F d)

/-! ## Transfer of the BK point-fiber weak equivalence -/

/-- If the BK point-fiber comparison of the right-comma diagram is a weak
homotopy equivalence, the actual realized right-comma comparison is one.
The hypothesis is the BK comparison itself; transition-map assumptions do
not occur in this transfer statement. -/
theorem rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences_of_bkPointFiberComparison
    (F : C ⥤ D) (d : D)
    (hFiber : TopCat.weakHomotopyEquivalences
      (bkPointFiberComparison (rightCommaNerveDiagram F) d)) :
    TopCat.weakHomotopyEquivalences
      (rightCommaHomotopyFiberComparison F d) := by
  have hTrans :=
    rightCommaBKFiberTransport_mem_weakHomotopyEquivalences F d
  have hComp := TopCat.weakHomotopyEquivalences.comp_mem _ _ hFiber hTrans
  have hIff := TopCat.weakHomotopyEquivalences_iff_of_homotopy
    (rightCommaBKFactorizationHomotopy F d)
  exact hIff.mp hComp

/-- Weak original arrow transitions and a conull original base make the comma projection weak. -/
theorem rightCommaProjection_mem_of_base_conull
    (F : C ⥤ D)
    (hTransition : ∀ (d d' : D) (g : d ⟶ d'),
      TopCat.weakHomotopyEquivalences
        (toTop.map ((rightCommaNerveDiagram.{max u w, max v w, u} F).map g)))
    (hBase : TopCat.weakHomotopyEquivalences (terminal.from (toTop.obj (nerve D))))
    (d : D) :
    realizationWeakEquivalences
      (nerveMapCommonHom.{max u w, v, w} (CostructuredArrow.proj F d)) := by
  let p := toTop.map (nerveMapCommonHom.{u, w, v} F)
  let b := SSet.realizedVertex (X := (nerve D : SSet.{max u v w}))
    (ComposableArrows.mk₀ d)
  let χ := rightCommaHomotopyFiberComparison F d
  let q := TopCat.homotopyFiberToTotal p b
  have hPoint : TopCat.weakHomotopyEquivalences
      (bkPointFiberComparison (rightCommaNerveDiagram.{max u w, max v w, u} F) d) :=
    bkPointFiberComparison_mem_weakHomotopyEquivalences
      (rightCommaNerveDiagram.{max u w, max v w, u} F) hTransition d
  have hχ : TopCat.weakHomotopyEquivalences χ :=
    rightCommaHomotopyFiberComparison_mem_weakHomotopyEquivalences_of_bkPointFiberComparison
      F d hPoint
  have hq : TopCat.weakHomotopyEquivalences q :=
    TopCat.homotopyFiberToTotal_mem_of_base_conull p b hBase
  have hComposite : TopCat.weakHomotopyEquivalences (χ ≫ q) :=
    TopCat.weakHomotopyEquivalences.comp_mem χ q hχ hq
  have hActual : χ ≫ q =
      toTop.map (nerveMapCommonHom.{max u w, v, w} (CostructuredArrow.proj F d)) :=
    rightCommaHomotopyFiberComparison_toTotal F d
  change TopCat.weakHomotopyEquivalences
    (toTop.map (nerveMapCommonHom.{max u w, v, w} (CostructuredArrow.proj F d)))
  exact hActual ▸ hComposite

end SSet

end
