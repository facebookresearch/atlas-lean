/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanPointInclusion
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizedNullhomotopy
public import MathlibExt.Topology.Category.TopCat.HomotopyPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

/-!
# Point-to-fiber comparison for a Bousfield--Kan homotopy colimit

For a simplicial-set diagram `E : J ⥤ SSet`, every object `j : J` determines
the constant outer bar chain at `j`.  Its weighted-bar coproduct inclusions
assemble to a canonical map from `E.obj j` to the Bousfield--Kan carrier.
The projection of this map to `nerve J` is the constant vertex at `j`, so its
realization lifts canonically to the homotopy fiber using the constant path.

This file constructs that comparison and records its total and path
coordinates.  It does not assert the Bousfield--Kan fiber lemma saying that
the comparison is a weak equivalence for a homotopically constant diagram.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace SSet

universe u v

variable {J : Type u} [Category.{v} J]

/-- Inclusion of a diagram value into one outer weighted-bar degree along
constant chains, specialized to the original inferable universes. -/
noncomputable def bkPointOuterComponent (E : J ⥤ SSet.{max u v}) (j : J) (n : ℕ) :
    E.obj j ⟶ StrictOrdinaryWeightedBar.wbarObj (CategoryBar.replUnit J) E n :=
  bkPointOuterComponentOf.{u,v,0} E j n

/-- The original inferable simplicial-data map specializes the single canonical inclusion core. -/
noncomputable def bkPointOuterDataMap (E : J ⥤ SSet.{max u v}) (j : J) :
    SimplicialObject.Data.constData (E.obj j) ⟶
      StrictOrdinaryWeightedBar.wbarData (CategoryBar.replUnit J) E :=
  bkPointOuterDataMapOf.{u,v,0} E j

/-- The original outer simplicial map specializes the canonical independent-universe
implementation. -/
noncomputable def bkPointOuterMap (E : J ⥤ SSet.{max u v}) (j : J) :
    (SimplicialObject.Data.constData (E.obj j)).toSimplicialObject ⟶
      StrictOrdinaryWeightedBar.wbarSimplicial (CategoryBar.replUnit J) E :=
  bkPointOuterMapOf.{u,v,0} E j

@[simp]
theorem bkPointOuterMap_app_mk (E : J ⥤ SSet.{max u v}) (j : J) (n : ℕ) :
    (bkPointOuterMap E j).app (op ⦋n⦌) = bkPointOuterComponent E j n :=
  bkPointOuterMapOf_app_mk.{u,v,0} E j n

/-- The original source Iso is the same canonical diagonal-of-constant comparison. -/
noncomputable def bkPointSourceIso (E : J ⥤ SSet.{max u v}) (j : J) :
    simplicialDiagonalFunctor.obj (SimplicialObject.Data.constData (E.obj
      j)).toSimplicialObject ≅ E.obj j :=
  bkPointSourceIsoOf.{u,v,0} E j

/-- The original inferable point inclusion uses the single canonical independent-universe core. -/
noncomputable def bkPointInclusion (E : J ⥤ SSet.{max u v}) (j : J) : E.obj j ⟶ bkHocolim E :=
  bkPointInclusionOf.{u,v,0} E j

@[simp]
theorem bkPointInclusion_app_mk (E : J ⥤ SSet.{max u v}) (j : J) (n : ℕ) :
    (bkPointInclusion E j).app (op ⦋n⦌) = (bkPointOuterComponent E j n).app (op ⦋n⦌) :=
  bkPointInclusionOf_app_mk.{u,v,0} E j n

/-- Objectwise terminal map from an arbitrary diagram to the constant point
diagram. -/
def bkDiagramToPoint (E : J ⥤ SSet.{max u v}) :
    E ⟶ bkPointDiagram J where
  app _ := stdSimplex.isTerminalObj₀.from _
  naturality _ _ _ := stdSimplex.isTerminalObj₀.hom_ext _ _

/-- Projection of a Bousfield--Kan carrier to the nerve of its indexing
category. -/
noncomputable def bkHocolimToNerve (E : J ⥤ SSet.{max u v}) :
    bkHocolim E ⟶ nerve J :=
  bkHocolimMap (bkDiagramToPoint E) ≫ (bkPointIsoNerve J).hom

/-- The point-diagram comparison sends a weighted summand to its indexing
chain. -/
theorem bkPointIsoNerve_hom_wbarIncl (n : ℕ)
    (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n) :
    (StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) (bkPointDiagram J) n p).app (op ⦋n⦌) ≫
      (bkPointIsoNerve J).hom.app (op ⦋n⦌) =
        ↾fun _ => p.1 := by
  unfold bkPointIsoNerve pointRowNatIso
  change (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) (bkPointDiagram J) n p).app (op ⦋n⦌) ≫
      (pointRowIso J (op ⦋n⦌)).hom.app (op ⦋n⦌) = _
  rw [← wbarRowIncl_eq_wbarIncl_app]
  have hRowMorph := terminalWeightRowIso_hom_rowIncl
    (bkPointDiagram J) (op ⦋n⦌) n p
  have hRoute :
      wbarRowIncl (bkPointDiagram J) (op ⦋n⦌) n p ≫
          (pointRowIso J (op ⦋n⦌)).hom.app (op ⦋n⦌) =
        terminalWeightReplIncl (bkPointDiagram J) (op ⦋n⦌) n p ≫
          ((pointReplacementIso J (op ⦋n⦌)).hom.app (op ⦋n⦌) ≫
            (bkPointReplacementNerveIso J).hom.app (op ⦋n⦌)) := by
    unfold pointRowIso
    simp only [Iso.trans_hom, NatTrans.comp_app]
    exact (Category.assoc _ _ _).symm.trans
      (congrArg (· ≫
        ((pointReplacementIso J (op ⦋n⦌)).hom.app (op ⦋n⦌) ≫
          (bkPointReplacementNerveIso J).hom.app (op ⦋n⦌))) hRowMorph)
  rw [hRoute]
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨s, w⟩ := p
  change PUnit at w
  cases w
  rfl

/-- The BK projection sends the constant-chain inclusion to the constant
vertex selected by the indexing object. -/
theorem bkPointInclusion_comp_bkHocolimToNerve
    (E : J ⥤ SSet.{max u v}) (j : J) :
    bkPointInclusion E j ≫ bkHocolimToNerve E =
      SSet.const (ComposableArrows.mk₀ j) := by
  ext Δ x
  obtain ⟨⟨n⟩⟩ := Δ
  let p := bkPointWeightedIndex j n
  have hMap := bkHocolimMap_app_mk_ι
    (bkDiagramToPoint E) n p
  have hMapApply := ConcreteCategory.congr_hom hMap x
  have hPoint := bkPointIsoNerve_hom_wbarIncl (J := J) n p
  have hPointApply := ConcreteCategory.congr_hom hPoint
    (((bkDiagramToPoint E).app j).app (op ⦋n⦌) x)
  change (bkHocolimMap (bkDiagramToPoint E)).app (op ⦋n⦌)
      ((bkPointOuterComponent E j n).app (op ⦋n⦌) x) =
    (StrictOrdinaryWeightedBar.wbarIncl
      (CategoryBar.replUnit J) (bkPointDiagram J) n p).app (op ⦋n⦌)
        (((bkDiagramToPoint E).app j).app (op ⦋n⦌) x) at hMapApply
  change (bkPointIsoNerve J).hom.app (op ⦋n⦌)
      ((StrictOrdinaryWeightedBar.wbarIncl
        (CategoryBar.replUnit J) (bkPointDiagram J) n p).app (op ⦋n⦌)
          (((bkDiagramToPoint E).app j).app (op ⦋n⦌) x)) = p.1 at hPointApply
  change (bkHocolimToNerve E).app (op ⦋n⦌)
      ((bkPointInclusion E j).app (op ⦋n⦌) x) =
    (SSet.const (ComposableArrows.mk₀ j)).app (op ⦋n⦌) x
  rw [bkPointInclusion_app_mk]
  change (bkPointIsoNerve J).hom.app (op ⦋n⦌)
      ((bkHocolimMap (bkDiagramToPoint E)).app (op ⦋n⦌)
        ((bkPointOuterComponent E j n).app (op ⦋n⦌) x)) = _
  rw [hMapApply, hPointApply]
  rfl

/-- Vertex of the indexing nerve selected by `j`, after realization. -/
noncomputable abbrev bkPointRealizedVertex (j : J) :
    SSet.toTop.obj (nerve J) :=
  SSet.realizedVertex
    (ComposableArrows.mk₀ j : (nerve J : SSet.{max u v}) _⦋0⦌)

/-- The constant compact-open path at the selected indexing vertex. -/
noncomputable def bkPointConstantPath (E : J ⥤ SSet.{max u v}) (j : J) :
    SSet.toTop.obj (E.obj j) ⟶
      TopCat.pathObject (SSet.toTop.obj (nerve J)) :=
  TopCat.const (bkPointRealizedVertex j) ≫
    TopCat.ofHom ContinuousMap.const'

@[reassoc]
theorem bkPointConstantPath_evalZero (E : J ⥤ SSet.{max u v}) (j : J) :
    bkPointConstantPath E j ≫
        TopCat.pathEvalZero (SSet.toTop.obj (nerve J)) =
      TopCat.const (X := SSet.toTop.obj (E.obj j))
        (bkPointRealizedVertex j) := by
  apply TopCat.ext
  intro x
  rfl

@[reassoc]
theorem bkPointConstantPath_evalOne (E : J ⥤ SSet.{max u v}) (j : J) :
    bkPointConstantPath E j ≫
        TopCat.pathEvalOne (SSet.toTop.obj (nerve J)) =
      TopCat.const (X := SSet.toTop.obj (E.obj j))
        (bkPointRealizedVertex j) := by
  apply TopCat.ext
  intro x
  rfl

/-- After realization, the BK point inclusion still lies over the selected
indexing vertex. -/
theorem bkPointInclusion_realized_projection
    (E : J ⥤ SSet.{max u v}) (j : J) :
    SSet.toTop.map (bkPointInclusion E j) ≫
        SSet.toTop.map (bkHocolimToNerve E) =
      TopCat.const (X := SSet.toTop.obj (E.obj j))
        (bkPointRealizedVertex j) := by
  rw [← Functor.map_comp, bkPointInclusion_comp_bkHocolimToNerve]
  apply TopCat.hom_ext
  exact SSet.toTop_map_const_hom (A := E.obj j) (Y := nerve J)
    (ComposableArrows.mk₀ j : (nerve J : SSet.{max u v}) _⦋0⦌)

/-- Canonical map from a diagram value to the homotopy fiber of the BK
projection over its indexing vertex. -/
noncomputable def bkPointFiberComparison
    (E : J ⥤ SSet.{max u v}) (j : J) :
    SSet.toTop.obj (E.obj j) ⟶
      TopCat.homotopyFiber
        (SSet.toTop.map (bkHocolimToNerve E))
        (bkPointRealizedVertex j) :=
  pullback.lift
    (Limits.prod.lift
      (SSet.toTop.map (bkPointInclusion E j))
      (TopCat.isTerminalPUnit.from _))
    (bkPointConstantPath E j)
    (by
      apply Limits.prod.hom_ext
      · simpa [TopCat.pathEndpoints, Category.assoc] using
          (bkPointInclusion_realized_projection E j).trans
            (bkPointConstantPath_evalZero E j).symm
      · have hconst :
            TopCat.isTerminalPUnit.from (SSet.toTop.obj (E.obj j)) ≫
                TopCat.const (X := TopCat.of PUnit)
                  (bkPointRealizedVertex j) =
              TopCat.const (X := SSet.toTop.obj (E.obj j))
                (bkPointRealizedVertex j) := by
            apply TopCat.ext
            intro x
            rfl
        simpa [TopCat.pathEndpoints, Category.assoc] using
          hconst.trans (bkPointConstantPath_evalOne E j).symm)

/-- The BK point-fiber comparison retains the constant-chain inclusion as
its total-space coordinate. -/
@[reassoc]
theorem bkPointFiberComparison_toTotal
    (E : J ⥤ SSet.{max u v}) (j : J) :
    bkPointFiberComparison E j ≫
        TopCat.homotopyFiberToTotal
          (SSet.toTop.map (bkHocolimToNerve E))
          (bkPointRealizedVertex j) =
      SSet.toTop.map (bkPointInclusion E j) := by
  rw [bkPointFiberComparison, ← Category.assoc, pullback.lift_fst]
  simp

/-- The BK point-fiber comparison carries the constant path at the selected
indexing vertex. -/
@[reassoc]
theorem bkPointFiberComparison_path
    (E : J ⥤ SSet.{max u v}) (j : J) :
    bkPointFiberComparison E j ≫
        TopCat.homotopyFiberPath
          (SSet.toTop.map (bkHocolimToNerve E))
          (bkPointRealizedVertex j) =
      bkPointConstantPath E j := by
  rw [bkPointFiberComparison, pullback.lift_snd]

end SSet

end
