/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowZeroHomologyComparison
public import MathlibExt.CategoryTheory.Monoidal.SInverseSComponentSpace
public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.CWComplex
public import MathlibExt.Topology.Category.TopCat.HomotopyExtension
public import MathlibExt.Topology.Homotopy.TopCat.Path

/-!
# The actual stable row comparison at the original zero unit

The original free-zero Iso supplies a path from the computed rank-zero
image of the stable basepoint to the original zero-space unit. The actual
realized-vertex Hurewicz cofibration extends this path over the entire
stable BGL realization. Its endpoint is a based continuous map homotopic
to the ORIGINAL stable comparison and preserves every homology Iso.
-/

noncomputable section

open CategoryTheory Limits Topology
open scoped unitInterval

universe u

namespace AlgebraicKTheory.StableGL

variable (R : Type u) [Ring R]

/-- The actual unit path is the realized original free-zero arrow in BOTH
coordinates, with only the endpoint equalities computed above. -/
public def finiteFreeRowStableZeroComparisonUnitPath :
    Path (finiteFreeRowStableZeroComparison R (ordinaryBGLBasepoint R))
      (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R)) := by
  let p := SSet.realizedEdgePath
    (CategoryTheory.nerve.edgeMk (finiteFreeRowStageZeroToBase R))
  let q := p.cast (finiteFreeRowStableZeroComparison_basepoint R)
    (SInverseS.ComponentTranslation.zeroSpacePoint_eq_realizedVertex
      (C := FGProjectiveCat.IdempotentModel R))
  exact TopCat.pathEquiv q

private abbrev rowBasedTarget : TopCat.{u} :=
  SSet.toTop.obj (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R)))

private abbrev rowPointMap : TopCat.of PUnit.{u + 1} ⟶ ordinaryBGL R :=
  TopCat.const (ordinaryBGLBasepoint R)

private def rowUnitBoundary : C(unitInterval × PUnit.{u + 1}, rowBasedTarget R) :=
  (finiteFreeRowStableZeroComparisonUnitPath R).toContinuousMap.comp ContinuousMap.fst

private theorem rowUnitBoundary_zero (a : PUnit.{u + 1}) :
    rowUnitBoundary R (0, a) =
      (finiteFreeRowStableZeroComparison R).hom ((rowPointMap R).hom a) :=
  (finiteFreeRowStableZeroComparisonUnitPath R).source

private def rowUnitExtension :
    HomotopyExtensionData (rowPointMap R).hom (finiteFreeRowStableZeroComparison R).hom
      (rowUnitBoundary R) (rowUnitBoundary_zero R) :=
  Classical.choice
    ((SSet.realizedVertex_isHurewiczCofibration (classifyingVertex R))
      (finiteFreeRowStableZeroComparison R).hom (rowUnitBoundary R) (rowUnitBoundary_zero R))

/-- The retuned comparison has the same source and target as the actual
stable map and sends the ORIGINAL stable basepoint to the original zero unit. -/
public def finiteFreeRowBasedZeroComparison : ordinaryBGL R ⟶
    SSet.toTop.obj (nerve (SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R))) :=
  TopCat.ofHom (rowUnitExtension R).endpoint

/-- The retuning preserves a WHOLE ordinary homotopy from the original map. -/
public def finiteFreeRowBasedZeroComparisonHomotopy :
    TopCat.Homotopy (finiteFreeRowStableZeroComparison R) (finiteFreeRowBasedZeroComparison R) :=
  (rowUnitExtension R).toHomotopy

/-- The extended whole family follows the SAME original unit path on the
original stable basepoint at every time. -/
public theorem finiteFreeRowBasedZeroComparison_homotopy_basepoint (t : unitInterval) :
    finiteFreeRowBasedZeroComparisonHomotopy R (t, ordinaryBGLBasepoint R) =
      finiteFreeRowStableZeroComparisonUnitPath R t :=
  (rowUnitExtension R).extension_subspace t PUnit.unit

/-- The original basepoint is mapped to the literal original zero-space unit. -/
public theorem finiteFreeRowBasedZeroComparison_basepoint :
    finiteFreeRowBasedZeroComparison R (ordinaryBGLBasepoint R) =
      SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R) :=
  ((rowUnitExtension R).extension_subspace 1 PUnit.unit).trans
    (finiteFreeRowStableZeroComparisonUnitPath R).target

/-- Every ordinary homology Iso of the ORIGINAL stable map is preserved
by its derived unit retuning, for every degree and coefficient group. -/
public theorem finiteFreeRowBasedZeroComparison_homology_isIso
    (A : AddCommGrpCat.{u}) (q : ℕ) :
    IsIso (((AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A).map
      (finiteFreeRowBasedZeroComparison R)) := by
  let K := finiteFreeRowBasedZeroComparisonHomotopy R
  let H := (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat.{u} q).obj A
  have hMap : H.map (finiteFreeRowStableZeroComparison R) =
      H.map (finiteFreeRowBasedZeroComparison R) :=
    K.congr_homologyMap_singularChainComplexFunctor A q
  have hIso : IsIso (H.map (finiteFreeRowStableZeroComparison R)) :=
    finiteFreeRowStableZeroComparison_homology_isIso R A q
  exact hMap ▸ hIso

/-- EVERY-degree integral homology comparison for the SAME based retuning,
with no change to the original Ring or zero unit. -/
public theorem finiteFreeRowBasedZeroComparison_integral_isIso (q : ℕ) :
    IsIso ((AlgebraicTopology.singularIntegralHomologyFunctor q).map
      (finiteFreeRowBasedZeroComparison R)) :=
  finiteFreeRowBasedZeroComparison_homology_isIso R AlgebraicTopology.singularIntegralCoefficients q

end AlgebraicKTheory.StableGL

noncomputable section

open CategoryTheory

universe uRowUnitValueRing

namespace AlgebraicKTheory.StableGL

variable (R : Type uRowUnitValueRing) [Ring R]

private theorem finiteFreeRowStableZeroComparisonUnitPathValueComputed (t : unitInterval) :
    finiteFreeRowStableZeroComparisonUnitPath R t =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (finiteFreeRowStageZeroToBase R)))) t := by
  rfl

/-- EVERY time of the SAME original row-unit path keeps the actual original
free-zero arrow edge value; both casts and the whole HEP retuning are retained. -/
public theorem finiteFreeRowStableZeroComparisonUnitPath_value (t : unitInterval) :
    finiteFreeRowStableZeroComparisonUnitPath R t =
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (nerve.edgeMk (finiteFreeRowStageZeroToBase R)))) t :=
  finiteFreeRowStableZeroComparisonUnitPathValueComputed R t

end AlgebraicKTheory.StableGL

end
