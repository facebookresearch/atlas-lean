/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroCoherence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelTwoZeroComparison
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct

/-!
# Realized root-path composition homotopy for G4

For exact categories `C`, `D`, `E` over the same universes with additive exact
`F : C ⥤ D` and `G : D ⥤ E`, the direct root path `zeroComparisonRootPath C E (F ⋙ G)`
is endpoint-fixed homotopic to the mapped `F` root path followed by the `G` root
path, with explicit endpoint casts and direct-to-concatenated orientation.

Reuses the diagonal `levelTwoZeroComparisonCompStruct` via
`SSet.realizedCompStructHomotopic` and the mapped-root-path bridge
`mappedZeroComparisonRootPath_homotopic`, with `stageWeakDiagonalReal.map_comp`
for the mapped source cast. Local proof `have`s only; no new path definitions.

No final K-space composition law, strict pointed functoriality, additivity,
or `π₀` claim.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]
variable (E : Type u) [Category.{v} E] [Preadditive E]
  [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

/-- Mapped root-path bridge: the realized G-mapped F diagonal zero edge agrees,
up to endpoint-fixed homotopy and explicit casts, with the `Path.map` image of
`zeroComparisonRootPath C D F` along `stageWeakDiagonalReal.map D E G`.
Orientation `(F ⋙ G)`-mapped zero → G-mapped zero. No realized triangle or
K-space composition law is claimed. -/
theorem stageWeakDiagonalKSpace.mappedZeroComparisonRootPath_homotopic :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      (TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalMapLevelZeroEdge C D F E G))).cast
        (stageWeakDiagonalLevelZeroMapped_basepoint C E (F ⋙ G))
        (stageWeakDiagonalLevelZeroMapped_basepoint D E G)).Homotopic
      (((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
        (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
        (by simp [stageWeakDiagonalReal.map_comp])
        rfl) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategory E := ExactCategory.waldhausenCategory E
  have hNat := SSet.realizedEdgePath_naturality_hom
    (stageWeakDiagonalMap D E G) (stageWeakDiagonalLevelZeroEdge C D F)
  have hEdge : (stageWeakDiagonalMapLevelZeroEdge C D F E G).edge =
      (((stageWeakDiagonalLevelZeroEdge C D F).map
        (stageWeakDiagonalMap D E G))).edge := rfl
  have hHomEq : (SSet.realizedEdgePath
      (stageWeakDiagonalMapLevelZeroEdge C D F E G)).hom =
      (SSet.realizedEdgePath ((stageWeakDiagonalLevelZeroEdge C D F).map
        (stageWeakDiagonalMap D E G))).hom := by
    rw [SSet.realizedEdgePath_hom, SSet.realizedEdgePath_hom, hEdge]
  have hMap : (stageWeakDiagonalReal.map D E G) =
      SSet.toTop.map (stageWeakDiagonalMap D E G) := rfl
  have hPathEq : ((TopCat.pathEquiv (SSet.realizedEdgePath
      (stageWeakDiagonalMapLevelZeroEdge C D F E G))).cast
      (stageWeakDiagonalLevelZeroMapped_basepoint C E (F ⋙ G))
      (stageWeakDiagonalLevelZeroMapped_basepoint D E G)) =
    (((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
      (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
      (by simp [stageWeakDiagonalReal.map_comp])
      rfl) := by
    apply Path.ext
    ext t
    change (SSet.realizedEdgePath
        (stageWeakDiagonalMapLevelZeroEdge C D F E G)).hom.hom
        (TopCat.I.homeomorph.symm t) =
      ((((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
        (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
        (by simp [stageWeakDiagonalReal.map_comp])
        rfl)) t
    simp only [Path.map_coe, Path.cast_coe, Function.comp_apply]
    simp only [stageWeakDiagonalKSpace.zeroComparisonRootPath,
      stageWeakDiagonalLevelZeroRealizedPath]
    simp only [Path.cast_coe]
    rw [hHomEq, hNat, hMap]
    simp only [show ((TopCat.pathEquiv
      (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F))) t =
      (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F)).hom.hom
      (TopCat.I.homeomorph.symm t)) from rfl]
    simp only [SSet.realizedEdgePath_hom,
      stageWeakDiagonalLevelZeroEdge_edge,
      TopCat.hom_comp, ContinuousMap.comp_apply]
  rw [hPathEq]

/-- Direct root path is homotopic to mapped-then-direct concatenation.

Orientation (do not flip): direct `(F ⋙ G)` path on the left, mapped `F` path
cast along `map_comp` followed by the `G` path on the right. Endpoints are
`(map C E (F ⋙ G)) (basepoint C)` to `basepoint E`. -/
theorem stageWeakDiagonalKSpace.zeroComparisonRootPath_comp_homotopic :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      (stageWeakDiagonalKSpace.zeroComparisonRootPath C E (F ⋙ G)).Homotopic
        ((((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
          (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
          (by simp [stageWeakDiagonalReal.map_comp])
          rfl).trans
          (stageWeakDiagonalKSpace.zeroComparisonRootPath D E G))) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategory E := ExactCategory.waldhausenCategory E
  have hTri := SSet.realizedCompStructHomotopic
    (levelTwoZeroComparisonCompStruct C D F E G)
  have hSrcComp := stageWeakDiagonalLevelZeroMapped_basepoint C E (F ⋙ G)
  have hMid := stageWeakDiagonalLevelZeroMapped_basepoint D E G
  have hTgt := stageWeakDiagonalReal.basepoint_eq_realizedVertex E
  have hCast := Path.Homotopic.pathCast hTri hSrcComp hTgt
  rw [Path.cast_trans (TopCat.pathEquiv (SSet.realizedEdgePath
    (stageWeakDiagonalMapLevelZeroEdge C D F E G))) (TopCat.pathEquiv
    (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge D E G)))
    hSrcComp hMid hTgt] at hCast
  have hpDirect :
      stageWeakDiagonalKSpace.zeroComparisonRootPath C E (F ⋙ G) =
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (stageWeakDiagonalLevelZeroEdge C E (F ⋙ G)))).cast
          hSrcComp hTgt := by
    apply Path.ext
    simp only [Path.cast_coe,
      stageWeakDiagonalKSpace.zeroComparisonRootPath,
      stageWeakDiagonalLevelZeroRealizedPath]
  have hpG :
      stageWeakDiagonalKSpace.zeroComparisonRootPath D E G =
        (TopCat.pathEquiv (SSet.realizedEdgePath
          (stageWeakDiagonalLevelZeroEdge D E G))).cast
          hMid hTgt := by
    apply Path.ext
    simp only [Path.cast_coe,
      stageWeakDiagonalKSpace.zeroComparisonRootPath,
      stageWeakDiagonalLevelZeroRealizedPath]
  have hBridge := stageWeakDiagonalKSpace.mappedZeroComparisonRootPath_homotopic
    C D F E G
  rw [← hpDirect, ← hpG] at hCast
  have hCong := hBridge.hcomp (Path.Homotopic.refl
    (stageWeakDiagonalKSpace.zeroComparisonRootPath D E G))
  exact hCast.trans hCong

end CategoryTheory.Waldhausen.SConstruction
