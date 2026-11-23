/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroCoherence
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroRealizationPath
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct
public import MathlibExt.Topology.Homotopy.PathConjugationHomotopic

/-!
# Identity homotopy for the weak-diagonal K-space map

For an exact category `C` over same universes with its local standard
Waldhausen structure, the exact-functor map on the one-fold K-space carrier
at the identity functor is pointwise endpoint-fixed homotopic to the identity:
`stageWeakDiagonalKSpaceMap C C (𝟭 C) γ ~ γ`.

The root path at identity is null-homotopic because the mapped-zero vertex
is the zero vertex (`stageWeakDiagonalLevelZero_mappedVertex_id`), the
mapped-zero edge is the degenerate edge (`stageWeakDiagonalLevelZeroEdge_id`),
and the degenerate realized edge path is null directly by
`SSet.realizedEdgePath_id_homotopic`, transported along
`stageWeakDiagonalLevelZeroMapped_basepoint` and
`stageWeakDiagonalReal.basepoint_eq_realizedVertex` with explicit casts.
The mapped loop at identity is homotopic to `γ` via
`stageWeakDiagonalReal.map_id` with explicit casts. Conjugation then
collapses by `Path.Homotopic.conj_null`.

Identity homotopy only. It provides no equality of maps, composition law,
strict pointed functoriality, additivity, or `π₀` identification.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [Limits.HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

/-- Null homotopy for the identity root path, with explicit endpoints. -/
private theorem stageWeakDiagonalKSpace_idRootPath_null
    (hSrc : (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      (stageWeakDiagonalReal.map C C (𝟭 C)) (stageWeakDiagonalReal.basepoint C) =
        stageWeakDiagonalReal.basepoint C)) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      ((stageWeakDiagonalKSpace.zeroComparisonRootPath C C (𝟭 C)).cast
        hSrc.symm rfl).Homotopic
        (Path.refl (stageWeakDiagonalReal.basepoint C))) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  have hMappedBasepoint :
      (stageWeakDiagonalReal.map C C (𝟭 C)) (stageWeakDiagonalReal.basepoint C) =
        SSet.realizedVertex (levelZeroEdgeMappedVertex C C (𝟭 C)) :=
    stageWeakDiagonalLevelZeroMapped_basepoint C C (𝟭 C)
  have hBaseVertex :
      stageWeakDiagonalReal.basepoint C =
        SSet.realizedVertex (stageWeakDiagonalZeroVertex C) :=
    stageWeakDiagonalReal.basepoint_eq_realizedVertex C
  have hEdgeId :
      SSet.Edge.ofEq (SSet.Edge.id (stageWeakDiagonalZeroVertex C))
        (stageWeakDiagonalLevelZero_mappedVertex_id C).symm rfl =
        stageWeakDiagonalLevelZeroEdge C C (𝟭 C) :=
    stageWeakDiagonalLevelZeroEdge_id C
  have hIdHomotopic :
      (TopCat.pathEquiv
        (SSet.realizedEdgePath (SSet.Edge.id (stageWeakDiagonalZeroVertex C)))).Homotopic
        (Path.refl (SSet.realizedVertex (stageWeakDiagonalZeroVertex C))) :=
    SSet.realizedEdgePath_id_homotopic _
  have hUnfold :
      stageWeakDiagonalKSpace.zeroComparisonRootPath C C (𝟭 C) =
        (TopCat.pathEquiv
          (stageWeakDiagonalLevelZeroRealizedPath C C (𝟭 C))).cast
          hMappedBasepoint hBaseVertex := rfl
  rw [hUnfold]
  have hCasted := Path.Homotopic.pathCast hIdHomotopic hBaseVertex hBaseVertex
  convert hCasted using 1
  · apply Path.ext
    ext t
    simp only [Path.cast_coe]
    have hRP : stageWeakDiagonalLevelZeroRealizedPath C C (𝟭 C) =
        SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C C (𝟭 C)) := rfl
    rw [hRP, ← hEdgeId]
    rfl
  · apply Path.ext
    ext t
    simp [hBaseVertex, Path.cast_coe]

/-- Identity functor induces a K-space map pointwise homotopic to the identity. -/
theorem stageWeakDiagonalKSpaceMap_id_homotopic
    (γ : (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalKSpace C)) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      (stageWeakDiagonalKSpaceMap C C (𝟭 C) γ).Homotopic γ) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  have hSrc :
      (stageWeakDiagonalReal.map C C (𝟭 C)) (stageWeakDiagonalReal.basepoint C) =
        stageWeakDiagonalReal.basepoint C := by
    rw [stageWeakDiagonalLevelZeroMapped_basepoint,
      stageWeakDiagonalLevelZero_mappedVertex_id,
      ← stageWeakDiagonalReal.basepoint_eq_realizedVertex]
  have hMapId : stageWeakDiagonalReal.map C C (𝟭 C) = 𝟙 _ :=
    stageWeakDiagonalReal.map_id C
  have hLoop :
      ((stageWeakDiagonalKSpace.mapLoop C C (𝟭 C) γ).cast
        hSrc.symm hSrc.symm).Homotopic γ := by
    have hLoopEq : ((stageWeakDiagonalKSpace.mapLoop C C (𝟭 C) γ).cast
        hSrc.symm hSrc.symm) = γ := by
      apply Path.ext
      funext t
      change (stageWeakDiagonalReal.map C C (𝟭 C)).hom (γ t) = γ t
      rw [hMapId]
      rfl
    rw [hLoopEq]
    exact Path.Homotopic.refl _
  have hShape :
      stageWeakDiagonalKSpaceMap C C (𝟭 C) γ =
        (((stageWeakDiagonalKSpace.zeroComparisonRootPath C C (𝟭 C)).cast
          hSrc.symm rfl).symm.trans
          ((((stageWeakDiagonalKSpace.mapLoop C C (𝟭 C) γ).cast
            hSrc.symm hSrc.symm).trans
            ((stageWeakDiagonalKSpace.zeroComparisonRootPath C C (𝟭 C)).cast
              hSrc.symm rfl)))) := by
    simp only [stageWeakDiagonalKSpaceMap, stageWeakDiagonalKSpace.zeroComparisonRootPath,
      stageWeakDiagonalKSpace.mapLoop]
    rfl
  -- Name the root path p for the exact conjugation shape below.
  let p : Path (stageWeakDiagonalReal.basepoint C) (stageWeakDiagonalReal.basepoint C) :=
    ((stageWeakDiagonalKSpace.zeroComparisonRootPath C C (𝟭 C)).cast hSrc.symm rfl)
  have hNull : p.Homotopic (Path.refl (stageWeakDiagonalReal.basepoint C)) :=
    stageWeakDiagonalKSpace_idRootPath_null C hSrc
  have hConj : (p.symm.trans (γ.trans p)).Homotopic γ :=
    Path.Homotopic.conj_null hNull
  rw [hShape]
  exact (Path.Homotopic.pathCast
    ((Path.Homotopic.refl _).hcomp (hLoop.hcomp (Path.Homotopic.refl _))) rfl rfl).trans
    (Path.Homotopic.pathCast hConj rfl rfl)

end CategoryTheory.Waldhausen.SConstruction
