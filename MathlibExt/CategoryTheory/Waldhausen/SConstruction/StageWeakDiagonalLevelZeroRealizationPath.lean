/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroEdge
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationMap

/-!
# Realized path for the mapped-zero edge in the weak-stage diagonal

For exact categories `C` and `D` with an additive exact functor `F`,
realize the mapped-zero edge `stageWeakDiagonalLevelZeroEdge C D F`
directly as a `TopCat.Path` in `stageWeakDiagonalReal D` from the realized
mapped-zero vertex to the realized target-zero vertex, via
`SSet.realizedEdgePath`.

Orientation convention (do not flip): `δ 1` is the source face and points at
`0 : TopCat.I`, while `δ 0` is the target face and points at `1 : TopCat.I`.
This matches `SSet.Edge.src_eq` (`δ 1` gives the mapped vertex) and
`SSet.Edge.tgt_eq` (`δ 0` gives the target vertex).

Path-only. It provides no strict pointed functor, additivity, `π₀ ≃ K₀`,
G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

open scoped Simplicial

universe v₁ u₁ v₂ u₂
universe v u

namespace CategoryTheory.Waldhausen.SConstruction

section CrossUniversePath

variable (C : Type u₁) [Category.{v₁} C]
  [Preadditive C]
  [Limits.HasZeroObject C]
  [HasBinaryBiproducts C]
  [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D]
  [Preadditive D]
  [Limits.HasZeroObject D]
  [HasBinaryBiproducts D]
  [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Named realized path from the mapped-zero vertex to the target-zero vertex. -/
noncomputable def stageWeakDiagonalLevelZeroRealizedPath :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalReal D).Path
        (SSet.realizedVertex (levelZeroEdgeMappedVertex C D F))
        (SSet.realizedVertex (stageWeakDiagonalZeroVertex D))) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F)

/-- Hom of the realized mapped-zero path, unfolded. -/
@[simp]
theorem stageWeakDiagonalLevelZeroRealizedPath_hom :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalLevelZeroRealizedPath C D F).hom =
        (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F)).hom) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  rfl

/-- Source endpoint: at `0 : TopCat.I` the path is the mapped-zero vertex. -/
theorem stageWeakDiagonalLevelZeroRealizedPath_hom₀ :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalLevelZeroRealizedPath C D F).hom (0 : TopCat.I) =
        SSet.realizedVertex (levelZeroEdgeMappedVertex C D F)) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F)).hom₀

/-- Target endpoint: at `1 : TopCat.I` the path is the target-zero vertex. -/
theorem stageWeakDiagonalLevelZeroRealizedPath_hom₁ :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalLevelZeroRealizedPath C D F).hom (1 : TopCat.I) =
        SSet.realizedVertex (stageWeakDiagonalZeroVertex D)) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F)).hom₁

end CrossUniversePath

section SameUniverseMappedBasepoint

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Mapped basepoint bridge: the mapped basepoint equals the realized mapped vertex. -/
theorem stageWeakDiagonalLevelZeroMapped_basepoint :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C) =
        SSet.realizedVertex (levelZeroEdgeMappedVertex C D F)) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  rw [stageWeakDiagonalReal.map_basepoint_eq_realizedVertex,
    stageWeakDiagonalMap_zeroVertex]
  rfl

end SameUniverseMappedBasepoint

end CategoryTheory.Waldhausen.SConstruction
