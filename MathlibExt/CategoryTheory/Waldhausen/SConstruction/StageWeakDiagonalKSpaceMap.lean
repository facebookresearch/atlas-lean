/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpace
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroRealizationPath

/-!
# Exact-functor maps on the weak-diagonal K-space, source layer

For exact categories `C` and `D` over the same universes `u, v` with their
local standard Waldhausen structures (`ExactCategory.waldhausenCategory`),
an additive exact functor `F : C ⥤ D` induces a map on the one-fold K-space
carrier `stageWeakDiagonalKSpaceMap F` by conjugation of the mapped loop with
the explicit mapped-zero-to-target-zero root path.

Orientation convention (do not flip): `zeroComparisonRootPath` goes from the
mapped basepoint `(map F) (basepoint C)` to the target basepoint
`basepoint D`, reusing `stageWeakDiagonalLevelZeroRealizedPath` via
`TopCat.pathEquiv` with `stageWeakDiagonalLevelZeroMapped_basepoint` and
`stageWeakDiagonalReal.basepoint_eq_realizedVertex` endpoint casts. The mapped
loop reuses `stageWeakDiagonalReal.map` via root `Path.map`. The K-space map
sends `γ` to `p.symm.trans ((mapLoop γ).trans p)`, a loop at the target
basepoint.

Same-universe constraints are inherited from `stageWeakDiagonalReal.map`.
Identity and composition homotopy laws are explicitly deferred to a later
module and are not stated here.

Source layer only. It provides no strict pointed maps, additivity,
`π₀`-to-`K₀` identification, weak equivalences, spectra, alternate carrier,
or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

section SameUniverseKSpaceMap

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Root-path version of the mapped-zero path, from the mapped basepoint to
the target basepoint. -/
noncomputable def stageWeakDiagonalKSpace.zeroComparisonRootPath :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      Path ((stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C))
        (stageWeakDiagonalReal.basepoint D)) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact (TopCat.pathEquiv (stageWeakDiagonalLevelZeroRealizedPath C D F)).cast
    (stageWeakDiagonalLevelZeroMapped_basepoint C D F)
    (stageWeakDiagonalReal.basepoint_eq_realizedVertex D)

/-- Mapped loop at the mapped basepoint, via the realization map. -/
noncomputable def stageWeakDiagonalKSpace.mapLoop :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalKSpace C →
        Path ((stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C))
          ((stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C))) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact fun γ => γ.map (map_continuous (stageWeakDiagonalReal.map C D F).hom)

/-- Exact-functor map on the K-space carrier by conjugation with the
mapped-zero-to-target-zero path. -/
noncomputable def stageWeakDiagonalKSpaceMap :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalKSpace C → stageWeakDiagonalKSpace D) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact fun γ =>
    (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).symm.trans
      ((stageWeakDiagonalKSpace.mapLoop C D F γ).trans
        (stageWeakDiagonalKSpace.zeroComparisonRootPath C D F))

end SameUniverseKSpaceMap

end CategoryTheory.Waldhausen.SConstruction
