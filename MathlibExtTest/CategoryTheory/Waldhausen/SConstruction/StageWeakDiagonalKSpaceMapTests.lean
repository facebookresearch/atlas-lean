/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceIdentity
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceMap

/-!
# Weak-diagonal K-space map consumer tests

Focused same-universe checks for `stageWeakDiagonalKSpaceMap`: exact-functor
typeclass inference, orientation of `zeroComparisonRootPath`, and source/target
of `mapLoop` before conjugation. No carrier-only, later-gate, additivity,
π₀/K₀, spectra, or Q/S claims.
-/

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalKSpaceMapTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategory C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategory D := ExactCategory.waldhausenCategory D

/-- Map elaborates with exact-functor/universe/typeclass inference.

Protects against a missing `Additive`/`IsExact` constraint or a
universe-mismatched signature that still names the same declaration. -/
noncomputable example : stageWeakDiagonalKSpace C → stageWeakDiagonalKSpace D :=
  stageWeakDiagonalKSpaceMap C D F

/-- Root path runs from the mapped basepoint to the target basepoint.

Protects against an orientation flip that would still satisfy the generic
`Path` API but swap the comparison direction. -/
noncomputable example :
    Path ((stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C))
      (stageWeakDiagonalReal.basepoint D) :=
  stageWeakDiagonalKSpace.zeroComparisonRootPath C D F

/-- Mapped loop stays at the mapped basepoint before conjugation.

Protects against wiring the pre-conjugation loop to the target basepoint or to
a different realization point while keeping the final conjugation shape. -/
noncomputable example (γ : stageWeakDiagonalKSpace C) :
    Path ((stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C))
      ((stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C)) :=
  stageWeakDiagonalKSpace.mapLoop C D F γ

/-- Identity exact-functor map is endpoint-fixed homotopic to the identity.

Protects against a dropped identity law that still names the same declaration,
without unfolding the proof or claiming composition/strict equality. -/
noncomputable example (γ : stageWeakDiagonalKSpace C) :
    Path.Homotopic (stageWeakDiagonalKSpaceMap C C (𝟭 C) γ) γ :=
  stageWeakDiagonalKSpaceMap_id_homotopic C γ

end StageWeakDiagonalKSpaceMapTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
