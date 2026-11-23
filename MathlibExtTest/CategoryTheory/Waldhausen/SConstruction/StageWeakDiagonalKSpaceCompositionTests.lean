/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceComposition
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalKSpaceCompositionPath

/-!
# K-space composition homotopy consumer tests

Focused same-universe checks for `stageWeakDiagonalKSpaceMap_comp_homotopic`:
the composite-functor map elaborates at the target carrier, and the direct
`(F ⋙ G)` map is endpoint-fixed homotopic to the iterated `G`-after-`F` map,
with the supporting zero-comparison root-path orientation and mapped-root
bridge pinned. No
duplication of the conjugation proof internals.

Nonclaims: no strict map/path equality, pointed-functor layer, additivity,
equivalence, or `π₀` identification.
-/

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalKSpaceCompositionTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]
variable (E : Type u) [Category.{v} E] [Preadditive E] [Limits.HasZeroObject E]
  [HasBinaryBiproducts E] [ExactCategory E]
variable (G : D ⥤ E) [G.Additive] [Functor.IsExact G]

local instance : WaldhausenCategory C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategory D := ExactCategory.waldhausenCategory D
local instance : WaldhausenCategory E := ExactCategory.waldhausenCategory E

/-- Composite-functor map elaborates at the target K-space carrier.

Protects against a missing composition `Additive`/`IsExact` constraint or a
universe-mismatched signature that still names the same declaration. -/
noncomputable example (γ : stageWeakDiagonalKSpace C) :
    stageWeakDiagonalKSpace E :=
  stageWeakDiagonalKSpaceMap C E (F ⋙ G) γ

/-- Direct `(F ⋙ G)` map is homotopic to the iterated `G`-after-`F` map.

Protects against a composition-order flip or endpoint swap that would still
satisfy the generic `Path.Homotopic` API with the two sides exchanged. -/
noncomputable example (γ : stageWeakDiagonalKSpace C) :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      _root_.Path.Homotopic
        (stageWeakDiagonalKSpaceMap C E (F ⋙ G) γ)
        (stageWeakDiagonalKSpaceMap D E G
          (stageWeakDiagonalKSpaceMap C D F γ))) :=
  stageWeakDiagonalKSpaceMap_comp_homotopic C D F E G γ

/-- Direct root path is homotopic to mapped-`F` path followed by the `G` path.

Protects against an endpoint/cast slip in the zero-comparison bridge the
composition conjugation transports along, including a flipped concatenation
order that keeps the same endpoint types. -/
noncomputable example :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      _root_.Path.Homotopic
        (stageWeakDiagonalKSpace.zeroComparisonRootPath C E (F ⋙ G))
        ((((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
          (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
          (by simp [stageWeakDiagonalReal.map_comp])
          rfl).trans
          (stageWeakDiagonalKSpace.zeroComparisonRootPath D E G))) :=
  stageWeakDiagonalKSpace.zeroComparisonRootPath_comp_homotopic C D F E G

/-- Mapped root path bridges the `(F ⋙ G)`-mapped zero to the G-mapped zero.

Protects against a universe-mismatched signature, swapped endpoints, or flipped
orientation that would still name the same declaration. -/
noncomputable example :
    Path.Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath
        (stageWeakDiagonalMapLevelZeroEdge C D F E G))).cast
        (stageWeakDiagonalLevelZeroMapped_basepoint C E (F ⋙ G))
        (stageWeakDiagonalLevelZeroMapped_basepoint D E G))
      (((stageWeakDiagonalKSpace.zeroComparisonRootPath C D F).map
        (map_continuous (stageWeakDiagonalReal.map D E G).hom)).cast
        (by simp [stageWeakDiagonalReal.map_comp])
        rfl) :=
  stageWeakDiagonalKSpace.mappedZeroComparisonRootPath_homotopic C D F E G

end StageWeakDiagonalKSpaceCompositionTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
