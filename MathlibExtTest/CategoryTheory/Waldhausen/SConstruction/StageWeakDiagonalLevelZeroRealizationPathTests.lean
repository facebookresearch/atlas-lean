/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalLevelZeroRealizationPath

/-!
# Direct weak-stage realized-path consumer tests

Focused public-API checks for `stageWeakDiagonalLevelZeroRealizedPath`: oriented path type,
`hom` formula via `realizedEdgePath`, endpoint laws `hom₀`/`hom₁`, and the mapped/target
basepoint bridges. No strict pointed functor, additivity, `π₀ ≃ K₀`, G-theory, spectra, or Q/S.
-/

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.Waldhausen.SConstruction

open scoped Simplicial

universe v u v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalLevelZeroRealizationPathTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategory C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategory D := ExactCategory.waldhausenCategory D

variable (C₁ : Type u₁) [Category.{v₁} C₁] [Preadditive C₁] [Limits.HasZeroObject C₁]
  [HasBinaryBiproducts C₁] [ExactCategory C₁]
variable (D₁ : Type u₂) [Category.{v₂} D₁] [Preadditive D₁] [Limits.HasZeroObject D₁]
  [HasBinaryBiproducts D₁] [ExactCategory D₁]
variable (F₁ : C₁ ⥤ D₁) [F₁.Additive] [Functor.IsExact F₁]

local instance : WaldhausenCategory C₁ := ExactCategory.waldhausenCategory C₁
local instance : WaldhausenCategory D₁ := ExactCategory.waldhausenCategory D₁

/-- Realized path runs from the mapped-zero vertex to the target-zero vertex.

Protects against an orientation flip that would still satisfy the generic `Path` API. -/
noncomputable example :
    (stageWeakDiagonalReal D₁).Path
      (SSet.realizedVertex (levelZeroEdgeMappedVertex C₁ D₁ F₁))
      (SSet.realizedVertex (stageWeakDiagonalZeroVertex D₁)) :=
  stageWeakDiagonalLevelZeroRealizedPath C₁ D₁ F₁

/-- Hom unfolds to the underlying realized edge-path hom.

Protects against rewiring the path to a different 1-simplex with the same endpoints. -/
example :
    (stageWeakDiagonalLevelZeroRealizedPath C D F).hom =
      (SSet.realizedEdgePath (stageWeakDiagonalLevelZeroEdge C D F)).hom :=
  stageWeakDiagonalLevelZeroRealizedPath_hom C D F

/-- Source endpoint is the realized mapped-zero vertex.

Protects against a path that starts at the target zero. -/
example :
    (stageWeakDiagonalLevelZeroRealizedPath C D F).hom (0 : TopCat.I) =
      SSet.realizedVertex (levelZeroEdgeMappedVertex C D F) :=
  stageWeakDiagonalLevelZeroRealizedPath_hom₀ C D F

/-- Target endpoint is the realized target-zero vertex.

Protects against a path that lands at the mapped zero. -/
example :
    (stageWeakDiagonalLevelZeroRealizedPath C₁ D₁ F₁).hom (1 : TopCat.I) =
      SSet.realizedVertex (stageWeakDiagonalZeroVertex D₁) :=
  stageWeakDiagonalLevelZeroRealizedPath_hom₁ C₁ D₁ F₁

/-- Target basepoint bridge: the basepoint is the realized target vertex.

Protects against a basepoint disconnected from the path endpoint. -/
example :
    stageWeakDiagonalReal.basepoint D₁ =
      SSet.realizedVertex (stageWeakDiagonalZeroVertex D₁) :=
  stageWeakDiagonalReal.basepoint_eq_realizedVertex D₁

/-- Mapped basepoint bridge: the mapped basepoint is the realized mapped vertex.

Protects against a mapped basepoint disconnected from the path start. -/
example :
    (stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C) =
      SSet.realizedVertex (levelZeroEdgeMappedVertex C D F) :=
  stageWeakDiagonalLevelZeroMapped_basepoint C D F

end StageWeakDiagonalLevelZeroRealizationPathTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
