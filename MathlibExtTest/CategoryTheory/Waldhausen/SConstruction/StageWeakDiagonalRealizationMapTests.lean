/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealizationMap

/-!
# Weak-diagonal realization-map consumer tests

Focused same-universe checks for `stageWeakDiagonalReal.map`: induced-map type,
identity/composition rewrite behavior via `map_id`/`map_comp`, basepoint as the
generic realized vertex, and mapped-basepoint naturality equality. No
zero-comparison edge/path or pointed-morphism claims.

Nonclaims: no paths, homotopies, additivity, π₀/K₀, G-theory, spectra, or Q/S
comparison.
-/

open CategoryTheory Limits Opposite Simplicial
open CategoryTheory.Waldhausen.SConstruction

open scoped Simplicial

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageWeakDiagonalRealizationMapTests

variable (C : Type u) [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u) [Category.{v} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

local instance : WaldhausenCategory C := ExactCategory.waldhausenCategory C
local instance : WaldhausenCategory D := ExactCategory.waldhausenCategory D

/-- Induced map elaborates as a map between realizations. -/
noncomputable example : stageWeakDiagonalReal C ⟶ stageWeakDiagonalReal D :=
  stageWeakDiagonalReal.map C D F

/-- Identity functor induces the identity realization map. -/
example : stageWeakDiagonalReal.map C C (𝟭 C) = 𝟙 (stageWeakDiagonalReal C) :=
  stageWeakDiagonalReal.map_id C

/-- Composite functors induce composite realization maps. -/
example (E : Type u) [Category.{v} E] [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E] (G : D ⥤ E) [G.Additive]
    [Functor.IsExact G] :
    stageWeakDiagonalReal.map C E (F ⋙ G) =
      stageWeakDiagonalReal.map C D F ≫ stageWeakDiagonalReal.map D E G :=
  stageWeakDiagonalReal.map_comp C D F E G

/-- Basepoint is the realized vertex of the diagonal zero vertex. -/
example : stageWeakDiagonalReal.basepoint C =
    SSet.realizedVertex (stageWeakDiagonalZeroVertex C) :=
  stageWeakDiagonalReal.basepoint_eq_realizedVertex C

/-- Mapped basepoint is the realized vertex of the mapped zero vertex. -/
example : (stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C) =
    SSet.realizedVertex
      ((stageWeakDiagonalMap C D F).app (op ⦋0⦌)
        (stageWeakDiagonalZeroVertex C)) :=
  stageWeakDiagonalReal.map_basepoint_eq_realizedVertex C D F

section GenericBasepoint

variable (G : Type u) [Category.{v} G] [Limits.HasZeroObject G] [WaldhausenCategory G]

/-- Basepoint equality holds for a generic Waldhausen category. -/
example : stageWeakDiagonalReal.basepoint G =
    SSet.realizedVertex (stageWeakDiagonalZeroVertex G) :=
  stageWeakDiagonalReal.basepoint_eq_realizedVertex G

end GenericBasepoint

end StageWeakDiagonalRealizationMapTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
