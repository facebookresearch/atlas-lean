/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalMap
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakDiagonalRealization
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

/-!
# Induced maps on weak-diagonal realizations

For exact categories `C` and `D` over the same universes `u, v` with their
local standard Waldhausen structures (`ExactCategory.waldhausenCategory`),
an additive exact functor `F : C ⥤ D` induces
`stageWeakDiagonalReal.map F : stageWeakDiagonalReal C ⟶ stageWeakDiagonalReal D`
as `SSet.toTop.map (stageWeakDiagonalMap C D F)`.

Only the exact-base strict-equality layer is added: identity and composition
laws reusing `stageWeakDiagonalMap_id`/`comp` with `SSet.toTop` functoriality,
the public basepoint-equals-realized-vertex bridge via `SSet.realizedVertex_eq_const`
on the diagonal zero vertex, and the mapped-basepoint equality via
`SSet.realizedVertex_naturality`.

Nonclaims: no zero-comparison edges, paths, homotopies, pointed morphisms,
additivity, π₀/K₀ identification, G-theory, spectra, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits Opposite Simplicial

open scoped Simplicial

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

section WaldhausenBasepoint

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategory C]

/-- Basepoint is the generic realized vertex of the diagonal zero vertex. -/
theorem stageWeakDiagonalReal.basepoint_eq_realizedVertex :
    stageWeakDiagonalReal.basepoint C =
      SSet.realizedVertex (stageWeakDiagonalZeroVertex C) := by
  simpa [stageWeakDiagonalReal.basepoint, stageWeakDiagonalZeroInclusion] using
    (SSet.realizedVertex_eq_const (stageWeakDiagonalZeroVertex C)).symm

end WaldhausenBasepoint

section ExactRealizationMap

variable (C D : Type u) [Category.{v} C] [Category.{v} D]
  [Preadditive C] [Preadditive D]
  [Limits.HasZeroObject C] [Limits.HasZeroObject D]
  [HasBinaryBiproducts C] [HasBinaryBiproducts D]
  [ExactCategory C] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F]

/-- Induced map on weak-diagonal realizations via `SSet.toTop.map`. -/
noncomputable def stageWeakDiagonalReal.map :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      stageWeakDiagonalReal C ⟶ stageWeakDiagonalReal D) := by
  letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  exact SSet.toTop.map (stageWeakDiagonalMap C D F)

/-- Identity functor induces the identity realization map. -/
@[simp]
theorem stageWeakDiagonalReal.map_id :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      stageWeakDiagonalReal.map C C (𝟭 C) = 𝟙 (stageWeakDiagonalReal C)) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  unfold stageWeakDiagonalReal.map
  rw [stageWeakDiagonalMap_id]
  exact SSet.toTop.map_id _

/-- Composite functors induce composite realization maps. -/
@[simp]
theorem stageWeakDiagonalReal.map_comp (E : Type u) [Category.{v} E]
    [Preadditive E] [Limits.HasZeroObject E]
    [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategory E := ExactCategory.waldhausenCategory E;
      stageWeakDiagonalReal.map C E (F ⋙ G) =
        stageWeakDiagonalReal.map C D F ≫ stageWeakDiagonalReal.map D E G) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  let : WaldhausenCategory E := ExactCategory.waldhausenCategory E
  unfold stageWeakDiagonalReal.map
  rw [stageWeakDiagonalMap_comp]
  rw [SSet.toTop.map_comp]

/-- Mapped basepoint is the realized vertex of the mapped zero vertex. -/
theorem stageWeakDiagonalReal.map_basepoint_eq_realizedVertex :
    (letI : WaldhausenCategory C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategory D := ExactCategory.waldhausenCategory D;
      (stageWeakDiagonalReal.map C D F) (stageWeakDiagonalReal.basepoint C) =
        SSet.realizedVertex
          ((stageWeakDiagonalMap C D F).app (op ⦋0⦌)
            (stageWeakDiagonalZeroVertex C))) := by
  let : WaldhausenCategory C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategory D := ExactCategory.waldhausenCategory D
  unfold stageWeakDiagonalReal.map
  rw [stageWeakDiagonalReal.basepoint_eq_realizedVertex]
  exact (SSet.realizedVertex_naturality (stageWeakDiagonalMap C D F)
    (stageWeakDiagonalZeroVertex C)).symm

end ExactRealizationMap

end CategoryTheory.Waldhausen.SConstruction
