/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.Stage
public import Mathlib.CategoryTheory.Products.Basic
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory

/-!
# Stage source/quotient evaluation functors

Paired evaluation of `Stage C 2` at the `(0, 1)` (source) and `(1, 2)`
(quotient) intervals: `sourceQuotientStage C := (eval C 2 01).prod'
(eval C 2 12)` with `rfl` object and `fst`/`snd` map computation laws, plus
its restriction `sourceQuotientStageWeak C` through `stageWeakInclusion`
with the corresponding `rfl` computation laws.

Same-universe categorical layer over `Stage`, `Products.Basic`, and
`StageWeakCategory` only. No preadditive, exact, or biproduct hypotheses.

Explicit nonclaims: no opposite composite or retraction, no equivalence,
no deformation, no realization, no weak equivalence, no additivity, no K₀,
no spectrum, and no Q/S comparison.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Paired source-quotient evaluation at `(0, 1)` and `(1, 2)`. -/
def sourceQuotientStage : Stage C 2 ⥤ C × C :=
  (eval C 2 (interval (0 : Fin 3) 1 (by decide))).prod'
    (eval C 2 (interval (1 : Fin 3) 2 (by decide)))

/-- Object part is the paired evaluations. -/
@[simp]
theorem sourceQuotientStage_obj (X : Stage C 2) :
    (sourceQuotientStage C).obj X =
      ((eval C 2 (interval (0 : Fin 3) 1 (by decide))).obj X,
        (eval C 2 (interval (1 : Fin 3) 2 (by decide))).obj X) := rfl

/-- First component map is the `(0, 1)` evaluation map. -/
@[simp]
theorem sourceQuotientStage_map_fst {X Y : Stage C 2} (φ : X ⟶ Y) :
    (((sourceQuotientStage C).map φ).1 =
      (eval C 2 (interval (0 : Fin 3) 1 (by decide))).map φ) := rfl

/-- Second component map is the `(1, 2)` evaluation map. -/
@[simp]
theorem sourceQuotientStage_map_snd {X Y : Stage C 2} (φ : X ⟶ Y) :
    (((sourceQuotientStage C).map φ).2 =
      (eval C 2 (interval (1 : Fin 3) 2 (by decide))).map φ) := rfl

/-- Weak restriction through `stageWeakInclusion`. -/
def sourceQuotientStageWeak : StageWeakCategory C 2 ⥤ C × C :=
  stageWeakInclusion C 2 ⋙ sourceQuotientStage C

/-- Object part factors through the inclusion. -/
@[simp]
theorem sourceQuotientStageWeak_obj (X : StageWeakCategory C 2) :
    (sourceQuotientStageWeak C).obj X =
      (sourceQuotientStage C).obj ((stageWeakInclusion C 2).obj X) := rfl

/-- Morphism part factors through the inclusion. -/
@[simp]
theorem sourceQuotientStageWeak_map {X Y : StageWeakCategory C 2} (f : X ⟶ Y) :
    (sourceQuotientStageWeak C).map f =
      (sourceQuotientStage C).map ((stageWeakInclusion C 2).map f) := rfl

end CategoryTheory.Waldhausen.SConstruction
