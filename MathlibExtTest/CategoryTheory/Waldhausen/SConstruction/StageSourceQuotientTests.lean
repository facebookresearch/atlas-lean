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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageSourceQuotient

/-!
# Stage source/quotient evaluation consumer tests

Focused public-API checks for `sourceQuotientStage` and `sourceQuotientStageWeak`:
object pairing reads back as the `(0, 1)` source and `(1, 2)` quotient evaluations,
morphism projections read back through `fst`/`snd`, and the weak restriction has the
public functor type and computes through `stageWeakInclusion`. Each check fails on a
component swap.

No opposite composite or retraction, no equivalence, no deformation, no realization,
no weak equivalence, no additivity, no K₀, no spectra, and no Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageSourceQuotientTests

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Object pairing computes as source `(0, 1)` and quotient `(1, 2)` evaluations. -/
example (X : Stage C 2) :
    (sourceQuotientStage C).obj X =
      ((eval C 2 (interval (0 : Fin 3) 1 (by decide))).obj X,
        (eval C 2 (interval (1 : Fin 3) 2 (by decide))).obj X) :=
  sourceQuotientStage_obj C X

/-- Morphism projections compute through the two evaluations; fails on swap. -/
example {X Y : Stage C 2} (φ : X ⟶ Y) :
    (((sourceQuotientStage C).map φ).1 =
      (eval C 2 (interval (0 : Fin 3) 1 (by decide))).map φ) ∧
    (((sourceQuotientStage C).map φ).2 =
      (eval C 2 (interval (1 : Fin 3) 2 (by decide))).map φ) :=
  ⟨sourceQuotientStage_map_fst C φ, sourceQuotientStage_map_snd C φ⟩

/-- Weak restriction has the public functor type. -/
example : StageWeakCategory C 2 ⥤ C × C :=
  sourceQuotientStageWeak C

/-- Weak restriction computes through the inclusion; fails on swap. -/
example (X : StageWeakCategory C 2) {Y : StageWeakCategory C 2} (f : X ⟶ Y) :
    (sourceQuotientStageWeak C).obj X =
      (sourceQuotientStage C).obj ((stageWeakInclusion C 2).obj X) ∧
    (sourceQuotientStageWeak C).map f =
      (sourceQuotientStage C).map ((stageWeakInclusion C 2).map f) :=
  ⟨sourceQuotientStageWeak_obj C X, sourceQuotientStageWeak_map C f⟩

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageSourceQuotientTests
