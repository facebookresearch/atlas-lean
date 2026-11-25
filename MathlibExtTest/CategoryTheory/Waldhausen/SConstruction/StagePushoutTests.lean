/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StagePushout

/-!
# Pointwise stage-pushout tests

Focused public-API checks for closure under a genuine stage cofibration,
including degree zero and a shifted cofiber triple.  These tests do not
assert an all-row propagation theorem or a Waldhausen structure on stages.
-/

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StagePushoutTests

variable (C : Type u) [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]

local instance stagePushoutTestsWaldhausenC : WaldhausenCategoryWithoutGluing C :=
  ExactCategory.waldhausenCategory C

/-- A componentwise pushout along a genuine stage cofibration is a stage. -/
example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (P : StagePushoutPresentation C f g) (hf : stageCofibrations C n f) :
    IsStage n P.apex :=
  P.isStage_of_stageCofibration hf

/-- Degree zero needs no successor witness beyond the vacuous predicate. -/
example {A M N : Stage C 0} {f : A ⟶ M} {g : A ⟶ N}
    (P : StagePushoutPresentation C f g) : IsStage 0 P.apex :=
  P.isStage_of_stageCofibration (by
    intro i
    exact Fin.elim0 i)

/-- The closure theorem supplies arbitrary shifted, not merely zero-row,
cofiber triples. -/
example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (P : StagePushoutPresentation C f g) (hf : stageCofibrations C n f)
    {i j k : Fin (n + 1)} (hij : i ≤ j) (hjk : j ≤ k) :
    IsCofibrationSequence
      (P.apex.map (horiz hij hjk))
      (P.apex.map (vert hij hjk)) :=
  (P.isStage_of_stageCofibration hf).cofiber_triple hij hjk

/-- Bundling preserves the candidate apex functor definitionally. -/
example {n : ℕ} {A M N : Stage C n} {f : A ⟶ M} {g : A ⟶ N}
    (P : StagePushoutPresentation C f g) (hf : stageCofibrations C n f) :
    (P.toStage hf).obj = P.apex :=
  rfl

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StagePushoutTests
