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

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.LowDegree
import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageTwo

/-!
# Object-level StageTwo converse consumer tests

Focused public-API checks for the bundled `stageTwo` converse: bundled object
values at `(0,1)`/`(0,2)`/`(1,2)`, orientation-sensitive central maps, and the central actual
pushout square. No helper API, equivalence, reindexing, simplicial object,
nerve, realization, K/G-theory, or Q/S comparison.
-/

open CategoryTheory
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageTwoTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Bundled `stageTwo` object values at `(0,1)`, `(0,2)`, and `(1,2)`. -/
example (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g) :
    (stageTwo C X Y Z f g hSeq).obj.obj (interval 0 1 (by decide)) = X ∧
      (stageTwo C X Y Z f g hSeq).obj.obj (interval 0 2 (by decide)) = Y ∧
      (stageTwo C X Y Z f g hSeq).obj.obj (interval 1 2 (by decide)) = Z :=
  ⟨stageTwo_obj_01 C X Y Z f g hSeq _,
    stageTwo_obj_02 C X Y Z f g hSeq _,
    stageTwo_obj_12 C X Y Z f g hSeq _⟩

/-- Central horizontal map is `f` and vertical map is `g`, catching swaps. -/
example (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g)
    (hij : (0 : Fin 3) ≤ 1) (hjk : (1 : Fin 3) ≤ 2) :
    (stageTwo C X Y Z f g hSeq).obj.map (horiz hij hjk) = f ∧
      (stageTwo C X Y Z f g hSeq).obj.map (vert hij hjk) = g :=
  ⟨stageTwo_map_horiz_012 C X Y Z f g hSeq hij hjk,
    stageTwo_map_vert_012 C X Y Z f g hSeq hij hjk⟩

/-- Central actual pushout square through the diagonal. -/
example (X Y Z : C) (f : X ⟶ Y) (g : Y ⟶ Z)
    (hSeq : IsCofibrationSequence (C := C) f g)
    (hij : (0 : Fin 3) ≤ 1) (hjk : (1 : Fin 3) ≤ 2) :
    IsPushout
      ((stageTwo C X Y Z f g hSeq).obj.map (horiz hij hjk))
      ((stageTwo C X Y Z f g hSeq).obj.map (toDiag hij))
      ((stageTwo C X Y Z f g hSeq).obj.map (vert hij hjk))
      ((stageTwo C X Y Z f g hSeq).obj.map (fromDiag hjk)) :=
  isPushout_actualSquare (stageTwo C X Y Z f g hSeq).property hij hjk

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.StageTwoTests
