/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage

/-!
# Finite Waldhausen-stage consumer tests

Consumer checks for `horiz`/`vert` endpoint behavior, `IsStage`
diagonal-zero and cofiber-triple extractions, and actual-square pushout coverage.
These clients exercise the original finite diagrams and their actual
endpoint, cofiber-triple, and pushout maps.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.FiniteStageTests

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [WaldhausenCategory C]

/-- `horiz` fixes the left endpoint. -/
example :
    (horiz (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).left = 𝟙 (0 : Fin 3) :=
  rfl

/-- `horiz` advances the right endpoint. -/
example :
    (horiz (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).right =
      homOfLE (show (1 : Fin 3) ≤ 2 by decide) :=
  rfl

/-- `vert` advances the left endpoint. -/
example :
    (vert (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).left =
      homOfLE (show (0 : Fin 3) ≤ 1 by decide) :=
  rfl

/-- `vert` fixes the right endpoint. -/
example :
    (vert (show (0 : Fin 3) ≤ 1 by decide)
      (show (1 : Fin 3) ≤ 2 by decide)).right = 𝟙 (2 : Fin 3) :=
  rfl

/-- `IsStage 1` diagonal-zero extraction at a concrete `Fin 2` index. -/
example (A : Ar 1 ⥤ C) (h : IsStage 1 A) :
    IsZero (A.obj (diag (1 : Fin 2))) :=
  h.diag_isZero (1 : Fin 2)

/-- `IsStage 2` cofiber extraction on the canonical `(0,1) ⟶ (0,2) ⟶ (1,2)` maps. -/
example (A : Ar 2 ⥤ C) (h : IsStage 2 A) :
    IsCofibrationSequence
      (A.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide))) :=
  h.cofiber_triple (show (0 : Fin 3) ≤ 1 by decide)
    (show (1 : Fin 3) ≤ 2 by decide)

/-- `IsStage 2` actual-square pushout at concrete `(0,1,2)`. -/
example (A : Ar 2 ⥤ C) (h : IsStage 2 A) :
    IsPushout
      (A.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (toDiag (show (0 : Fin 3) ≤ 1 by decide)))
      (A.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (fromDiag (show (1 : Fin 3) ≤ 2 by decide))) :=
  isPushout_actualSquare h _ _

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.FiniteStageTests
