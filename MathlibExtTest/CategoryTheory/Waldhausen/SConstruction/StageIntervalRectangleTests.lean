/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageIntervalRectangle

/-!
# Finite-stage interval rectangle tests

These tests spell the four maps in the pushout orientation for one strict
quadruple and for degeneracies on either side.  They make no span, flag,
realization, additivity, or comparison claim.
-/

open CategoryTheory Limits
open CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
namespace StageIntervalRectangleTests

variable {C : Type u} [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

/-- The strict rectangle `0 < 1 < 2 < 3` has the declared top, left,
right, and bottom orientation. -/
example {A : Ar 3 ⥤ C} (hA : IsStage 3 A) :
    IsPushout
      (A.map (horiz
        (show (0 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide)))
      (A.map (vert
        (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 2 by decide)))
      (A.map (vert
        (show (0 : Fin 4) ≤ 1 by decide)
        (show (1 : Fin 4) ≤ 3 by decide)))
      (A.map (horiz
        (show (1 : Fin 4) ≤ 2 by decide)
        (show (2 : Fin 4) ≤ 3 by decide))) := by
  exact hA.isPushout_intervalRectangle
    (show (0 : Fin 4) ≤ 1 by decide)
    (show (1 : Fin 4) ≤ 2 by decide)
    (show (2 : Fin 4) ≤ 3 by decide)

/-- The same theorem is uniform when the first two indices coincide. -/
example {A : Ar 2 ⥤ C} (hA : IsStage 2 A) :
    IsPushout
      (A.map (horiz
        (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (vert
        (show (0 : Fin 3) ≤ 0 by decide)
        (show (0 : Fin 3) ≤ 1 by decide)))
      (A.map (vert
        (show (0 : Fin 3) ≤ 0 by decide)
        (show (0 : Fin 3) ≤ 2 by decide)))
      (A.map (horiz
        (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide))) := by
  exact hA.isPushout_intervalRectangle
    (show (0 : Fin 3) ≤ 0 by decide)
    (show (0 : Fin 3) ≤ 1 by decide)
    (show (1 : Fin 3) ≤ 2 by decide)

/-- The same theorem is uniform when the final two indices coincide. -/
example {A : Ar 2 ⥤ C} (hA : IsStage 2 A) :
    IsPushout
      (A.map (horiz
        (show (0 : Fin 3) ≤ 2 by decide)
        (show (2 : Fin 3) ≤ 2 by decide)))
      (A.map (vert
        (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (vert
        (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.map (horiz
        (show (1 : Fin 3) ≤ 2 by decide)
        (show (2 : Fin 3) ≤ 2 by decide))) := by
  exact hA.isPushout_intervalRectangle
    (show (0 : Fin 3) ≤ 1 by decide)
    (show (1 : Fin 3) ≤ 2 by decide)
    (show (2 : Fin 3) ≤ 2 by decide)

end StageIntervalRectangleTests
end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction
