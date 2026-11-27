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

/-!
# Degree-two finite-stage consumer

Data-level `S₂` coverage only: applies `Stage.cofiber_zero_one_two` to a
generic `A : Stage C 2` and states the full existing `IsCofibrationSequence`
on the concrete `(0, 1, 2) : Fin 3` maps.

Orientation: `horiz` fixes the left endpoint and moves the right endpoint
`(i, j) ⟶ (i, k)`; `vert` fixes the right endpoint and moves the left
endpoint `(i, k) ⟶ (j, k)`. This is data-level `S₂` coverage only; it proves
no stage equivalence, simplicial object, nerve, realization, K-theory, or
G-theory content.
-/

open CategoryTheory CategoryTheory.Waldhausen.SConstruction

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.LowDegreeTests

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

example (A : Stage C 2) :
    IsCofibrationSequence
      (A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide))) :=
  Stage.cofiber_zero_one_two C A

end MathlibExtTest.CategoryTheory.Waldhausen.SConstruction.LowDegreeTests
