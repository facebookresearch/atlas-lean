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

/-!
# Degree-two low-degree cofiber projection

Data-level `S₂` sanity result only: extracts the canonical
`IsCofibrationSequence` for the concrete `(0, 1, 2) : Fin 3` maps.
Proves no stage equivalence, simplicial object, nerve, realization,
K-theory, or G-theory content.
-/

@[expose] public section

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [Limits.HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Canonical degree-two cofiber data for `A : Stage C 2`.

Returns the existing `IsCofibrationSequence` for the concrete
`(0, 1, 2) : Fin 3` maps `horiz` then `vert`. This is the data-level
`S₂` sanity projection only; not a categorical equivalence. -/
theorem Stage.cofiber_zero_one_two (A : Stage C 2) :
    IsCofibrationSequence
      (A.obj.map (horiz (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide)))
      (A.obj.map (vert (show (0 : Fin 3) ≤ 1 by decide)
        (show (1 : Fin 3) ≤ 2 by decide))) :=
  A.property.cofiber_triple (show (0 : Fin 3) ≤ 1 by decide)
    (show (1 : Fin 3) ≤ 2 by decide)

end CategoryTheory.Waldhausen.SConstruction
