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

public import Mathlib.MeasureTheory.Group.ModularCharacter

/-!
# Trivial modular character of a locally compact abelian group

Commutativity makes the canonical left Haar measure invariant under right
translations. Its modular character is therefore identically one. This
measure-theoretic fact is independent of Hilbert regular representations.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace MeasureTheory.Measure

universe uG

variable {G : Type uG} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- The modular character of a locally compact abelian group is identically one. -/
theorem modularCharacter_eq_one_of_comm (g : G) : modularCharacter g = 1 := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  change modularCharacterFun g = 1
  rw [modularCharacterFun_eq_haarScalarFactor (Measure.haar (G := G)) g]
  simp only [map_mul_right_eq_self, haarScalarFactor_self]

end MeasureTheory.Measure
