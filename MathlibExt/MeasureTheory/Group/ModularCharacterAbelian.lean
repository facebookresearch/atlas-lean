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
# Modular character of a locally compact abelian group

Commutativity makes the left Haar measure of a locally compact abelian topological group
invariant under right translations. Its modular character is therefore identically one.

No chosen Hilbert representation or measurable structure is an input to this group-theoretic
statement.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace MeasureTheory.Measure

universe uG

variable {G : Type uG} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- **Trivial modular character of a locally compact abelian group.** Let `G` be a locally
compact abelian topological group. For every `g∈G`, `Measure.modularCharacter g=1`. -/
theorem modularCharacter_eq_one_of_comm (g : G) : modularCharacter g = 1 := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  change modularCharacterFun g = 1
  rw [modularCharacterFun_eq_haarScalarFactor (Measure.haar (G := G)) g]
  simp only [map_mul_right_eq_self, haarScalarFactor_self]

end MeasureTheory.Measure
