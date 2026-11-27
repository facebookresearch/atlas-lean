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
# Modular scaling of Haar measure under right translation

For a locally compact topological group with Borel structure and regular left Haar measure `μ`,
the pushforward by `x ↦ xg` is `Δ(g) • μ`, where `Δ=Measure.modularCharacter`.

This fixes the modular-character convention used by right-translation operators and requires no
Hilbert-space representation.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

namespace MeasureTheory.Measure

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- **Right-translation pushforward of a regular Haar measure.** Let `G` be a locally compact
topological group with its Borel structure and `μ` a regular Haar measure. For `g∈G`,
`Measure.map (fun x => x*g) μ = Measure.modularCharacter g • μ`. -/
theorem map_right_mul_modular (g : G) :
    Measure.map (fun x : G => x * g) μ = Measure.modularCharacter g • μ := by
  let : (Measure.map (fun x : G => x * g) μ).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g)
  change Measure.map (fun x : G => x * g) μ = Measure.modularCharacterFun g • μ
  rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  exact Measure.isMulLeftInvariant_eq_smul_of_regular _ μ

end MeasureTheory.Measure
