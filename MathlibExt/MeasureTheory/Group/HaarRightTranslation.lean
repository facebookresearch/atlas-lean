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
# Right translation of a regular Haar measure

The pushforward by right multiplication is the original left Haar measure
scaled by the pinned modular character. This measure statement is independent
of Hilbert spaces and square-integrable representations.
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

/-- Actual regular Haar measures have the pinned right-translation scalar. -/
theorem map_right_mul_modular (g : G) :
    Measure.map (fun x : G => x * g) μ = Measure.modularCharacter g • μ := by
  let : (Measure.map (fun x : G => x * g) μ).Regular :=
    Measure.Regular.map (Homeomorph.mulRight g)
  change Measure.map (fun x : G => x * g) μ = Measure.modularCharacterFun g • μ
  rw [Measure.modularCharacterFun_eq_haarScalarFactor μ g]
  exact Measure.isMulLeftInvariant_eq_smul_of_regular _ μ

end MeasureTheory.Measure
