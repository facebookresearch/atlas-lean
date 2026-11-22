/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.PlusStateErgodic

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.IsingPlusTIFromPlacement`

The three headline properties of the plus state, with all hypotheses discharged:
* `iptp_plusState_isTranslationInvariant` on `ℤ²` at `β = 1`, `h = 0`, and on `ℤ³` with a positive
  field;
* `ising_plus_extreme` and `iptp_plusState_isErgodic` on `ℤ²` at `β = 1`, `h = 0` (deep in the
  low-temperature phase) and at `β = 0`;
* the translation invariance is used: a measurable event and its translate have the same
  probability under the plus state.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.IsingPlusTIFromPlacement

open MeasureTheory
open _root_.StatMech _root_.StatMech.Ising _root_.StatMech.Lattice

-- Translation invariance on `ℤ²` at `β = 1`, `h = 0`.
example : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site 2))
    (plusState 2 1 0 : Measure (ConfigSpace (Site 2))) :=
  iptp_plusState_isTranslationInvariant zero_le_one le_rfl

-- Translation invariance on `ℤ³` with field `h = 1/2`.
example : ConfigSpace.IsTranslationInvariant (G := Multiplicative (Site 3))
    (plusState 3 2 (1 / 2) : Measure (ConfigSpace (Site 3))) :=
  iptp_plusState_isTranslationInvariant (by norm_num) (by norm_num)

-- Extremality on `ℤ²` at `β = 1`, `h = 0`.
example : FK.IsInvariantExtremePoint (G := Multiplicative (Site 2))
    (plusState 2 1 0 : Measure (ConfigSpace (Site 2))) :=
  ising_plus_extreme (by norm_num) zero_le_one le_rfl

-- Ergodicity on `ℤ²` at `β = 1`, `h = 0` and at infinite temperature.
example : ConfigSpace.IsErgodic (G := Multiplicative (Site 2))
      (plusState 2 1 0 : Measure (ConfigSpace (Site 2))) ∧
    ConfigSpace.IsErgodic (G := Multiplicative (Site 2))
      (plusState 2 0 0 : Measure (ConfigSpace (Site 2))) :=
  ⟨iptp_plusState_isErgodic (by norm_num) zero_le_one le_rfl,
    iptp_plusState_isErgodic (by norm_num) le_rfl le_rfl⟩

-- Using translation invariance: an event and its translate have the same probability.
example (g : Multiplicative (Site 2)) (s : Set (ConfigSpace (Site 2))) (hs : MeasurableSet s) :
    (plusState 2 1 0 : Measure (ConfigSpace (Site 2))) (ConfigSpace.shift g ⁻¹' s)
      = (plusState 2 1 0 : Measure (ConfigSpace (Site 2))) s :=
  (iptp_plusState_isTranslationInvariant zero_le_one le_rfl g).measure_preimage hs.nullMeasurableSet

end PhyslibExtTest.CondensedMatter.IsingModel.IsingPlusTIFromPlacement
