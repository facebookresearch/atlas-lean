/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredErgodicity

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CrossBoxGeneralKeystone`

* the headline `cbk_wiredIV_isErgodic` (ergodicity of the wired `q = 2` infinite-volume
  random-cluster measure) on `ℤ²` at `p = 1/2` and on `ℤ` at `p = 1/4`;
* its consequence: every measurable translation-invariant event has wired probability `0` or `1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CrossBoxGeneralKeystone

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice
  _root_.StatMech.ConfigSpace

-- The headline on `ℤ²` at `p = 1/2`.
example : IsErgodic (G := Multiplicative (Site 2))
    (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) :=
  cbk_wiredIV_isErgodic (by norm_num) (by norm_num) (by norm_num)

-- The headline on `ℤ` at `p = 1/4`.
example : IsErgodic (G := Multiplicative (Site 1))
    (wiredInfiniteVolume 1 (p := 1 / 4) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 1)))) :=
  cbk_wiredIV_isErgodic le_rfl (by norm_num) (by norm_num)

-- Consequence (zero–one law): a measurable invariant event has wired probability `0` or `1`.
example (s : Set (ConfigSpace (Sym2 (Site 2)))) (hs : MeasurableSet s)
    (hinv : ∀ g : Multiplicative (Site 2), (shift g : ConfigSpace _ → ConfigSpace _) ⁻¹' s = s) :
    (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) s = 0 ∨
    (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) s = 1 := by
  have h := (cbk_wiredIV_isErgodic (d := 2) (p := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)).2 s hs hinv
  rwa [measure_univ] at h

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CrossBoxGeneralKeystone
