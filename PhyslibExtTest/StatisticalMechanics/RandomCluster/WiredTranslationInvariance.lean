/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredTranslationInvariance

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKLimitsClose`

* the headline `flc_wiredIV_isTranslationInvariant` (translation invariance of the wired `q = 2`
  infinite-volume random-cluster measure) on `ℤ²` at `p = 1/2` and on `ℤ³` at `p = 1/3`;
* its consequence: a translate of the event "the edge `e` is open" has the same wired probability
  as the event itself.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKLimitsClose

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice
  _root_.StatMech.ConfigSpace

-- The headline on `ℤ²` at `p = 1/2`.
example : IsTranslationInvariant (G := Multiplicative (Site 2))
    (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) :=
  flc_wiredIV_isTranslationInvariant (by norm_num) (by norm_num)

-- The headline on `ℤ³` at `p = 1/3`.
example : IsTranslationInvariant (G := Multiplicative (Site 3))
    (wiredInfiniteVolume 3 (p := 1 / 3) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 3)))) :=
  flc_wiredIV_isTranslationInvariant (by norm_num) (by norm_num)

-- Consequence: shifting the event "edge `e` open" by `g` does not change its probability.
example (g : Multiplicative (Site 2)) (e : Sym2 (Site 2)) :
    (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) (shift g ⁻¹' {ω | ω e = true})
    = (wiredInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) {ω | ω e = true} :=
  (flc_wiredIV_isTranslationInvariant (d := 2) (by norm_num) (by norm_num) g).measure_preimage
    (measurableSet_eq_fun (measurable_pi_apply e) measurable_const).nullMeasurableSet

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKLimitsClose
