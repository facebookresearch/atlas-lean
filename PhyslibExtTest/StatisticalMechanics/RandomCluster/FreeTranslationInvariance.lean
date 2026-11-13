/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FreeTranslationInvariance

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BulkDeviationProof`

* the headline `bdp_freeIV_isTranslationInvariant` (translation invariance of the free `q = 2`
  infinite-volume random-cluster measure) on `ℤ²` at `p = 1/2` and on `ℤ` at `p = 3/4`;
* its consequence: a translate of the event "the edge `e` is open" has the same free probability
  as the event itself.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BulkDeviationProof

open MeasureTheory _root_.StatMech _root_.StatMech.FK _root_.StatMech.Lattice
  _root_.StatMech.ConfigSpace

-- The headline on `ℤ²` at `p = 1/2`.
example : IsTranslationInvariant (G := Multiplicative (Site 2))
    (freeInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) :=
  bdp_freeIV_isTranslationInvariant (by norm_num) (by norm_num)

-- The headline on `ℤ` at `p = 3/4`.
example : IsTranslationInvariant (G := Multiplicative (Site 1))
    (freeInfiniteVolume 1 (p := 3 / 4) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 1)))) :=
  bdp_freeIV_isTranslationInvariant (by norm_num) (by norm_num)

-- Consequence: shifting the event "edge `e` open" by `g` does not change its probability.
example (g : Multiplicative (Site 2)) (e : Sym2 (Site 2)) :
    (freeInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) (shift g ⁻¹' {ω | ω e = true})
    = (freeInfiniteVolume 2 (p := 1 / 2) (by norm_num) (by norm_num) (by norm_num : (0 : ℝ) < 2)
      : Measure (ConfigSpace (Sym2 (Site 2)))) {ω | ω e = true} :=
  (bdp_freeIV_isTranslationInvariant (d := 2) (by norm_num) (by norm_num) g).measure_preimage
    (measurableSet_eq_fun (measurable_pi_apply e) measurable_const).nullMeasurableSet

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BulkDeviationProof
