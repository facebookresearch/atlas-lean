/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationPatternMeasure

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationPatternMeasure`

* `threeMeetBox_subset_pattern_canonical_trifurcations` in pointwise form: a configuration with
  three infinite clusters meeting `B_n` becomes one with a canonical trifurcation after a box
  pattern;
* `trifurcation_pos_of_threeMeetBox_patternAC` and
  `canonical_trifurcation_at_origin_pos_of_patternAC` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationPatternMeasure

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation
open _root_.StatMech.ConfigSpace MeasureTheory

variable {d : ℕ}

-- A box pattern produces a canonical trifurcation.
example (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))) (hω : ω ∈ threeMeetBox d n) :
    ∃ (eta : ConfigSpace ↥(_root_.StatMech.Ising.bondFinsetTouch d n)) (hub : Site d),
      IsCanonicalTrifurcation d
        (_root_.StatMech.FK.setPattern (_root_.StatMech.Ising.bondFinsetTouch d n) eta ω) hub := by
  simpa only [Set.mem_iUnion, Set.mem_preimage, Set.mem_ofPred_eq] using
    threeMeetBox_subset_pattern_canonical_trifurcations n hω

-- Pattern absolute continuity turns three clusters meeting a box into a trifurcation.
example (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (_root_.StatMech.FK.setPattern I eta) ≪ mu)
    (n : ℕ) (hpos : 0 < mu (threeMeetBox d n)) :
    ∃ hub : Site d, 0 < mu {omega | IsTrifurcation d omega hub} :=
  trifurcation_pos_of_threeMeetBox_patternAC mu hpattern n hpos

-- With translation invariance, a canonical trifurcation at the origin has positive probability.
example (mu : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure mu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (hpattern : ∀ (I : Finset (Sym2 (Site d))) (eta : ConfigSpace ↥I),
      mu.map (_root_.StatMech.FK.setPattern I eta) ≪ mu)
    (htop : 0 < mu {omega | numInfiniteClusters d omega = ⊤}) :
    0 < mu {omega | IsCanonicalTrifurcation d omega 0} :=
  canonical_trifurcation_at_origin_pos_of_patternAC mu hinv hpattern htop

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationPatternMeasure
