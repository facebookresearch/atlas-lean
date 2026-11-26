/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonTrifProb

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonTrifProb`

* `ctp_measurableSet_isCanonicalTrifurcation` at the origin of `ℤ²`;
* `ctp_isCanonicalTrifurcation_shift` for the all-open configuration;
* `ctp_canonical_trifurcation_prob_eq_zero` in conditional form.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonTrifProb

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.ConfigSpace
open _root_.StatMech.Percolation

-- Canonical trifurcation at the origin is measurable.
example : MeasurableSet {ω : ConfigSpace (Sym2 (Site 2)) | IsCanonicalTrifurcation 2 ω 0} :=
  ctp_measurableSet_isCanonicalTrifurcation 0

-- Canonical trifurcations are shift covariant (all-open configuration).
example (g : Multiplicative (Site 2)) (x : Site 2) :
    IsCanonicalTrifurcation 2 (shift g (fun _ => true)) (g • x) ↔
      IsCanonicalTrifurcation 2 (fun _ => true) x :=
  ctp_isCanonicalTrifurcation_shift g _ x

-- A translation-invariant measure gives canonical trifurcations probability zero.
example {d : ℕ} (μ : MeasureTheory.Measure (ConfigSpace (Sym2 (Site d))))
    [MeasureTheory.IsProbabilityMeasure μ]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0)) :
    μ {ω | IsCanonicalTrifurcation d ω 0} = 0 :=
  ctp_canonical_trifurcation_prob_eq_zero μ hinv hvol hdens

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.CanonTrifProb
