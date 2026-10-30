/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.SelfDualCritical

/-!
# The Beffara–Duminil-Copin theorem

For `q ≥ 1` the critical point of the random-cluster model on `ℤ²` is the self-dual point
`p_sd(q) = √q / (1 + √q)`: the wired measure `φ¹_{p,q}` does not percolate for `p < p_sd(q)` and
percolates for `p > p_sd(q)`.

The ported library proves only the identification of `p_c(q)` from these two facts
(`StatMech.BeffaraDC.beffaraDC_critical_point`, which takes them as hypotheses `hNoPercBelow`
and `hPercAbove`). Proofs of `beffaraDC_no_percolation_below` and
`beffaraDC_percolation_above` discharge those hypotheses.

For `q ≥ 1` the wired box measures converge, so `StatMech.FK.wiredInfiniteVolume` (a
subsequential limit chosen by Prokhorov compactness) is the standard wired measure `φ¹_{p,q}`.

## Main statements

* `beffaraDC_no_percolation_below`: `θ¹(p, q) = 0` for `0 < p < p_sd(q)`.
* `beffaraDC_percolation_above`: `θ¹(p, q) > 0` for `p_sd(q) < p < 1`.
* `beffaraDC_fkPc_eq_selfDualPoint`: `p_c(q) = √q / (1 + √q)`.

## References

* V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster model
  is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), 511–542.
* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Continuity of the phase transition for planar
  random-cluster and Potts models with 1 ≤ q ≤ 4*, Comm. Math. Phys. 349 (2017), 47–107.
-/

@[expose] public section

namespace MathlibExt.Probability.RandomCluster.BeffaraDuminilCopinWanted

open StatMech StatMech.FK StatMech.BeffaraDC

/-- **Beffara–Duminil-Copin theorem**, subcritical half. For `q ≥ 1` and
`0 < p < √q / (1 + √q)`, the wired random-cluster measure on `ℤ²` does not percolate:
`θ¹(p, q) = 0`.

Source: V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), Theorem 1. -/
public theorem_wanted beffaraDC_no_percolation_below :
    ∀ (q : ℝ) (hq : 1 ≤ q) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1),
      p < Real.sqrt q / (1 + Real.sqrt q) →
        fkTheta 2 hp0 hp1 (zero_lt_one.trans_le hq) (q := q) = 0

/-- **Beffara–Duminil-Copin theorem**, supercritical half. For `q ≥ 1` and
`√q / (1 + √q) < p < 1`, the wired random-cluster measure on `ℤ²` percolates: `θ¹(p, q) > 0`.

Source: V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), Theorem 1. -/
public theorem_wanted beffaraDC_percolation_above :
    ∀ (q : ℝ) (hq : 1 ≤ q) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1),
      Real.sqrt q / (1 + Real.sqrt q) < p →
        0 < fkTheta 2 hp0 hp1 (zero_lt_one.trans_le hq) (q := q)

/-- **Beffara–Duminil-Copin theorem.** For `q ≥ 1` the critical point of the random-cluster model
on `ℤ²` is the self-dual point: `p_c(q) = √q / (1 + √q)`. This follows from the two halves above
by `StatMech.BeffaraDC.beffaraDC_critical_point`.

Source: V. Beffara, H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), Theorem 1. -/
public theorem_wanted beffaraDC_fkPc_eq_selfDualPoint :
    ∀ (q : ℝ), 1 ≤ q → fkPc 2 q = Real.sqrt q / (1 + Real.sqrt q)

end MathlibExt.Probability.RandomCluster.BeffaraDuminilCopinWanted
