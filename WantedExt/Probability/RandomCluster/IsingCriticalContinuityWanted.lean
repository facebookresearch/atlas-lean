/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import PhyslibExt.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc

/-!
# No percolation at the critical point of the `q = 2` random-cluster model

For `d ≥ 2` the wired `q = 2` random-cluster measure on `ℤ^d` does not percolate at its critical
point: `θ¹(p_c(2, d), 2) = 0`. Through the Edwards–Sokal coupling this is the vanishing of the
spontaneous magnetization of the nearest-neighbour Ising model at the critical temperature.

The ported library proves `θ¹(p, 2) = 0` for `p < p_c(2, d)`
(`StatMech.FK.tzp_fkTheta_eq_zero_of_lt_pc`) and takes the critical case as the hypothesis
`hθpc` of `StatMech.FK.tzp_fkTheta_eq_zero_of_le_pc_of_pc`. A proof of
`fkTheta_eq_zero_at_pc_q_two` discharges `hθpc` for `d ≥ 2`.

For `q ≥ 1` the wired box measures converge, so `StatMech.FK.wiredInfiniteVolume` (a
subsequential limit chosen by Prokhorov compactness) is the standard wired measure `φ¹_{p,q}`.

## Main statements

* `fkTheta_eq_zero_at_pc_q_two`: `θ¹(p_c(2, d), 2) = 0` for `d ≥ 2`.

## References

* M. Aizenman, H. Duminil-Copin, V. Sidoravicius, *Random currents and continuity of Ising
  model's spontaneous magnetization*, Comm. Math. Phys. 334 (2015), 719–742 (`d ≥ 3`).
* C. N. Yang, *The spontaneous magnetization of a two-dimensional Ising model*, Phys. Rev. 85
  (1952), 808–816 (`d = 2`).
* H. Duminil-Copin, V. Sidoravicius, V. Tassion, *Continuity of the phase transition for planar
  random-cluster and Potts models with 1 ≤ q ≤ 4*, Comm. Math. Phys. 349 (2017), 47–107
  (`d = 2`, all `q ∈ [1, 4]`).
-/

@[expose] public section

namespace MathlibExt.Probability.RandomCluster.IsingCriticalContinuityWanted

open StatMech StatMech.FK

/-- **Continuity of the Ising phase transition** in random-cluster form. For `d ≥ 2`, the wired
`q = 2` random-cluster measure on `ℤ^d` does not percolate at `p_c(2, d)`:
`θ¹(p_c(2, d), 2) = 0`. The positivity hypotheses `0 < p_c(2, d) < 1` hold for `d ≥ 2`.

Source: M. Aizenman, H. Duminil-Copin, V. Sidoravicius, *Random currents and continuity of Ising
model's spontaneous magnetization*, Comm. Math. Phys. 334 (2015) for `d ≥ 3`; C. N. Yang, *The
spontaneous magnetization of a two-dimensional Ising model*, Phys. Rev. 85 (1952) and
H. Duminil-Copin, V. Sidoravicius, V. Tassion, Comm. Math. Phys. 349 (2017) for `d = 2`. -/
public theorem_wanted fkTheta_eq_zero_at_pc_q_two :
    ∀ (d : ℕ), 2 ≤ d → ∀ (hp : 0 < fkPc d 2) (hp1 : fkPc d 2 < 1),
      fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0

end MathlibExt.Probability.RandomCluster.IsingCriticalContinuityWanted
