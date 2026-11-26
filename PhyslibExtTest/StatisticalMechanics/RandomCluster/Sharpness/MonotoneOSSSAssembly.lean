/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MonotoneOSSSAssembly

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.MonotoneOSSSAssembly`

* `osss_monotone_sharp` (unconditional) for the random-cluster mass on `K₂` at `p = 1/2`,
  `q = 2` and the observable "edge `s(0, 1)` is open", for an arbitrary order;
* `osss_onestep_cov_bound` on the same instance.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.MonotoneOSSSAssembly

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Monotonic
open _root_.StatMech.OSSS.Coding _root_.StatMech.OSSS.GrandCoupling
open _root_.StatMech.OSSS.AdaptMConditional _root_.StatMech.OSSS.AdaptDisintegration

-- The OSSS inequality for a monotonic measure, instantiated on `K₂`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (Lindeberg.coord s(0, 1))
      ≤ ∑ e, revealAdapt (MonotonicFK.fkMass ⊤ (1 / 2) 2) σ (Lindeberg.coord s(0, 1)) e
          * Lindeberg.cov (MonotonicFK.fkMass ⊤ (1 / 2) 2) (Lindeberg.coord s(0, 1))
            (Lindeberg.coord e) :=
  osss_monotone_sharp
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    (MonotonicFK.fkMass_isMonotonic (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    σ (Lindeberg.coord_mono _) (Lindeberg.coord_nonneg _)
    (fun ω => by unfold Lindeberg.coord; split_ifs <;> norm_num)

-- The per-step covariance bound on the same instance.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    AdaptStepCovBound (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) σ
      (Lindeberg.coord s(0, 1)) :=
  osss_onestep_cov_bound
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    (MonotonicFK.fkMass_isMonotonic (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    σ (Lindeberg.coord_mono _) (Lindeberg.coord_nonneg _)
    (fun ω => by unfold Lindeberg.coord; split_ifs <;> norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.MonotoneOSSSAssembly
