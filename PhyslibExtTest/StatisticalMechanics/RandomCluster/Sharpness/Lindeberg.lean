/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Lindeberg

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.Lindeberg`

* `coord` evaluated on the all-open configuration;
* `mean_const` under the random-cluster mass on `K₂`;
* `monotonic_poincare` via `fk_monotonic_poincare` for the coordinate observable on `K₂`;
* `fk_monotonicOSSSBound_poincare` on the same instance.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.Lindeberg

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Lindeberg

-- The coordinate observable is `1` on the all-open configuration.
example : coord (s(0, 1) : Sym2 (Fin 2)) (fun _ => true) = 1 := by
  simp [coord]

-- The mean of a constant under the random-cluster mass on `K₂` is that constant.
example : mean (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (fun _ => 3) = 3 :=
  mean_const _ (MonotonicFK.fkMass_sum_eq_one ⊤ (by norm_num) (by norm_num) (by norm_num)) 3

-- The monotonic Poincaré inequality on `K₂` for the observable "`s(0, 1)` is open".
example :
    var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) (coord s(0, 1))
      ≤ ∑ e, cov (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (coord s(0, 1)) (coord e) :=
  fk_monotonic_poincare ⊤ (by norm_num) (by norm_num) (by norm_num) (coord_mono _)
    (coord_nonneg _) (fun ω => by unfold coord; split_ifs <;> norm_num)

-- The OSSS bound with constants `1, 1, 1` holds on `K₂` for a monotone observable.
example {f : ConfigSpace (Sym2 (Fin 2)) → ℝ} (hf : Monotone f) (hf0 : 0 ≤ f)
    (hf1 : ∀ ω, f ω ≤ 1) :
    MonotonicMeasure.MonotonicOSSSBound
      (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) Finset.univ f 1 1 1 :=
  fk_monotonicOSSSBound_poincare ⊤ (by norm_num) (by norm_num) (by norm_num) hf hf0 hf1

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.Lindeberg
