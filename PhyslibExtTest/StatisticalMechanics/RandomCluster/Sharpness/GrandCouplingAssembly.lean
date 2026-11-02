/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.GrandCouplingAssembly

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.GrandCouplingAssembly`

* `tree_osss_unconditional` (the headline Poincaré inequality) for the random-cluster mass on
  `K₂` at `p = 1/2`, `q = 2` and the coordinate observable;
* `fk_q2_osss` on `K₂` at `p = 1/2` for the same observable;
* `Wt_zero` and `Wt_card` (the interpolation endpoints) on explicit vectors.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.GrandCouplingAssembly

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.Monotonic
open _root_.StatMech.OSSS.Coding _root_.StatMech.OSSS.GrandCoupling
open _root_.StatMech.OSSS.GrandCouplingAssembly

-- The Poincaré inequality for a monotonic measure, instantiated on `K₂`.
example :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (Lindeberg.coord (s(0, 1) : Sym2 (Fin 2)))
      ≤ ∑ e, Lindeberg.cov (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (Lindeberg.coord s(0, 1))
          (Lindeberg.coord e) :=
  tree_osss_unconditional
    (MonotonicFK.fkMass_pos (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num) (by norm_num))
    (MonotonicFK.fkMass_sum_eq_one (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    (MonotonicFK.fkMass_isMonotonic (p := 1 / 2) (q := 2) ⊤ (by norm_num) (by norm_num)
      (by norm_num))
    (Lindeberg.coord_mono _) (Lindeberg.coord_nonneg _) (fun ω => by
      unfold Lindeberg.coord; split_ifs <;> norm_num)

-- The `q = 2` random-cluster case on `K₂` at `p = 1/2`.
example :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (Lindeberg.coord (s(0, 1) : Sym2 (Fin 2)))
      ≤ ∑ e, Lindeberg.cov (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
          (Lindeberg.coord s(0, 1))
          (Lindeberg.coord e) :=
  fk_q2_osss ⊤ (by norm_num) (by norm_num) (Lindeberg.coord_mono _)
    (Lindeberg.coord_nonneg _) (fun ω => by unfold Lindeberg.coord; split_ifs <;> norm_num)

-- The interpolation `Wt U V s` starts at `U` and ends at `V`.
example : Wt (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1) 0 = (fun _ => 0) ∧
    Wt (fun _ : Fin 2 => (0 : ℝ)) (fun _ => 1) 2 = (fun _ => 1) :=
  ⟨Wt_zero _ _, Wt_card _ _⟩

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.GrandCouplingAssembly
