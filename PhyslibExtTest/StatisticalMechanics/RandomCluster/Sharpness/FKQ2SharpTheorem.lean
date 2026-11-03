/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FKQ2SharpTheorem

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.FKQ2SharpTheorem`

* `oqu_fk_q2_sharp` applied to the complete graph on `Fin 2` at `p = 1/2`, with an arbitrary
  revealment order, for a monotone observable `0 ≤ f ≤ 1`;
* `oqu_fk_q2_sharp` applied to the explicit monotone observable "edge `s(0, 1)` is open".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.FKQ2SharpTheorem

open _root_.StatMech _root_.StatMech.OSSS

-- The q = 2 OSSS inequality on `K₂` at `p = 1/2`, for any order and monotone `0 ≤ f ≤ 1`.
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) {f : ConfigSpace (Sym2 (Fin 2)) → ℝ}
    (hf : Monotone f) (hf0 : 0 ≤ f) (hf1 : ∀ ω, f ω ≤ 1) :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2) f
      ≤ ∑ e, AdaptMConditional.revealAdapt (MonotonicFK.fkMass ⊤ (1 / 2) 2) σ f e
          * Lindeberg.cov (MonotonicFK.fkMass ⊤ (1 / 2) 2) f (Lindeberg.coord e) :=
  AdaptDisintegration.oqu_fk_q2_sharp ⊤ (by norm_num) (by norm_num) σ hf hf0 hf1

-- The same inequality for the explicit monotone observable "`s(0, 1)` is open".
example {n : ℕ} (σ : Fin n ≃ Sym2 (Fin 2)) :
    Lindeberg.var (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
        (Lindeberg.coord s(0, 1))
      ≤ ∑ e, AdaptMConditional.revealAdapt (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
            σ (Lindeberg.coord s(0, 1)) e
          * Lindeberg.cov (MonotonicFK.fkMass (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2)
            (Lindeberg.coord s(0, 1)) (Lindeberg.coord e) :=
  AdaptDisintegration.oqu_fk_q2_sharp ⊤ (by norm_num) (by norm_num) σ (Lindeberg.coord_mono _)
    (Lindeberg.coord_nonneg _) (fun ω => by unfold Lindeberg.coord; split_ifs <;> norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.FKQ2SharpTheorem
