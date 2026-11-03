/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalDecayDischarged

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalDecayDischarged`

* `fk_russo_discharges` on the complete graph on `Fin 2` at `p = 1/2`, `q = 2`, for an
  arbitrary event;
* `osss_differential_inequality_disch` at explicit numbers;
* `connectedToSet_increasing`: the crossing event `crossEvent` on one edge of `ℤ¹` is increasing;
* `covSum_ge_explore` stated by name.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalDecayDischarged

open _root_.StatMech _root_.StatMech.OSSS _root_.StatMech.OSSS.RevealmentConstruction
open _root_.StatMech.Lattice

-- Russo's inequality for the random-cluster model on `K₂`.
example (A : Set (ConfigSpace (Sym2 (Fin 2)))) :
    0 < FK.russoPrefactor (1 / 2) ∧
      FK.russoPrefactor (1 / 2)
          * (∑ e ∈ (⊤ : SimpleGraph (Fin 2)).edgeFinset,
              FK.fkCov ⊤ (1 / 2) 2 (A.indicator (fun _ => (1 : ℝ))) (FK.coord e))
        ≤ deriv (fun p => FK.fkProbOf (⊤ : SimpleGraph (Fin 2)) p 2 A) (1 / 2) :=
  fk_russo_discharges ⊤ (by norm_num) (by norm_num) (by norm_num) A

-- The algebraic differential-inequality step at explicit values.
example : ((1 : ℕ) : ℝ) * 1 * 1 / 1 * ((1 / 2 : ℝ) * (1 - 1 / 2)) ≤ 1 :=
  osss_differential_inequality_disch 1 1 1 1 (1 / 2) 1 1 one_pos one_pos (by norm_num)
    (by norm_num)

-- The crossing event of one edge of `ℤ¹` is increasing.
example (edge : Fin 1 → Sym2 (Site 1)) (B : Set (Site 1)) :
    IsIncreasing (crossEvent edge 0 B) :=
  connectedToSet_increasing edge 0 B

-- The exploration covariance bound exists with the expected name.
example := @covSum_ge_explore

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.SubcriticalDecayDischarged
