/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.AntitoneInQ

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.AntitoneInQ`

On the one-edge graph `⊤` on `Fin 2` at `p = 1/2`, with `q₁ = 1 ≤ q₂ = 2`:
* `fkProb_cross_q`: Holley's cross condition at the all-closed and all-open configurations;
* `fk_antitone_in_q`: the measure at `q = 2` is dominated by the measure at `q = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.AntitoneInQ

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- Holley's cross condition between `q = 2` and `q = 1`.
example : fkProb G2 (1 / 2) 2 (fun _ => false) * fkProb G2 (1 / 2) 1 (fun _ => true) ≤
    fkProb G2 (1 / 2) 2 ((fun _ => false) ⊓ fun _ => true) *
      fkProb G2 (1 / 2) 1 ((fun _ => false) ⊔ fun _ => true) :=
  fkProb_cross_q G2 (by norm_num) (by norm_num) le_rfl (by norm_num) _ _

-- Stochastic domination: the measure at `q = 2` lies below the measure at `q = 1`.
example : measOfMass (fkProb G2 (1 / 2) 2) ≼ measOfMass (fkProb G2 (1 / 2) 1) :=
  fk_antitone_in_q G2 (by norm_num) (by norm_num) le_rfl (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.AntitoneInQ
