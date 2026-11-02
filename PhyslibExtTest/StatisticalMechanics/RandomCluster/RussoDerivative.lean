/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivative

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.RussoDerivative`

On the one-edge graph `⊤` on `Fin 2` at `p = 1/2`, `q = 2`:
* `russoPrefactor (1/2) = 4` and `russoPrefactor_pos`;
* `fkMean_const` (the partition function is positive by `fkZ_pos`);
* `hasDerivAt_fkProbOf` (Russo's formula) and `russo_bound` for the event "the edge is open".
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.RussoDerivative

open _root_.StatMech _root_.StatMech.FK

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- The Russo prefactor at `1/2`.
example : russoPrefactor (1 / 2) = 4 ∧ 0 < russoPrefactor (1 / 2) :=
  ⟨by norm_num [russoPrefactor], russoPrefactor_pos (by norm_num) (by norm_num)⟩

-- The expectation of a constant.
example : fkMean G2 (1 / 2) 2 (fun _ => 3) = 3 :=
  fkMean_const G2 _ _ (fkZ_pos G2 (by norm_num) (by norm_num) two_pos).ne'

-- Russo's formula for the event "the edge `s(0, 1)` is open".
example : HasDerivAt (fun p => fkProbOf G2 p 2 {ω | ω s(0, 1) = true})
    ((∑ e ∈ G2.edgeFinset, fkCov G2 (1 / 2) 2
      (({ω | ω s(0, 1) = true} : Set _).indicator fun _ => (1 : ℝ)) (coord e)) /
        (1 / 2 * (1 - 1 / 2))) (1 / 2) :=
  hasDerivAt_fkProbOf G2 (by norm_num) (by norm_num) two_pos _

-- The Russo lower bound.
example := russo_bound G2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) two_pos
  {ω | ω s(0, 1) = true}

end PhyslibExtTest.StatisticalMechanics.RandomCluster.RussoDerivative
