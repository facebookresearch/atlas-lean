/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.FKQ2Sharp

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FKQ2Sharp`

* `mul_one_sub_le_quarter` at `x = 1/3` and `russoPrefactor_ge_four` at `x = 1/2`;
* `fkProbOf_nonneg` and `fkProbOf_le_one` on the one-edge graph `⊤` on `Fin 2`, `p = 1/2`,
  `q = 2`;
* `fk_q2_crossing_decay` in conditional form on that graph.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FKQ2Sharp

open _root_.StatMech _root_.StatMech.FK Set

/-- The one-edge test graph. -/
abbrev G2 : SimpleGraph (Fin 2) := ⊤

-- `x (1 - x) ≤ 1/4` at `x = 1/3`, and the Russo prefactor at `1/2` is at least `4`.
example : (1 / 3 : ℝ) * (1 - 1 / 3) ≤ 1 / 4 ∧ (4 : ℝ) ≤ russoPrefactor (1 / 2) :=
  ⟨mul_one_sub_le_quarter _, russoPrefactor_ge_four (by norm_num) (by norm_num)⟩

-- FK event probabilities lie in `[0, 1]`.
example (A : Set (ConfigSpace (Sym2 (Fin 2)))) :
    0 ≤ fkProbOf G2 (1 / 2) 2 A ∧ fkProbOf G2 (1 / 2) 2 A ≤ 1 :=
  ⟨fkProbOf_nonneg G2 (by norm_num) (by norm_num) (by norm_num) A,
   fkProbOf_le_one G2 (by norm_num) (by norm_num) (by norm_num) A⟩

-- Exponential decay from the covariance input, on `[1/4, 3/4]` with `n = 1`.
example (A : Set (ConfigSpace (Sym2 (Fin 2))))
    (hdiff : ∀ p ∈ Icc (1 / 4 : ℝ) (3 / 4), HasDerivAt (fun p => fkProbOf G2 p 2 A)
      (deriv (fun p => fkProbOf G2 p 2 A) p) p)
    (hcov : ∀ p ∈ Icc (1 / 4 : ℝ) (3 / 4), ((1 : ℕ) : ℝ) * 1
        * (fkProbOf G2 p 2 A * (1 - fkProbOf G2 p 2 A))
      ≤ 1 * ∑ e ∈ G2.edgeFinset, fkCov G2 p 2 (A.indicator (fun _ => (1 : ℝ))) (coord e))
    (hub : ∀ p ∈ Icc (1 / 4 : ℝ) (3 / 4), fkProbOf G2 p 2 A ≤ 1 - 1 / 2) :
    fkProbOf G2 (1 / 4) 2 A
      ≤ Real.exp (-(4 * ((1 : ℕ) : ℝ) * 1 * (1 / 2) / 1 * (3 / 4 - 1 / 4))) :=
  fk_q2_crossing_decay G2 le_rfl A 1 1 (1 / 2) one_pos one_pos (by norm_num) _ _
    (by norm_num) (by norm_num) (by norm_num) hdiff hcov hub

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FKQ2Sharp
