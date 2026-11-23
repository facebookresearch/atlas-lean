/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.PcNontrivial`

On `ℤ²` with `q = 2` (the FK representation of the Ising model) and `q = 1`:
* `fkTheta` lies in `[0, 1]`;
* `fkTheta_le_pow`: `θ¹(1/8, 2) ≤ (1/2)^m` for every `m`;
* `fkTheta_eq_zero_of_lt`: `θ¹(1/8, 2) = 0`, since `2 d p = 1/2 < 1`, so `1/8` lies in
  `fkSubcriticalSet 2 2` and `1/8 ≤ fkPc 2 2` (the bound `p_c ≥ 1/(4d)` at `d = 2`);
* the headline `fkPc_pos` at `d = 2`, `q = 2` and at `d = 1`, `q = 1`, and
  `fkPc_pos_of_two_le` at `d = 3`;
* `fkPc d q ≤ 1` from `fkSubcriticalSet_bddAbove`.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.PcNontrivial

open _root_.StatMech _root_.StatMech.FK

-- `θ¹(p, q)` is a probability.
example : 0 ≤ fkTheta 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) ∧
    fkTheta 2 (p := 1 / 2) (q := 2) (by norm_num) (by norm_num) (by norm_num) ≤ 1 :=
  ⟨fkTheta_nonneg _ _ _ _, fkTheta_le_one _ _ _ _⟩

-- The path-counting bound `θ¹(1/8, 2) ≤ (2 d p)^m = (1/2)^m` on `ℤ²`.
example (m : ℕ) :
    fkTheta 2 (p := 1 / 8) (q := 2) (by norm_num) (by norm_num) (by norm_num) ≤ (1 / 2) ^ m := by
  have h := fkTheta_le_pow (d := 2) (by norm_num) (p := 1 / 8) (q := 2) (by norm_num)
    (by norm_num) (by norm_num) m
  norm_num at h ⊢
  exact h

/-- No percolation on `ℤ²` at `p = 1/8`, `q = 2`. -/
theorem fkTheta_eighth :
    fkTheta 2 (p := 1 / 8) (q := 2) (by norm_num) (by norm_num) (by norm_num) = 0 :=
  fkTheta_eq_zero_of_lt (d := 2) (by norm_num) (p := 1 / 8) (q := 2) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- `1/8` is subcritical for `q = 2` on `ℤ²`. -/
theorem eighth_mem_fkSubcriticalSet : (1 / 8 : ℝ) ∈ fkSubcriticalSet 2 2 :=
  ⟨by norm_num, by norm_num, by norm_num, fkTheta_eighth⟩

-- The lower bound `p_c(2, 2) ≥ 1/(4 d) = 1/8`.
example : (1 / 8 : ℝ) ≤ fkPc 2 2 := le_fkPc_of_mem eighth_mem_fkSubcriticalSet

-- `p_c ≤ 1`, since every subcritical `p` is below `1`.
example : fkPc 2 2 ≤ 1 :=
  csSup_le ⟨_, eighth_mem_fkSubcriticalSet⟩ fun _ ⟨_, hp1, _, _⟩ => hp1.le

-- Positivity of the critical point (headline) for the FK–Ising model on `ℤ²`.
example : 0 < fkPc 2 2 := fkPc_pos (by norm_num) (by norm_num)

-- Positivity of the critical point for Bernoulli percolation (`q = 1`) on `ℤ`.
example : 0 < fkPc 1 1 := fkPc_pos (by norm_num) (le_refl _)

-- `fkPc_pos_of_two_le` on `ℤ³` with `q = 4`.
example : 0 < fkPc 3 4 := fkPc_pos_of_two_le (by norm_num) (by norm_num)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.PcNontrivial
