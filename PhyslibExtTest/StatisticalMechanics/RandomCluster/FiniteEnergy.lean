/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.FiniteEnergy

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.FiniteEnergy`

On the one-edge graph `⊤ : SimpleGraph (Fin 2)` at `p = 1/2`, `q = 2`:
* `cFE (1/2) 2 = 1/3`, and `cFE` is positive and at most `1/2` at further parameters;
* `finite_energy` applies to the genuine edge `s(0, 1)` and to every configuration, giving
  `1/3 ≤ condOpen ≤ 2/3`;
* for the non-edge coordinate `s(0, 0)` the conditional probability is exactly `1/2`
  (`condOpen_eq_half`), the artifact of the uniform law of non-edge coordinates.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.FiniteEnergy

open _root_.StatMech _root_.StatMech.FK

/-- The finite-energy constant at `p = 1/2`, `q = 2` is `min (1/3) (1/2) = 1/3`. -/
theorem cFE_half_two : cFE (1 / 2) 2 = 1 / 3 := by
  rw [cFE]; norm_num

-- `cFE` is positive and at most `1/2` (here at `p = 9/10`, `q = 3`).
example : 0 < cFE (9 / 10) 3 ∧ cFE (9 / 10) 3 ≤ 1 / 2 :=
  ⟨cFE_pos (by norm_num) (by norm_num) (by norm_num),
    cFE_le_half (by norm_num) (by norm_num) (by norm_num)⟩

-- Finite energy on the edge `s(0, 1)` of `⊤ : SimpleGraph (Fin 2)`, for every configuration:
-- the conditional probability of the edge being open lies in `[1/3, 2/3]`.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    1 / 3 ≤ condOpen (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 s(0, 1) ω ∧
      condOpen (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 s(0, 1) ω ≤ 2 / 3 := by
  have h := finite_energy (⊤ : SimpleGraph (Fin 2)) (p := 1 / 2) (q := 2) (by norm_num)
    (by norm_num) (by norm_num) s(0, 1) ω
  rw [cFE_half_two] at h
  constructor
  · exact h.1
  · linarith [h.2]

-- At `q = 1` (Bernoulli percolation, `p = 1/4`) the bound is `[1/4, 3/4]`.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    1 / 4 ≤ condOpen (⊤ : SimpleGraph (Fin 2)) (1 / 4) 1 s(0, 1) ω := by
  have h := finite_energy (⊤ : SimpleGraph (Fin 2)) (p := 1 / 4) (q := 1) (by norm_num)
    (by norm_num) (le_refl _) s(0, 1) ω
  have hc : cFE (1 / 4) 1 = 1 / 4 := by rw [cFE]; norm_num
  rw [hc] at h
  exact h.1

-- A non-edge coordinate is a fair coin: its conditional probability is `1/2`.
example (ω : ConfigSpace (Sym2 (Fin 2))) :
    condOpen (⊤ : SimpleGraph (Fin 2)) (1 / 2) 2 s(0, 0) ω = 1 / 2 :=
  condOpen_eq_half _ (by norm_num) (by norm_num) (by norm_num) (by simp) ω

end PhyslibExtTest.StatisticalMechanics.RandomCluster.FiniteEnergy
