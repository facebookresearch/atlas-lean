/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Q2

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Q2`

* `pOfBeta` and `betaOfP` at `0`, at `p = 1/2` (`β = log 2 / 2`), and their inverse laws
  (`betaOfP_pOfBeta`, `pOfBeta_betaOfP`), with `pOfBeta_mem_Ico` at `β = 1`;
* `toIsing` on constant two-state colorings;
* `isingProb_eq_pottsProb` on the single edge `⊤ : SimpleGraph (Fin 2)` at `β_Ising = 1`,
  `β_Potts = 2`, `J = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.Q2

open _root_.StatMech _root_.StatMech.IsingFK

-- Infinite temperature corresponds to `p = 0`.
example : pOfBeta 0 = 0 := by simp [pOfBeta]

-- `p = 0` corresponds to `β = 0`.
example : betaOfP 0 = 0 := by simp [betaOfP]

-- `β = log 2 / 2` gives the FK parameter `p = 1/2`.
example : pOfBeta (Real.log 2 / 2) = 1 / 2 := by
  unfold pOfBeta
  rw [show -2 * (Real.log 2 / 2) = -Real.log 2 by ring, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

-- `p = 1/2` gives `β = log 2 / 2`.
example : betaOfP (1 / 2) = Real.log 2 / 2 := by
  unfold betaOfP
  rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
  ring

-- The two parametrizations are inverse.
example : betaOfP (pOfBeta 3) = 3 := betaOfP_pOfBeta 3

-- The two parametrizations are inverse on `p < 1`.
example : pOfBeta (betaOfP (1 / 3)) = 1 / 3 := pOfBeta_betaOfP _ (by norm_num)

-- At `β = 1` the FK parameter lies in `[0, 1)`.
example : pOfBeta 1 ∈ Set.Ico (0 : ℝ) 1 := pOfBeta_mem_Ico 1 zero_le_one

-- The constant coloring `0` is the all-minus Ising configuration.
example : toIsing (fun _ : Fin 3 => (0 : Fin 2)) = fun _ => false := by
  rfl

-- The constant coloring `1` is the all-plus Ising configuration.
example : toIsing (fun _ : Fin 3 => (1 : Fin 2)) = fun _ => true := by
  rfl

-- Ising and two-state Potts probabilities agree on the single edge when `β_P J = 2 β_I`.
example (σ : Fin 2 → Fin 2) :
    Ising.isingProb (⊤ : SimpleGraph (Fin 2)) 1 0 (toIsing σ) =
      Potts.pottsProb (⊤ : SimpleGraph (Fin 2)) 2 2 1 σ :=
  isingProb_eq_pottsProb _ 1 2 1 (by norm_num) σ

end PhyslibExtTest.CondensedMatter.IsingModel.FKRepresentation.Q2
