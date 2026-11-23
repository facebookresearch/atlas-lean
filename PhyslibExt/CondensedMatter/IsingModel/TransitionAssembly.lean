/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.BoxMagnetization
public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.MagnetizationFK
public import PhyslibExt.StatisticalMechanics.RandomCluster.PcLtOnePeierls
public import PhyslibExt.StatisticalMechanics.RandomCluster.ThetaZeroBelowPc

/-!
# Assembling the Ising phase transition from FK results

The phase transition from the box identity between Ising and FK, non-percolation at `p_c`, and `p_c
< 1`.

## i. Overview

The magnetization is nonnegative for `β ≥ 0`. If the finite-volume magnetization equals the wired FK
one-point function in boxes, the FK percolation probability vanishes at `p_c`, and `p_c < 1`, the
Ising model on `ℤ^d`, `d ≥ 2`, has a phase transition at `β_c = -½ log (1 - p_c) > 0`.

The statements here are conditional: they take as hypotheses the identification of the Ising
magnetization with the FK percolation probability and the nontriviality of the FK critical point.
The unconditional phase transition for `d ≥ 2` is `ising_phase_transition_of_two_le` in
`FKRepresentation.PcUpperAllDimensions`.

## ii. Key results

- `StatMech.Ising.ita_hmag_nonneg` : nonnegativity of the magnetization
- `StatMech.Ising.ita_ising_transition` : the phase transition
- `StatMech.Ising.ita_isingBetaC_eq` : `β_c = -½ log (1 - p_c)`

## iii. Table of contents

- A. Assembly

## iv. References

- H. Duminil-Copin, *Lectures on the Ising and Potts models on the hypercubic lattice*, PIMS–CRM
  Summer School in Probability (2017), arXiv:1707.00520
- G. Grimmett, *The Random-Cluster Model*, Springer (2006)
-/

@[expose] public section

open Real

namespace StatMech

namespace Ising

open StatMech.IsingFK StatMech.FK

/-! ## A. Assembly -/

lemma ita_hmag_nonneg (d : ℕ) {β : ℝ} (hβ : 0 ≤ β) : 0 ≤ magnetization d β :=
  IsingFK.magnetization_nonneg d hβ

lemma ita_hFKsub_of_atCriticality (d : ℕ)
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0) :
    ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0 :=
  FK.tzp_fkTheta_eq_zero_of_le_pc_of_pc hθpc

lemma ita_ising_transition (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ising_transition_of_fkPc_lt_one d hd
    (mfc_magPercoId d (le_trans (by norm_num) hd) hisingBox)
    (ita_hFKsub_of_atCriticality d hθpc) hpc1

lemma ita_ising_transition_two_of_fkNonPercolationBound
    (hθpc : ∀ (hp : 0 < FK.fkPc 2 2) (hp1 : FK.fkPc 2 2 < 1),
      FK.fkTheta 2 hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hBound : ∃ p₀ : ℝ, p₀ < 1 ∧
      ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p₀ < p →
        FK.FkNonPercolationBound 2 hp hp1 (by norm_num : (0 : ℝ) < 2)) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization 2 β = 0) ∧
      (∀ β, βc < β → 0 < magnetization 2 β) := by
  have hpc1 : FK.fkPc 2 2 < 1 := FK.fkPc_lt_one (q := 2) (by norm_num) hBound
  exact ita_ising_transition 2 (le_refl 2) (IsingFK.hbx_hisingBox 2) hθpc hpc1

lemma ita_isingBetaC_eq (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  isingBetaC_eq_of_fkPc_lt_one d hd
    (mfc_magPercoId d (le_trans (by norm_num) hd) hisingBox)
    (ita_hFKsub_of_atCriticality d hθpc) hpc1

lemma ita_isingBetaC_pos (d : ℕ) (hd : 2 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hθpc : ∀ (hp : 0 < FK.fkPc d 2) (hp1 : FK.fkPc d 2 < 1),
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  isingBetaC_pos_of_fkPc_lt_one d hd
    (mfc_magPercoId d (le_trans (by norm_num) hd) hisingBox)
    (ita_hFKsub_of_atCriticality d hθpc) hpc1

end Ising

end StatMech
