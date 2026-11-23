/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.StatisticalMechanics.RandomCluster.WiredDomChain

/-!
# Magnetization and FK percolation, shifted boxes

The variant of `MagPercoIdBox` in which the finite-volume magnetization in `Λ_n` is compared with
the wired Edwards–Sokal one-point function on the box graph of `Λ_{n+1}`.

## i. Overview

The plus boundary condition of `Λ_n` lives on the outer boundary of `Λ_{n+1}`, so the natural
identity compares the magnetization in `Λ_n` with the box graph of `Λ_{n+1}`. Under that identity
the boundary connection profile on `Λ_{n+1}` converges to `θ(p)`, the spontaneous magnetization
equals `θ(1 - e^{-2β})`, and the Ising critical inverse temperature is
`-(1/2) log (1 - p_c) > 0`.

## ii. Key results

- `mfc_magPercoId` : `m*(β) = θ(pOfBeta β)` for all `β > 0`.
- `mfc_ising_transition` : the magnetization is positive exactly for `β > pToBeta 2 p_c`.
- `mfc_isingBetaC_eq` : `β_c = pToBeta 2 p_c`.

## iii. Table of contents

- A. The boundary connection profile on shifted boxes
- B. Magnetization, percolation and the critical point

## iv. References

- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model I. Introduction and relation to
  other models*, Physica 57 (1972) 536–564.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988) 2009–2012.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 1.4.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped BigOperators

namespace StatMech

namespace Ising

open StatMech.IsingFK StatMech.FK

variable {d : ℕ}

/-! ## A. The boundary connection profile on shifted boxes -/

lemma mfc_boxBoundaryConnProfile_succ_tendsto {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    Tendsto (fun n => IsingFK.boxBoundaryConnProfile d hp hp1
        (by norm_num : (0 : ℝ) < 2) (n + 1))
      atTop (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) :=
  (FK.boxBoundaryConnProfile_tendsto hp hp1).comp (tendsto_add_atTop_nat 1)

lemma mfc_fvMagnetization_eq_profile_succ (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2)
    (hd : 1 ≤ d) {n : ℕ} (_hn : 1 ≤ n)
    (hisingBox : fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            p (boxOrigin d (n + 1))) :
    fvMagnetization d β n = boxBoundaryConnProfile d hp hp1 hq (n + 1) := by
  obtain ⟨v₀, hv₀⟩ := boxBoundary_nonempty d (n + 1) hd (by omega)
  rw [hisingBox,
    show boxBoundaryConnProfile d hp hp1 hq (n + 1)
        = wiredConnToBdryProb (boxGraph d (n + 1)) (boxBoundary d (n + 1)) p
            (boxOrigin d (n + 1)) from rfl,
    esWiredOnePoint_eq_wiredConnToBdryProb (boxGraph d (n + 1)) (boxBoundary d (n + 1)) p
      (boxOrigin d (n + 1)) v₀ hv₀]

/-! ## B. Magnetization, percolation and the critical point -/

lemma mfc_magPercoId (d : ℕ) (hd : 1 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1))) :
    ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  intro β hβ hp hp1
  set hq : (0 : ℝ) < 2 := by norm_num with hqdef
  set b : ℕ → ℝ := fun n => if 1 ≤ n then boxBoundaryConnProfile d hp hp1 hq (n + 1)
    else fvMagnetization d β n with hb
  have hES : ∀ n, fvMagnetization d β n = b n := by
    intro n
    by_cases hn : 1 ≤ n
    · simp only [hb, ite_eq_left hn]
      exact mfc_fvMagnetization_eq_profile_succ d β hp hp1 hq hd hn (hisingBox β hβ n hn)
    · simp only [hb, ite_eq_right hn]
  have hlim : Tendsto b atTop (𝓝 (FK.fkTheta d hp hp1 hq (q := 2))) := by
    refine (mfc_boxBoundaryConnProfile_succ_tendsto hp hp1).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [hb, ite_eq_left hn]
  exact magPercoId_of_fvES_of_fkLim d β hp hp1 hq b hES hlim

lemma mfc_htransition (d : ℕ) (hd : 1 ≤ d)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∀ β, 0 < β → (0 < magnetization d β ↔ pToBeta 2 (FK.fkPc d 2) < β) :=
  htransition_fk_of_identity d (mfc_magPercoId d hd hisingBox) hFKsub hpc1

lemma mfc_ising_transition (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  ising_transition d hmag_nonneg (mfc_htransition d hd hisingBox hFKsub hpc1) hpc0 hpc1

lemma mfc_isingBetaC_eq (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  ising_betaC_eq d hmag_nonneg (mfc_htransition d hd hisingBox hFKsub hpc1) hpc0 hpc1

lemma mfc_isingBetaC_pos (d : ℕ) (hd : 1 ≤ d)
    (hmag_nonneg : ∀ β, 0 ≤ magnetization d β)
    (hisingBox : ∀ β, 0 < β → ∀ n, 1 ≤ n → fvMagnetization d β n
        = esWiredOnePoint (boxGraph d (n + 1)) (boxBoundary d (n + 1)) (0 : Fin 2)
            (pOfBeta β) (boxOrigin d (n + 1)))
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc0 : 0 < FK.fkPc d 2) (hpc1 : FK.fkPc d 2 < 1) :
    0 < IsingFK.betaC (magnetization d) :=
  isingBetaC_pos d hmag_nonneg (mfc_htransition d hd hisingBox hFKsub hpc1) hpc0 hpc1

end Ising

end StatMech
