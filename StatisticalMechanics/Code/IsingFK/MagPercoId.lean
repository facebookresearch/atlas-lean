/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.IsingFK.EsInfinite
import Code.FK.TailLimit
import Code.Ising.TransitionRegime

open MeasureTheory Filter Topology

namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK

variable {d : ℕ}














noncomputable def boundaryConnProfile (d : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (n : ℕ) : ℝ :=
  fkBoundaryConnReal d hp hp1 hq n






theorem boundaryConnProfile_tendsto_fkTheta {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    Tendsto (fun n => boundaryConnProfile d hp hp1 hq n) atTop
      (𝓝 (fkTheta d hp hp1 hq (q := q))) :=
  fkBoundaryConnReal_tendsto_fkTheta hp hp1 hq

























theorem magPercoId_of_fvES (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2)
    (hfvES : ∀ n, fvMagnetization d β n = boundaryConnProfile d hp hp1 hq n) :
    magnetization d β = fkTheta d hp hp1 hq (q := 2) :=
  magPercoId_of_fvES_of_fkLim d β hp hp1 hq
    (fun n => boundaryConnProfile d hp hp1 hq n) hfvES
    (boundaryConnProfile_tendsto_fkTheta hp hp1 hq)

















theorem magPercoId_final (d : ℕ)
    (hfvES : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1) (n : ℕ),
      fvMagnetization d β n
        = boundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n) :
    ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  intro β hβ hp hp1
  exact magPercoId_of_fvES d β hp hp1 (by norm_num) (hfvES β hβ hp hp1)



































theorem ising_transition_of_fvES_of_fkPc_lt_one (d : ℕ) (hd : 2 ≤ d)
    (hfvES : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1) (n : ℕ),
      fvMagnetization d β n
        = boundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    ∃ βc : ℝ, 0 < βc ∧
      (∀ β, 0 < β → β < βc → magnetization d β = 0) ∧
      (∀ β, βc < β → 0 < magnetization d β) :=
  Ising.ising_transition_of_fkPc_lt_one d hd (magPercoId_final d hfvES) hFKsub hpc1








theorem isingBetaC_eq_of_fvES_of_fkPc_lt_one (d : ℕ) (hd : 2 ≤ d)
    (hfvES : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1) (n : ℕ),
      fvMagnetization d β n
        = boundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) n)
    (hFKsub : ∀ (p : ℝ) (hp : 0 < p) (hp1 : p < 1), p ≤ FK.fkPc d 2 →
      FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) = 0)
    (hpc1 : FK.fkPc d 2 < 1) :
    IsingFK.betaC (magnetization d) = -(1 / 2) * Real.log (1 - FK.fkPc d 2) :=
  Ising.isingBetaC_eq_of_fkPc_lt_one d hd (magPercoId_final d hfvES) hFKsub hpc1

end IsingFK

end StatMech
