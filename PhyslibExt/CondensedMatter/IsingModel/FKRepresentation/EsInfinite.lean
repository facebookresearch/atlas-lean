/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.FKRepresentation.Q2
public import PhyslibExt.CondensedMatter.IsingModel.MagNonneg
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint

/-!
# Infinite-volume magnetization from finite-volume Edwards–Sokal identities

The plus-boundary magnetization at the origin in the box `Λ_n` converges along a subsequence to
the infinite-volume magnetization, so a finite-volume identity with an FK connection probability
passes to the limit.

## i. Overview

`fvMagnetization d β n` is the expectation of `σ_0` under the plus-boundary Ising measure on
`Λ_n` at zero field. Along a subsequence it converges to the spontaneous magnetization
`magnetization d β`. If for every `n` it equals an FK boundary-connection probability whose limit
is the FK percolation probability `θ(p)` at `p = 1 - e^{-2β}`, then `m*(β) = θ(p)`.

## ii. Key results

- `fvMagnetization` : the plus-boundary magnetization at the origin in `Λ_n`.
- `magnetization_eq_limit` : it converges to the spontaneous magnetization along a subsequence.
- `magPercoId_of_fvES_of_fkLim` : the identification `m*(β) = θ(p)` from the finite-volume
  identities and the FK limit.

## iii. Table of contents

- A. Finite-volume magnetization
- B. Passage to the limit

## iv. References

- C. M. Fortuin and P. W. Kasteleyn, *On the random-cluster model I. Introduction and relation to
  other models*, Physica 57 (1972) 536–564.
- R. G. Edwards and A. D. Sokal, *Generalization of the Fortuin–Kasteleyn–Swendsen–Wang
  representation and Monte Carlo algorithm*, Phys. Rev. D 38 (1988) 2009–2012.
- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Section 1.4.
-/

@[expose] public section

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## A. Finite-volume magnetization -/

/-- The magnetization `⟨σ_0⟩` at the origin under the plus-boundary Ising measure on the box `Λ_n`
at inverse temperature `β` and zero field. -/
noncomputable def fvMagnetization (d : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  ∫ ω, spin ω (origin d) ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))

lemma magnetization_eq_limit (d : ℕ) (β : ℝ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => fvMagnetization d β (φ n)) atTop (𝓝 (magnetization d β)) := by
  obtain ⟨φ, hφ, htends⟩ := plusState_isInfiniteVolumeState d β 0
  refine ⟨φ, hφ, ?_⟩
  have hlim := htends.tendsto_integral (spinBCF (origin d))
  rw [integral_spinBCF_eq] at hlim
  have hterm : (fun n => ∫ ω, (spinBCF (origin d)) ω
      ∂((fun n => plusMeasure d n β 0) ∘ φ) n) = (fun n => fvMagnetization d β (φ n)) := by
    funext n
    simp only [Function.comp_apply, spinBCF_apply, fvMagnetization]
  rwa [hterm] at hlim

/-! ## B. Passage to the limit -/

lemma magPercoId_of_fvES_of_fkLim (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2)
    (fvBoundaryConn : ℕ → ℝ)
    (hfvES : ∀ n, fvMagnetization d β n = fvBoundaryConn n)
    (hfkLim : Tendsto fvBoundaryConn atTop (𝓝 (FK.fkTheta d hp hp1 hq (q := 2)))) :
    magnetization d β = FK.fkTheta d hp hp1 hq (q := 2) := by
  obtain ⟨φ, hφ, hmagLim⟩ := magnetization_eq_limit d β
  have hfk : Tendsto (fun n => fvBoundaryConn (φ n)) atTop
      (𝓝 (FK.fkTheta d hp hp1 hq (q := 2))) := hfkLim.comp hφ.tendsto_atTop
  exact tendsto_nhds_unique (hmagLim.congr fun n => hfvES (φ n)) hfk

lemma magPercoId_of_fvES_of_fkLim_hyp (d : ℕ)
    (fvBoundaryConn : ℝ → ℕ → ℝ)
    (hfvES : ∀ β, 0 < β → ∀ n, fvMagnetization d β n = fvBoundaryConn β n)
    (hfkLim : ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
        Tendsto (fvBoundaryConn β) atTop
          (𝓝 (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2)))) :
    ∀ β, 0 < β → ∀ (hp : 0 < pOfBeta β) (hp1 : pOfBeta β < 1),
      magnetization d β = FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2) := by
  intro β hβ hp hp1
  exact magPercoId_of_fvES_of_fkLim d β hp hp1 (by norm_num) (fvBoundaryConn β)
    (hfvES β hβ) (hfkLim β hβ hp hp1)

end IsingFK

end StatMech
