/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












































































































import Mathlib
import Code.Ising.MagNonneg
import Code.Ising.TransitionFK
import Code.FK.CriticalPoint

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators

namespace StatMech

namespace IsingFK

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

















theorem tendsto_eq_of_eq_of_tendsto {a b : ℕ → ℝ} {A B : ℝ}
    (hab : ∀ n, a n = b n) (ha : Tendsto a atTop (𝓝 A)) (hb : Tendsto b atTop (𝓝 B)) :
    A = B := by
  have hb' : Tendsto a atTop (𝓝 B) := by
    have : b = a := funext fun n => (hab n).symm
    rwa [this] at hb
  exact tendsto_nhds_unique ha hb'













noncomputable def fvMagnetization (d : ℕ) (β : ℝ) (n : ℕ) : ℝ :=
  ∫ ω, spin ω (origin d) ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))














theorem magnetization_eq_limit (d : ℕ) (β : ℝ) :
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









































theorem magPercoId_of_fvES_of_fkLim (d : ℕ) (β : ℝ)
    {p : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : (0 : ℝ) < 2)
    (fvBoundaryConn : ℕ → ℝ)
    (hfvES : ∀ n, fvMagnetization d β n = fvBoundaryConn n)
    (hfkLim : Tendsto fvBoundaryConn atTop (𝓝 (FK.fkTheta d hp hp1 hq (q := 2)))) :
    magnetization d β = FK.fkTheta d hp hp1 hq (q := 2) := by
  obtain ⟨φ, hφ, hmagLim⟩ := magnetization_eq_limit d β
  
  have hfk : Tendsto (fun n => fvBoundaryConn (φ n)) atTop
      (𝓝 (FK.fkTheta d hp hp1 hq (q := 2))) := hfkLim.comp hφ.tendsto_atTop
  
  exact tendsto_eq_of_eq_of_tendsto (a := fun n => fvMagnetization d β (φ n))
    (b := fun n => fvBoundaryConn (φ n)) (fun n => hfvES (φ n)) hmagLim hfk




















theorem magPercoId_of_fvES_of_fkLim_hyp (d : ℕ)
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
