/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Ising.Magnetization

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}







theorem continuous_spinObs (x : Site d) :
    Continuous (fun ω : ConfigSpace (Site d) => spin ω x) := by
  have hcoord : Continuous (fun ω : ConfigSpace (Site d) => ω x) := continuous_apply x
  have hbool : Continuous (fun b : Bool => if b then (1 : ℝ) else -1) :=
    continuous_of_discreteTopology
  simpa only [spin] using hbool.comp hcoord



theorem spinObs_le_one (x : Site d) (ω : ConfigSpace (Site d)) :
    ‖spin ω x‖ ≤ 1 := by
  rw [Real.norm_eq_abs]; exact abs_spin_le_one ω x




noncomputable def spinBCF (x : Site d) : ConfigSpace (Site d) →ᵇ ℝ :=
  ⟨⟨fun ω => spin ω x, continuous_spinObs x⟩,
    ⟨2, fun ω ω' => by
      have h1 := spinObs_le_one x ω
      have h2 := spinObs_le_one x ω'
      calc dist (spin ω x) (spin ω' x) ≤ ‖spin ω x‖ + ‖spin ω' x‖ := dist_le_norm_add_norm _ _
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by ring⟩⟩

@[simp] theorem spinBCF_apply (x : Site d) (ω : ConfigSpace (Site d)) :
    spinBCF x ω = spin ω x := rfl



theorem integral_spinBCF_eq (d : ℕ) (β : ℝ) :
    ∫ ω, (spinBCF (origin d)) ω ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))
      = magnetization d β := by
  rfl









theorem nonneg_integral_of_weakLimit
    {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
    {ν : ProbabilityMeasure (ConfigSpace (Site d))}
    (h : WeakConvergesTo μ ν) (f : ConfigSpace (Site d) →ᵇ ℝ)
    (hpos : ∀ n, 0 ≤ ∫ ω, f ω ∂(μ n : Measure (ConfigSpace (Site d)))) :
    0 ≤ ∫ ω, f ω ∂(ν : Measure (ConfigSpace (Site d))) :=
  ge_of_tendsto (h.tendsto_integral f) (Filter.Eventually.of_forall hpos)




















theorem magnetization_nonneg_of_fv (d : ℕ) (β : ℝ)
    (hfv : ∀ n, 0 ≤ ∫ ω, spin ω (origin d)
      ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))) :
    0 ≤ magnetization d β := by
  
  obtain ⟨φ, _hφ, htends⟩ := plusState_isInfiniteVolumeState d β 0
  
  have hpos : ∀ n, 0 ≤ ∫ ω, (spinBCF (origin d)) ω
      ∂((fun n => plusMeasure d n β 0) (φ n) : Measure (ConfigSpace (Site d))) :=
    fun n => by simpa only [spinBCF_apply] using hfv (φ n)
  have hlim : 0 ≤ ∫ ω, (spinBCF (origin d)) ω
      ∂(plusState d β 0 : Measure (ConfigSpace (Site d))) :=
    nonneg_integral_of_weakLimit htends (spinBCF (origin d)) hpos
  rwa [integral_spinBCF_eq] at hlim







theorem hmag_nonneg_of_fv (d : ℕ)
    (hfv : ∀ β, ∀ n, 0 ≤ ∫ ω, spin ω (origin d)
      ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))) :
    ∀ β, 0 ≤ magnetization d β :=
  fun β => magnetization_nonneg_of_fv d β (hfv β)

end Ising

end StatMech
