/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib
import Code.Ising.MagNonneg
import Code.Sharpness.BkCriterionInfinite
import Code.Sharpness.TildeBc

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators

namespace StatMech
namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


noncomputable def spinPairBCF (x y : Site d) :
    ConfigSpace (Site d) →ᵇ ℝ :=
  spinBCF x * spinBCF y

@[simp] theorem spinPairBCF_apply (x y : Site d)
    (ω : ConfigSpace (Site d)) :
    spinPairBCF x y ω = spin ω x * spin ω y := rfl


noncomputable def plusCorr (d : ℕ) (β : ℝ) (x y : Site d) : ℝ :=
  ∫ ω, spin ω x * spin ω y
    ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))



theorem plusMeasure_pair_tendsto (β : ℝ) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0)
      (plusState d β 0)) (x y : Site d) :
    Tendsto
      (fun n ↦ ∫ ω, spin ω x * spin ω y
        ∂(plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds (plusCorr d β x y)) := by
  simpa only [spinPairBCF_apply, plusCorr] using
    hconv.tendsto_integral (spinPairBCF x y)


noncomputable def simonBoundaryIntegral
    (β : ℝ) (S : Finset (Site d)) (o z : Site d)
    (μ : Measure (ConfigSpace (Site d))) : ℝ :=
  ∑ e ∈ boundaryEdges d S,
    Real.tanh β * corrOriginInner d β S e.1 *
      (∫ ω, spin ω e.2 * spin ω z ∂μ)



noncomputable def simonBoundaryPlus
    (β : ℝ) (S : Finset (Site d)) (o z : Site d) : ℝ :=
  ∑ e ∈ boundaryEdges d S,
    Real.tanh β * corrOriginInner d β S e.1 * plusCorr d β e.2 z



theorem simonBoundaryIntegral_tendsto (β : ℝ) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0)
      (plusState d β 0)) (S : Finset (Site d)) (o z : Site d) :
    Tendsto
      (fun n ↦ simonBoundaryIntegral β S o z
        (plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds (simonBoundaryPlus β S o z)) := by
  unfold simonBoundaryIntegral simonBoundaryPlus
  apply tendsto_finset_sum
  intro e he
  apply Tendsto.const_mul
  exact plusMeasure_pair_tendsto β φ hconv e.2 z







theorem plusCorr_simon_of_eventually_finite
    (β : ℝ) (S : Finset (Site d)) (o z : Site d)
    (hfinite : ∀ φ : ℕ → ℕ, StrictMono φ →
      ∀ᶠ n in atTop,
        (∫ ω, spin ω o * spin ω z
          ∂(plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) ≤
        simonBoundaryIntegral β S o z
          (plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d)))) :
    plusCorr d β o z ≤ simonBoundaryPlus β S o z := by
  obtain ⟨φ, hφ, hconv⟩ := plusState_isInfiniteVolumeState d β 0
  exact le_of_tendsto_of_tendsto
    (plusMeasure_pair_tendsto β φ hconv o z)
    (simonBoundaryIntegral_tendsto β φ hconv S o z)
    (hfinite φ hφ)

end Sharpness
end StatMech
