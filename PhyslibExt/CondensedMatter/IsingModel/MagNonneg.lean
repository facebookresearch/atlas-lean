/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Magnetization

/-!
# Nonnegativity of the spontaneous magnetization

If the finite-volume plus-state magnetizations are nonnegative, so is the infinite-volume
magnetization.

## i. Overview

The origin spin is a bounded continuous function on the configuration space. Weak convergence of the
plus-boundary box measures along the subsequence defining `plusState` therefore carries the bound `0
≤ ⟨σ_0⟩⁺_{Λ_n, β}` to the limit, giving `0 ≤ m*(β)`.

## ii. Key results

- `StatMech.Ising.nonneg_integral_of_weakLimit` : nonnegative integrals of a bounded continuous
  function pass to weak limits
- `StatMech.Ising.magnetization_nonneg_of_fv` : the magnetization is nonnegative if the box
  magnetizations are
- `StatMech.Ising.hmag_nonneg_of_fv` : the same statement for all `β`

## iii. Table of contents

- A. The spin as a bounded continuous function
- B. Passing to the weak limit

## iv. References

- S. Friedli and Y. Velenik, *Statistical Mechanics of Lattice Systems: A Concrete Mathematical
  Introduction*, Cambridge University Press (2017), Chapter 3
-/

@[expose] public section

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators

namespace StatMech

namespace Ising

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}

/-! ## A. The spin as a bounded continuous function -/

lemma continuous_spinObs (x : Site d) :
    Continuous (fun ω : ConfigSpace (Site d) => spin ω x) := by
  have hcoord : Continuous (fun ω : ConfigSpace (Site d) => ω x) := continuous_apply x
  have hbool : Continuous (fun b : Bool => if b then (1 : ℝ) else -1) :=
    continuous_of_discreteTopology
  exact hbool.comp hcoord

lemma spinObs_le_one (x : Site d) (ω : ConfigSpace (Site d)) :
    ‖spin ω x‖ ≤ 1 := by
  rw [Real.norm_eq_abs]; exact abs_spin_le_one ω x

/-- The spin at `x` as a bounded continuous real function on the configuration space. -/
noncomputable def spinBCF (x : Site d) : ConfigSpace (Site d) →ᵇ ℝ :=
  ⟨⟨fun ω => spin ω x, continuous_spinObs x⟩,
    ⟨2, fun ω ω' => by
      have h1 := spinObs_le_one x ω
      have h2 := spinObs_le_one x ω'
      calc dist (spin ω x) (spin ω' x) ≤ ‖spin ω x‖ + ‖spin ω' x‖ := dist_le_norm_add_norm _ _
        _ ≤ 1 + 1 := by linarith
        _ = 2 := by ring⟩⟩

@[simp] lemma spinBCF_apply (x : Site d) (ω : ConfigSpace (Site d)) :
    spinBCF x ω = spin ω x := rfl

lemma integral_spinBCF_eq (d : ℕ) (β : ℝ) :
    ∫ ω, (spinBCF (origin d)) ω ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))
      = magnetization d β := by
  rfl

/-! ## B. Passing to the weak limit -/

lemma nonneg_integral_of_weakLimit
    {μ : ℕ → ProbabilityMeasure (ConfigSpace (Site d))}
    {ν : ProbabilityMeasure (ConfigSpace (Site d))}
    (h : WeakConvergesTo μ ν) (f : ConfigSpace (Site d) →ᵇ ℝ)
    (hpos : ∀ n, 0 ≤ ∫ ω, f ω ∂(μ n : Measure (ConfigSpace (Site d)))) :
    0 ≤ ∫ ω, f ω ∂(ν : Measure (ConfigSpace (Site d))) :=
  ge_of_tendsto (h.tendsto_integral f) (Filter.Eventually.of_forall hpos)

lemma magnetization_nonneg_of_fv (d : ℕ) (β : ℝ)
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

lemma hmag_nonneg_of_fv (d : ℕ)
    (hfv : ∀ β, ∀ n, 0 ≤ ∫ ω, spin ω (origin d)
      ∂(plusMeasure d n β 0 : Measure (ConfigSpace (Site d)))) :
    ∀ β, 0 ≤ magnetization d β :=
  fun β => magnetization_nonneg_of_fv d β (hfv β)

end Ising

end StatMech
