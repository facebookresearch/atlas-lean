/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.MagNonneg
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.TildeBc

/-!
# The Simon–Lieb inequality in the infinite-volume plus state

The plus-state two-point function and the passage of the Simon–Lieb bound from finite-volume plus
measures to the infinite-volume plus state.

## i. Overview

`plusCorr d β x y = ⟨σ_xσ_y⟩^+_β` is the two-point function of the infinite-volume plus state at
zero field. The product `σ_xσ_y` is a bounded continuous function, so weak convergence of
finite-volume plus measures along a subsequence gives convergence of two-point functions. A
Simon–Lieb bound that holds eventually along every subsequence therefore passes to the limit.

## ii. Key results

- `plusCorr` : the plus-state two-point function
- `simonBoundaryPlus` : the right side of the Simon–Lieb bound in the plus state
- `plusCorr_simon_of_eventually_finite` : the limit passage

## iii. Table of contents

- A. Two-point functions as bounded continuous functions
- B. The limit passage

## iv. References

- B. Simon, "Correlation inequalities and the decay of correlations in ferromagnets", Comm. Math.
  Phys. 77 (1980) 111–126
- E. H. Lieb, "A refinement of Simon's correlation inequality", Comm. Math. Phys. 77 (1980) 127–135

-/

@[expose] public section

open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped BigOperators

namespace StatMech
namespace Sharpness

open Ising StatMech.Lattice Percolation

variable {d : ℕ}

/-! ## A. Two-point functions as bounded continuous functions -/

/-- The bounded continuous function `σ ↦ σ_x σ_y` on configuration space. -/
noncomputable def spinPairBCF (x y : Site d) :
    ConfigSpace (Site d) →ᵇ ℝ :=
  spinBCF x * spinBCF y

@[simp] lemma spinPairBCF_apply (x y : Site d)
    (ω : ConfigSpace (Site d)) :
    spinPairBCF x y ω = spin ω x * spin ω y := rfl

/-- The plus-state two-point function `⟨σ_xσ_y⟩^+_β` at zero field. -/
noncomputable def plusCorr (d : ℕ) (β : ℝ) (x y : Site d) : ℝ :=
  ∫ ω, spin ω x * spin ω y
    ∂(plusState d β 0 : Measure (ConfigSpace (Site d)))

lemma plusMeasure_pair_tendsto (β : ℝ) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0)
      (plusState d β 0)) (x y : Site d) :
    Tendsto
      (fun n ↦ ∫ ω, spin ω x * spin ω y
        ∂(plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds (plusCorr d β x y)) := by
  simpa only [spinPairBCF_apply, plusCorr] using
    hconv.tendsto_integral (spinPairBCF x y)

/-! ## B. The limit passage -/

/-- The Simon–Lieb boundary sum `∑_{(x,y) ∈ ∂S} tanh β ⟨σ_0σ_x⟩_S ∫ σ_yσ_z dμ` for a measure `μ`. -/
noncomputable def simonBoundaryIntegral
    (β : ℝ) (S : Finset (Site d)) (_o z : Site d)
    (μ : Measure (ConfigSpace (Site d))) : ℝ :=
  ∑ e ∈ boundaryEdges d S,
    Real.tanh β * corrOriginInner d β S e.1 *
      (∫ ω, spin ω e.2 * spin ω z ∂μ)

/-- The Simon–Lieb boundary sum `∑_{(x,y) ∈ ∂S} tanh β ⟨σ_0σ_x⟩_S ⟨σ_yσ_z⟩^+_β` in the plus state.
-/
noncomputable def simonBoundaryPlus
    (β : ℝ) (S : Finset (Site d)) (_o z : Site d) : ℝ :=
  ∑ e ∈ boundaryEdges d S,
    Real.tanh β * corrOriginInner d β S e.1 * plusCorr d β e.2 z

lemma simonBoundaryIntegral_tendsto (β : ℝ) (φ : ℕ → ℕ)
    (hconv : WeakConvergesTo (fun n ↦ plusMeasure d (φ n) β 0)
      (plusState d β 0)) (S : Finset (Site d)) (o z : Site d) :
    Tendsto
      (fun n ↦ simonBoundaryIntegral β S o z
        (plusMeasure d (φ n) β 0 : Measure (ConfigSpace (Site d))))
      atTop (nhds (simonBoundaryPlus β S o z)) := by
  unfold simonBoundaryIntegral simonBoundaryPlus
  apply tendsto_finsetSum
  intro e he
  apply Tendsto.const_mul
  exact plusMeasure_pair_tendsto β φ hconv e.2 z

lemma plusCorr_simon_of_eventually_finite
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
