/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Paninski: consistency of the spike-triggered average for elliptical stimuli

In a linear–nonlinear (LN) model a neuron responds to a stimulus `x ∈ ℝⁿ` with mean spike count
`g(k · x)` for a filter `k` and a nonnegative nonlinearity `g`. The spike-triggered average of
`N` stimulus–response pairs is `STA_N = (∑ y_i)⁻¹ ∑ y_i x_i`. Paninski (2003) showed that when the
stimulus distribution is elliptically symmetric with covariance `Σ`, the rescaled estimator
`Σ⁻¹ STA_N` is consistent for the filter direction: `STA_N` converges almost surely to
`κ Σ k` with `κ = E[g(k · x) (k · x)] / (E[g(k · x)] · kᵀ Σ k)`; for non-elliptical stimulus
distributions this can fail.

A law on `ℝⁿ` is elliptically symmetric when it is the image of a law invariant under every
orthogonal matrix by an invertible linear map. Stimulus–response pairs are identically
distributed and pairwise independent (Etemadi's form of the strong law, as in
`ProbabilityTheory.strong_law_ae`). The asymptotic normality and explicit rates are not
recorded here, because the statement used for this module does not fix them.

Sources: L. Paninski, "Convergence properties of three spike-triggered analysis techniques",
Network: Comput. Neural Syst. 14 (2003) 437–464.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.StrongLaw
public import Mathlib.LinearAlgebra.UnitaryGroup

@[expose] public section

namespace WantedExt.Biology.Neuroscience.SpikeTriggeredAverageWanted

open MeasureTheory ProbabilityTheory Matrix Filter Topology Finset Function

variable {n : ℕ}

/-- A law `ν` on `ℝⁿ` is **spherically symmetric** if `O x` has law `ν` for every orthogonal
matrix `O`. -/
def IsSpherical (ν : Measure (Fin n → ℝ)) : Prop :=
  ∀ O ∈ Matrix.orthogonalGroup (Fin n) ℝ, ν.map (fun x => O *ᵥ x) = ν

/-- A law `ν` on `ℝⁿ` is **elliptically symmetric** if `ν` is the image of a spherically
symmetric law under an invertible matrix `A`. -/
def IsElliptical (ν : Measure (Fin n → ℝ)) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) ℝ, IsUnit A.det ∧ ∃ ρ : Measure (Fin n → ℝ), IsSpherical ρ ∧
    ν = ρ.map (fun z => A *ᵥ z)

/-- The second-moment (covariance) matrix `Σ_ij = ∫ x_i x_j dν` of a law `ν` on `ℝⁿ`. -/
noncomputable def covMatrix (ν : Measure (Fin n → ℝ)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => ∫ x, x i * x j ∂ν

/-- The spike-triggered average `(∑_{i<N} y_i)⁻¹ ∑_{i<N} y_i x_i` of the first `N` pairs. -/
noncomputable def spikeTriggeredAverage {Ω : Type*} (Z : ℕ → Ω → (Fin n → ℝ) × ℝ) (N : ℕ)
    (ω : Ω) : Fin n → ℝ :=
  (∑ i ∈ range N, (Z i ω).2)⁻¹ • ∑ i ∈ range N, (Z i ω).2 • (Z i ω).1

/-- **Consistency of the spike-triggered average** (Paninski 2003). Let `P` be a probability
measure and `Z i = (x_i, y_i)` stimulus–response pairs that are pairwise independent and
identically distributed. Assume the stimulus law `ν` of `x_0` is elliptically symmetric with
finite second moments, `y_0 ≥ 0`, `y_0` and `y_0 ‖x_0‖` are integrable, and the LN model holds:
`E[y_0 φ(x_0)] = E[g(k · x_0) φ(x_0)]` for every bounded measurable `φ`, for a measurable
`g ≥ 0` with `g(k · x_0)` and `g(k · x_0) (k · x_0)` integrable, `E[g(k · x_0)] > 0`,
`kᵀ Σ k > 0`, and nonzero gain `E[g(k · x_0) (k · x_0)] ≠ 0`. Then almost surely
`STA_N → κ Σ k` with nonzero scalar
`κ = E[g(k · x_0) (k · x_0)] / (E[g(k · x_0)] · kᵀ Σ k) ≠ 0`, so `Σ⁻¹ STA_N` converges to the
nonzero multiple `κ k` of the filter `k`.

Source: Paninski (2003). -/
public theorem_wanted tendsto_spikeTriggeredAverage {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : ℕ → Ω → (Fin n → ℝ) × ℝ)
    (hmeas : ∀ i, Measurable (Z i)) (hindep : Pairwise ((· ⟂ᵢ[P] ·) on Z))
    (hident : ∀ i, IdentDistrib (Z i) (Z 0) P P)
    (hell : IsElliptical (P.map fun ω => (Z 0 ω).1))
    (hsq : ∀ i j, Integrable (fun ω => (Z 0 ω).1 i * (Z 0 ω).1 j) P)
    (hy : ∀ ω, 0 ≤ (Z 0 ω).2) (hyint : Integrable (fun ω => (Z 0 ω).2) P)
    (hyx : Integrable (fun ω => (Z 0 ω).2 * ‖(Z 0 ω).1‖) P)
    (k : Fin n → ℝ) (g : ℝ → ℝ) (hg : Measurable g) (hg0 : ∀ s, 0 ≤ g s)
    (hgint : Integrable (fun ω => g (k ⬝ᵥ (Z 0 ω).1)) P)
    (hgs : Integrable (fun ω => g (k ⬝ᵥ (Z 0 ω).1) * (k ⬝ᵥ (Z 0 ω).1)) P)
    (hLN : ∀ φ : (Fin n → ℝ) → ℝ, Measurable φ → (∃ M, ∀ x, |φ x| ≤ M) →
      ∫ ω, (Z 0 ω).2 * φ (Z 0 ω).1 ∂P = ∫ ω, g (k ⬝ᵥ (Z 0 ω).1) * φ (Z 0 ω).1 ∂P)
    (hgpos : 0 < ∫ ω, g (k ⬝ᵥ (Z 0 ω).1) ∂P)
    (hkSk : 0 < k ⬝ᵥ covMatrix (P.map fun ω => (Z 0 ω).1) *ᵥ k)
    (hgain : ∫ ω, g (k ⬝ᵥ (Z 0 ω).1) * (k ⬝ᵥ (Z 0 ω).1) ∂P ≠ 0) :
    ∀ᵐ ω ∂P, Tendsto (fun N => spikeTriggeredAverage Z N ω) atTop
      (𝓝 (((∫ ω', g (k ⬝ᵥ (Z 0 ω').1) * (k ⬝ᵥ (Z 0 ω').1) ∂P) /
          ((∫ ω', g (k ⬝ᵥ (Z 0 ω').1) ∂P) *
            (k ⬝ᵥ covMatrix (P.map fun ω' => (Z 0 ω').1) *ᵥ k))) •
        (covMatrix (P.map fun ω' => (Z 0 ω').1) *ᵥ k)))

/-- **Consistency can fail without elliptical symmetry** (Paninski 2003). There are a probability
law `ν` on `ℝ²` that is centered (`∫ x_i dν = 0` for each `i`), has finite second moments and is
not elliptically symmetric, a filter `k` with positive variance `kᵀ Σ k > 0`, and a measurable
nonlinearity `g ≥ 0` with `g(k · x)` and `g(k · x) x` integrable and `∫ g(k · x) dν > 0`, such
that the population spike-triggered average `(∫ g(k · x) dν)⁻¹ ∫ g(k · x) x dν` (the almost sure
limit of `STA_N` under the strong law) is not a multiple of `Σ k`.

Source: Paninski (2003). -/
public theorem_wanted exists_spikeTriggeredAverage_not_parallel :
    ∃ ν : Measure (Fin 2 → ℝ), IsProbabilityMeasure ν ∧
      (∀ i, Integrable (fun x => x i) ν ∧ ∫ x, x i ∂ν = 0) ∧
      (∀ i j, Integrable (fun x => x i * x j) ν) ∧ ¬ IsElliptical ν ∧
      ∃ k : Fin 2 → ℝ, 0 < k ⬝ᵥ covMatrix ν *ᵥ k ∧ ∃ g : ℝ → ℝ, Measurable g ∧ (∀ s, 0 ≤ g s) ∧
        Integrable (fun x => g (k ⬝ᵥ x)) ν ∧ Integrable (fun x => g (k ⬝ᵥ x) • x) ν ∧
        0 < ∫ x, g (k ⬝ᵥ x) ∂ν ∧
        ¬ ∃ κ : ℝ, (∫ x, g (k ⬝ᵥ x) ∂ν)⁻¹ • ∫ x, g (k ⬝ᵥ x) • x ∂ν = κ • (covMatrix ν *ᵥ k)

end WantedExt.Biology.Neuroscience.SpikeTriggeredAverageWanted
