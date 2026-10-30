/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Ported from fairinternal/formal-math at `bc0a5a31aa07d127ead55e6848aa133300c4ce0a`.
Original formalization by Manasa Hariharan (@manasahari-meta); ported with permission.
-/

module

public import Mathlib.Probability.Density
public import Mathlib.Order.Filter.Extr
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.CompleteLattice.Basic

/-!
# Iid likelihood, MLE maps, and induced likelihood (Casella–Berger §7.2.2)

Summary: genuine normalized iid density/mass model with finite-product
likelihood; complete all-sample MLE map predicate; whole-fiber supremum
induced likelihood on the image of a parameter transformation.

Source locators only: normalized `text.txt` 11226–11237 (iid product and
complete MLE map) and 11335–11359 (induced fiber supremum, equation 7.2.5);
raw OCR inspected directly by Muse. No source text is reproduced here.

Representation: an `AEMeasurable` `ℝ≥0∞` density family normalized by
`∫⁻ = 1` under a common dominating measure, with laws defined by
`withDensity`. No pointwise finiteness is assumed. Counting measure gives
the discrete case; volume gives the continuous case.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

open scoped BigOperators ENNReal

/-- Genuine dominated population family: `AEMeasurable` densities normalized
to one under a common dominating measure. Both counting measure (pmf) and
volume (pdf) are permitted. No pointwise finiteness is imposed. -/
structure NormalizedDensityFamily (Ω : Type*) (Θ : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  dens : Θ → Ω → ℝ≥0∞
  measurable : ∀ θ, AEMeasurable (dens θ) μ
  normalized : ∀ θ, ∫⁻ x, dens θ x ∂μ = 1

namespace NormalizedDensityFamily

variable {Ω Θ : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Two families with pointwise equal density data are equal. Only `dens` is
compared; measurability and normalization fields are propositions. -/
@[ext]
theorem ext {F G : NormalizedDensityFamily Ω Θ μ}
    (h : ∀ θ x, F.dens θ x = G.dens θ x) : F = G := by
  obtain ⟨densF, _, _⟩ := F
  obtain ⟨densG, _, _⟩ := G
  have hdens : densF = densG := funext fun θ => funext fun x => h θ x
  subst hdens
  rfl

/-- Population law defined by `withDensity`. -/
noncomputable def law (F : NormalizedDensityFamily Ω Θ μ) (θ : Θ) :
    Measure Ω :=
  μ.withDensity (F.dens θ)

/-- Probability normalization derived from the density integral. -/
theorem isProbabilityMeasure_law (F : NormalizedDensityFamily Ω Θ μ)
    (θ : Θ) : IsProbabilityMeasure (F.law θ) := by
  constructor
  rw [law, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    F.normalized θ]

/-- Iid sample likelihood: the actual finite product of population densities.
For `n = 0` this is the empty product `1`. -/
noncomputable def iidLikelihood (F : NormalizedDensityFamily Ω Θ μ) (n : ℕ)
    (θ : Θ) (x : Fin n → Ω) : ℝ≥0∞ :=
  ∏ i, F.dens θ (x i)

@[simp]
theorem iidLikelihood_apply (F : NormalizedDensityFamily Ω Θ μ) (n : ℕ)
    (θ : Θ) (x : Fin n → Ω) :
    F.iidLikelihood n θ x = ∏ i, F.dens θ (x i) :=
  rfl

/-- Empty sample gives the empty product `1`. -/
@[simp]
theorem iidLikelihood_nil (F : NormalizedDensityFamily Ω Θ μ) (θ : Θ)
    (x : Fin 0 → Ω) : F.iidLikelihood 0 θ x = 1 := by
  simp [iidLikelihood]

/-- Complete all-sample MLE map: one fixed map attaining the global likelihood
maximum at every sample. The pointwise order predicate is native `IsMaxOn`. -/
def IsMaximumLikelihoodEstimator (F : NormalizedDensityFamily Ω Θ μ) (n : ℕ)
    (θhat : (Fin n → Ω) → Θ) : Prop :=
  ∀ x, IsMaxOn (fun θ => F.iidLikelihood n θ x) Set.univ (θhat x)

/-- Unfolded form: every sample, every parameter is below the estimate. -/
theorem isMaximumLikelihoodEstimator_iff (F : NormalizedDensityFamily Ω Θ μ)
    (n : ℕ) (θhat : (Fin n → Ω) → Θ) :
    F.IsMaximumLikelihoodEstimator n θhat ↔
      ∀ x θ, F.iidLikelihood n θ x ≤ F.iidLikelihood n (θhat x) x := by
  constructor
  · intro h x θ
    exact (isMaxOn_univ_iff.mp (h x)) θ
  · intro h x
    exact isMaxOn_univ_iff.mpr (h x)

/-- Induced likelihood under a parameter transformation: whole-fiber supremum
on the image of `τ`. The argument `η` ranges over `Set.range τ`, so each
fiber is inhabited. No inverse selection is assumed. -/
noncomputable def inducedLikelihood (F : NormalizedDensityFamily Ω Θ μ)
    (n : ℕ) {H : Type*} (τ : Θ → H) (x : Fin n → Ω)
    (η : Set.range τ) : ℝ≥0∞ :=
  ⨆ θ : { θ : Θ // τ θ = η.val }, F.iidLikelihood n θ.val x

end NormalizedDensityFamily

end ProbabilityTheory
