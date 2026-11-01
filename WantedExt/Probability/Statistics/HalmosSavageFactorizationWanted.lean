/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.Statistics.Sufficiency.Basic

/-!
# The Halmos–Savage factorization theorem, necessity half: wishlist

`MathlibExt.Probability.Statistics.Sufficiency.isSufficient_comap_of_factorization` proves
that a factorization `dP_θ/dμ = g_θ(T) · h` makes the statistic `T` sufficient. The converse
for a family dominated by a σ-finite measure is the necessity half of the Halmos–Savage
theorem. Its proof needs a countable mixture of the family that is equivalent to it
(Halmos and Savage 1949), which is not formalized here.
-/

namespace MathlibExt.Probability.Statistics.Sufficiency

@[expose] public section

open MeasureTheory
open scoped ENNReal

/-- **Halmos–Savage factorization, necessity.** If the family of probability measures `P` is
dominated by a σ-finite measure `μ` and the statistic `T` is sufficient for `P`, then the
densities factor as `dP_θ/dμ = g_θ(T) · h` with measurable `g_θ` and `h`, `h` free of `θ`.

Source: P. R. Halmos and L. J. Savage, *Application of the Radon–Nikodym theorem to the theory
of sufficient statistics*, Ann. Math. Statist. 20 (1949), 225–241. -/
public theorem_wanted exists_factorization_of_isSufficient_comap {Ω Θ τ : Type*}
    [MeasurableSpace τ] {m₀ : MeasurableSpace Ω} {T : Ω → τ} (hT : Measurable T)
    (μ : Measure[m₀] Ω) [SigmaFinite μ] (P : Θ → Measure[m₀] Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (hdom : ∀ θ, P θ ≪ μ)
    (hP : IsSufficient (MeasurableSpace.comap T ‹MeasurableSpace τ›) P) :
    ∃ (g : Θ → τ → ℝ≥0∞) (h : Ω → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧ Measurable h ∧
      ∀ θ, P θ = μ.withDensity (fun ω => g θ (T ω) * h ω)

end

end MathlibExt.Probability.Statistics.Sufficiency
