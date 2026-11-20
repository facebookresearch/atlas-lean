/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Azuma's inequality

A martingale `Z₀, …, Zₙ` whose increments are bounded, `|Zᵢ - Zᵢ₋₁| ≤ cᵢ`, satisfies the
Gaussian tail bound `P(Zₙ - Z₀ ≥ a) ≤ exp(-a² / (2 ∑ cᵢ²))`. Applied to exposure martingales
of random graphs it gives concentration of the chromatic number and of other graph parameters
that change by a bounded amount when one edge or one vertex is revealed; it is the starting
point of the martingale inequalities used in semi-random constructions. Mathlib has the
sub-Gaussian form (`ProbabilityTheory.measure_sum_ge_le_of_hasCondSubgaussianMGF`) but not the
conditional Hoeffding lemma that turns bounded increments into conditionally sub-Gaussian ones.

Reference: Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 lecture notes,
Spring 2019, Theorem 8.6 (https://yufeizhao.com/pm/sp19/pmnotes.pdf); K. Azuma (1967).
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Probability.AzumaInequalityWanted

/-- **Azuma's inequality.** Let `Z₀, Z₁, …` be a martingale with respect to a filtration on a
probability space, let `n` be a natural number and suppose `|Zᵢ - Zᵢ₋₁| ≤ cᵢ` everywhere for
`1 ≤ i ≤ n`. Then for every `a > 0`,
`P(Zₙ - Z₀ ≥ a) ≤ exp(-a² / (2 ∑_{i=1}^{n} cᵢ²))`
(Y. Zhao, *The Probabilistic Method in Combinatorics*, MIT 18.218 notes, 2019, Theorem 8.6,
general form; the case `cᵢ = 1`, `a = λ√n` gives `P(Zₙ - Z₀ ≥ λ√n) ≤ e^{-λ²/2}`). -/
theorem_wanted azuma_inequality {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : Martingale Z ℱ μ) (n : ℕ) (c : ℕ → ℝ)
    (hc : ∀ i ∈ Finset.Icc 1 n, ∀ ω, |Z i ω - Z (i - 1) ω| ≤ c i) {a : ℝ} (ha : 0 < a) :
    μ.real {ω | a ≤ Z n ω - Z 0 ω} ≤
      Real.exp (-a ^ 2 / (2 * ∑ i ∈ Finset.Icc 1 n, c i ^ 2))

end MathlibExt.Probability.AzumaInequalityWanted
