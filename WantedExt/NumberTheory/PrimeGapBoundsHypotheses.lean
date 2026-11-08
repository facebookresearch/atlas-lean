/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.PrimeDistribution
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Polymath8b's concrete dyadic distribution assumptions

This is the retained arXiv:1407.4897v4 formulation. The separately published 2015
erratum correction text is unavailable, so its applicability is unresolved.
These predicates are source assumptions for private proof requests, not assumed
theorems. No equivalence to the distinct cumulative C66 predicate is asserted.
All non-fixed source quantities vary with the real parameter `x`; constants,
exponents and thresholds in eventual estimates are independent of `x`.
-/

@[expose] public section

namespace WantedExt.NumberTheory.Polymath8b

open Filter MathlibExt.NumberTheory.PrimeDistribution

/-- Domination with every fixed positive subpower loss.
Source: Polymath8b, arXiv:1407.4897v4, Definition 1.6. -/
def SubpowerBound (f g : ℝ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → Asymptotics.IsBigO atTop f (fun x ↦ x ^ δ * g x)

/-- Support in the source dyadic interval, with no extra zero coefficient.
Source: Polymath8b v4, Claim 2.6. -/
def DyadicSupport (α : ℕ →₀ ℝ) (N : ℝ) : Prop :=
  ∀ n ∈ α.support, 1 ≤ n ∧ N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N

/-- The pointwise divisor/logarithm estimate has constants fixed in both `x` and `n`.
Source: Polymath8b v4, Claim 2.6, TeX label `ab-div`. -/
def DivisorLogBound (α : ℝ → ℕ →₀ ℝ) : Prop :=
  ∃ C : ℝ, ∃ k l : ℕ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ n : ℕ, 1 ≤ n → |α x n| ≤
      C * (n.divisors.card : ℝ) ^ k * Real.log x ^ l

/-- A uniform Siegel-Walfisz bound after the actual coprimality mask.
Source: Polymath8b v4, Claim 2.6, TeX label `sig` and its uniformity footnote. -/
def SiegelWalfisz (β : ℝ → ℕ →₀ ℝ) (M : ℝ → ℝ) : Prop :=
  ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, ∃ k : ℕ, 0 < C ∧
    ∀ᶠ x : ℝ in atTop, ∀ q r a : ℕ, (h1q : 1 ≤ q) → 1 ≤ r → Nat.Coprime a q →
      |discrepancy ((β x).filter (fun n ↦ Nat.Coprime n r)) ⟨q, h1q⟩ a| ≤
        C * ((q * r).divisors.card : ℝ) ^ k * M x / Real.log x ^ A

/-- Dyadic von Mangoldt discrepancy at a fixed distribution level.
Source: Polymath8b v4, Claim 2.2. -/
def ElliottHalberstamAt (θ : ℝ) : Prop :=
  ∀ Q : ℝ → ℕ, SubpowerBound (fun x ↦ (Q x : ℝ)) (fun x ↦ x ^ θ) →
    ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
      averagedDiscrepancy (dyadicVonMangoldt x) (Q x) ≤ C * x / Real.log x ^ A

/-- The generalized distribution estimate for real finite sequence families.
Source: Polymath8b v4, Claim 2.6, TeX labels `ab-div`, `sig`, and `qq-gen`. -/
def GeneralizedElliottHalberstamAt (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N M : ℝ → ℝ, ∀ α β : ℝ → ℕ →₀ ℝ,
    (∀ᶠ x : ℝ in atTop, 0 < N x ∧ 0 < M x ∧
      DyadicSupport (α x) (N x) ∧ DyadicSupport (β x) (M x)) →
    SubpowerBound (fun x ↦ x ^ ε) N →
    SubpowerBound N (fun x ↦ x ^ (1 - ε)) →
    SubpowerBound (fun x ↦ x ^ ε) M →
    SubpowerBound M (fun x ↦ x ^ (1 - ε)) →
    Asymptotics.IsTheta atTop (fun x ↦ N x * M x) (fun x ↦ x) →
    DivisorLogBound α → DivisorLogBound β → SiegelWalfisz β M →
    ∀ Q : ℝ → ℕ, SubpowerBound (fun x ↦ (Q x : ℝ)) (fun x ↦ x ^ θ) →
      ∀ A : ℝ, 1 ≤ A → ∃ C : ℝ, 0 < C ∧ ∀ᶠ x : ℝ in atTop,
        averagedDiscrepancy (convolution (α x) (β x)) (Q x) ≤ C * x / Real.log x ^ A

/-- The complete dyadic EH assumption below its excluded endpoint one.
Source: Polymath8b v4, Theorems 1.1 and 1.3 and Claim 2.2. -/
def ElliottHalberstam : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → ElliottHalberstamAt θ

/-- The complete dyadic GEH assumption below its excluded endpoint one.
Source: Polymath8b v4, Theorem 1.4 and Claim 2.6. -/
def GeneralizedElliottHalberstam : Prop :=
  ∀ θ : ℝ, 0 < θ → θ < 1 → GeneralizedElliottHalberstamAt θ

end WantedExt.NumberTheory.Polymath8b
