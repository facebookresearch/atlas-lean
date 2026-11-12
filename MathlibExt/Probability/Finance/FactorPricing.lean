/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.StatePriceVector
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring

/-!
# Linear factor pricing from exact factor spanning

Source: Atlas roadmap FI07.T04: a finite exact factor-spanning model with no
arbitrage yields the linear factor-price relation. `factor_price_relation` is
the pricing-algebra step: given a pricing
vector `ψ` that prices every asset, exact spanning yields the linear
factor-price relation (positivity of `ψ` is not needed for this step).
`factor_price_relation_of_no_arbitrage` is the unconditional claim: under no
arbitrage on funded gains, the pricing vector is supplied by FI08.T02 and the
same conclusion follows. The factors need not be traded assets: a factor price
is the `ψ`-value of the factor payoff.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.FactorPricing

set_option linter.unusedFintypeInType false in
/-- **Linear factor-price relation (FI07.T04).** In a finite exact
factor-spanning model, given a pricing vector `ψ` that prices every asset
(`p a = ∑ ω, ψ ω * X a ω`), every asset price is the loading-weighted sum of
factor prices: there are `π k` with `p a = ∑ k, b a k * π k` for every asset
`a`, where `π k = ∑ ω, ψ ω * F k ω`. FI08.T02 supplies such a `ψ` (strictly
positive) under no arbitrage on funded gains. -/
theorem factor_price_relation
    {Ω : Type*} [Fintype Ω]
    {A : Type*} [Fintype A]
    {K : Type*} [Fintype K]
    (X : A → Ω → ℝ) (p : A → ℝ) (ψ : Ω → ℝ)
    (hprice : ∀ a : A, p a = ∑ ω : Ω, ψ ω * X a ω)
    (F : K → Ω → ℝ) (b : A → K → ℝ)
    (hspan : ∀ a : A, ∀ ω : Ω, X a ω = ∑ k : K, b a k * F k ω) :
    ∃ π : K → ℝ, ∀ a : A, p a = ∑ k : K, b a k * π k := by
  refine ⟨fun k => ∑ ω : Ω, ψ ω * F k ω, fun a => ?_⟩
  calc p a = ∑ ω : Ω, ψ ω * X a ω := hprice a
    _ = ∑ ω : Ω, ψ ω * (∑ k : K, b a k * F k ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [hspan]
    _ = ∑ ω : Ω, ∑ k : K, ψ ω * (b a k * F k ω) := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [Finset.mul_sum]
    _ = ∑ k : K, ∑ ω : Ω, ψ ω * (b a k * F k ω) := Finset.sum_comm
    _ = ∑ k : K, b a k * (∑ ω : Ω, ψ ω * F k ω) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ω _
        ring

set_option linter.unusedFintypeInType false in
/-- **Linear factor-price relation under no arbitrage (FI07.T04, unconditional
claim).** In a finite exact factor-spanning model with no arbitrage on funded
gains, every asset price is the loading-weighted sum of factor prices, with
factor prices `π k = ∑ ω, ψ ω * F k ω` for the state-price vector `ψ`
supplied by FI08.T02. -/
theorem factor_price_relation_of_no_arbitrage
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A : Type*} [Fintype A]
    {K : Type*} [Fintype K]
    (X : A → Ω → ℝ) (p : A → ℝ) (R : ℝ) (hR : 0 < R)
    (hNA : MathlibExt.Probability.Finance.StatePriceVector.NoFundedArbitrage X p R)
    (F : K → Ω → ℝ) (b : A → K → ℝ)
    (hspan : ∀ a : A, ∀ ω : Ω, X a ω = ∑ k : K, b a k * F k ω) :
    ∃ π : K → ℝ, ∀ a : A, p a = ∑ k : K, b a k * π k := by
  classical
  obtain ⟨ψ, -, -, hpricing⟩ :=
    MathlibExt.Probability.Finance.StatePriceVector.exists_statePriceVector_prices_replicated
      X p R hR hNA
  have hsingle : ∀ g : A → ℝ, ∀ a : A,
      (∑ a' : A, (Pi.single a 1 : A → ℝ) a' * g a') = g a := by
    intro g a
    rw [Finset.sum_eq_single a]
    · simp [Pi.single_eq_same]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_mul]
    · intro hcon
      exact absurd (Finset.mem_univ a) hcon
  have hprice : ∀ a : A, p a = ∑ ω : Ω, ψ ω * X a ω := by
    intro a
    have h := hpricing (Pi.single a 1 : A → ℝ)
    simp only [hsingle] at h
    exact h.symm
  exact factor_price_relation X p ψ hprice F b hspan

end MathlibExt.Probability.Finance.FactorPricing
