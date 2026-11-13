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
# Law of one price

Source: Atlas roadmap FI08.T04: equal attainable payoffs have equal prices
under no arbitrage. `law_of_one_price` is the pricing-algebra step: given a pricing
vector `ψ` that prices every asset, equal attainable payoffs have equal prices
(positivity of `ψ` is not needed for this step). `law_of_one_price_of_no_arbitrage`
is the unconditional claim: under no arbitrage on funded gains, the pricing
vector is supplied by FI08.T02 and the same conclusion follows.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.LawOfOnePrice

/-- **Law of one price (FI08.T04).** Given a pricing vector `ψ` that prices
every asset (`p a = ∑ ω, ψ ω * X a ω`), two portfolios with the same attainable
payoff in every state have the same price: if
`∑ a, h a * X a ω = ∑ a, h' a * X a ω` for every `ω`, then
`∑ a, h a * p a = ∑ a, h' a * p a`. FI08.T02 supplies such a `ψ` (strictly
positive) under no arbitrage on funded gains. -/
theorem law_of_one_price
    {Ω : Type*} [Fintype Ω]
    {A : Type*} [Fintype A]
    (X : A → Ω → ℝ) (p : A → ℝ) (ψ : Ω → ℝ)
    (hprice : ∀ a : A, p a = ∑ ω : Ω, ψ ω * X a ω)
    {h h' : A → ℝ}
    (hpay : ∀ ω : Ω, ∑ a : A, h a * X a ω = ∑ a : A, h' a * X a ω) :
    ∑ a : A, h a * p a = ∑ a : A, h' a * p a := by
  have key : ∀ k : A → ℝ, ∑ a : A, k a * p a
      = ∑ ω : Ω, ψ ω * (∑ a : A, k a * X a ω) := by
    intro k
    calc ∑ a : A, k a * p a
        = ∑ a : A, ∑ ω : Ω, k a * (ψ ω * X a ω) := by
          apply Finset.sum_congr rfl
          intro a _
          rw [hprice a, Finset.mul_sum]
      _ = ∑ a : A, ∑ ω : Ω, ψ ω * (k a * X a ω) := by
          apply Finset.sum_congr rfl
          intro a _
          apply Finset.sum_congr rfl
          intro ω _
          show k a * (ψ ω * X a ω) = ψ ω * (k a * X a ω)
          ring
      _ = ∑ ω : Ω, ∑ a : A, ψ ω * (k a * X a ω) := Finset.sum_comm
      _ = ∑ ω : Ω, ψ ω * (∑ a : A, k a * X a ω) := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [Finset.mul_sum]
  rw [key h, key h']
  apply Finset.sum_congr rfl
  intro ω _
  rw [hpay ω]

/-- **Law of one price under no arbitrage (FI08.T04, unconditional claim).**
Under no arbitrage on funded gains, two portfolios with the same attainable
payoff in every state have the same price. The pricing vector is the state-price
vector supplied by FI08.T02. -/
theorem law_of_one_price_of_no_arbitrage
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {A : Type*} [Fintype A]
    (X : A → Ω → ℝ) (p : A → ℝ) (R : ℝ) (hR : 0 < R)
    (hNA : MathlibExt.Probability.Finance.StatePriceVector.NoFundedArbitrage X p R)
    {h h' : A → ℝ}
    (hpay : ∀ ω : Ω, ∑ a : A, h a * X a ω = ∑ a : A, h' a * X a ω) :
    ∑ a : A, h a * p a = ∑ a : A, h' a * p a := by
  classical
  obtain ⟨ψ, _, _, hpricing⟩ :=
    MathlibExt.Probability.Finance.StatePriceVector.exists_statePriceVector_prices_replicated
      X p R hR hNA
  have hprice : ∀ a : A, p a = ∑ ω : Ω, ψ ω * X a ω := by
    intro a
    have hspec := hpricing (Pi.single (M := fun _ => ℝ) a 1)
    have hRHS : ∑ a' : A, Pi.single (M := fun _ => ℝ) a 1 a' * p a' = p a := by
      have h0 : ∀ b ∈ (Finset.univ : Finset A), b ≠ a →
          Pi.single (M := fun _ => ℝ) a 1 b * p b = 0 := by
        intro b _ hb
        rw [Pi.single_eq_of_ne (M := fun _ => ℝ) hb 1, zero_mul]
      have h1 : a ∉ (Finset.univ : Finset A) →
          Pi.single (M := fun _ => ℝ) a 1 a * p a = 0 :=
        fun h => absurd (Finset.mem_univ a) h
      have hsum := Finset.sum_eq_single (a := a) (s := Finset.univ) h0 h1
      simp only [Pi.single_eq_same, one_mul] at hsum
      exact hsum
    have hinner : ∀ ω : Ω, ∑ a' : A, Pi.single (M := fun _ => ℝ) a 1 a' * X a' ω = X a ω := by
      intro ω
      have h0 : ∀ b ∈ (Finset.univ : Finset A), b ≠ a →
          Pi.single (M := fun _ => ℝ) a 1 b * X b ω = 0 := by
        intro b _ hb
        rw [Pi.single_eq_of_ne (M := fun _ => ℝ) hb 1, zero_mul]
      have h1 : a ∉ (Finset.univ : Finset A) →
          Pi.single (M := fun _ => ℝ) a 1 a * X a ω = 0 :=
        fun h => absurd (Finset.mem_univ a) h
      have hsum := Finset.sum_eq_single (a := a) (s := Finset.univ) h0 h1
      simp only [Pi.single_eq_same, one_mul] at hsum
      exact hsum
    calc p a = ∑ a' : A, Pi.single (M := fun _ => ℝ) a 1 a' * p a' := hRHS.symm
      _ = ∑ ω : Ω, ψ ω * (∑ a' : A, Pi.single (M := fun _ => ℝ) a 1 a' * X a' ω) :=
          hspec.symm
      _ = ∑ ω : Ω, ψ ω * X a ω := by
          apply Finset.sum_congr rfl
          intro ω _
          rw [hinner ω]
  exact law_of_one_price X p ψ hprice hpay

end MathlibExt.Probability.Finance.LawOfOnePrice
