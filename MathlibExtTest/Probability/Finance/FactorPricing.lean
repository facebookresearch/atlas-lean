/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.FactorPricing
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Tests for linear factor pricing

* Concrete test: one asset with loadings `![2, -1]` over two factors; its
  price is `2 * π 0 + (-1) * π 1`.
* Discharge test: the unconditional theorem on a concrete two-factor market
  with one asset, loadings `![2, -1]`, `R = 2`, payoffs `![5, 1]` and price
  `1`, proving no arbitrage before applying it.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.FactorPricing

open MathlibExt.Probability.Finance.FactorPricing
open MathlibExt.Probability.Finance.StatePriceVector

/-- Concrete test: one asset with loadings `![2, -1]` over two factors. -/
example {Ω : Type*} [Fintype Ω]
    (X : Unit → Ω → ℝ) (p : Unit → ℝ) (ψ : Ω → ℝ)
    (hprice : ∀ a : Unit, p a = ∑ ω : Ω, ψ ω * X a ω)
    (F : Fin 2 → Ω → ℝ)
    (hspan : ∀ ω : Ω, X () ω = ∑ k : Fin 2, ![2, -1] k * F k ω) :
    ∃ π : Fin 2 → ℝ, p () = 2 * π 0 + (-1) * π 1 := by
  obtain ⟨π, hπ⟩ := factor_price_relation X p ψ hprice F (fun _ => ![2, -1]) (by
    intro a ω
    cases a
    simpa using hspan ω)
  refine ⟨π, ?_⟩
  have h := hπ ()
  rw [Fin.sum_univ_two] at h
  simpa using h

/-- Discharge test: the unconditional factor-price relation on a concrete two-factor market.
Two-factor market with one asset: loadings `![2, -1]`, `R = 2`,
payoffs `X 0 = ![5, 1]`, price `p 0 = 1`. Funded gains are `3 * h 0`
and `-h 0`, so no-arbitrage holds by forcing `h 0 = 0`. -/
example : ∃ π : Fin 2 → ℝ, (1 : ℝ) = 2 * π 0 + (-1) * π 1 := by
  have hR : (0 : ℝ) < 2 := by norm_num
  have hspan : ∀ a : Fin 1, ∀ ω : Fin 2,
      (fun _ => ![5, 1] : Fin 1 → Fin 2 → ℝ) a ω
        = ∑ k : Fin 2, (fun _ => ![2, -1] : Fin 1 → Fin 2 → ℝ) a k
          * (![![3, 1], ![1, 1]] : Fin 2 → Fin 2 → ℝ) k ω := by
    intro a ω
    fin_cases a <;> fin_cases ω <;> simp [Fin.sum_univ_two] <;> norm_num
  have hNA : NoFundedArbitrage (fun _ => ![5, 1] : Fin 1 → Fin 2 → ℝ)
      (fun _ => (1 : ℝ) : Fin 1 → ℝ) 2 := by
    rintro ⟨h, hnonneg, ω, hpos⟩
    simp only [Fin.sum_univ_one] at hnonneg hpos
    have h0 := hnonneg 0
    have h1 := hnonneg 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 hpos
    fin_cases ω <;> norm_num at h0 h1 hpos ⊢ <;> linarith
  obtain ⟨π, hπ⟩ := factor_price_relation_of_no_arbitrage
    (fun _ => ![5, 1] : Fin 1 → Fin 2 → ℝ) (fun _ => (1 : ℝ) : Fin 1 → ℝ)
    2 hR hNA (![![3, 1], ![1, 1]] : Fin 2 → Fin 2 → ℝ)
    (fun _ => ![2, -1] : Fin 1 → Fin 2 → ℝ) hspan
  refine ⟨π, ?_⟩
  have h0 := hπ 0
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h0
  exact h0


end MathlibExtTest.Probability.Finance.FactorPricing
