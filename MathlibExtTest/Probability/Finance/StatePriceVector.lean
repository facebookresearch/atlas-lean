/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Finance.StatePriceVector
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Tactic.NormNum
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith

/-!
# Tests for state-price vectors

* A two-state, one-asset market with `R = 2`, `X = ![4, 0]`, `p = 1`
  (funded gains `[2, -2]`): no funded arbitrage, and the state-price vector
  from `exists_statePriceVector_prices_replicated` is strictly positive,
  sums to `1 / 2`, and prices the holding-`3` payoff at `3`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Finance.StatePriceVector

open MathlibExt.Probability.Finance.StatePriceVector

/-- Test market payoff: one asset paying `4` in state `0` and `0` in state `1`. -/
def Xtest : Fin 1 → Fin 2 → ℝ := fun _ => (![4, 0] : Fin 2 → ℝ)

/-- Test market price: `1`. -/
def ptest : Fin 1 → ℝ := fun _ => 1

/-- Test gross risk-free return: `2`. -/
def Rtest : ℝ := 2

/-- No funded arbitrage by the forcing argument: nonnegative funded gains in both
states force the holding to `0`, contradicting a strictly positive gain. -/
theorem noArbTest : NoFundedArbitrage Xtest ptest Rtest := by
  rintro ⟨h, hnonneg, ω, hpos⟩
  have h0 := hnonneg 0
  have h1 := hnonneg 1
  simp only [Fin.sum_univ_one, Xtest, ptest, Rtest, Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1 hpos
  norm_num at h0 h1
  have hz : h 0 = 0 := by linarith
  rw [hz, zero_mul] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- The theorem applies to the test market: some `ψ` is strictly positive, sums
to `1 / 2`, and prices the holding-`3` payoff at `3`. -/
theorem test_statePriceVector :
    ∃ ψ : Fin 2 → ℝ, (∀ ω, 0 < ψ ω) ∧ (∑ ω, ψ ω = 1 / 2) ∧
      (∑ ω : Fin 2, ψ ω * (∑ a : Fin 1, (3 : ℝ) * Xtest a ω)) = 3 := by
  obtain ⟨ψ, hψpos, hψsum, hψprice⟩ :=
    exists_statePriceVector_prices_replicated Xtest ptest Rtest (by norm_num [Rtest]) noArbTest
  refine ⟨ψ, hψpos, ?_, ?_⟩
  · simpa [Rtest] using hψsum
  · have h3 := hψprice (fun _ => (3 : ℝ))
    have hrhs : (∑ a : Fin 1, (fun _ => (3 : ℝ)) a * ptest a) = 3 := by
      simp [ptest]
    rw [hrhs] at h3
    exact h3

end MathlibExtTest.Probability.Finance.StatePriceVector
