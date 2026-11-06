/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.ZeroSum
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for the sum over zeros `∑ n^ρ` (Landau's formula)

The hypothesis `hΛ` is met by `ζ` with the von Mangoldt function.
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

theorem LSeriesHasSum_vonMangoldt {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n => (Λ n : ℂ)) s (-deriv riemannZeta s / riemannZeta s) := by
  rw [← LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  exact (LSeriesSummable_vonMangoldt hs).LSeriesHasSum

example : ∃ C : ℝ, ∀ n : ℕ, 1 < n → ∀ T : ℝ, 2 ≤ T →
    ‖(∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ |ρ.im| ≤ T},
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (n : ℂ) ^ ρ) + T / Real.pi * (Λ n : ℂ)‖ ≤
      C * (n : ℝ) ^ (3 / 2 : ℝ) * Real.log T ^ 2 :=
  exists_norm_finsum_zeros_cpow_add_le zetaC zeta_mem_selbergClass riemannZeta
    isLSeriesContinuation_zeta _ fun _ hs => LSeriesHasSum_vonMangoldt hs

end SelbergClassTest
