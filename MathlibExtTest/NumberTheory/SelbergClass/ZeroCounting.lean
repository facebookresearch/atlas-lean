/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SelbergClass.ZeroCounting
public import MathlibExtTest.NumberTheory.SelbergClass.Basic

/-!
# Tests for Selberg's zero-counting theorem

At `ζ` (degree `1`), `isEquivalent_zeroCount` is the Riemann–von Mangoldt asymptotic
`N(T) ∼ T log T / 2π`.
-/

open Complex ArithmeticFunction SelbergClass

@[expose] public section

namespace SelbergClassTest

example : Asymptotics.IsEquivalent Filter.atTop
    (fun T : ℝ => ((∑ᶠ ρ ∈ {ρ : ℂ | riemannZeta ρ = 0 ∧ 0 ≤ ρ.re ∧ 0 ≤ ρ.im ∧ ρ.im ≤ T},
      analyticOrderNatAt riemannZeta ρ : ℕ) : ℝ))
    (fun T : ℝ => T * Real.log T / (2 * Real.pi)) := by
  have := isEquivalent_zeroCount zetaC zeta_mem_selbergClass riemannZeta
    isLSeriesContinuation_zeta zetaFE
  simpa [zetaFE_degree] using this

end SelbergClassTest
