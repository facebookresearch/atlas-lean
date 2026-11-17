/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.RiemannZetaLogDerivZeros

/-!
# Tests for `ζ'/ζ` and the zeros of `ζ`

Conjugation symmetry, the functional equation of `ζ'/ζ` at `w = 2`, and the existence of good
heights.
-/

@[expose] public section

open ComplexConjugate

namespace RiemannZetaLogDerivZerosTest

example (s : ℂ) : deriv riemannZeta (conj s) = conj (deriv riemannZeta s) :=
  deriv_riemannZeta_conj s

/-- The functional equation of `ζ'/ζ` at `w = 2`, where `cos π = -1 ≠ 0`:
`-ζ'/ζ(-1) = -log 2π + ψ(2) - (π/2) tan π + ζ'/ζ(2)`. -/
example : -logDeriv riemannZeta (1 - 2) = -Complex.log (2 * Real.pi) + Complex.digamma 2
      - (Real.pi / 2) * (Complex.sin (Real.pi * 2 / 2) / Complex.cos (Real.pi * 2 / 2))
      + logDeriv riemannZeta 2 := by
  refine neg_logDeriv_riemannZeta_one_sub (by norm_num) ?_
  rw [show (Real.pi : ℂ) * 2 / 2 = Real.pi by ring, Complex.cos_pi]
  norm_num

/-- Good heights exist above every large `T`. -/
example : ∃ C T₀ : ℝ, ∀ T ≥ T₀, ∃ T' : ℝ, |T' - T| ≤ 1 ∧
    ∀ σ : ℝ, -1 ≤ σ → σ ≤ 2 →
      ‖deriv riemannZeta (σ + T' * Complex.I) / riemannZeta (σ + T' * Complex.I)‖ ≤
        C * Real.log T' ^ 2 := by
  obtain ⟨C, T₀, h⟩ := exists_good_height_norm_logDeriv_riemannZeta_le
  exact ⟨C, T₀, fun T hT => by
    obtain ⟨T', h1, -, h3⟩ := h T hT
    exact ⟨T', h1, h3⟩⟩

end RiemannZetaLogDerivZerosTest
