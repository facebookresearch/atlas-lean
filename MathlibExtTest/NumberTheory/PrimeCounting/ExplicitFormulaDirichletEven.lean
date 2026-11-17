/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaDirichletEven

/-!
# Tests for the explicit formula for `ψ(x, χ)`, `χ` even

Instantiation at an actual enumeration of the zeros of `ξ(s, χ)` and at `x = 5/2` (not a prime
power).
-/

@[expose] public section

open DirichletCharacter Filter Topology

namespace ExplicitFormulaDirichletEvenTest

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (he : χ.Even) : ∃ (ι : Type) (z : ι → ℂ),
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then ((5 / 2 : ℝ) : ℂ) ^ z n / z n else 0))
      atTop (𝓝 (-χ.chebyshevPsi (5 / 2) - (Real.log (5 / 2) : ℂ) - χ.logDerivConstAtZero -
        ((1 / 2 * Real.log (1 - (5 / 2 : ℝ) ^ (-2 : ℤ)) : ℝ) : ℂ))) := by
  have hz := Complex.card_sigma_fin_analyticOrderAt (differentiable_xi hχ1)
    (xi_zero_ne_zero hχ hχ1)
  refine ⟨_, _, tendsto_tsum_cpow_div_zeros_explicit_formula_of_even hχ hχ1 he _ hz
    (by norm_num) fun n hn => ?_⟩
  have : (2 * n : ℝ) = 5 := by rw [hn]; norm_num
  have h : 2 * n = 5 := by exact_mod_cast this
  omega

end ExplicitFormulaDirichletEvenTest
