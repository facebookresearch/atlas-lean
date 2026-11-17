/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaDirichletOdd

/-!
# Tests for the explicit formula for `ψ(x, χ)`, `χ` odd

Instantiation at an actual enumeration of the zeros of `ξ(s, χ)` and at `x = 5/2`. An odd
character is automatically nonprincipal, so the enumeration exists.
-/

@[expose] public section

open DirichletCharacter Filter Topology

namespace ExplicitFormulaDirichletOddTest

/-- An odd character is not the trivial character (`χ(-1) = -1 ≠ 1`). -/
private theorem ne_one_of_odd {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (ho : χ.Odd) :
    χ ≠ 1 := by
  rintro rfl
  have h : (1 : DirichletCharacter ℂ q) (-1) = -1 := ho
  rw [MulChar.one_apply isUnit_one.neg] at h
  norm_num at h

example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (ho : χ.Odd) :
    ∃ (ι : Type) (z : ι → ℂ),
    Tendsto (fun R : ℝ => ∑' n, (if |(z n).im| < R then ((5 / 2 : ℝ) : ℂ) ^ z n / z n else 0))
      atTop (𝓝 (-(deriv (LFunction χ) 0 / LFunction χ 0) +
        ((∑' m : ℕ, (5 / 2 : ℝ) ^ (-(2 * (m : ℤ) + 1)) / (2 * m + 1) : ℝ) : ℂ) -
          χ.chebyshevPsi (5 / 2))) := by
  have hχ1 := ne_one_of_odd ho
  have hz := Complex.card_sigma_fin_analyticOrderAt (differentiable_xi hχ1)
    (xi_zero_ne_zero hχ hχ1)
  refine ⟨_, _, tendsto_tsum_cpow_div_zeros_explicit_formula_of_odd hχ ho _ hz
    (by norm_num) fun n hn => ?_⟩
  have : (2 * n : ℝ) = 5 := by rw [hn]; norm_num
  have h : 2 * n = 5 := by exact_mod_cast this
  omega

end ExplicitFormulaDirichletOddTest
