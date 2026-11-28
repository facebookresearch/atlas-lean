/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.ExplicitFormulaDirichlet
import MathlibExt.NumberTheory.LSeries.DirichletLeftHalfPlane

/-!
# Tests for the explicit formula for `ψ(x, χ)`

The truncated explicit formula and its GRH corollary instantiated at an actual enumeration of the
zeros of `ξ(s, χ)` for a primitive `χ ≠ 1`, at the smallest admissible `x = 3/2`; the explicit
formula of any parity at an `x` that is not a half-integer; and the classification of the zeros
of `L(s, χ)`.
-/

@[expose] public section

open DirichletCharacter

namespace ExplicitFormulaDirichletTest

/-- The truncated explicit formula at `x = 3/2` (where `ψ(x, χ) = 0`) for every height `R ≥ 2`,
including the ordinates of the zeros. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∃ C : ℝ, ∃ (ι : Type) (z : ι → ℂ), ∀ R : ℝ, 2 ≤ R →
      ‖χ.chebyshevPsi (3 / 2) -
          (-(∑' n, (if |(z n).im| < R then ((3 / 2 : ℝ) : ℂ) ^ z n / z n else 0))
            - (1 - (1 - χ (-1)) / 2) * ((Real.log (3 / 2) : ℂ) + χ.logDerivConstAtZero)
            - (1 - χ (-1)) / 2 * (deriv (LFunction χ) 0 / LFunction χ 0)
            + ∑' m : ℕ, ((3 / 2 : ℝ) : ℂ) ^ ((1 - χ (-1)) / 2 - 2 * ((m : ℂ) + 1)) /
                (2 * ((m : ℂ) + 1) - (1 - χ (-1)) / 2))‖
        ≤ C * ((3 / 2) * Real.log (q * (3 / 2) * R) ^ 2 / R) := by
  obtain ⟨C, hC⟩ := exists_truncated_explicit_formula_chebyshevPsi.{0}
  have hz := Complex.card_sigma_fin_analyticOrderAt (differentiable_xi hχ1)
    (xi_zero_ne_zero hχ hχ1)
  exact ⟨C, _, _, fun R hR => hC χ hχ hχ1 _ hz (3 / 2) ⟨1, one_pos, by norm_num⟩ R hR⟩

/-- Under GRH for `L(s, χ)`, `ψ(x, χ) ≪ √x log² (q x)`. The hypothesis is the faithful
statement "every nontrivial zero lies on `Re s = 1/2`". -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    (hGRH : ∀ ρ ∈ χ.nontrivialZeros, ρ.re = 1 / 2) :
    ∃ C : ℝ, ∀ x : ℝ, 2 ≤ x → ‖χ.chebyshevPsi x‖ ≤ C * Real.sqrt x * Real.log (q * x) ^ 2 := by
  obtain ⟨C, hC⟩ := exists_norm_chebyshevPsi_le_of_forall_re_eq_half
  exact ⟨C, hC χ hχ hχ1 hGRH⟩

/-- The explicit formula of any parity, at `x = 7/3`, which is not a half-integer. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1) :
    ∃ (ι : Type) (z : ι → ℂ), Filter.Tendsto (fun R : ℝ =>
      ∑' n, (if |(z n).im| < R then ((7 / 3 : ℝ) : ℂ) ^ z n / z n else 0)) Filter.atTop
      (nhds (-χ.chebyshevPsi (7 / 3)
        - (1 - (1 - χ (-1)) / 2) * ((Real.log (7 / 3) : ℂ) + χ.logDerivConstAtZero)
        - (1 - χ (-1)) / 2 * (deriv (LFunction χ) 0 / LFunction χ 0)
        + ∑' m : ℕ, ((7 / 3 : ℝ) : ℂ) ^ ((1 - χ (-1)) / 2 - 2 * ((m : ℂ) + 1)) /
            (2 * ((m : ℂ) + 1) - (1 - χ (-1)) / 2))) := by
  have hz := Complex.card_sigma_fin_analyticOrderAt (differentiable_xi hχ1)
    (xi_zero_ne_zero hχ hχ1)
  refine ⟨_, _, tendsto_tsum_cpow_div_zeros_explicit_formula hχ hχ1 _ hz (by norm_num)
    fun n hn => ?_⟩
  have h3 : (3 * n : ℝ) = 7 := by rw [hn]; norm_num
  have h : 3 * n = 7 := by exact_mod_cast h3
  omega

/-- The zeros of `L(s, χ)` are the nontrivial zeros and the trivial zeros `-a - 2n`; in
particular every zero with `Re s > 0` is nontrivial. -/
example {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ.IsPrimitive) (hχ1 : χ ≠ 1)
    {s : ℂ} (hs : LFunction χ s = 0) (hre : 0 < s.re) : s ∈ χ.nontrivialZeros := by
  obtain ⟨a, ha, hapar, hgf, -⟩ := exists_parity_gammaFactor_eq χ
  rcases mem_nontrivialZeros_or_eq_of_LFunction_eq_zero hχ hχ1 hapar hgf hs with h | ⟨n, rfl⟩
  · exact h
  · have ha0 : 0 ≤ a := by rcases ha with h | h <;> simp [h]
    simp at hre
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

end ExplicitFormulaDirichletTest
