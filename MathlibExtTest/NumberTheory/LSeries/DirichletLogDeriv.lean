/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LSeries.DirichletLogDeriv

/-!
# Tests for `L'/L` near `Re s = 1` and the constant `b(χ)`

The Dirichlet series of `-L'/L` at `s = 2`, the `1`-`1` and `3`-`4`-`1` inequalities at the
character mod `1`, the definition of `DirichletCharacter.logDerivConstAtZero`, and the
Hadamard bound with the empty set of zeros.
-/

@[expose] public section

open Filter Topology DirichletCharacter

namespace DirichletLogDerivTest

example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    -logDeriv (LFunction χ) 2 =
      LSeries ((fun n : ℕ => χ n) * fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) 2 :=
  neg_logDeriv_LFunction_eq_LSeries_vonMangoldt χ (by norm_num)

/-- The `1`-`1` inequality for the character mod `1` says `Re(-ζ'/ζ(σ)) ≥ 0`. -/
example {σ : ℝ} (hσ : 1 < σ) : 0 ≤ (-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re +
    (-logDeriv (LFunction (1 : DirichletCharacter ℂ 1)) (σ : ℂ)).re :=
  re_neg_logDeriv_riemannZeta_add_LFunction_nonneg 1 hσ

/-- `b(χ)` is the constant term of `L'/L` at `0`, as a `limUnder` over `s → 0`, `s ≠ 0`. -/
example {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) : χ.logDerivConstAtZero =
    limUnder (𝓝[≠] (0 : ℂ)) fun s => logDeriv (LFunction χ) s - 1 / s :=
  rfl

/-- If `L(s, χ) = s E(s)` near `0` then `b(χ) = E'(0)/E(0)`. -/
example {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} {E : ℂ → ℂ} (hE : AnalyticAt ℂ E 0)
    (hE0 : E 0 ≠ 0) (h : ∀ᶠ s in 𝓝[≠] (0 : ℂ), LFunction χ s = s * E s) :
    χ.logDerivConstAtZero = deriv E 0 / E 0 := by
  rw [logDerivConstAtZero_eq_logDeriv hE hE0 h, logDeriv_apply]

/-- The Hadamard bound with no zeros subtracted. -/
example : ∃ C : ℝ, ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive → χ ≠ 1 →
    ∀ s : ℂ, 1 < s.re → s.re ≤ 2 →
      -(logDeriv (LFunction χ) s).re ≤ Real.log (N * (|s.im| + 2)) / 2 + C := by
  obtain ⟨C, hC⟩ := exists_neg_re_logDeriv_LFunction_le
  refine ⟨C, fun N _ χ hχ hχ1 s hs1 hs2 => ?_⟩
  simpa using hC N χ hχ hχ1 s hs1 hs2 ∅ (fun _ => 0) (by simp)

end DirichletLogDerivTest
