/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.NumberTheory.LSeries.DirichletContinuation

namespace MetaMathlibExt

@[expose] public section

open Complex

/-- Twelfth moment of `ζ` on the critical line (Heath-Brown's bound, as quoted): for every
`ε > 0`, `∫_1^T |ζ(1/2 + i t)|^{12} dt ≪_ε T^{2 + ε}` uniformly for `T ≥ 1`.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Lemma 2.4, equation (9); Guodong Hua, *On
Higher Moments of Dirichlet Coefficients Attached to Symmetric Power L-Functions Over
Certain Sequences of Positive Integers*, INTEGERS 24 (2024), Article A28, Lemma 5,
equation (21). -/
public theorem_wanted riemannZeta_twelfth_moment_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 12 ≤ C * T ^ (2 + ε)

/-- Heath-Brown's twelfth-moment bound on the critical line with the logarithmic factor:
`∫_1^T |ζ(1/2 + i t)|^{12} dt ≪ T^2 (log T)^{17}` for all sufficiently large `T`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 4 (`integers-2026-A70-lem-4`). -/
public theorem_wanted riemannZeta_twelfth_moment_le_log :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 12 ≤ C * T ^ 2 * Real.log T ^ 17

/-- Twelfth moment of `ζ` on the line `σ = 5/7`: for every `ε > 0`,
`∫_0^T |ζ(5/7 + i t)|^{12} dt ≪_ε T^{1 + ε}` uniformly for `T ≥ 1`.

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 1 (`integers-2026-A70-lem-1`). -/
public theorem_wanted riemannZeta_twelfth_moment_five_sevenths_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫ t in (0 : ℝ)..T, ‖riemannZeta (5 / 7 + t * I)‖ ^ 12 ≤ C * T ^ (1 + ε)

/-- Subconvexity bound for `ζ` in the critical strip (from the exponent `13/84` on the
critical line): for every `ε > 0`,
`ζ(σ + i t) ≪_ε (1 + |t|)^{max(13(1 - σ)/42, 0) + ε}` uniformly for `1/2 ≤ σ ≤ 1 + ε` and
`|t| ≥ 1`. The truncation `max(·, 0)` is printed in both cited equations.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Lemma 2.4, equation (10); Guodong Hua, *On
Higher Moments of Dirichlet Coefficients Attached to Symmetric Power L-Functions Over
Certain Sequences of Positive Integers*, INTEGERS 24 (2024), Article A28, Lemma 5,
equation (22). -/
public theorem_wanted riemannZeta_norm_le_subconvex {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 + ε → 1 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * (1 + |t|) ^ (max (13 / 42 * (1 - σ)) 0 + ε)

/-- Subconvexity bound for the `L`-function of the non-principal character `χ` modulo `4`:
for every `ε > 0`, `L(σ + i t, χ) ≪_ε (1 + |t|)^{max((1 - σ)/3, 0) + ε}` uniformly for
`1/2 ≤ σ ≤ 1 + ε` and `|t| ≥ 1`. (Modulo `4` there is exactly one non-principal character;
the paper fixes it throughout.) The truncation `max(·, 0)` is printed in equation (23).

Source: Guodong Hua, *On Higher Moments of Dirichlet Coefficients Attached to Symmetric
Power L-Functions Over Certain Sequences of Positive Integers*, INTEGERS 24 (2024),
Article A28, Lemma 5, equation (23). -/
public theorem_wanted dirichletLFunction_mod_four_norm_le_subconvex {ε : ℝ} (hε : 0 < ε)
    (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 + ε → 1 ≤ |t| →
      ‖χ.LFunction (σ + t * I)‖ ≤ C * (1 + |t|) ^ (max (1 / 3 * (1 - σ)) 0 + ε)

end

end MetaMathlibExt
