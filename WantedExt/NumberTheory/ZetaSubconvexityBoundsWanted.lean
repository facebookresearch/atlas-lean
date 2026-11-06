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

/-- **Twelfth moment of the Riemann zeta function on the critical line.** For every
$\varepsilon > 0$ there is a constant $C$ such that for every real $T \ge 1$,
$$\int_1^T |\zeta(1/2 + it)|^{12} \, dt \le C T^{2+\varepsilon}.$$
This is Heath-Brown's bound in the form quoted by the sources.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Lemma 2.4, equation (9); Guodong Hua, *On
Higher Moments of Dirichlet Coefficients Attached to Symmetric Power L-Functions Over
Certain Sequences of Positive Integers*, INTEGERS 24 (2024), Article A28, Lemma 5,
equation (21). -/
public theorem_wanted riemannZeta_twelfth_moment_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 12 ≤ C * T ^ (2 + ε)

/-- **Heath-Brown's twelfth moment bound with the logarithmic factor.** There are constants $C$
and $T_0$ such that for every real $T \ge T_0$,
$$\int_1^T |\zeta(1/2 + it)|^{12} \, dt \le C T^2 (\log T)^{17}.$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 4 (`integers-2026-A70-lem-4`). -/
public theorem_wanted riemannZeta_twelfth_moment_le_log :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ∫ t in (1 : ℝ)..T, ‖riemannZeta (1 / 2 + t * I)‖ ^ 12 ≤ C * T ^ 2 * Real.log T ^ 17

/-- **Twelfth moment of the Riemann zeta function on the line of real part 5/7.** For every
$\varepsilon > 0$ there is a constant $C$ such that for every real $T \ge 1$,
$$\int_0^T |\zeta(5/7 + it)|^{12} \, dt \le C T^{1+\varepsilon}.$$

Source: M. S. Datt, Ekta Soni, and A. Sankaranarayanan, *On the Asymptotic Formula for the
Gcd-Sum Function*, INTEGERS 26 (2026), Article A70, Lemma 1 (`integers-2026-A70-lem-1`). -/
public theorem_wanted riemannZeta_twelfth_moment_five_sevenths_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ T : ℝ, 1 ≤ T →
      ∫ t in (0 : ℝ)..T, ‖riemannZeta (5 / 7 + t * I)‖ ^ 12 ≤ C * T ^ (1 + ε)

/-- **Subconvexity bound for the Riemann zeta function.** For every $\varepsilon > 0$ there is
a constant $C$ such that for all real $\sigma$ and $t$ with $1/2 \le \sigma \le 1 + \varepsilon$
and $|t| \ge 1$,
$$|\zeta(\sigma + it)| \le C (1 + |t|)^{\max(13(1 - \sigma)/42,\, 0) + \varepsilon}.$$
The exponent comes from the exponent $13/84$ on the critical line; the truncation at $0$
follows both cited equations.

Source: Guodong Hua, *The General Divisor Problem of Cusp Form Coefficients over Arithmetic
Progressions*, INTEGERS 24 (2024), Article A3, Lemma 2.4, equation (10); Guodong Hua, *On
Higher Moments of Dirichlet Coefficients Attached to Symmetric Power L-Functions Over
Certain Sequences of Positive Integers*, INTEGERS 24 (2024), Article A28, Lemma 5,
equation (22). -/
public theorem_wanted riemannZeta_norm_le_subconvex {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 + ε → 1 ≤ |t| →
      ‖riemannZeta (σ + t * I)‖ ≤ C * (1 + |t|) ^ (max (13 / 42 * (1 - σ)) 0 + ε)

/-- **Subconvexity bound for the Dirichlet L-function modulo 4.** Let $\varepsilon > 0$ and let
$\chi$ be a non-principal Dirichlet character modulo $4$ (there is exactly one). Then there is a
constant $C$ such that for all real $\sigma$ and $t$ with $1/2 \le \sigma \le 1 + \varepsilon$ and
$|t| \ge 1$,
$$|L(\sigma + it, \chi)| \le C (1 + |t|)^{\max((1 - \sigma)/3,\, 0) + \varepsilon}.$$
The truncation at $0$ follows equation (23) of the source.

Source: Guodong Hua, *On Higher Moments of Dirichlet Coefficients Attached to Symmetric
Power L-Functions Over Certain Sequences of Positive Integers*, INTEGERS 24 (2024),
Article A28, Lemma 5, equation (23). -/
public theorem_wanted dirichletLFunction_mod_four_norm_le_subconvex {ε : ℝ} (hε : 0 < ε)
    (χ : DirichletCharacter ℂ 4) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ 1 + ε → 1 ≤ |t| →
      ‖χ.LFunction (σ + t * I)‖ ≤ C * (1 + |t|) ^ (max (1 / 3 * (1 - σ)) 0 + ε)

end

end MetaMathlibExt
