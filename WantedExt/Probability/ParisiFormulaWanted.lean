/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Probability.SpinGlass.SherringtonKirkpatrick
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Order.Real

/-!
# The Parisi formula and Guerra's bound for the SK model: wanted

Talagrand's Theorem 1.1 (2006) computes the limiting free energy of mean-field Gaussian spin
glasses whose covariance satisfies `|E H_N(σ¹) H_N(σ²) / N - ξ(R_{1,2})| ≤ c(N) → 0` (its (1.3))
for a three times continuously differentiable `ξ` with the conditions (1.5):
`lim_N (1 / N) E log ∑_σ exp(H_N(σ) + h ∑_i σ_i) = inf P_k(m, q)`, the infimum of the Parisi
functional over all admissible parameters. Guerra (2003) had proved the upper bound by his
interpolation scheme. Both are stated below for the Sherrington–Kirkpatrick model, the case
`ξ(x) = β² x² / 2` (`MathlibExt.Probability.SherringtonKirkpatrick.skCovariance`), which meets
these hypotheses for `β > 0`.

The infimum is encoded as a greatest lower bound (`IsGLB`), so that no convention for an
unbounded set is involved; the upper bound is stated as `limsup_N F_N ≤ P_k(m, q)` in the form
"eventually `F_N ≤ P_k(m, q) + ε` for every `ε > 0`", which needs no boundedness side condition.

## References

* M. Talagrand, *The Parisi formula*, Ann. of Math. 163 (2006), 221–263, Theorem 1.1 and the
  discussion after it (Guerra's bound, his reference [3]: F. Guerra, *Broken replica symmetry
  bounds in the mean field spin glass model*, Comm. Math. Phys. 233 (2003), 1–12).
-/

@[expose] public section

namespace MathlibExt.Probability.ParisiFormulaWanted

open Filter Topology MathlibExt.Probability.SherringtonKirkpatrick

/-- **The Parisi formula for the SK model** (Talagrand, *The Parisi formula*, Ann. of Math. 163
(2006), Theorem 1.1, with `ξ(x) = β² x² / 2`). For `β > 0` and every field `h`, the set of values
of the Parisi functional over admissible parameters has a greatest lower bound `P(ξ, h)`, and the
free energy `F_N` of the SK model converges to it. -/
theorem_wanted tendsto_freeEnergy_parisi (β h : ℝ) (hβ : 0 < β) :
    ∃ P₀ : ℝ, IsGLB {P | ∃ (k : ℕ) (m q : ℕ → ℝ), IsParisiParameter k m q ∧
        P = parisiFunctional (skCovariance β) h k m q} P₀ ∧
      Tendsto (fun N : ℕ => freeEnergy β h N) atTop (𝓝 P₀)

/-- **Guerra's replica-symmetry-breaking bound for the SK model** (Talagrand, *The Parisi
formula*, Ann. of Math. 163 (2006), discussion after Theorem 1.1: Guerra proves that the left-hand
side of (1.14) is bounded by its right-hand side). For `β > 0`, every field `h` and all admissible
Parisi parameters `k, m, q`, `limsup_N F_N ≤ P_k(m, q)`. -/
theorem_wanted freeEnergy_le_parisiFunctional_eventually (β h : ℝ) (hβ : 0 < β) {k : ℕ}
    {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, freeEnergy β h N ≤ parisiFunctional (skCovariance β) h k m q + ε

end MathlibExt.Probability.ParisiFormulaWanted
