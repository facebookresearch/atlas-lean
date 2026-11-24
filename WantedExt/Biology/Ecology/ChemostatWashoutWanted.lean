/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The single-species chemostat: washout or convergence by the break-even concentration

A chemostat with input substrate concentration `S⁰`, dilution rate `D`, maximal growth rate `m`,
half-saturation constant `a` and yield `y` (all positive) and Monod uptake obeys
`S' = (S⁰ - S) D - (1/y) m S x / (a + S)` and `x' = x (m S / (a + S) - D)`. Let `b = m / D`
and, when `b > 1`, let `λ = a / (b - 1)` be the break-even concentration, where growth balances
dilution. For every solution with `S(0) ≥ 0` and `x(0) > 0`: if `b ≤ 1`, or `b > 1` and
`λ ≥ S⁰`, the organism washes out (`x → 0`, `S → S⁰`); if `b > 1` and `λ < S⁰`, then `S → λ`
and `x → y (S⁰ - λ)`. The proof uses that `S + x / y → S⁰` and reduces to one dimension.

Recorded here: the washout and convergence alternatives for solutions on `[0, ∞)`. The monograph
of Smith and Waltman (1995) was not read; the statement follows Hsu, Hubbell and Waltman (1977)
with one species and Rapaport (2017, Lemma 1 and Proposition 1, with the yield rescaled to `1`).

Sources: H. L. Smith and P. Waltman, *The Theory of the Chemostat: Dynamics of Microbial
Competition*, Cambridge Univ. Press (1995), doi:10.1017/CBO9780511530043; S. B. Hsu, S. Hubbell
and P. Waltman, "A mathematical theory for single-nutrient competition in continuous cultures of
micro-organisms", SIAM J. Appl. Math. 32 (1977) 366–383, doi:10.1137/0132030; A. Rapaport, "A
new proof of the competitive exclusion principle in the chemostat", arXiv:1711.06928 (2017).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.ChemostatWashoutWanted

open Filter Topology

/-- `(S, x)` solves the **single-species chemostat** with input concentration `S⁰`, dilution
rate `D`, maximal growth rate `m`, half-saturation constant `a` and yield `y` on `[0, ∞)`: for
every `t ≥ 0`, `S'(t) = (S⁰ - S(t)) D - (1/y) m S(t) x(t) / (a + S(t))` and
`x'(t) = x(t) (m S(t) / (a + S(t)) - D)`. -/
def IsSolution (S₀ D m a y : ℝ) (S x : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, 0 ≤ t →
    HasDerivAt S ((S₀ - S t) * D - 1 / y * m * S t * x t / (a + S t)) t ∧
      HasDerivAt x (x t * (m * S t / (a + S t) - D)) t

/-- The **break-even concentration** `λ = a / (m / D - 1)`, meaningful when `m > D`. -/
noncomputable def breakEven (D m a : ℝ) : ℝ := a / (m / D - 1)

/-- **Washout** (Hsu–Hubbell–Waltman 1977 with one species; Rapaport 2017, Lemma 1): let
`S⁰, D, m, a, y > 0`, and suppose `m ≤ D`, or `m > D` and `λ = a / (m / D - 1) ≥ S⁰`. Then every
solution `(S, x)` of the chemostat on `[0, ∞)` with `S(0) ≥ 0` and `x(0) > 0` satisfies
`x(t) → 0` and `S(t) → S⁰` as `t → ∞`.

Sources: Hsu, Hubbell and Waltman (1977); Rapaport (2017), Lemma 1. -/
public theorem_wanted washout (S₀ D m a y : ℝ) (hS₀ : 0 < S₀) (hD : 0 < D) (hm : 0 < m)
    (ha : 0 < a) (hy : 0 < y) (hwash : m ≤ D ∨ (D < m ∧ S₀ ≤ breakEven D m a))
    (S x : ℝ → ℝ) (hsol : IsSolution S₀ D m a y S x) (hS : 0 ≤ S 0) (hx : 0 < x 0) :
    Tendsto x atTop (𝓝 0) ∧ Tendsto S atTop (𝓝 S₀)

/-- **Convergence to the break-even equilibrium** (Hsu–Hubbell–Waltman 1977 with one species;
Rapaport 2017, Proposition 1): let `S⁰, D, m, a, y > 0` with `m > D` and
`λ = a / (m / D - 1) < S⁰`. Then every solution `(S, x)` of the chemostat on `[0, ∞)` with
`S(0) ≥ 0` and `x(0) > 0` satisfies `S(t) → λ` and `x(t) → y (S⁰ - λ)` as `t → ∞`.

Sources: Hsu, Hubbell and Waltman (1977); Rapaport (2017), Proposition 1. -/
public theorem_wanted tendsto_breakEven (S₀ D m a y : ℝ) (hS₀ : 0 < S₀) (hD : 0 < D)
    (hm : D < m) (ha : 0 < a) (hy : 0 < y) (hlt : breakEven D m a < S₀)
    (S x : ℝ → ℝ) (hsol : IsSolution S₀ D m a y S x) (hS : 0 ≤ S 0) (hx : 0 < x 0) :
    Tendsto S atTop (𝓝 (breakEven D m a)) ∧ Tendsto x atTop (𝓝 (y * (S₀ - breakEven D m a)))

end WantedExt.Biology.Ecology.ChemostatWashoutWanted
