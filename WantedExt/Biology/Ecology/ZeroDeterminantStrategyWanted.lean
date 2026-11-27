/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Press–Dyson zero-determinant strategies enforce linear payoff relations

In the iterated two-player game with stage payoffs `S_X = (R, S, T, P)` and `S_Y = (R, T, S, P)`
over the outcomes `cc, cd, dc, dd` (seen from X), player X uses a memory-one strategy
`p = (p₁, p₂, p₃, p₄)` (her cooperation probabilities after each outcome) and Y uses
`q = (q₁, q₂, q₃, q₄)` in his own order (outcomes seen from Y). Outcomes are indexed
`0 = cc, 1 = cd, 2 = dc, 3 = dd`. With `M(p, q)` the Markov matrix of outcomes and `v` a
stationary distribution, Press and Dyson show that `v · f = D(p, q, f) / D(p, q, 1)` for every
`f`, where `D(p, q, f)` is the determinant with columns `(-1 + p₁q₁, p₂q₃, p₃q₂, p₄q₄)`,
`p̃ = (-1 + p₁, -1 + p₂, p₃, p₄)`, `q̃ = (-1 + q₁, q₃, -1 + q₂, q₄)` and `f`. If X chooses a
feasible `p` with `p̃ = α S_X + β S_Y + γ 1`, then `α s_X + β s_Y + γ = 0` whatever Y does.
The determinant formula `v · f = D(p, q, f) / D(p, q, 1)` needs the nondegeneracy condition
`D(p, q, 1) ≠ 0` and is proved with it in
`Domains.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet`. The linear payoff
relations do not: they follow from
`v · p̃ = 0`, which holds for every stationary distribution `v` because `p̃` is the sum of the
first two columns of `M(p, q) - I` (X cooperates next with probability `p_s` from outcome `s`).
So they are stated for every stationary distribution. The paper notes that not all such
strategies are feasible and that singular cases exist. The existence of a strategy fixing the
score (`exists_strategy_fixing_score`) is proved in
`Domains.Biology.Ecology.ZeroDeterminantStrategyExistsStrategyFixingScore`.

Sources: W. H. Press and F. J. Dyson, "Iterated Prisoner's Dilemma contains strategies that
dominate any evolutionary opponent", Proc. Natl. Acad. Sci. USA 109 (2012) 10409–10413,
"Zero-determinant strategies", eqs. (1)–(7), and "X unilaterally sets Y's score", eqs. (8)–(10).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Order.Interval.Set.Basic
public import Domains.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet
public import Domains.Biology.Ecology.ZeroDeterminantStrategyExistsStrategyFixingScore

@[expose] public section

namespace WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

open Matrix Set

/-- X's stage payoffs `S_X = (R, S, T, P)` over `cc, cd, dc, dd`. -/
def payoffX (R S T P : ℝ) : Fin 4 → ℝ :=
  ![R, S, T, P]

/-- **Zero-determinant strategies** (Press and Dyson 2012, eq. (7)). Let `p` be a memory-one
strategy with `p̃ = α S_X + β S_Y + γ 1` for reals `α, β, γ` and payoffs `R, S, T, P`. Then for
every memory-one strategy `q` of Y and every stationary distribution `v` of `M(p, q)`, the long-run
scores `s_X = v · S_X`, `s_Y = v · S_Y` satisfy `α s_X + β s_Y + γ = 0`. No nondegeneracy assumption
`D(p, q, 1) ≠ 0` is needed: every stationary `v` satisfies `v · p̃ = 0`, since `p̃` is the sum of
the first two columns of `M(p, q) - I`.

Source: Press and Dyson (2012), "Zero-determinant strategies", eq. (7). -/
public theorem_wanted zeroDeterminant_linear_relation {R S T P α β γ : ℝ} {p : Fin 4 → ℝ}
    (hp : IsStrategy p)
    (hzd : pTilde p = fun i => α * payoffX R S T P i + β * payoffY R S T P i + γ)
    {q : Fin 4 → ℝ} (hq : IsStrategy q) {v : Fin 4 → ℝ}
    (hv : IsStationary (markovMatrix p q) v) :
    α * (v ⬝ᵥ payoffX R S T P) + β * (v ⬝ᵥ payoffY R S T P) + γ = 0

/-- **X sets Y's score: equalizer strategies** (Press and Dyson 2012, eqs. (8)–(9)). Let `R ≠ P`,
let `p` be a memory-one strategy with `p₂ = (p₁ (T - P) - (1 + p₄)(T - R)) / (R - P)`,
`p₃ = ((1 - p₁)(P - S) + p₄ (R - S)) / (R - P)` and `(1 - p₁) + p₄ ≠ 0`. Then for every memory-one
strategy `q` of Y and every stationary distribution `v` of `M(p, q)`,
`v · S_Y = ((1 - p₁) P + p₄ R) / ((1 - p₁) + p₄)`. No nondegeneracy assumption `D(p, q, 1) ≠ 0` is
needed: every stationary `v` satisfies `v · p̃ = 0`, since `p̃` is the sum of the first two columns
of `M(p, q) - I`.

Source: Press and Dyson (2012), "X unilaterally sets Y's score", eqs. (8)–(9). -/
public theorem_wanted equalizer_score {R S T P : ℝ} (hRP : R ≠ P) {p : Fin 4 → ℝ}
    (hp : IsStrategy p) (hp2 : p 1 = (p 0 * (T - P) - (1 + p 3) * (T - R)) / (R - P))
    (hp3 : p 2 = ((1 - p 0) * (P - S) + p 3 * (R - S)) / (R - P))
    (hden : (1 - p 0) + p 3 ≠ 0) {q : Fin 4 → ℝ} (hq : IsStrategy q) {v : Fin 4 → ℝ}
    (hv : IsStationary (markovMatrix p q) v) :
    v ⬝ᵥ payoffY R S T P = ((1 - p 0) * P + p 3 * R) / ((1 - p 0) + p 3)

/-- **X cannot fix her own score** (Press and Dyson 2012, eq. (10)). If `T > R > P > S` and a
memory-one strategy `p` satisfies `p̃ = α S_X + γ 1` for reals `α, γ`, then `α = 0` and `p` is
the singular strategy `(1, 1, 0, 0)`.

Source: Press and Dyson (2012), "X tries to set her own score", eq. (10). -/
public theorem_wanted own_score_singular {R S T P α γ : ℝ} (hTR : R < T) (hRP : P < R)
    (hPS : S < P) {p : Fin 4 → ℝ} (hp : IsStrategy p)
    (hzd : pTilde p = fun i => α * payoffX R S T P i + γ) :
    α = 0 ∧ p = ![1, 1, 0, 0]

end WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted
