/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
public import Domains.Biology.Ecology.ZeroDeterminantStrategyDotProductEqDivPdDet

/-!
# X sets Y's score: equalizer strategies

This module defines `yView`, `markovMatrix`, `IsStationary`, `payoffY`, and `IsStrategy`
and proves `equalizer_score`: X's equalizer equations fix Y's payoff for every stationary
distribution, including when the Markov matrix is singular.

## References

* W. H. Press and F. J. Dyson, "Iterated Prisoner's Dilemma contains strategies that
  dominate any evolutionary opponent", Proc. Natl. Acad. Sci. USA 109 (2012) 10409–10413,
  "X unilaterally sets Y's score", eqs. (8)–(9).
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted

open Matrix Set

/-- Y's stage payoffs `S_Y = (R, T, S, P)` over `cc, cd, dc, dd` (seen from X). -/
def payoffY (R S T P : ℝ) : Fin 4 → ℝ :=
  ![R, T, S, P]

private theorem stationary_cooperation_change {p q v : Fin 4 → ℝ}
    (hv : IsStationary (markovMatrix p q) v) :
    v 0 * (-1 + p 0) + v 1 * (-1 + p 1) + v 2 * p 2 + v 3 * p 3 = 0 := by
  have h0 : (v ᵥ* markovMatrix p q) 0 = v 0 := by rw [hv.1]
  have h1 : (v ᵥ* markovMatrix p q) 1 = v 1 := by rw [hv.1]
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_four, markovMatrix] at h0 h1
  linear_combination h0 + h1

/-- **X sets Y's score: equalizer strategies** (Press and Dyson 2012, eqs. (8)–(9)). Let `R ≠ P`,
let `p` be a memory-one strategy with `p₂ = (p₁ (T - P) - (1 + p₄)(T - R)) / (R - P)`,
`p₃ = ((1 - p₁)(P - S) + p₄ (R - S)) / (R - P)` and `(1 - p₁) + p₄ ≠ 0`. Then for every memory-one
strategy `q` of Y and every stationary distribution `v` of `M(p, q)`,
`v · S_Y = ((1 - p₁) P + p₄ R) / ((1 - p₁) + p₄)`. No nondegeneracy assumption `D(p, q, 1) ≠ 0` is
needed: every stationary `v` satisfies `v · p̃ = 0`, since `p̃` is the sum of the first two columns
of `M(p, q) - I`.

Source: Press and Dyson (2012), "X unilaterally sets Y's score", eqs. (8)–(9). -/
public theorem equalizer_score {R S T P : ℝ} (hRP : R ≠ P) {p : Fin 4 → ℝ}
    (hp : IsStrategy p) (hp2 : p 1 = (p 0 * (T - P) - (1 + p 3) * (T - R)) / (R - P))
    (hp3 : p 2 = ((1 - p 0) * (P - S) + p 3 * (R - S)) / (R - P))
    (hden : (1 - p 0) + p 3 ≠ 0) {q : Fin 4 → ℝ} (hq : IsStrategy q) {v : Fin 4 → ℝ}
    (hv : IsStationary (markovMatrix p q) v) :
    v ⬝ᵥ payoffY R S T P = ((1 - p 0) * P + p 3 * R) / ((1 - p 0) + p 3) := by
  have _ := hp
  have _ := hq
  have hD : R - P ≠ 0 := sub_ne_zero.mpr hRP
  have h2 := (eq_div_iff hD).mp hp2
  have h3 := (eq_div_iff hD).mp hp3
  have hcoop := stationary_cooperation_change hv
  have hsum : v 0 + v 1 + v 2 + v 3 = 1 := by
    simpa [Fin.sum_univ_four, add_assoc] using hv.2.2
  apply (eq_div_iff hden).mpr
  simp [dotProduct, Fin.sum_univ_four, payoffY]
  linear_combination -(R - P) * hcoop + v 1 * h2 + v 2 * h3 +
    ((1 - p 0) * P + p 3 * R) * hsum

end WantedExt.Biology.Ecology.ZeroDeterminantStrategyWanted
