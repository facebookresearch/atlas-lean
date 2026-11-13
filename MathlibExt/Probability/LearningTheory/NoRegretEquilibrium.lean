/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.Linarith

/-!
# No-regret dynamics give approximate saddle points of matrix games

Two players repeatedly play the finite zero-sum matrix game `A : Matrix (Fin m) (Fin n) ℝ` in the
convention of `MathlibExt.GameTheory.ZeroSumMinimax`: mixed strategies are points of
`Convexity.StdSimplex ℝ (Fin m)` and `Convexity.StdSimplex ℝ (Fin n)`, the row player receives
`u(p, q) = p.weights ⬝ᵥ (A *ᵥ q.weights)` and maximizes, and the column player pays it and
minimizes. In round `t < T` they play `p t` and `q t`. The row player's average regret against a
fixed strategy `x` is `(1/T) ∑ₜ u(x, q t) - (1/T) ∑ₜ u(p t, q t)`, and the column player's against
`y` is `(1/T) ∑ₜ u(p t, q t) - (1/T) ∑ₜ u(p t, y)`.

## Main results

* `avgStrategy`: the time average of `T > 0` mixed strategies, as a mixed strategy.
* `dotProduct_mulVec_avgStrategy_left`, `dotProduct_mulVec_avgStrategy_right`: the payoff of an
  average strategy is the average payoff.
* `no_regret_approx_saddle`: if the row player's average regret is at most `εrow` against every
  mixed strategy and the column player's is at most `εcol`, then the average strategies `p̄`, `q̄`
  satisfy `u(x, q̄) - u(p̄, y) ≤ εrow + εcol` for all mixed strategies `x` and `y`. Taking `y = q̄`
  and `x = p̄` gives the two inequalities of an `(εrow + εcol)`-approximate saddle point: neither
  player gains more than `εrow + εcol` by deviating from the average strategies.

## References

* Y. Freund and R. E. Schapire, *Adaptive game playing using multiplicative weights*, Games and
  Economic Behavior 29 (1999), 79–103.
* N. Cesa-Bianchi and G. Lugosi, *Prediction, Learning, and Games*, Cambridge University Press
  (2006), Chapter 7.
-/

@[expose] public section

namespace MathlibExt.Probability.LearningTheory.NoRegretEquilibrium

open Matrix Convexity

/-- The time average of the mixed strategies `p 0, …, p (T - 1)`, `T > 0`: its weights are the
averages of their weights. -/
noncomputable def avgStrategy {k T : ℕ} (hT : 0 < T) (p : Fin T → StdSimplex ℝ (Fin k)) :
    StdSimplex ℝ (Fin k) where
  weights := Finsupp.equivFunOnFinite.symm fun i => (∑ t, (p t).weights i) / T
  nonneg i := by
    simpa using div_nonneg (Finset.sum_nonneg fun t _ => (p t).weights_nonneg i) T.cast_nonneg
  total := by
    have hT' : (T : ℝ) ≠ 0 := by exact_mod_cast hT.ne'
    have h : ∑ i, (∑ t, (p t).weights i) / T = 1 := by
      rw [← Finset.sum_div, Finset.sum_comm]
      simp [hT']
    simpa [Finsupp.sum_fintype] using h

theorem avgStrategy_weights {k T : ℕ} (hT : 0 < T) (p : Fin T → StdSimplex ℝ (Fin k))
    (i : Fin k) : (avgStrategy hT p).weights i = (∑ t, (p t).weights i) / T := rfl

theorem coe_avgStrategy_weights {k T : ℕ} (hT : 0 < T) (p : Fin T → StdSimplex ℝ (Fin k)) :
    ⇑(avgStrategy hT p).weights = (T : ℝ)⁻¹ • ∑ t, ⇑(p t).weights := by
  ext i
  simp [avgStrategy_weights, Finset.sum_apply, div_eq_inv_mul]

/-- The payoff of the average row strategy is the average payoff. -/
theorem dotProduct_mulVec_avgStrategy_left {m n T : ℕ} (hT : 0 < T)
    (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin T → StdSimplex ℝ (Fin m)) (y : Fin n → ℝ) :
    (avgStrategy hT p).weights ⬝ᵥ (A *ᵥ y) = (∑ t, (p t).weights ⬝ᵥ (A *ᵥ y)) / T := by
  rw [coe_avgStrategy_weights, smul_dotProduct, sum_dotProduct, smul_eq_mul, div_eq_inv_mul]

/-- The payoff against the average column strategy is the average payoff. -/
theorem dotProduct_mulVec_avgStrategy_right {m n T : ℕ} (hT : 0 < T)
    (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin m → ℝ) (q : Fin T → StdSimplex ℝ (Fin n)) :
    x ⬝ᵥ (A *ᵥ (avgStrategy hT q).weights) = (∑ t, x ⬝ᵥ (A *ᵥ (q t).weights)) / T := by
  rw [coe_avgStrategy_weights, mulVec_smul, mulVec_sum, dotProduct_smul, dotProduct_sum,
    smul_eq_mul, div_eq_inv_mul]

/-- **No-regret dynamics give approximate saddle points.** In the matrix game `A` (row player
maximizes `u(p, q) = p.weights ⬝ᵥ (A *ᵥ q.weights)`), suppose the row player's average regret
`(1/T) ∑ₜ u(x, q t) - (1/T) ∑ₜ u(p t, q t)` is at most `εrow` for every mixed strategy `x` and the
column player's average regret `(1/T) ∑ₜ u(p t, q t) - (1/T) ∑ₜ u(p t, y)` is at most `εcol` for
every mixed strategy `y`. Then the average strategies `p̄ = avgStrategy hT p` and
`q̄ = avgStrategy hT q` satisfy `u(x, q̄) - u(p̄, y) ≤ εrow + εcol` for all `x` and `y`. -/
theorem no_regret_approx_saddle {m n T : ℕ} (hT : 0 < T) (A : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin T → StdSimplex ℝ (Fin m)) (q : Fin T → StdSimplex ℝ (Fin n)) (εrow εcol : ℝ)
    (hrow : ∀ x : StdSimplex ℝ (Fin m),
      (∑ t, x.weights ⬝ᵥ (A *ᵥ (q t).weights)) / T -
        (∑ t, (p t).weights ⬝ᵥ (A *ᵥ (q t).weights)) / T ≤ εrow)
    (hcol : ∀ y : StdSimplex ℝ (Fin n),
      (∑ t, (p t).weights ⬝ᵥ (A *ᵥ (q t).weights)) / T -
        (∑ t, (p t).weights ⬝ᵥ (A *ᵥ y.weights)) / T ≤ εcol)
    (x : StdSimplex ℝ (Fin m)) (y : StdSimplex ℝ (Fin n)) :
    x.weights ⬝ᵥ (A *ᵥ (avgStrategy hT q).weights) -
      (avgStrategy hT p).weights ⬝ᵥ (A *ᵥ y.weights) ≤ εrow + εcol := by
  rw [dotProduct_mulVec_avgStrategy_right, dotProduct_mulVec_avgStrategy_left]
  linarith [hrow x, hcol y]

end MathlibExt.Probability.LearningTheory.NoRegretEquilibrium
