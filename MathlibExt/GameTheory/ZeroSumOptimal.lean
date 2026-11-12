/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumMinimax

import Mathlib.Tactic

@[expose] public section

/-!
# Optimal strategies of a zero-sum matrix game form a Nash equilibrium

In the finite zero-sum matrix game `A` the row player receives `p ⬝ᵥ (A *ᵥ q)` and the column
player pays it (the convention of `MathlibExt.GameTheory.ZeroSumMinimax`). A row strategy is
maximin (optimal) when the payoff it guarantees equals the maximin value, and a column strategy is
minimax when the most it concedes equals the minimax value. Whenever the two values agree, every
pair of optimal strategies is a Nash equilibrium (a saddle point). For finite matrix games the
values agree by von Neumann's minimax theorem `matrixGame_minimax`, which
`matrixGame_isSaddlePoint_of_optimal` cites. `matrixGame_exists_isSaddlePointOn` already gives the
existence of some saddle point; the result here is that every optimal pair is one.

The Nash condition is written as the two saddle-point inequalities in the matrix-game convention of
`MathlibExt.GameTheory.ZeroSumMinimax`; it is the two-player case, with payoffs `A` and `-A`, of
`IsMixedNash` in `MathlibExt.GameTheory.MixedNashExistence` (merged after this file was frozen),
and the two formulations should be unified.

## Main results

* `isSaddlePoint_of_optimal_of_value_eq`: optimal strategies form a saddle point when maximin
  equals minimax.
* `matrixGame_isSaddlePoint_of_optimal`: optimal strategies of a finite matrix game form a
  saddle point.

## References

* J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Annalen 100 (1928), 295--320.
* M. J. Osborne and A. Rubinstein, *A Course in Game Theory*, MIT Press (1994), Section 2.5
  (strictly competitive games).
-/

namespace MathlibExt.GameTheory.ZeroSumOptimal

open Matrix Convexity

/-- `p` is an optimal (maximin) mixed strategy of the row player in the zero-sum matrix game `A`
(row player receives `p ⬝ᵥ (A *ᵥ q)`): the payoff `p` guarantees against every column strategy
equals the maximin value. -/
def IsMaximinStrategy {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (p : StdSimplex ℝ (Fin m)) :
    Prop :=
  (⨅ q : StdSimplex ℝ (Fin n), p.weights ⬝ᵥ (A *ᵥ q.weights)) =
    ⨆ p' : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n), p'.weights ⬝ᵥ (A *ᵥ q.weights)

/-- `q` is an optimal (minimax) mixed strategy of the column player in the zero-sum matrix game
`A`: the most the row player can get against `q` equals the minimax value. -/
def IsMinimaxStrategy {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (q : StdSimplex ℝ (Fin n)) :
    Prop :=
  (⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q.weights)) =
    ⨅ q' : StdSimplex ℝ (Fin n), ⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q'.weights)

/-- Each payoff term is bounded by the absolute matrix entry, since weights lie in `[0, 1]`. -/
private theorem abs_payoff_term_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (p : StdSimplex ℝ (Fin m)) (q : StdSimplex ℝ (Fin n)) (i : Fin m) (j : Fin n) :
    |p.weights i * A i j * q.weights j| ≤ |A i j| := by
  have hpi : 0 ≤ p.weights i := StdSimplex.weights_nonneg i
  have hpi1 : p.weights i ≤ 1 := StdSimplex.weights_apply_le_one p i
  have hqj : 0 ≤ q.weights j := StdSimplex.weights_nonneg j
  have hqj1 : q.weights j ≤ 1 := StdSimplex.weights_apply_le_one q j
  have hA : 0 ≤ |A i j| := abs_nonneg _
  simp only [abs_mul, abs_of_nonneg hpi, abs_of_nonneg hqj]
  calc p.weights i * |A i j| * q.weights j
      ≤ 1 * |A i j| * q.weights j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpi1 hA) hqj
    _ ≤ 1 * |A i j| * 1 := mul_le_mul_of_nonneg_left hqj1 (by positivity)
    _ = |A i j| := by ring

/-- The row-player payoff is bounded by the sum of absolute entries. -/
private theorem abs_payoff_le {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (p : StdSimplex ℝ (Fin m)) (q : StdSimplex ℝ (Fin n)) :
    |p.weights ⬝ᵥ (A *ᵥ q.weights)| ≤ ∑ j : Fin n, ∑ i : Fin m, |A i j| := by
  rw [Matrix.dot_mulVec_eq_sum_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine Finset.sum_le_sum fun j _ => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  exact Finset.sum_le_sum fun i _ => abs_payoff_term_le A p q i j

/-- Payoffs against a fixed row strategy are bounded below. -/
private theorem bddBelow_payoff_left {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (p : StdSimplex ℝ (Fin m)) :
    BddBelow (Set.range fun q : StdSimplex ℝ (Fin n) => p.weights ⬝ᵥ (A *ᵥ q.weights)) := by
  refine ⟨-(∑ j : Fin n, ∑ i : Fin m, |A i j|), ?_⟩
  intro b hb
  obtain ⟨q, rfl⟩ := hb
  exact neg_le_of_abs_le (abs_payoff_le A p q)

/-- Payoffs against a fixed column strategy are bounded above. -/
private theorem bddAbove_payoff_right {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (q : StdSimplex ℝ (Fin n)) :
    BddAbove (Set.range fun p : StdSimplex ℝ (Fin m) => p.weights ⬝ᵥ (A *ᵥ q.weights)) := by
  refine ⟨∑ j : Fin n, ∑ i : Fin m, |A i j|, ?_⟩
  intro b hb
  obtain ⟨p, rfl⟩ := hb
  exact le_of_abs_le (abs_payoff_le A p q)

/-- **Optimal strategies form a saddle point**, i.e. a Nash equilibrium of the zero-sum game,
given that the game has a value (maximin = minimax, hypothesis `hv`; discharged in Atlas by
citing `matrixGame_minimax`): if `p` is maximin and `q` is minimax, neither player gains by a
unilateral deviation. -/
theorem isSaddlePoint_of_optimal_of_value_eq {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hv : (⨆ p : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
      p.weights ⬝ᵥ (A *ᵥ q.weights)) =
      ⨅ q : StdSimplex ℝ (Fin n), ⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q.weights))
    {p : StdSimplex ℝ (Fin m)} {q : StdSimplex ℝ (Fin n)} (hp : IsMaximinStrategy A p)
    (hq : IsMinimaxStrategy A q) :
    (∀ p' : StdSimplex ℝ (Fin m),
      p'.weights ⬝ᵥ (A *ᵥ q.weights) ≤ p.weights ⬝ᵥ (A *ᵥ q.weights)) ∧
      ∀ q' : StdSimplex ℝ (Fin n),
        p.weights ⬝ᵥ (A *ᵥ q.weights) ≤ p.weights ⬝ᵥ (A *ᵥ q'.weights) := by
  have hp' : (⨅ q : StdSimplex ℝ (Fin n), p.weights ⬝ᵥ (A *ᵥ q.weights)) =
      (⨆ p' : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
        p'.weights ⬝ᵥ (A *ᵥ q.weights)) := hp
  have hq' : (⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q.weights)) =
      (⨅ q' : StdSimplex ℝ (Fin n), ⨆ p : StdSimplex ℝ (Fin m),
        p.weights ⬝ᵥ (A *ᵥ q'.weights)) := hq
  have hbBelow : BddBelow (Set.range fun q : StdSimplex ℝ (Fin n) =>
      p.weights ⬝ᵥ (A *ᵥ q.weights)) :=
    bddBelow_payoff_left A p
  have hbAbove : BddAbove (Set.range fun p' : StdSimplex ℝ (Fin m) =>
      p'.weights ⬝ᵥ (A *ᵥ q.weights)) :=
    bddAbove_payoff_right A q
  have hge : (⨆ p' : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
      p'.weights ⬝ᵥ (A *ᵥ q.weights)) ≤ p.weights ⬝ᵥ (A *ᵥ q.weights) := by
    rw [← hp']
    exact ciInf_le hbBelow q
  have hle : p.weights ⬝ᵥ (A *ᵥ q.weights) ≤ (⨅ q' : StdSimplex ℝ (Fin n),
      ⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q'.weights)) := by
    rw [← hq']
    exact le_ciSup hbAbove p
  rw [← hv] at hle
  have hval : p.weights ⬝ᵥ (A *ᵥ q.weights) = (⨆ p' : StdSimplex ℝ (Fin m),
      ⨅ q : StdSimplex ℝ (Fin n), p'.weights ⬝ᵥ (A *ᵥ q.weights)) :=
    le_antisymm hle hge
  refine ⟨fun p' => ?_, fun q' => ?_⟩
  · calc p'.weights ⬝ᵥ (A *ᵥ q.weights)
        ≤ (⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q.weights)) :=
          le_ciSup hbAbove p'
      _ = (⨅ q' : StdSimplex ℝ (Fin n), ⨆ p : StdSimplex ℝ (Fin m),
          p.weights ⬝ᵥ (A *ᵥ q'.weights)) := hq'
      _ = (⨆ p' : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
          p'.weights ⬝ᵥ (A *ᵥ q.weights)) := hv.symm
      _ = p.weights ⬝ᵥ (A *ᵥ q.weights) := hval.symm
  · calc p.weights ⬝ᵥ (A *ᵥ q.weights)
        = (⨆ p' : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
          p'.weights ⬝ᵥ (A *ᵥ q.weights)) := hval
      _ = (⨅ q : StdSimplex ℝ (Fin n), p.weights ⬝ᵥ (A *ᵥ q.weights)) := hp'.symm
      _ ≤ p.weights ⬝ᵥ (A *ᵥ q'.weights) := ciInf_le hbBelow q'

/-- **Optimal strategies of a finite zero-sum matrix game form a saddle point** (a Nash
equilibrium of the zero-sum game). With at least one row and one column, if `p` is a maximin
strategy and `q` a minimax strategy, neither player gains by a unilateral deviation; the value
equality is von Neumann's minimax theorem `matrixGame_minimax`. -/
theorem matrixGame_isSaddlePoint_of_optimal {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A : Matrix (Fin m) (Fin n) ℝ} {p : StdSimplex ℝ (Fin m)} {q : StdSimplex ℝ (Fin n)}
    (hp : IsMaximinStrategy A p) (hq : IsMinimaxStrategy A q) :
    (∀ p' : StdSimplex ℝ (Fin m),
      p'.weights ⬝ᵥ (A *ᵥ q.weights) ≤ p.weights ⬝ᵥ (A *ᵥ q.weights)) ∧
      ∀ q' : StdSimplex ℝ (Fin n),
        p.weights ⬝ᵥ (A *ᵥ q.weights) ≤ p.weights ⬝ᵥ (A *ᵥ q'.weights) :=
  isSaddlePoint_of_optimal_of_value_eq (matrixGame_minimax hm hn A) hp hq

end MathlibExt.GameTheory.ZeroSumOptimal
