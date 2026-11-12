/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.ZeroSumMinimax
public import MathlibExt.GameTheory.MixedNashExistence

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
`MathlibExt.GameTheory.ZeroSumMinimax`. The two-player encoding `zeroSumPayoffs` /
`zeroSumProfile` below identifies this with the two-player case, with payoffs `A` and `-A`, of
`IsMixedNash` in `MathlibExt.GameTheory.MixedNashExistence`: `isMixedNash_of_optimal_of_value_eq`
states the saddle-point result in that canonical form.

## Main results

* `isSaddlePoint_of_optimal_of_value_eq`: optimal strategies form a saddle point when maximin
  equals minimax.
* `matrixGame_isSaddlePoint_of_optimal`: optimal strategies of a finite matrix game form a
  saddle point.
* `isMixedNash_of_optimal_of_value_eq`: optimal strategies form an `IsMixedNash` profile
  under the two-player encoding `zeroSumPayoffs` / `zeroSumProfile`.
* `matrixGame_isMixedNash_of_optimal`: optimal strategies of a finite matrix game form an
  `IsMixedNash` profile.

## References

* J. von Neumann, "Zur Theorie der Gesellschaftsspiele", Math. Annalen 100 (1928), 295--320.
* M. J. Osborne and A. Rubinstein, *A Course in Game Theory*, MIT Press (1994), Section 2.5
  (strictly competitive games).
-/

namespace MathlibExt.GameTheory.ZeroSumOptimal

open Matrix Convexity
open MathlibExt.GameTheory.MixedNashExistence

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

/-- Action sets of the two-player zero-sum game: player `false` (row) plays `Fin m`,
player `true` (column) plays `Fin n`. -/
def zeroSumActions (m n : ℕ) : Bool → Type _ := fun b => match b with
  | false => Fin m
  | true => Fin n

instance zeroSumActions_fintype (m n : ℕ) (b : Bool) : Fintype (zeroSumActions m n b) := by
  cases b
  · change Fintype (Fin m)
    exact inferInstance
  · change Fintype (Fin n)
    exact inferInstance

/-- The two-player payoff encoding of a zero-sum matrix game: the row player
(`false`) receives `A (a false) (a true)`, the column player (`true`) pays it. -/
def zeroSumPayoffs {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Bool → (∀ b, zeroSumActions m n b) → ℝ := fun b a => match b with
  | false => A (a false) (a true)
  | true => -A (a false) (a true)

/-- The mixed profile with row strategy `p` and column strategy `q`. -/
def zeroSumProfile {m n : ℕ} (p : StdSimplex ℝ (Fin m)) (q : StdSimplex ℝ (Fin n)) :
    ∀ b, StdSimplex ℝ (zeroSumActions m n b) := fun b => match b with
  | false => p
  | true => q

/-- Pure profiles of the two-player game are pairs of actions. -/
private def piBoolEquiv {m n : ℕ} : (∀ b : Bool, zeroSumActions m n b) ≃ Fin m × Fin n where
  toFun f := (f false, f true)
  invFun p := fun b => match b with
    | false => p.1
    | true => p.2
  left_inv f := by
    funext b
    cases b <;> rfl
  right_inv p := by
    cases p
    rfl

/-- The row player's expected payoff in the two-player encoding is the matrix payoff. -/
private theorem expectedPayoff_zeroSum_row {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (σ : ∀ b, StdSimplex ℝ (zeroSumActions m n b)) :
    expectedPayoff (zeroSumPayoffs A) σ false =
      (σ false).weights ⬝ᵥ (A *ᵥ (σ true).weights) := by
  unfold expectedPayoff
  set p : StdSimplex ℝ (Fin m) := σ false with hp
  set q : StdSimplex ℝ (Fin n) := σ true with hq
  rw [Fintype.sum_equiv piBoolEquiv
    (fun a => (∏ b, (σ b).weights (a b)) * zeroSumPayoffs A false a)
    (fun x => p.weights x.1 * q.weights x.2 * A x.1 x.2)
    (fun a => by
      rw [Fintype.prod_bool, hp, hq]
      change (σ true).weights (a true) * (σ false).weights (a false) * A (a false) (a true) =
        (σ false).weights (a false) * (σ true).weights (a true) * A (a false) (a true)
      ring)]
  rw [Fintype.sum_prod_type]
  calc (∑ i, ∑ j, p.weights i * q.weights j * A i j)
      = ∑ j, ∑ i, p.weights i * A i j * q.weights j := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
    _ = p.weights ⬝ᵥ (A *ᵥ q.weights) :=
        (Matrix.dot_mulVec_eq_sum_sum p.weights A q.weights).symm

/-- The column player's expected payoff in the two-player encoding is the negated
matrix payoff. -/
private theorem expectedPayoff_zeroSum_col {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (σ : ∀ b, StdSimplex ℝ (zeroSumActions m n b)) :
    expectedPayoff (zeroSumPayoffs A) σ true =
      -((σ false).weights ⬝ᵥ (A *ᵥ (σ true).weights)) := by
  have hneg : expectedPayoff (zeroSumPayoffs A) σ true =
      -expectedPayoff (zeroSumPayoffs A) σ false := by
    unfold expectedPayoff
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    simp [zeroSumPayoffs]
  rw [hneg, expectedPayoff_zeroSum_row]

/-- **Optimal strategies form a mixed Nash equilibrium**, in the canonical
`IsMixedNash` form: if `p` is maximin and `q` is minimax and the game has a value,
neither player gains by a unilateral deviation in the two-player encoding. -/
theorem isMixedNash_of_optimal_of_value_eq {m n : ℕ} {A : Matrix (Fin m) (Fin n) ℝ}
    (hv : (⨆ p : StdSimplex ℝ (Fin m), ⨅ q : StdSimplex ℝ (Fin n),
      p.weights ⬝ᵥ (A *ᵥ q.weights)) =
      ⨅ q : StdSimplex ℝ (Fin n), ⨆ p : StdSimplex ℝ (Fin m), p.weights ⬝ᵥ (A *ᵥ q.weights))
    {p : StdSimplex ℝ (Fin m)} {q : StdSimplex ℝ (Fin n)} (hp : IsMaximinStrategy A p)
    (hq : IsMinimaxStrategy A q) :
    IsMixedNash (zeroSumPayoffs A) (zeroSumProfile p q) := by
  obtain ⟨hrow, hcol⟩ :=
    isSaddlePoint_of_optimal_of_value_eq hv hp hq
  intro i τ
  cases i
  · rw [expectedPayoff_zeroSum_row, expectedPayoff_zeroSum_row]
    have h1 : Function.update (zeroSumProfile p q) false τ false = τ :=
      Function.update_self _ _ _
    have h2 : Function.update (zeroSumProfile p q) false τ true = q := by
      rw [Function.update_of_ne (by decide : (true : Bool) ≠ false)]
      rfl
    have hp1 : zeroSumProfile p q false = p := rfl
    have hq1 : zeroSumProfile p q true = q := rfl
    rw [h1, h2, hp1, hq1]
    exact hrow τ
  · rw [expectedPayoff_zeroSum_col, expectedPayoff_zeroSum_col]
    have h1 : Function.update (zeroSumProfile p q) true τ true = τ :=
      Function.update_self _ _ _
    have h2 : Function.update (zeroSumProfile p q) true τ false = p := by
      rw [Function.update_of_ne (by decide : (false : Bool) ≠ true)]
      rfl
    have hp1 : zeroSumProfile p q false = p := rfl
    have hq1 : zeroSumProfile p q true = q := rfl
    rw [h1, h2, hp1, hq1]
    exact neg_le_neg (hcol τ)

/-- **Optimal strategies of a finite zero-sum matrix game form a mixed Nash equilibrium**,
in the canonical `IsMixedNash` form. -/
theorem matrixGame_isMixedNash_of_optimal {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    {A : Matrix (Fin m) (Fin n) ℝ} {p : StdSimplex ℝ (Fin m)} {q : StdSimplex ℝ (Fin n)}
    (hp : IsMaximinStrategy A p) (hq : IsMinimaxStrategy A q) :
    IsMixedNash (zeroSumPayoffs A) (zeroSumProfile p q) :=
  isMixedNash_of_optimal_of_value_eq (matrixGame_minimax hm hn A) hp hq

end MathlibExt.GameTheory.ZeroSumOptimal
