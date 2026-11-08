/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.MinMax
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Ski rental: the deterministic competitive ratio is `2 - 1/B`

Skis cost `B ≥ 1` to buy and `1` per day to rent; the number of skiing days `d` is revealed only
when the season ends. A deterministic online strategy (`Strategy`) either rents forever (`none`)
or buys on day `t ≥ 1` (`some t`): it rents on days `1, …, t - 1` and buys on day `t`, if the
season lasts that long (`cost`). The offline optimum pays `min d B` (`opt`).

Main results (Karlin, Manasse, Rudolph and Sleator, *Competitive snoopy caching*, 1988; Borodin
and El-Yaniv, *Online Computation and Competitive Analysis*, Section 1.1; Karlin, *On the
performance of competitive algorithms in practice*, 1998):

* `cost_breakEven_le` (**upper bound**): the break-even strategy, buy on day `B`, pays at most
  `(2 - 1/B)` times the optimum on every season, `B * cost ≤ (2 B - 1) * opt`; in particular it
  is `2`-competitive (`cost_breakEven_le_two_mul`).
* `exists_cost_ge` (**lower bound**): every deterministic strategy pays at least `(2 - 1/B)`
  times the optimum on some season: the adversary ends the season on the day the strategy buys
  (or after `2 B - 1` days if it never buys).

So the deterministic competitive ratio of ski rental is exactly `2 - 1/B`.

## Cost model

The cost is the money paid (`cost`, `opt`); there is no computation to charge.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Online.SkiRental

/-- A deterministic strategy: buy on day `t ≥ 1` (`some t`), or rent forever (`none`). -/
abbrev Strategy := Option ℕ

/-- The cost of a strategy when the season lasts `d` days: rent for `t - 1` days and buy on day
`t` if `t ≤ d`, otherwise rent every day. -/
def cost (B : ℕ) : Strategy → ℕ → ℕ
  | some t, d => if 1 ≤ t ∧ t ≤ d then (t - 1) + B else d
  | none, d => d

/-- The offline optimum: rent every day or buy on day one, whichever is cheaper. -/
def opt (B d : ℕ) : ℕ := min d B

/-- The break-even strategy: buy on day `B`. -/
def breakEven (B : ℕ) : Strategy := some B

/-- The offline optimum is a lower bound for every strategy's cost. -/
theorem opt_le_cost (B : ℕ) (s : Strategy) (d : ℕ) : opt B d ≤ cost B s d := by
  unfold opt
  cases s with
  | none => exact min_le_left _ _
  | some t =>
      simp only [cost]
      split_ifs with h
      · exact (min_le_right _ _).trans (by omega)
      · exact min_le_left _ _

/-- **Upper bound**: the break-even strategy pays at most `(2 - 1/B)` times the optimum,
`B * cost ≤ (2 B - 1) * opt`. -/
theorem cost_breakEven_le {B : ℕ} (hB : 1 ≤ B) (d : ℕ) :
    B * cost B (breakEven B) d ≤ (2 * B - 1) * opt B d := by
  simp only [cost, breakEven, opt]
  split_ifs with h
  · rw [min_eq_right h.2]
    have : B - 1 + B = 2 * B - 1 := by omega
    rw [this, Nat.mul_comm]
  · rw [min_eq_left (by omega)]
    have : B ≤ 2 * B - 1 := by omega
    exact Nat.mul_le_mul_right d this

/-- The break-even strategy is `2`-competitive. -/
theorem cost_breakEven_le_two_mul {B : ℕ} (hB : 1 ≤ B) (d : ℕ) :
    cost B (breakEven B) d ≤ 2 * opt B d := by
  have h := cost_breakEven_le hB d
  have h2 : (2 * B - 1) * opt B d ≤ B * (2 * opt B d) := by
    have : 2 * B - 1 ≤ 2 * B := Nat.sub_le _ _
    calc (2 * B - 1) * opt B d ≤ 2 * B * opt B d := Nat.mul_le_mul_right _ this
      _ = B * (2 * opt B d) := by ring
  exact Nat.le_of_mul_le_mul_left (h.trans h2) (by omega)

/-- **Lower bound**: every deterministic strategy pays at least `(2 - 1/B)` times the optimum on
some season, `(2 B - 1) * opt ≤ B * cost`. -/
theorem exists_cost_ge {B : ℕ} (hB : 1 ≤ B) (s : Strategy) :
    ∃ d, (2 * B - 1) * opt B d ≤ B * cost B s d := by
  cases s with
  | none =>
      refine ⟨2 * B - 1, ?_⟩
      simp only [cost, opt]
      rw [min_eq_right (by omega), Nat.mul_comm]
  | some t =>
      by_cases ht : 1 ≤ t
      · refine ⟨t, ?_⟩
        simp only [cost, opt, ht, le_refl, and_self, ↓reduceIte]
        rcases le_total t B with htB | htB
        · rw [min_eq_left htB]
          -- (2B - 1) t ≤ B (t - 1 + B) ⟺ 0 ≤ (B - t)(B - 1)
          have key : (2 * B - 1) * t + (B - t) * (B - 1) = B * (t - 1 + B) := by
            obtain ⟨u, rfl⟩ : ∃ u, B = t + u := ⟨B - t, by omega⟩
            obtain ⟨w, rfl⟩ : ∃ w, t = w + 1 := ⟨t - 1, by omega⟩
            simp only [Nat.add_sub_cancel, show 2 * (w + 1 + u) - 1 = 2 * w + 2 * u + 1 by omega,
              show w + 1 + u - (w + 1) = u by omega, show w + 1 + u - 1 = w + u by omega]
            ring
          omega
        · rw [min_eq_right htB]
          have : 2 * B - 1 ≤ t - 1 + B := by omega
          rw [Nat.mul_comm]
          exact Nat.mul_le_mul_left B this
      · -- buying "on day 0" means renting forever in `cost`
        refine ⟨2 * B - 1, ?_⟩
        simp only [cost, opt, ht, false_and, ↓reduceIte]
        rw [min_eq_right (by omega), Nat.mul_comm]

end Cslib.Algorithms.Lean.Online.SkiRental
