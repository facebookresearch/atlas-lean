/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Logic.Function.Basic

import Mathlib.Tactic.Linarith
import Mathlib.Tactic

@[expose] public section

/-! # Myerson's lemma: monotonicity

In a dominant-strategy incentive compatible single-parameter
auction, each bidder's allocation is monotone nondecreasing in
their own bid: adding the two DSIC inequalities for bidding `z`
versus `z'` cancels the payments. This is part (a) of roadmap
package DPA-45 of the Atlas TCS canon roadmap; the step-allocation
payment formula and uniqueness are follow-ups.

Source: R. Myerson, "Optimal auction design", Mathematics of
Operations Research 6 (1981), 58--73, Lemma 1.
-/

/-- Dominant-strategy incentive compatibility for a single-parameter
auction with allocation rule `x` and payment rule `pay`: every bidder
with a nonnegative valuation maximizes quasilinear utility by bidding
their valuation, whatever the others bid (`bminus` is the profile of
other bids; the bidder's own entry is overwritten by the update). -/
def DSIC {n : ℕ} (x : (Fin n → ℝ) → Fin n → ℝ) (pay : (Fin n → ℝ) → Fin n → ℝ) : Prop :=
  ∀ (i : Fin n) (vi bi : ℝ) (bminus : Fin n → ℝ), 0 ≤ vi →
    vi * x (Function.update bminus i bi) i - pay (Function.update bminus i bi) i ≤
    vi * x (Function.update bminus i vi) i - pay (Function.update bminus i vi) i

/-- Myerson monotonicity: in a DSIC single-parameter auction, the
allocation of each bidder is monotone nondecreasing in their own
bid, holding the others fixed. -/
theorem myerson_monotone {n : ℕ} {x : (Fin n → ℝ) → Fin n → ℝ}
    {pay : (Fin n → ℝ) → Fin n → ℝ} (h : DSIC x pay)
    (i : Fin n) (bminus : Fin n → ℝ) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (hzz : z ≤ z') :
    x (Function.update bminus i z) i ≤ x (Function.update bminus i z') i := by
  by_cases heq : z = z'
  · subst heq
    exact le_rfl
  · have hlt : z < z' := lt_of_le_of_ne hzz heq
    have h1 := h i z z' bminus hz
    have h2 := h i z' z bminus hz'
    by_contra hcon
    have hlt2 : x (Function.update bminus i z') i < x (Function.update bminus i z) i :=
      lt_of_not_ge hcon
    nlinarith [h1, h2, hlt, hlt2, mul_pos (sub_pos.mpr hlt) (sub_pos.mpr hlt2)]
