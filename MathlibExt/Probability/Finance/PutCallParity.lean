/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Put-call parity

Replicable European claims satisfy put-call parity under an additive pricing
functional, with the dividend convention that `D` is the present value of
dividends over the option's life, so the ex-dividend stock price `S0 - D`
prices the terminal payoff alone. The payoff definitions are local copies of
the FI11.T01 payoffs; future unification with
`MathlibExt.Probability.Finance.OptionPayoffs` is noted in the PR body.

## Main results

* `callPayoff_sub_putPayoff`: the payoff identity (FI11.T01 helper).
* `putCallParity`: `C - P = (S0 - D) - K / R` for a positive gross return `R`.
* `putCallParity_example`: a concrete instance.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.PutCallParity

/-- European call payoff at expiry: `max (S - K) 0`. Local copy of the
FI11.T01 payoff (same lane); future unification with FI11.T01's
`MathlibExt.Probability.Finance.OptionPayoffs.europeanCallPayoff` is noted in
the PR body. -/
noncomputable def callPayoff (S K : ℝ) : ℝ := max (S - K) 0

/-- European put payoff at expiry: `max (K - S) 0`. Local copy of the FI11.T01
payoff; see `callPayoff` for the unification note. -/
noncomputable def putPayoff (S K : ℝ) : ℝ := max (K - S) 0

/-- Payoff identity (FI11.T01, proved here as a local helper so this file is
self-contained): call payoff minus put payoff equals `S - K`. -/
theorem callPayoff_sub_putPayoff (S K : ℝ) :
    callPayoff S K - putPayoff S K = S - K := by
  unfold callPayoff putPayoff
  have h : K - S = -(S - K) := by ring
  rw [h]
  exact max_zero_sub_max_neg_zero_eq_self (S - K)

/-- Put-call parity for replicable European claims. `price` is an additive
pricing functional on terminal payoffs (functions of the terminal underlying
`ω`): an additive homomorphism `(ℝ → ℝ) →+ ℝ`, so the price of a difference of
payoffs is the difference of their prices (`map_sub`). Hypotheses:

* `_hR`: the gross risk-free return `R` is positive. The algebra below does not
  use it (hence the underscore); it excludes `R = 0`, where Lean's `K / 0 = 0`
  would let the zero functional satisfy `hBond`.
* `hStock`: the price of the terminal-underlying payoff is `S0 - D`, where
  `S0` is today's spot and `D` is the present value of dividends paid over the
  option's life (dividend convention: the holder of the replicating stock
  position receives the dividends, so the ex-dividend stock price `S0 - D`
  prices the terminal payoff alone).
* `hBond`: the price of the constant payoff `K` is `K / R`, the strike
  discounted at the gross risk-free return `R`.
* `hC`, `hP`: `C` and `P` are the prices of the call and put payoffs.

Conclusion: `C - P = (S0 - D) - K / R`. No no-arbitrage theorem is reproved:
the law of one price is the additivity of `price` plus the payoff identity,
applied once. -/
theorem putCallParity {price : (ℝ → ℝ) →+ ℝ} {S0 D K R C P : ℝ} (_hR : 0 < R)
    (hStock : price (fun ω => ω) = S0 - D)
    (hBond : price (fun _ => K) = K / R)
    (hC : C = price (fun ω => callPayoff ω K))
    (hP : P = price (fun ω => putPayoff ω K)) :
    C - P = (S0 - D) - K / R := by
  rw [hC, hP, ← hStock, ← hBond, ← map_sub price, ← map_sub price]
  congr 1
  funext ω
  exact callPayoff_sub_putPayoff ω K

/-- Concrete instance: one terminal state `ω = 110`, `S0 = 110`, `D = 0`,
`K = 100`, `R = 1` (zero interest), and the one-state pricing functional
`price f = f 110 / 1`. Then `C - P = 10 = 110 - 100`. (For another gross return
`R > 0`, the one-state functional `price f = f ω / R` satisfies `hStock` exactly
when `ω = R * (S0 - D)`; the `R = 1` case keeps the arithmetic exact.) -/
theorem putCallParity_example :
    let price : (ℝ → ℝ) → ℝ := fun f => f 110 / 1
    price (fun ω => callPayoff ω 100) - price (fun ω => putPayoff ω 100) =
      (110 - 0) - 100 / 1 := by
  simp only [callPayoff, putPayoff]
  norm_num

end MathlibExt.Probability.Finance.PutCallParity
