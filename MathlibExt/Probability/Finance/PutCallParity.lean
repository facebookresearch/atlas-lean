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

Replicable European claims satisfy put-call parity under a linear pricing
functional, with the dividend convention that `D` is the present value of
dividends over the option's life, so the ex-dividend stock price `S0 - D`
prices the terminal payoff alone. The payoff definitions are local copies of
the FI11.T01 payoffs; future unification with
`MathlibExt.Probability.Finance.OptionPayoffs` is noted in the PR body.

## Main results

* `callPayoff_sub_putPayoff`: the payoff identity (FI11.T01 helper).
* `putCallParity`: `C - P = (S0 - D) - K / R`.
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

/-- Put-call parity for replicable European claims. `price` is a linear
pricing functional on terminal payoffs (functions of the terminal underlying
`ω`). Hypotheses:

* `hSub`: `price` distributes over pointwise subtraction of payoffs.
* `hStock`: the price of the terminal-underlying payoff is `S0 - D`, where
  `S0` is today's spot and `D` is the present value of dividends paid over the
  option's life (dividend convention: the holder of the replicating stock
  position receives the dividends, so the ex-dividend stock price `S0 - D`
  prices the terminal payoff alone).
* `hBond`: the price of the constant payoff `K` is `K / R`, where `R` is the
  gross risk-free return.
* `hC`, `hP`: `C` and `P` are the prices of the call and put payoffs.

Conclusion: `C - P = (S0 - D) - K / R`. No no-arbitrage theorem is reproved:
the law of one price is the `hSub` + payoff-identity input, applied once. -/
theorem putCallParity {price : (ℝ → ℝ) → ℝ} {S0 D K R C P : ℝ}
    (hSub : ∀ f g : ℝ → ℝ, price (fun ω => f ω - g ω) = price f - price g)
    (hStock : price (fun ω => ω) = S0 - D)
    (hBond : price (fun _ => K) = K / R)
    (hC : C = price (fun ω => callPayoff ω K))
    (hP : P = price (fun ω => putPayoff ω K)) :
    C - P = (S0 - D) - K / R := by
  rw [hC, hP]
  have h := hSub (fun ω => callPayoff ω K) (fun ω => putPayoff ω K)
  rw [← h]
  have hpay : (fun ω => callPayoff ω K - putPayoff ω K) = (fun ω => ω - K) := by
    funext ω
    exact callPayoff_sub_putPayoff ω K
  rw [hpay]
  have h2 : price (fun ω : ℝ => ω - K) = price (fun ω => ω) - price (fun _ => K) :=
    hSub (fun ω => ω) (fun _ => K)
  rw [h2, hStock, hBond]

/-- Concrete instance: one terminal state `ω = 110`, `S0 = 110`, `D = 0`,
`K = 100`, `R = 1` (zero interest), and the one-state pricing functional
`price f = f 110 / 1`. Then `C - P = 10 = 110 - 100`. (With `R ≠ 1` a valid
instance needs `ω = R * (S0 - D)` so that `hStock` holds; the `R = 1` case
keeps the arithmetic exact.) -/
theorem putCallParity_example :
    let price : (ℝ → ℝ) → ℝ := fun f => f 110 / 1
    price (fun ω => callPayoff ω 100) - price (fun ω => putPayoff ω 100) =
      (110 - 0) - 100 / 1 := by
  simp only [callPayoff, putPayoff]
  norm_num

end MathlibExt.Probability.Finance.PutCallParity
