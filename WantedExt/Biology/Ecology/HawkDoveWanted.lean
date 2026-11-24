/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hawk–Dove game: the unique evolutionarily stable strategy

In the Hawk–Dove game with value of the resource `V > 0` and cost of injury `C > 0`, the
row-player payoff matrix (rows and columns ordered Hawk, Dove) is
`[[(V - C) / 2, V], [0, V / 2]]`. A mixed strategy is the probability `p ∈ [0, 1]` of playing
Hawk, with payoff `E(p, q)` against `q`. In Maynard Smith's sense `p` is an evolutionarily stable
strategy (ESS) if for every `q ≠ p` either `E(q, p) < E(p, p)`, or `E(q, p) = E(p, p)` and
`E(q, q) < E(p, q)`. Maynard Smith (1982, Ch. 2): if `C > V` there is no pure ESS and the unique
ESS plays Hawk with probability `V / C`; if `V ≥ C`, pure Hawk is the unique ESS (at `V = C` it
meets the first condition with equality and the second strictly).

Recorded here: the complete ESS characterization for all `V, C > 0`. The book was not read; the
statement follows lecture notes and the Encyclopedia of Mathematics entry on evolutionarily stable
strategies; Maynard Smith and Price (1973) introduce the game but do not contain this result.

Sources: J. Maynard Smith, *Evolution and the Theory of Games*, Cambridge Univ. Press (1982),
Ch. 2; J. Maynard Smith and G. R. Price, "The logic of animal conflict", Nature 246 (1973)
15–18, doi:10.1038/246015a0.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.HawkDoveWanted

/-- The expected payoff `E(p, q)` of playing Hawk with probability `p` against an opponent playing
Hawk with probability `q`: `p q (V - C)/2 + p (1 - q) V + (1 - p)(1 - q) V/2`. -/
noncomputable def payoff (V C p q : ℝ) : ℝ :=
  p * q * ((V - C) / 2) + p * (1 - q) * V + (1 - p) * (1 - q) * (V / 2)

/-- `p ∈ [0, 1]` is an **evolutionarily stable strategy** (Maynard Smith): for every `q ∈ [0, 1]`
with `q ≠ p`, either `E(q, p) < E(p, p)`, or `E(q, p) = E(p, p)` and `E(q, q) < E(p, q)`. -/
def IsESS (V C p : ℝ) : Prop :=
  0 ≤ p ∧ p ≤ 1 ∧ ∀ q : ℝ, 0 ≤ q → q ≤ 1 → q ≠ p →
    payoff V C q p < payoff V C p p ∨
      (payoff V C q p = payoff V C p p ∧ payoff V C q q < payoff V C p q)

/-- **Hawk–Dove with costly fights** (Maynard Smith 1982, Ch. 2): let `V > 0` and `C > V`. A
mixed strategy `p` is an ESS if and only if `p = V / C`; in particular neither pure Hawk (`p = 1`)
nor pure Dove (`p = 0`) is an ESS.

Source: Maynard Smith (1982), Ch. 2. -/
public theorem_wanted isESS_iff_of_lt (V C : ℝ) (hV : 0 < V) (hVC : V < C) (p : ℝ) :
    IsESS V C p ↔ p = V / C

/-- **Hawk–Dove with cheap fights** (Maynard Smith 1982, Ch. 2): let `C > 0` and `V ≥ C`. A mixed
strategy `p` is an ESS if and only if `p = 1` (pure Hawk).

Source: Maynard Smith (1982), Ch. 2. -/
public theorem_wanted isESS_iff_of_le (V C : ℝ) (hC : 0 < C) (hCV : C ≤ V) (p : ℝ) :
    IsESS V C p ↔ p = 1

end WantedExt.Biology.Ecology.HawkDoveWanted
