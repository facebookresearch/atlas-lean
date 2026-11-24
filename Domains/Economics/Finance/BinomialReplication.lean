/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Replication by backward induction in the multi-period binomial model

A stock moves up by the factor `u` or down by the factor `d` each period, and a riskless asset
returns `R` per period. Market histories are lists of moves, most recent first (`true` is an up
move). A contingent claim `V` paid at horizon `N` may depend on the whole history. Backward
induction with the risk-neutral up probability `(R - d) / (u - d)` assigns a value to every node;
holding, over each period, the change in claim value divided by the change in stock price across
the two successor nodes (the delta hedge) and keeping the rest of the wealth in the riskless asset
is a self-financing strategy. Started with the claim's value at the root, its wealth equals the
claim value at every node and the claim itself at the horizon.

The holdings at a node depend only on the history up to that node, and are fixed before the next
price move. The construction needs only that prices never vanish (`S₀, u, d ≠ 0`), that the two
successors differ (`u ≠ d`) and that `R ≠ 0`; the no-arbitrage condition `d < R < u` (positive
risk-neutral probabilities) is not needed for replication and is not assumed.

## Main definitions

* `price S₀ u d s`: the stock price after history `s`.
* `rnProb u d R`: the risk-neutral up probability `(R - d) / (u - d)`.
* `claimValue u d R V k s`: the backward-induction value with `k` periods left.
* `hedgeRatio S₀ u d R V N s`: the delta hedge at history `s` for horizon `N`.
* `wealth S₀ u d R x₀ δ s`: the wealth of the self-financing strategy `δ` from capital `x₀`.

## Main results

* `wealth_hedgeRatio_eq_claimValue`: the delta-hedging wealth equals the claim value at every node
  up to the horizon.
* `wealth_hedgeRatio_replicates`: it equals the claim at the horizon (replication).

## References

* J. C. Cox, S. A. Ross, M. Rubinstein, *Option pricing: a simplified approach*, J. Financial
  Economics 7 (1979), 229–263.
* S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*, Springer
  (2004), Theorem 1.2.2.
-/

@[expose] public section

namespace MathlibExt.Probability.Finance.BinomialReplication

/-- Stock price in the binomial tree at the node reached by the history `s` of moves (most recent
move first; `true` is an up move by the factor `u`, `false` a down move by the factor `d`),
starting from the initial price `S₀`. -/
def price (S₀ u d : ℝ) : List Bool → ℝ
  | [] => S₀
  | true :: s => u * price S₀ u d s
  | false :: s => d * price S₀ u d s

/-- The risk-neutral up probability `(R - d) / (u - d)` for the per-period gross riskless return
`R`. -/
noncomputable def rnProb (u d R : ℝ) : ℝ :=
  (R - d) / (u - d)

/-- Backward induction for a path-dependent claim `V` paid at the horizon: with `k` periods left at
history `s`, the claim value is `V s` when `k = 0`, and otherwise the discounted risk-neutral
average of the two successor values. -/
noncomputable def claimValue (u d R : ℝ) (V : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, s => V s
  | k + 1, s =>
    (rnProb u d R * claimValue u d R V k (true :: s) +
      (1 - rnProb u d R) * claimValue u d R V k (false :: s)) / R

/-- The delta-hedging ratio for horizon `N` at history `s` (time `s.length < N`): the number of
shares held over the next period, the change in claim value divided by the change in stock price
across the two successor nodes. It depends only on the history up to now (nonanticipating). -/
noncomputable def hedgeRatio (S₀ u d R : ℝ) (V : List Bool → ℝ) (N : ℕ) (s : List Bool) : ℝ :=
  (claimValue u d R V (N - s.length - 1) (true :: s) -
      claimValue u d R V (N - s.length - 1) (false :: s)) /
    (price S₀ u d (true :: s) - price S₀ u d (false :: s))

/-- Wealth of the self-financing strategy with initial capital `x₀` that holds `δ s` shares over
the period following history `s` and keeps the rest in the riskless asset with gross return `R`:
`X_{t+1} = δ_t S_{t+1} + R (X_t - δ_t S_t)`. -/
def wealth (S₀ u d R x₀ : ℝ) (δ : List Bool → ℝ) : List Bool → ℝ
  | [] => x₀
  | b :: s => δ s * price S₀ u d (b :: s) + R * (wealth S₀ u d R x₀ δ s - δ s * price S₀ u d s)

/-- Prices never vanish when the initial price and both move factors are nonzero. -/
theorem price_ne_zero (S₀ u d : ℝ) (hS₀ : S₀ ≠ 0) (hu : u ≠ 0) (hd : d ≠ 0)
    (s : List Bool) : price S₀ u d s ≠ 0 := by
  induction s with
  | nil =>
    simp only [price]
    exact hS₀
  | cons b t ih =>
    cases b
    · simp only [price]
      exact mul_ne_zero hd ih
    · simp only [price]
      exact mul_ne_zero hu ih

/-- Along every history of length at most `N`, the self-financing delta-hedging strategy started
with the backward-induction value `claimValue u d R V N []` has wealth equal to the claim value at
that node. -/
theorem wealth_hedgeRatio_eq_claimValue {S₀ u d R : ℝ} (hS₀ : S₀ ≠ 0) (hu : u ≠ 0) (hd : d ≠ 0)
    (hud : u ≠ d) (hR : R ≠ 0) (V : List Bool → ℝ) (N : ℕ) (s : List Bool)
    (hs : s.length ≤ N) :
    wealth S₀ u d R (claimValue u d R V N []) (hedgeRatio S₀ u d R V N) s =
      claimValue u d R V (N - s.length) s := by
  revert hs
  induction s with
  | nil =>
    intro _
    simp only [wealth]
    rw [show List.length ([] : List Bool) = 0 from rfl, Nat.sub_zero]
  | cons b t ih =>
    intro hs
    rw [List.length_cons] at hs
    have hs' : t.length ≤ N := by omega
    have ih' := ih hs'
    have hNt : N - t.length = (N - t.length - 1) + 1 := by omega
    have hNb : N - (b :: t).length = N - t.length - 1 := by
      rw [List.length_cons]
      omega
    rw [hNb]
    rw [hNt] at ih'
    simp only [wealth]
    rw [ih']
    have hS : price S₀ u d t ≠ 0 := price_ne_zero S₀ u d hS₀ hu hd t
    have hud' : u - d ≠ 0 := sub_ne_zero.mpr hud
    have hden : u * price S₀ u d t - d * price S₀ u d t ≠ 0 := by
      have heq : u * price S₀ u d t - d * price S₀ u d t = (u - d) * price S₀ u d t := by
        ring
      rw [heq]
      exact mul_ne_zero hud' hS
    cases b
    · simp only [claimValue, hedgeRatio, rnProb, price]
      field_simp
      ring
    · simp only [claimValue, hedgeRatio, rnProb, price]
      field_simp
      ring

/-- **Replication in the multi-period binomial model** (Cox, Ross and Rubinstein 1979): every
path-dependent claim `V` paid at horizon `N` is replicated by the self-financing delta-hedging
strategy started with its backward-induction value: the terminal wealth equals `V` on every
history of length `N`. -/
theorem wealth_hedgeRatio_replicates {S₀ u d R : ℝ} (hS₀ : S₀ ≠ 0) (hu : u ≠ 0) (hd : d ≠ 0)
    (hud : u ≠ d) (hR : R ≠ 0) (V : List Bool → ℝ) (N : ℕ) (s : List Bool)
    (hs : s.length = N) :
    wealth S₀ u d R (claimValue u d R V N []) (hedgeRatio S₀ u d R V N) s = V s := by
  have h := wealth_hedgeRatio_eq_claimValue hS₀ hu hd hud hR V N s hs.le
  rw [hs, Nat.sub_self] at h
  simp only [claimValue] at h
  exact h

end MathlibExt.Probability.Finance.BinomialReplication
