/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Bounds.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Order.MinMax

@[expose] public section

/-!
# Finite-horizon optimal stopping on a binomial tree

Nodes of a binary (binomial) tree are histories `s : List Bool` of up/down
moves, most recent first. From each node the next move is up with probability
`p` and down with probability `1 - p`, and values one period ahead are
discounted by `disc`. The exercise payoff `g` may depend on the whole history
(path-dependent claims are not reduced to a terminal state).

The Snell envelope `snell p disc g k s` (with `k` periods left) is defined by
backward induction: `g s` at the horizon, and otherwise
`max (g s) (disc * (p * U (up :: s) + (1 - p) * U (down :: s)))`. A
nonanticipating stopping rule decides from the history and the time to go
whether to exercise; `ruleValue` is its expected discounted payoff.

For `0 ≤ p ≤ 1` and `0 ≤ disc`, every stopping rule is worth at most the
envelope (`ruleValue_le_snell`), the rule that exercises as soon as the payoff
reaches the envelope attains it (`ruleValue_snellRule`), and so the envelope is
the optimal stopping value (`isGreatest_snell`). This is the American-exercise
valuation on a binomial tree, stated without measure theory: expectations are
computed by the one-step recursion.

## Main results

* `MathlibExt.Economics.Finance.BinomialOptimalStopping.ruleValue_le_snell`
* `MathlibExt.Economics.Finance.BinomialOptimalStopping.ruleValue_snellRule`
* `MathlibExt.Economics.Finance.BinomialOptimalStopping.isGreatest_snell`

## References

* S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing
  Model*, Springer (2004), Chapter 4 (American derivative securities).
* H. Föllmer and A. Schied, *Stochastic Finance*, de Gruyter, §6.1 (Snell
  envelope).

Atlas roadmap target FI12.T04.
-/

namespace MathlibExt.Economics.Finance.BinomialOptimalStopping

/-- One-period discounted expected continuation value at node `s` of a binary
tree: from `s` the next move is `true` with probability `p` and `false` with
probability `1 - p`, and the value one period later is discounted by `disc`.
Nodes are histories of moves, most recent move first. -/
def continuation (p disc : ℝ) (V : List Bool → ℝ) (s : List Bool) : ℝ :=
  disc * (p * V (true :: s) + (1 - p) * V (false :: s))

/-- Snell envelope by backward induction: with `k` periods left at node `s`,
the value of the optimal stopping problem for the (path-dependent) exercise
payoff `g` is `g s` when no period is left, and otherwise the larger of
exercising now and the discounted expected continuation. -/
def snell (p disc : ℝ) (g : List Bool → ℝ) : ℕ → List Bool → ℝ
  | 0, s => g s
  | k + 1, s => max (g s) (continuation p disc (snell p disc g k) s)

/-- Value of a nonanticipating stopping rule: `stop k s` decides, from the
history `s` and the number `k` of periods left, whether to exercise now;
exercise is forced at the horizon (`k = 0`). -/
def ruleValue (p disc : ℝ) (g : List Bool → ℝ) (stop : ℕ → List Bool → Bool) :
    ℕ → List Bool → ℝ
  | 0, s => g s
  | k + 1, s => if stop (k + 1) s then g s else continuation p disc (ruleValue p disc g stop k) s

/-- The rule that exercises as soon as the payoff reaches the Snell envelope. -/
noncomputable def snellRule (p disc : ℝ) (g : List Bool → ℝ) : ℕ → List Bool → Bool :=
  fun k s => decide (snell p disc g k s ≤ g s)

/-- Every stopping rule is worth at most the Snell envelope (for branch
probabilities in `[0, 1]` and a nonnegative discount factor). -/
theorem ruleValue_le_snell {p disc : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hdisc : 0 ≤ disc)
    (g : List Bool → ℝ) (stop : ℕ → List Bool → Bool) (k : ℕ) (s : List Bool) :
    ruleValue p disc g stop k s ≤ snell p disc g k s := by
  induction k generalizing s with
  | zero =>
    simp only [ruleValue, snell, le_refl]
  | succ k ih =>
    simp only [ruleValue, snell]
    by_cases h : stop (k + 1) s = true
    · rw [ite_eq_left h]
      exact le_max_left _ _
    · rw [ite_eq_right h]
      apply le_trans _ (le_max_right _ _)
      unfold continuation
      apply mul_le_mul_of_nonneg_left _ hdisc
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ hp₀
        exact ih _
      · apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hp₁)
        exact ih _

/-- Exercising when the payoff first reaches the Snell envelope attains it. -/
theorem ruleValue_snellRule (p disc : ℝ) (g : List Bool → ℝ) (k : ℕ) (s : List Bool) :
    ruleValue p disc g (snellRule p disc g) k s = snell p disc g k s := by
  induction k generalizing s with
  | zero =>
    simp only [ruleValue, snell]
  | succ k ih =>
    simp only [ruleValue, snell]
    by_cases h : snell p disc g (k + 1) s ≤ g s
    · have hmax_le : max (g s) (continuation p disc (snell p disc g k) s) ≤ g s := by
        simpa [snell] using h
      have hsnell_eq : max (g s) (continuation p disc (snell p disc g k) s) = g s :=
        le_antisymm hmax_le (le_max_left _ _)
      simp [snellRule, h, hsnell_eq]
    · simp only [snellRule, h, decide_false, Bool.false_eq_true, ↓reduceIte]
      have hmax_nle : ¬ max (g s) (continuation p disc (snell p disc g k) s) ≤ g s := by
        simpa [snell] using h
      have hcont_nle : ¬ continuation p disc (snell p disc g k) s ≤ g s := by
        intro hle
        exact hmax_nle (max_le_iff.mpr ⟨le_refl _, hle⟩)
      have hle : g s ≤ continuation p disc (snell p disc g k) s :=
        le_of_not_ge hcont_nle
      have hsnell_eq : max (g s) (continuation p disc (snell p disc g k) s) =
          continuation p disc (snell p disc g k) s :=
        max_eq_right hle
      rw [hsnell_eq]
      have hfun : ruleValue p disc g (snellRule p disc g) k = snell p disc g k :=
        funext ih
      rw [hfun]

/-- Finite-horizon optimal stopping: the Snell envelope at the root is the
largest value of any nonanticipating stopping rule over horizon `N`, and it
satisfies the recursion `max (exercise, discounted continuation)`. -/
theorem isGreatest_snell {p disc : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (hdisc : 0 ≤ disc)
    (g : List Bool → ℝ) (N : ℕ) :
    IsGreatest (Set.range fun stop : ℕ → List Bool → Bool => ruleValue p disc g stop N [])
      (snell p disc g N []) := by
  constructor
  · exact ⟨snellRule p disc g, ruleValue_snellRule p disc g N []⟩
  · rw [mem_upperBounds]
    intro x hx
    obtain ⟨stop, rfl⟩ := hx
    exact ruleValue_le_snell hp₀ hp₁ hdisc g stop N []

end MathlibExt.Economics.Finance.BinomialOptimalStopping
