/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-! # No-regret dynamics, coarse correlated equilibria and smoothness

For a finite strategic game in cost form (players `ι`, strategies `S i`, costs
`cost i s`), a probability distribution `μ` on strategy profiles is an `ε`-*coarse
correlated equilibrium* (CCE) when no player can lower its expected cost by more than `ε`
by committing in advance to a fixed strategy `a`, i.e. by replacing its coordinate of
every profile by `a`.

When the game is played repeatedly, `T` rounds with realised profiles
`play 0, …, play (T-1)`, the regret of player `i` against the fixed strategy `a` is
`∑ₜ cost i (play t) − ∑ₜ cost i (play t with i's strategy replaced by a)`. If every
player's regret against every fixed strategy is at most `T ε`, the empirical
distribution of play is an `ε`-CCE. No-regret algorithms such as Hedge make the
average regret `ε` tend to `0`.

Roughgarden's *smoothness*: a game is `(λ, μ)`-smooth if
`∑ᵢ costᵢ(t_i, s_{-i}) ≤ λ C(t) + μ C(s)` for all profiles `s, t`, where
`C = ∑ᵢ costᵢ` is the social cost. For `μ < 1` every CCE then has expected social cost
at most `λ / (1 − μ)` times the cost of any profile (plus an additive approximation term), so the
time-averaged social cost of no-regret dynamics obeys the same price-of-anarchy bound as
pure Nash equilibria. This is the robustness phenomenon that Lykouris, Syrgkanis and
Tardos extend to games with a dynamic population of learners.

## Main results

* `isCoarseCorrelatedEq_empirical`: no-regret play yields an approximate CCE
  (Roughgarden, CS364A Lecture 17, Proposition 3.1).
* `IsSmooth.expected_socialCost_le`: the extension theorem for CCE
  (Roughgarden 2015, Theorem 3.2).
* `IsSmooth.average_socialCost_le`: the repeated version for no-regret dynamics
  (Roughgarden 2015, Theorem 3.3).

## References

* T. Roughgarden, "Intrinsic robustness of the price of anarchy", J. ACM 62(5) (2015),
  Article 32 (STOC 2009): Definition 2.1, Theorems 3.2 and 3.3.
* T. Roughgarden, CS364A *Algorithmic Game Theory*, Lecture #17 "No-regret dynamics",
  Stanford, 2013, Proposition 3.1.
* T. Lykouris, V. Syrgkanis and É. Tardos, "Learning and efficiency in games with dynamic
  population", SODA 2016, arXiv:1505.00391.
-/

namespace MathlibExt.GameTheory.NoRegretDynamics

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {S : ι → Type*} [∀ i, Fintype (S i)]
  [∀ i, DecidableEq (S i)]

/-- `μ` is a probability distribution on the finite set of strategy profiles. -/
def IsDistribution (μ : (∀ i, S i) → ℝ) : Prop :=
  (∀ s, 0 ≤ μ s) ∧ ∑ s, μ s = 1

/-- `μ` is an `ε`-coarse correlated equilibrium: it is a probability distribution on
profiles, and no player lowers its expected cost by more than `ε` by switching to a fixed
strategy `a`. The error `ε` is additive, as in Roughgarden, CS364A Lecture 17,
Proposition 3.1; for `ε = 0` this is the coarse correlated equilibrium of Roughgarden 2015,
§3.1, equation (15). (Roughgarden 2015, §4.1, uses a multiplicative variant instead.) -/
def IsCoarseCorrelatedEq (cost : ι → (∀ i, S i) → ℝ) (μ : (∀ i, S i) → ℝ) (ε : ℝ) :
    Prop :=
  IsDistribution μ ∧
    ∀ i (a : S i), ∑ s, μ s * cost i s ≤ ∑ s, μ s * cost i (Function.update s i a) + ε

/-- The empirical distribution of `T ≥ 1` rounds of play: the fraction of rounds in which the
profile `s` was played. After no rounds, which is excluded, every profile would get probability
`0`. -/
noncomputable def empirical {T : ℕ} [NeZero T] (play : Fin T → ∀ i, S i) (s : ∀ i, S i) : ℝ :=
  (#{t | play t = s} : ℝ) / T

/-- The regret of player `i` against the fixed strategy `a` over the rounds `play`. -/
def regret (cost : ι → (∀ i, S i) → ℝ) {T : ℕ} (play : Fin T → ∀ i, S i) (i : ι)
    (a : S i) : ℝ :=
  ∑ t, cost i (play t) - ∑ t, cost i (Function.update (play t) i a)

/-- Expectations under the empirical distribution are time averages. -/
theorem sum_empirical_mul {T : ℕ} [NeZero T] (play : Fin T → ∀ i, S i) (g : (∀ i, S i) → ℝ) :
    ∑ s, empirical play s * g s = (∑ t, g (play t)) / T := by
  rw [← sum_fiberwise univ play (fun t => g (play t)), sum_div]
  refine sum_congr rfl fun s _ => ?_
  rw [sum_congr rfl fun t (ht : t ∈ univ.filter (fun t => play t = s)) => by
    rw [(mem_filter.1 ht).2], sum_const, nsmul_eq_mul, empirical]
  ring

/-- The empirical distribution of `T ≥ 1` rounds of play is a probability distribution. -/
theorem isDistribution_empirical {T : ℕ} [NeZero T] (play : Fin T → ∀ i, S i) :
    IsDistribution (empirical play) := by
  refine ⟨fun s => by unfold empirical; positivity, ?_⟩
  have := sum_empirical_mul play (fun _ => 1)
  simp only [mul_one, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rw [this]
  have : (T : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne T
  field_simp

/-- **No-regret dynamics converge to coarse correlated equilibria** (Roughgarden, CS364A
Lecture 17, Proposition 3.1): if after `T ≥ 1` rounds every player's regret against every
fixed strategy is at most `T ε`, the empirical distribution of play is an `ε`-CCE. -/
theorem isCoarseCorrelatedEq_empirical {cost : ι → (∀ i, S i) → ℝ} {T : ℕ} [NeZero T]
    {play : Fin T → ∀ i, S i} {ε : ℝ} (hreg : ∀ i a, regret cost play i a ≤ T * ε) :
    IsCoarseCorrelatedEq cost (empirical play) ε := by
  refine ⟨isDistribution_empirical play, fun i a => ?_⟩
  rw [sum_empirical_mul play (cost i),
    sum_empirical_mul play (fun s => cost i (Function.update s i a))]
  have hT' : (0 : ℝ) < T := by exact_mod_cast NeZero.pos T
  have := hreg i a
  unfold regret at this
  rw [div_add' _ _ _ hT'.ne', div_le_div_iff_of_pos_right hT']
  linarith

/-- The social cost `∑ᵢ costᵢ(s)` of a profile. -/
def socialCost (cost : ι → (∀ i, S i) → ℝ) (s : ∀ i, S i) : ℝ :=
  ∑ i, cost i s

/-- A cost-minimisation game is `(λ, μ)`-smooth if `∑ᵢ costᵢ(tᵢ, s₋ᵢ) ≤ λ C(t) + μ C(s)`
for all profiles `s` and `t` (Roughgarden 2015, Definition 2.1). -/
def IsSmooth (cost : ι → (∀ i, S i) → ℝ) (lam mu : ℝ) : Prop :=
  ∀ s t : ∀ i, S i,
    ∑ i, cost i (Function.update s i (t i)) ≤ lam * socialCost cost t + mu * socialCost cost s

omit [∀ i, DecidableEq (S i)] in
/-- **Extension theorem for coarse correlated equilibria** (Roughgarden 2015,
Theorem 3.2, extended to an additive `ε`): in a `(λ, μ)`-smooth game, the
expected social cost `E` of an `ε`-CCE satisfies `(1 − μ) E ≤ λ C(t) + |ι| ε` for every
profile `t`; for `μ < 1` and `ε = 0` this is the robust price-of-anarchy bound
`E ≤ λ / (1 − μ) · C(t)`. -/
theorem IsSmooth.expected_socialCost_le {cost : ι → (∀ i, S i) → ℝ} {lam mu ε : ℝ}
    {σ : (∀ i, S i) → ℝ} (hsm : IsSmooth cost lam mu) (hσ : IsCoarseCorrelatedEq cost σ ε)
    (t : ∀ i, S i) :
    (1 - mu) * ∑ s, σ s * socialCost cost s ≤
      lam * socialCost cost t + Fintype.card ι * ε := by
  have hexp : ∑ s, σ s * socialCost cost s = ∑ i, ∑ s, σ s * cost i s := by
    simp only [socialCost, mul_sum]
    exact sum_comm
  have hdev : ∑ i, ∑ s, σ s * cost i s ≤
      ∑ s, σ s * ∑ i, cost i (Function.update s i (t i)) + Fintype.card ι * ε := by
    calc ∑ i, ∑ s, σ s * cost i s
        ≤ ∑ i, (∑ s, σ s * cost i (Function.update s i (t i)) + ε) :=
          sum_le_sum fun i _ => hσ.2 i (t i)
      _ = _ := by
          rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_comm]
          simp only [mul_sum]
  have hsmooth : ∑ s, σ s * ∑ i, cost i (Function.update s i (t i)) ≤
      lam * socialCost cost t + mu * ∑ s, σ s * socialCost cost s := by
    calc ∑ s, σ s * ∑ i, cost i (Function.update s i (t i))
        ≤ ∑ s, σ s * (lam * socialCost cost t + mu * socialCost cost s) :=
          sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hsm s t) (hσ.1.1 s)
      _ = _ := by
          simp only [mul_add, sum_add_distrib, ← sum_mul, hσ.1.2, mul_sum]
          congr 1
          · ring
          · exact sum_congr rfl fun s _ => by ring
  rw [← hexp] at hdev
  linarith

omit [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)] in
/-- **Repeated extension theorem** (Roughgarden 2015, Theorem 3.3): in a `(λ, μ)`-smooth
game, if after `T ≥ 1` rounds every player's regret against every fixed strategy is at most
`T ε`, the time-averaged social cost `A` satisfies `(1 − μ) A ≤ λ C(t) + |ι| ε` for every
profile `t`. -/
theorem IsSmooth.average_socialCost_le [∀ i, Finite (S i)] {cost : ι → (∀ i, S i) → ℝ}
    {lam mu ε : ℝ}
    (hsm : IsSmooth cost lam mu) {T : ℕ} (hT : 0 < T) {play : Fin T → ∀ i, S i}
    (hreg : ∀ i a, regret cost play i a ≤ T * ε) (t : ∀ i, S i) :
    (1 - mu) * ((∑ k, socialCost cost (play k)) / T) ≤
      lam * socialCost cost t + Fintype.card ι * ε := by
  classical
  have : ∀ i, Fintype (S i) := fun i => Fintype.ofFinite (S i)
  have : NeZero T := ⟨hT.ne'⟩
  have := hsm.expected_socialCost_le (isCoarseCorrelatedEq_empirical hreg) t
  rwa [sum_empirical_mul] at this

end MathlibExt.GameTheory.NoRegretDynamics
