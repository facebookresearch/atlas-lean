/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.ProbabilityMassFunction.Expectation

/-!
# Oblivious adversarial bandits

In a `k`-armed oblivious adversarial bandit with horizon `n`, an adversary fixes a reward table
`x = (x_{t,i})`, the reward `x_{t,i}` of arm `i` in round `t`, before play begins. In each round a
randomized policy chooses an arm from its past choices and the rewards it observed, and then
observes only the reward of the arm it chose. The regret of the policy `π` on the table `x` is

  `R_n(π, x) = max_i ∑_t x_{t,i} - 𝔼[∑_t x_{t,A_t}]`,

the expectation being over the policy's internal randomization (Lattimore and Szepesvári,
Section 11.1).

## Main definitions

* `Policy k`: for each round and each history of the earlier arms and observed rewards, a
  probability mass function on the arms.
* `history x a`: the history `(a_1, x_{1,a_1}, …, a_n, x_{n,a_n})` of playing the arms `a` on
  the table `x`.
* `actionLaw π x`: the law of the arms `(A_1, …, A_n)` chosen when `π` plays on `x`, a
  probability mass function on `Fin n → Fin k`, built by drawing one arm after the other.
* `regret π x`: the regret `R_n(π, x)`, with the expectation `PMF.expect` under `actionLaw π x`.

`expect_actionLaw_succ` computes an expectation under the action law of `n + 1` rounds from the
one of `n` rounds.

## Conventions

Arms and rounds are counted from `0`: the arm `i ∈ {1, …, k}` of the source is stored as
`i - 1`, the round `t ∈ {1, …, n}` as `t - 1`, so the source's `x_{t,i}` is `x (t - 1) (i - 1)`
for a table `x : Fin n → Fin k → ℝ`, and the policy's distribution `π t h` at a history `h` of
`t` rounds is the source's `π_{t+1}(· | h)`. A policy is a sequence over all rounds, so the same
policy runs for every horizon; the horizon `n = 0` is allowed.

The source takes the rewards in `[0, 1]`. Here a reward table is any real table
`Fin n → Fin k → ℝ`: the definitions make sense for every such table, and results that need the
range `[0, 1]` take it as a hypothesis. The policy needs no measurability: on a fixed table, only
the finitely many histories `history x a` occur. The regret is not always nonnegative: an
adaptive policy can collect more reward than every fixed arm on a given table. On the two-armed
table whose rewards are `(1, 0)` in the first round and `(0, 1)` in the second, each arm collects
`1`, while the policy that plays the first arm and then switches to the second after observing the
reward `1` collects `2`: its regret is `-1`.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 11.1 (adversarial bandits, policies and the regret (11.1)) and Section 11.5, Notes 4
  (oblivious adversaries) and 12 (no measurability condition on the policy).
-/

@[expose] public section

open Finset

namespace Cslib.MachineLearning.Bandit.Adversarial

/-- **Policy for an oblivious adversarial bandit** (Lattimore and Szepesvári, Section 11.1). A
policy for `k` arms gives, for each round `t` and each history `h : Fin t → Fin k × ℝ` of the `t`
earlier rounds, the pairs `(a_s, r_s)` of the arm chosen and the reward observed, a probability
mass function `π t h` on the arms: the law of the arm chosen next. The sequence runs over all
rounds, so the same policy serves every horizon. No measurability is required: on a fixed reward
table only finitely many histories occur. Rounds and arms are counted from `0`, the arm
`i ∈ {1, …, k}` being stored as `i - 1`: `π t h` is the source's `π_{t+1}(· | h)`, which reads a
history of `t` rounds. -/
abbrev Policy (k : ℕ) : Type := (t : ℕ) → (Fin t → Fin k × ℝ) → PMF (Fin k)

variable {k n : ℕ}

/-- **History of play on a reward table.** The history of playing the arms `a = (a_1, …, a_n)` on
the reward table `x = (x_{t,i})` is the sequence of pairs `(a_s, x_{s,a_s})` of the arm chosen and
the reward observed in each round `s`: a policy that chooses these arms on `x` observes exactly
this history. Rounds and arms are counted from `0`: the coordinate `s` holds round `s + 1`. -/
def history (x : Fin n → Fin k → ℝ) (a : Fin n → Fin k) : Fin n → Fin k × ℝ :=
  fun s ↦ (a s, x s (a s))

@[simp]
theorem history_apply (x : Fin n → Fin k → ℝ) (a : Fin n → Fin k) (s : Fin n) :
    history x a s = (a s, x s (a s)) := rfl

/-- **Action law of a policy on a reward table.** Fix `k` arms, a horizon `n`, a real reward table
`x = (x_{t,i})` and a policy `π`. The action law is the law of the arms `(A_1, …, A_n)` that `π`
chooses when it plays on `x`: `A_1` has law `π_1(· | ∅)`, and given `A_1, …, A_t`, the arm
`A_{t+1}` has law `π_{t+1}(· | A_1, x_{1,A_1}, …, A_t, x_{t,A_t})`. It is defined by recursion
on `n`: the action law of `n + 1` rounds draws the first `n` arms from the action law of `n`
rounds, then an arm from `π_{n+1}` at the history they produce, and appends it. For `n = 0` it is
the point mass at the empty sequence. Rounds and arms are counted from `0`: the coordinate `t` of
the arm sequence is `A_{t+1} - 1`. -/
noncomputable def actionLaw (π : Policy k) :
    {n : ℕ} → (Fin n → Fin k → ℝ) → PMF (Fin n → Fin k)
  | 0, _ => PMF.pure default
  | n + 1, x => (actionLaw π (Fin.init x)).bind fun a ↦
      (π n (history (Fin.init x) a)).map fun i ↦ (Fin.snoc a i : Fin (n + 1) → Fin k)

@[simp]
theorem actionLaw_zero (π : Policy k) (x : Fin 0 → Fin k → ℝ) :
    actionLaw π x = PMF.pure default := rfl

theorem actionLaw_succ (π : Policy k) (x : Fin (n + 1) → Fin k → ℝ) :
    actionLaw π x = (actionLaw π (Fin.init x)).bind fun a ↦
      (π n (history (Fin.init x) a)).map fun i ↦ (Fin.snoc a i : Fin (n + 1) → Fin k) := rfl

/- The expectation of a function under a `PMF.bind`, on finite types. -/
private theorem expect_bind {α β : Type*} [Finite α] [Finite β] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace β] [MeasurableSingletonClass β]
    (p : PMF α) (f : α → PMF β) (g : β → ℝ) :
    (p.bind f).expect g = p.expect fun a ↦ (f a).expect g := by
  have := Fintype.ofFinite α
  have := Fintype.ofFinite β
  simp_rw [PMF.expect_eq_sum, PMF.bind_apply, tsum_fintype, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [ENNReal.toReal_sum fun a _ ↦ ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    (PMF.apply_ne_top _ _), Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ ↦ by rw [ENNReal.toReal_mul, mul_assoc]

/- An expectation under the action law of `n + 1` rounds is the expectation, under the action law
of the first `n` rounds, of the expectation over the arm of the last round. -/
theorem expect_actionLaw_succ (π : Policy k) (x : Fin (n + 1) → Fin k → ℝ)
    (f : (Fin (n + 1) → Fin k) → ℝ) :
    (actionLaw π x).expect f = (actionLaw π (Fin.init x)).expect fun a ↦
      (π n (history (Fin.init x) a)).expect fun i ↦ f (Fin.snoc a i) := by
  rw [actionLaw_succ, expect_bind]
  simp_rw [PMF.expect_map]
  rfl

/-- **Regret in an oblivious adversarial bandit** (Lattimore and Szepesvári, Section 11.1). Fix
`k ≥ 1` arms, a horizon `n`, a reward table `x = (x_{t,i})` fixed in advance by the adversary and
a policy `π`. The regret of `π` on `x` is
`R_n(π, x) = max_i ∑_t x_{t,i} - 𝔼[∑_t x_{t,A_t}]`,
where `(A_1, …, A_n)` has the action law of `π` on `x` (`actionLaw π x`) and the expectation is
the expectation under that probability mass function (`PMF.expect`). The source takes
`x ∈ [0, 1]^{n × k}`; the definition applies to every real table, and results that need the
range take it as a hypothesis. The regret can be negative: an adaptive policy can collect more
reward than every fixed arm. Rounds and arms are counted from `0`: the source's `x_{t,i}` is
`x (t - 1) (i - 1)`. -/
noncomputable def regret [NeZero k] (π : Policy k) (x : Fin n → Fin k → ℝ) : ℝ :=
  univ.sup' univ_nonempty (fun i ↦ ∑ t, x t i) - (actionLaw π x).expect fun a ↦ ∑ t, x t (a t)

end Cslib.MachineLearning.Bandit.Adversarial
