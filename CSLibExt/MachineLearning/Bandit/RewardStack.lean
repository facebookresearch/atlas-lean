/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.MachineLearning.Bandit.CanonicalModel
public import Mathlib.Probability.Independence.InfinitePi

/-!
# The reward-stack model of a stochastic bandit

In the reward-stack model of a stochastic `k`-armed bandit `ν = (P_1, …, P_k)` played by a
policy `π`, every arm `i` has a stack of rewards `X_{1,i}, X_{2,i}, …`, all mutually independent
with `X_{s,i} ~ P_i`, drawn before the first round. At each round the arm `A_t` is drawn from the
policy's kernel applied to the history so far, and the reward is the next unused entry of the
chosen arm's stack. `rewardStackLaw ν π n` is the joint law of the stacks and of the history of
the first `n` rounds.

## Main definitions

* `rewardStackLaw ν π n`: the reward-stack model, a probability measure on
  `(ℕ → Fin k → ℝ) × History k n`.

## Main statements

* `rewardStackLaw_zero`, `rewardStackLaw_succ`: the recursion that defines the model.
* `map_stack_apply`, `iIndepFun_stack`: under the law of the stacks, each entry `x s i` has the
  reward law `P_i` of its arm, and the entries are mutually independent.
* `map_fst_rewardStackLaw`: the stacks keep their law, the product of the reward laws, at every
  horizon.
* `map_take_rewardStackLaw`: restricting the history to its first `m ≤ n` rounds gives the
  reward-stack model of horizon `m`, with the same stacks.
* `map_take_action_rewardStackLaw`: the joint law of the stacks, the history before a round and
  the arm chosen in it is the composition-product of the reward-stack model of the earlier
  rounds with the policy's kernel, which reads the history only.
* `ae_reward_eq_stack`: almost surely, the reward of each round is the entry of the
  chosen arm's stack just after those already used.

## Conventions

As in `CSLibExt.MachineLearning.Bandit.CanonicalModel`, arms and rounds are counted from `0`, and
so are the positions in a stack: for a stack `x : ℕ → Fin k → ℝ`, the entry `x s a` is the
source's `X_{s+1, a+1}`. At round `t + 1`, after a history `h` of `t` rounds, the chosen arm `a`
has been pulled `pullCount a h` times, so the reward is `x (pullCount a h) a`; in the source's
notation, `X_t = X_{T_{A_t}(t), A_t}`, where `T_i(t)` counts the rounds among `1, …, t` in which
arm `i` is chosen. Only the first `n` entries of each stack are read in `n` rounds. The stacks
are infinite, so that the same stacks serve every horizon, as the same policy does, and the
model of a horizon is the restriction of the model of every longer horizon. The source's stacks
hold `n` entries and its arms are measurable functions of the history: that model is the case
of a policy whose kernels are point masses, with each stack cut to its first `n` entries.

## Construction

`rewardStackLaw ν π 0` is the product law `⨂_s ⨂_i P_i` of the stacks with the empty history.
`rewardStackLaw ν π (n + 1)` is the image of the composition-product of `rewardStackLaw ν π n`
with the policy's kernel `π.kernel n`, applied to the history and ignoring the stacks, under
the map that keeps the stacks and appends to the history the chosen arm and the next unused
entry of its stack. Drawing the arm from the kernel plays the role of the policy's internal
randomization, independent of the stacks given the history.

## References

* T. Lattimore and Cs. Szepesvári, *Bandit Algorithms*, Cambridge University Press, 2020,
  Section 4.6 (the reward-stack model) and Exercise 4.4.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset

namespace Cslib.MachineLearning.Bandit

variable {k : ℕ}

section Measurability

/- Reading a stack at a position and an arm is measurable in the stack, the position and the
arm. -/
private theorem measurable_stack_apply :
    Measurable (fun p : (ℕ → Fin k → ℝ) × (ℕ × Fin k) ↦ p.1 p.2.1 p.2.2) :=
  measurable_from_prod_countable_left fun q ↦
    (measurable_pi_apply q.2).comp (measurable_pi_apply q.1)

/- The reward of the round after a history `h`, when arm `a` is chosen: the entry of `a`'s stack
just after the `pullCount a h` entries already used. -/
private theorem measurable_stack_next (t : ℕ) :
    Measurable (fun p : ((ℕ → Fin k → ℝ) × History k t) × Fin k ↦
      p.1.1 (pullCount p.2 p.1.2) p.2) := by
  have hc : Measurable (fun p : ((ℕ → Fin k → ℝ) × History k t) × Fin k ↦ pullCount p.2 p.1.2) :=
    measurable_from_prod_countable_left fun a ↦ (measurable_pullCount a).comp measurable_snd
  exact measurable_stack_apply.comp (measurable_fst.fst.prodMk (hc.prodMk measurable_snd))

/- The step of round `t + 1`: the stacks are kept, and the chosen arm and the next unused entry
of its stack are appended to the history. -/
private theorem measurable_step (t : ℕ) :
    Measurable (fun p : ((ℕ → Fin k → ℝ) × History k t) × Fin k ↦
      (p.1.1, (Fin.snoc p.1.2 (p.2, p.1.1 (pullCount p.2 p.1.2) p.2) : History k (t + 1)))) :=
  measurable_fst.fst.prodMk ((History.measurable_snoc t).comp
    ((measurable_fst.snd.prodMk measurable_snd).prodMk (measurable_stack_next t)))

end Measurability

variable (ν : StochasticBandit k) (π : Policy k)

/-- **Reward-stack model of a stochastic bandit.** Fix a stochastic `k`-armed bandit
`ν = (P_1, …, P_k)`, a policy `π = (π_t)` and a horizon `n`. Every arm `i` has a stack of rewards
`X_{1,i}, X_{2,i}, …`, and the random variables `X_{s,i}` (`s ≥ 1`, `1 ≤ i ≤ k`) are mutually
independent with `X_{s,i} ~ P_i`. At round `t`, given the stacks and the history
`(A_1, X_1, …, A_{t-1}, X_{t-1})`, the arm `A_t` is drawn from
`π_t(· | A_1, X_1, …, A_{t-1}, X_{t-1})`, so that it depends on the stacks only through the
history, and the reward is `X_t = X_{T_{A_t}(t), A_t}`, the next unused entry of the chosen arm's
stack, where `T_i(t)` is the number of rounds among `1, …, t` in which arm `i` is chosen.
`rewardStackLaw ν π n` is the joint law of the stacks and of the history
`(A_1, X_1, …, A_n, X_n)`; for `n = 0` it is the law of the stacks with the empty history. Only
the first `n` entries of each stack are read in `n` rounds. In the source, the stacks hold `n`
entries and each arm `A_t` is a measurable function of `(A_1, X_1, …, A_{t-1}, X_{t-1})`: that
model is the case of a policy whose kernels are point masses, with each stack cut to its first `n`
entries. In Lean, positions, arms and rounds are counted from `0`: a stack is
`x : ℕ → Fin k → ℝ`, whose entry `x s a` is `X_{s+1, a+1}`, the coordinate `t : Fin n` of the
history holds round `t + 1`, `π.kernel t` is `π_{t+1}`, and the reward of round `t + 1`, after a
history `h` of `t` rounds in which the chosen arm `a` was pulled `pullCount a h` times, is
`x (pullCount a h) a`. -/
noncomputable def rewardStackLaw : (n : ℕ) → Measure ((ℕ → Fin k → ℝ) × History k n)
  | 0 => (Measure.infinitePi fun _ : ℕ ↦ Measure.pi ν.law).map fun x ↦ (x, default)
  | n + 1 => (rewardStackLaw n ⊗ₘ Kernel.prodMkLeft (ℕ → Fin k → ℝ) (π.kernel n)).map
      fun p ↦ (p.1.1, Fin.snoc p.1.2 (p.2, p.1.1 (pullCount p.2 p.1.2) p.2))

@[simp]
theorem rewardStackLaw_zero :
    rewardStackLaw ν π 0 =
      (Measure.infinitePi fun _ : ℕ ↦ Measure.pi ν.law).map fun x ↦ (x, default) := rfl

theorem rewardStackLaw_succ (n : ℕ) :
    rewardStackLaw ν π (n + 1) =
      (rewardStackLaw ν π n ⊗ₘ Kernel.prodMkLeft (ℕ → Fin k → ℝ) (π.kernel n)).map
        fun p ↦ (p.1.1, Fin.snoc p.1.2 (p.2, p.1.1 (pullCount p.2 p.1.2) p.2)) := rfl

instance isProbabilityMeasure_rewardStackLaw (n : ℕ) :
    IsProbabilityMeasure (rewardStackLaw ν π n) := by
  induction n with
  | zero => rw [rewardStackLaw_zero]; infer_instance
  | succ n ih => rw [rewardStackLaw_succ]; infer_instance

section Stacks

/- Under the law of the stacks, the product of the reward laws over all positions and arms, the
entry `x s i` has the reward law `P_i` of its arm. -/
theorem map_stack_apply (s : ℕ) (i : Fin k) :
    (Measure.infinitePi fun _ : ℕ ↦ Measure.pi ν.law).map (fun x ↦ x s i) = ν.law i := by
  have key : (fun x : ℕ → Fin k → ℝ ↦ x s i) = (fun y : Fin k → ℝ ↦ y i) ∘ fun x ↦ x s := rfl
  rw [key, ← Measure.map_map (measurable_pi_apply i) (measurable_pi_apply s),
    Measure.infinitePi_map_eval, ← Measure.infinitePi_eq_pi, Measure.infinitePi_map_eval]

/- Under the law of the stacks, the entries `x s i`, for all positions `s` and arms `i`, are
mutually independent. -/
theorem iIndepFun_stack :
    iIndepFun (fun (p : ℕ × Fin k) (x : ℕ → Fin k → ℝ) ↦ x p.1 p.2)
      (Measure.infinitePi fun _ : ℕ ↦ Measure.pi ν.law) := by
  rw [iIndepFun_iff_map_fun_eq_infinitePi_map fun p ↦
    (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)]
  simp_rw [map_stack_apply, ← Measure.infinitePi_eq_pi]
  exact Measure.infinitePi_map_curry_symm fun (_ : ℕ) (j : Fin k) ↦ ν.law j

end Stacks

section Marginals

/- Restricting a history to its first `m` rounds forgets a round appended after them. -/
private theorem take_snoc {n m : ℕ} (hm : m ≤ n) (h : History k n) (x : Fin k × ℝ) :
    Fin.take m (hm.trans n.le_succ) (Fin.snoc h x : History k (n + 1)) = Fin.take m hm h := by
  rw [← Fin.take_init m hm, Fin.init_snoc]

/- The stacks keep their law at every horizon: the image of the reward-stack model under the
projection to the stacks is the product of the reward laws over all positions and arms. -/
theorem map_fst_rewardStackLaw (n : ℕ) :
    (rewardStackLaw ν π n).map Prod.fst = Measure.infinitePi fun _ : ℕ ↦ Measure.pi ν.law := by
  induction n with
  | zero =>
    rw [rewardStackLaw_zero, Measure.map_map measurable_fst (by fun_prop)]
    exact Measure.map_id
  | succ n ih =>
    have key : (Prod.fst ∘ fun p : ((ℕ → Fin k → ℝ) × History k n) × Fin k ↦
        (p.1.1, (Fin.snoc p.1.2 (p.2, p.1.1 (pullCount p.2 p.1.2) p.2) : History k (n + 1)))) =
        Prod.fst ∘ Prod.fst := rfl
    rw [rewardStackLaw_succ, Measure.map_map measurable_fst (measurable_step n), key,
      ← Measure.map_map measurable_fst measurable_fst]
    exact (congrArg (Measure.map Prod.fst) (Measure.fst_compProd _ _)).trans ih

/- The image of the reward-stack model of horizon `n` under the restriction of the history to
its first `m ≤ n` rounds, the stacks being kept, is the reward-stack model of horizon `m`. -/
theorem map_take_rewardStackLaw {n m : ℕ} (hm : m ≤ n) :
    (rewardStackLaw ν π n).map (Prod.map id (Fin.take m hm)) = rewardStackLaw ν π m := by
  induction n with
  | zero =>
    obtain rfl := Nat.le_zero.1 hm
    have : (Prod.map id (Fin.take 0 hm) : (ℕ → Fin k → ℝ) × History k 0 → _) = id :=
      funext fun p ↦ Prod.ext rfl (Fin.take_eq_self p.2)
    rw [this, Measure.map_id]
  | succ n ih =>
    rcases Nat.of_le_succ hm with hm' | rfl
    · have key : (Prod.map id (Fin.take m hm) ∘ fun p : ((ℕ → Fin k → ℝ) × History k n) × Fin k ↦
          (p.1.1, (Fin.snoc p.1.2 (p.2, p.1.1 (pullCount p.2 p.1.2) p.2) : History k (n + 1)))) =
          Prod.map id (Fin.take m hm') ∘ Prod.fst := by
        funext p
        exact Prod.ext rfl (take_snoc hm' _ _)
      rw [rewardStackLaw_succ, Measure.map_map
        (measurable_id.prodMap (History.measurable_take _ _)) (measurable_step n), key,
        ← Measure.map_map (measurable_id.prodMap (History.measurable_take _ _)) measurable_fst]
      exact (congrArg (Measure.map (Prod.map id (Fin.take m hm')))
        (Measure.fst_compProd _ _)).trans (ih hm')
    · have : (Prod.map id (Fin.take (n + 1) hm) :
          (ℕ → Fin k → ℝ) × History k (n + 1) → _) = id :=
        funext fun p ↦ Prod.ext rfl (Fin.take_eq_self p.2)
      rw [this, Measure.map_id]

/- The last round of a history of `t + 1` rounds, split off: the stacks with the history of the
first `t` rounds, and the arm chosen in round `t + 1`. It undoes the step of round `t + 1`. -/
private theorem measurable_split_last (t : ℕ) :
    Measurable (fun p : (ℕ → Fin k → ℝ) × History k (t + 1) ↦
      ((p.1, (Fin.init p.2 : History k t)), (p.2 (Fin.last t)).1)) :=
  (measurable_fst.prodMk (measurable_pi_iff.2 fun _ ↦ (measurable_pi_apply _).comp
    measurable_snd)).prodMk ((measurable_pi_apply _).comp measurable_snd).fst

/- The joint law of the stacks, the history of the rounds before `t` and the arm chosen at round
`t` (counted from zero) is the composition-product of the reward-stack model of horizon `t` with
the policy's kernel `π.kernel t`, which reads the history and ignores the stacks. -/
theorem map_take_action_rewardStackLaw {n : ℕ} (t : Fin n) :
    (rewardStackLaw ν π n).map (fun p ↦ ((p.1, Fin.take t t.isLt.le p.2), (p.2 t).1)) =
      rewardStackLaw ν π t ⊗ₘ Kernel.prodMkLeft (ℕ → Fin k → ℝ) (π.kernel t) := by
  have key : (fun p : (ℕ → Fin k → ℝ) × History k n ↦
      ((p.1, Fin.take t t.isLt.le p.2), (p.2 t).1)) =
      (fun p : (ℕ → Fin k → ℝ) × History k (t + 1) ↦
        ((p.1, (Fin.init p.2 : History k t)), (p.2 (Fin.last t)).1)) ∘
        Prod.map id (Fin.take (t + 1) t.isLt) := by
    funext p
    refine Prod.ext (Prod.ext rfl (funext fun i ↦ ?_)) rfl
    simp [Fin.take_apply, Fin.init]
  have key' : (fun p : (ℕ → Fin k → ℝ) × History k (t + 1) ↦
      ((p.1, (Fin.init p.2 : History k t)), (p.2 (Fin.last t)).1)) ∘
      (fun p : ((ℕ → Fin k → ℝ) × History k t) × Fin k ↦
        (p.1.1, (Fin.snoc p.1.2 (p.2, p.1.1 (pullCount p.2 p.1.2) p.2) : History k (t + 1)))) =
      id := by
    funext p
    simp
  rw [key, ← Measure.map_map (measurable_split_last t)
    (measurable_id.prodMap (History.measurable_take _ _)), map_take_rewardStackLaw,
    rewardStackLaw_succ, Measure.map_map (measurable_split_last t) (measurable_step t), key',
    Measure.map_id]

/- Under the reward-stack model, almost surely, the reward of round `t` (counted from zero) is
the entry of the chosen arm's stack at the position `pullCount a h`, where `a` is the arm chosen
at round `t` and `h` the history of the earlier rounds: the next unused entry of `a`'s
stack. -/
theorem ae_reward_eq_stack {n : ℕ} (t : Fin n) :
    ∀ᵐ p ∂rewardStackLaw ν π n,
      (p.2 t).2 = p.1 (pullCount (p.2 t).1 (Fin.take t t.isLt.le p.2)) (p.2 t).1 := by
  have hlast : Measurable (fun q : (ℕ → Fin k → ℝ) × History k (t + 1) ↦
      q.1 (pullCount (q.2 (Fin.last t)).1 (Fin.init q.2 : History k t)) (q.2 (Fin.last t)).1) :=
    (measurable_stack_next t).comp (measurable_split_last t)
  have hS : MeasurableSet {q : (ℕ → Fin k → ℝ) × History k (t + 1) |
      (q.2 (Fin.last t)).2 =
        q.1 (pullCount (q.2 (Fin.last t)).1 (Fin.init q.2 : History k t)) (q.2 (Fin.last t)).1} :=
    measurableSet_eq_fun ((measurable_pi_apply _).comp measurable_snd).snd hlast
  have h : ∀ᵐ q ∂(rewardStackLaw ν π n).map (Prod.map id (Fin.take (t + 1) t.isLt)),
      (q.2 (Fin.last t)).2 =
        q.1 (pullCount (q.2 (Fin.last t)).1 (Fin.init q.2 : History k t)) (q.2 (Fin.last t)).1 := by
    rw [map_take_rewardStackLaw, rewardStackLaw_succ,
      ae_map_iff (measurable_step t).aemeasurable hS]
    exact ae_of_all _ fun p ↦ by simp
  filter_upwards [ae_of_ae_map (measurable_id.prodMap (History.measurable_take _ _)).aemeasurable h]
    with p hp
  have hinit : (Fin.init (Fin.take (t + 1) t.isLt p.2) : History k t) =
      Fin.take t t.isLt.le p.2 :=
    funext fun i ↦ by simp [Fin.init, Fin.take_apply]
  have hlast : (Fin.castLE t.isLt (Fin.last t) : Fin n) = t := Fin.ext rfl
  simpa [Fin.take_apply, hinit, hlast] using hp

end Marginals

end Cslib.MachineLearning.Bandit
