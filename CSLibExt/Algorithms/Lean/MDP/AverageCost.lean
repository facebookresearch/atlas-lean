/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.HistoryPolicy
public import Mathlib.Order.LiminfLimsup

import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Verification theorem for average-cost Markov decision processes

For a finite Markov decision process `M` whose field `reward` is read as a cost `c(s, a)`, the
average expected cost of the first `N` steps of a history-dependent randomized policy `π`
(`HistoryPolicy`, with every action available) from the initial state `s₀` is
`(∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t) / N`, where `π.expectedReward M hM s₀ t` is
the expected cost `E[c(S_t, A_t)]` of stage `t` under the finite-history law
`HistoryPolicy.law`. Elsewhere in this library rewards are maximized, with cost `-M.reward`; this
module keeps the cost form of its source, and applying the theorem to the MDP with reward `-r`
gives the reward form, in which the lim sup of the average expected reward `r` is at most `-g`.

## Main results

* `average_cost_verification`: if `g` and `h` satisfy
  `g + h s ≤ c(s, a) + ∑ s', P(s' | s, a) * h s'` for all states `s` and actions `a`, then the
  lim inf of the average expected cost of every history-dependent randomized policy, from every
  initial state, is at least `g`; and if a deterministic stationary policy `σ` attains equality,
  the average expected cost of the policy that plays `σ` in the current state tends to `g` from
  every initial state.

The proof sums the inequality along the trajectory: in expectation,
`N g + h(s₀) ≤ E[∑_{t < N} c(S_t, A_t)] + E[h(S_N)]`, with equality under `σ`, and `h` is
bounded. The averages are bounded too, so the lim inf in `ℝ` is the usual one.

## References

*2.997 Decision-Making in Large-Scale Systems*, Lecture Note 4 (Handout #6), MIT, Spring 2004,
§2, Theorem 1, states the special case in which `g` and `h` satisfy Bellman's equation
`g + h(s) = min_a (c(s, a) + ∑ s', P(s' | s, a) h(s'))`, `σ` is greedy for `h`, the competing
policies are deterministic Markov policies and the average cost is a lim sup.
-/

@[expose] public section

set_option autoImplicit false

open Filter Topology

namespace Cslib.Algorithms.Lean.MarkovDecision

universe u

namespace HistoryPolicy

variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S]

/-- The real masses of a PMF on a finite type sum to one. -/
private theorem sum_toReal_pmf {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 :=
  (isRowStochastic_ofPMF fun _ : Unit => p).2 ()

variable {available : S → Set A} (M : MDP S A ℝ) (hM : M.Stochastic)
  (π : HistoryPolicy available) (s₀ : S)

/-- The expectation of `f` at the state reached after `t` transitions. -/
private noncomputable def stateMean (f : S → ℝ) (t : ℕ) : ℝ :=
  ∑ x : History S A t, (law M hM π s₀ t x).toReal * f (History.last t x)

/-- The expectation of `F` at the state and action of stage `t`. -/
private noncomputable def stepMean (F : S → A → ℝ) (t : ℕ) : ℝ :=
  ∑ x : History S A t, (law M hM π s₀ t x).toReal *
    ∑ a, (π.actionLaw t x a).toReal * F (History.last t x) a

private theorem stateMean_zero (f : S → ℝ) : stateMean M hM π s₀ f 0 = f s₀ := by
  have hlaw (s : S) : (law M hM π s₀ 0 s).toReal = if s = s₀ then 1 else 0 := by
    rw [law_toReal_apply]
    by_cases hs : s = s₀ <;> simp [weight, factors, History.origin, hs]
  change ∑ s : S, (law M hM π s₀ 0 s).toReal * f s = f s₀
  simp [hlaw]

/-- Integrating over the last action and state of a history of `t + 1` transitions. -/
private theorem sum_law_succ (t : ℕ) (F : History S A t → A → S → ℝ) :
    ∑ p : History S A t × (A × S), (law M hM π s₀ (t + 1) p).toReal * F p.1 p.2.1 p.2.2 =
      ∑ x : History S A t, (law M hM π s₀ t x).toReal *
        ∑ a, (π.actionLaw t x a).toReal * ∑ s, M.prob (History.last t x) a s * F x a s := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [law_toReal_apply_succ M hM π s₀ t x a s]
  ring

private theorem expectedReward_eq_stepMean (t : ℕ) :
    π.expectedReward M hM s₀ t = stepMean M hM π s₀ M.reward t := by
  unfold expectedReward stepMean
  rw [sum_law_succ M hM π s₀ t fun x a _ => M.reward (History.last t x) a]
  simp only [← Finset.sum_mul, hM.2, one_mul]

private theorem stateMean_succ (f : S → ℝ) (t : ℕ) :
    stateMean M hM π s₀ f (t + 1) =
      stepMean M hM π s₀ (fun s a => ∑ s', M.prob s a s' * f s') t := by
  change ∑ p : History S A t × (A × S), (law M hM π s₀ (t + 1) p).toReal * f p.2.2 = _
  exact sum_law_succ M hM π s₀ t fun _ _ s => f s

private theorem add_stateMean (g : ℝ) (f : S → ℝ) (t : ℕ) :
    g + stateMean M hM π s₀ f t = stepMean M hM π s₀ (fun s _ => g + f s) t := by
  have hπ (x : History S A t) (c : ℝ) : ∑ a, (π.actionLaw t x a).toReal * c = c := by
    rw [← Finset.sum_mul, sum_toReal_pmf, one_mul]
  unfold stateMean stepMean
  simp only [hπ, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, sum_toReal_pmf, one_mul]

private theorem stepMean_add (F G : S → A → ℝ) (t : ℕ) :
    stepMean M hM π s₀ (fun s a => F s a + G s a) t =
      stepMean M hM π s₀ F t + stepMean M hM π s₀ G t := by
  simp only [stepMean, mul_add, Finset.sum_add_distrib]

private theorem stepMean_mono {F G : S → A → ℝ} (hFG : ∀ s a, F s a ≤ G s a) (t : ℕ) :
    stepMean M hM π s₀ F t ≤ stepMean M hM π s₀ G t :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (hFG _ _) ENNReal.toReal_nonneg)
    ENNReal.toReal_nonneg

private theorem stepMean_of_actionLaw_eq_pure {σ : S → A}
    (hπ : ∀ t x, π.actionLaw t x = PMF.pure (σ (History.last t x))) (F : S → A → ℝ) (t : ℕ) :
    stepMean M hM π s₀ F t =
      ∑ x : History S A t, (law M hM π s₀ t x).toReal *
        F (History.last t x) (σ (History.last t x)) := by
  unfold stepMean
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hπ, Finset.sum_eq_single (σ (History.last t x))
    (fun a _ ha => by rw [PMF.pure_apply_of_ne _ _ ha, ENNReal.toReal_zero, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), PMF.pure_apply_self, ENNReal.toReal_one, one_mul]

private theorem abs_stateMean_le (f : S → ℝ) (t : ℕ) :
    |stateMean M hM π s₀ f t| ≤ ∑ s, |f s| := by
  unfold stateMean
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ x : History S A t, (law M hM π s₀ t x).toReal * ∑ s, |f s| := by
      refine Finset.sum_le_sum fun x _ => ?_
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      exact mul_le_mul_of_nonneg_left
        (Finset.single_le_sum (fun s _ => abs_nonneg (f s)) (Finset.mem_univ _))
        ENNReal.toReal_nonneg
    _ = _ := by rw [← Finset.sum_mul, sum_toReal_pmf, one_mul]

private theorem stepMean_const (k : ℝ) (t : ℕ) : stepMean M hM π s₀ (fun _ _ => k) t = k := by
  have h := add_stateMean M hM π s₀ k (fun _ => 0) t
  simp only [stateMean, mul_zero, Finset.sum_const_zero, add_zero] at h
  exact h.symm

private theorem expectedReward_le (t : ℕ) :
    π.expectedReward M hM s₀ t ≤ ∑ s, ∑ a, |M.reward s a| := by
  rw [expectedReward_eq_stepMean, ← stepMean_const M hM π s₀ (∑ s, ∑ a, |M.reward s a|) t]
  refine stepMean_mono M hM π s₀ (fun s a => ?_) t
  exact (le_abs_self _).trans <| (Finset.single_le_sum (fun a _ => abs_nonneg (M.reward s a))
    (Finset.mem_univ a)).trans <| Finset.single_le_sum (f := fun s => ∑ a, |M.reward s a|)
      (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ s)

/-- Summing the inequality along the trajectory: in expectation,
`N g + h(s₀) ≤ E[∑_{t < N} c(S_t, A_t)] + E[h(S_N)]`. -/
private theorem mul_add_le_sum {g : ℝ} {h : S → ℝ}
    (hgh : ∀ s a, g + h s ≤ M.reward s a + ∑ s', M.prob s a s' * h s') (N : ℕ) :
    N * g + h s₀ ≤
      ∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t + stateMean M hM π s₀ h N := by
  induction N with
  | zero => simp [stateMean_zero]
  | succ N ih =>
    have hstep : g + stateMean M hM π s₀ h N ≤
        π.expectedReward M hM s₀ N + stateMean M hM π s₀ h (N + 1) := by
      rw [add_stateMean, expectedReward_eq_stepMean, stateMean_succ, ← stepMean_add]
      exact stepMean_mono M hM π s₀ hgh N
    rw [Finset.sum_range_succ]
    push_cast
    linarith

/-- Under the policy that plays `σ`, where `σ` attains equality, the inequality of
`mul_add_le_sum` is an equality. -/
private theorem mul_add_eq_sum {g : ℝ} {h : S → ℝ} {σ : S → A}
    (hσ : ∀ s, g + h s = M.reward s (σ s) + ∑ s', M.prob s (σ s) s' * h s')
    (hπ : ∀ t x, π.actionLaw t x = PMF.pure (σ (History.last t x))) (N : ℕ) :
    N * g + h s₀ =
      ∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t + stateMean M hM π s₀ h N := by
  induction N with
  | zero => simp [stateMean_zero]
  | succ N ih =>
    have hstep : g + stateMean M hM π s₀ h N =
        π.expectedReward M hM s₀ N + stateMean M hM π s₀ h (N + 1) := by
      rw [add_stateMean, expectedReward_eq_stepMean, stateMean_succ, ← stepMean_add,
        stepMean_of_actionLaw_eq_pure M hM π s₀ hπ, stepMean_of_actionLaw_eq_pure M hM π s₀ hπ]
      exact Finset.sum_congr rfl fun x _ => by rw [hσ]
    rw [Finset.sum_range_succ]
    push_cast
    linarith

end HistoryPolicy

open HistoryPolicy

variable {S A : Type u} [Fintype S] [Fintype A] [DecidableEq S]

/-- **Verification theorem for average-cost Markov decision processes.** Let $M$ be a Markov
decision process with finitely many states and actions, costs $c(s, a)$ (the field `reward`, read
as a cost) and transition probabilities $P(s' \mid s, a)$. Suppose that a real number $g$ and a
function $h$ on states satisfy
$$g + h(s) \le c(s, a) + \sum_{s'} P(s' \mid s, a) \, h(s')$$
for all states $s$ and actions $a$. Then for every initial state $s_0$ and every
history-dependent, possibly randomized, policy $\pi$,
$$\liminf_{N \to \infty} \frac{1}{N} \, \mathbb{E}\Big[\sum_{t < N} c(S_t, A_t)\Big] \ge g,$$
where $S_t$ and $A_t$ are the state and action at stage $t$ under $\pi$ from $s_0$. If moreover
a deterministic stationary policy $\sigma$ attains equality,
$g + h(s) = c(s, \sigma(s)) + \sum_{s'} P(s' \mid s, \sigma(s)) \, h(s')$ for every state $s$,
then under $\sigma$ (the policy that plays $\sigma(s)$ in the current state $s$ after every
history) $\frac{1}{N} \, \mathbb{E}\big[\sum_{t < N} c(S_t, A_t)\big] \to g$ from every initial
state; so $\sigma$ attains the least long-run average cost.

Source: *2.997 Decision-Making in Large-Scale Systems*, Lecture Note 4 (Handout #6), MIT,
Spring 2004, §2, Theorem 1, the special case in which $g$ and $h$ satisfy Bellman's equation
with equality, $\sigma$ is greedy for $h$, the competing policies are deterministic Markov
policies, and the average cost is a lim sup. -/
theorem average_cost_verification {M : MDP S A ℝ} (hM : M.Stochastic) {g : ℝ} {h : S → ℝ}
    (hgh : ∀ s a, g + h s ≤ M.reward s a + ∑ s', M.prob s a s' * h s') :
    (∀ (π : HistoryPolicy (fun _ : S => (Set.univ : Set A))) (s₀ : S),
      g ≤ liminf (fun N : ℕ => (∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t) / N)
        atTop) ∧
    ∀ σ : S → A, (∀ s, g + h s = M.reward s (σ s) + ∑ s', M.prob s (σ s) s' * h s') →
      ∀ π : HistoryPolicy (fun _ : S => (Set.univ : Set A)),
        (∀ t x, π.actionLaw t x = PMF.pure (σ (History.last t x))) → ∀ s₀ : S,
          Tendsto (fun N : ℕ => (∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t) / N)
            atTop (𝓝 g) := by
  set B := ∑ s, |h s|
  set C := ∑ s, ∑ a, |M.reward s a|
  have hB (s : S) : |h s| ≤ B :=
    Finset.single_le_sum (fun s _ => abs_nonneg (h s)) (Finset.mem_univ s)
  have hC : 0 ≤ C := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _
  have hpos {N : ℕ} (hN : 1 ≤ N) : (0 : ℝ) < N := by exact_mod_cast hN
  -- The averages are bounded above by `C`.
  have hcobdd (π : HistoryPolicy (fun _ : S => (Set.univ : Set A))) (s₀ : S) :
      IsCoboundedUnder (· ≥ ·) atTop
        (fun N : ℕ => (∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t) / N) := by
    refine isCoboundedUnder_ge_of_le atTop (x := C) fun N => ?_
    refine div_le_of_le_mul₀ (Nat.cast_nonneg N) hC ?_
    calc
      _ ≤ ∑ t ∈ Finset.range N, C := Finset.sum_le_sum fun t _ => expectedReward_le M hM π s₀ t
      _ = C * N := by simp [mul_comm]
  -- After `N ≥ 1` steps the average is at least `g - 2 B / N`.
  have hlower (π : HistoryPolicy (fun _ : S => (Set.univ : Set A))) (s₀ : S) {N : ℕ}
      (hN : 1 ≤ N) :
      g - 2 * B / N ≤ (∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t) / N := by
    have key := mul_add_le_sum M hM π s₀ hgh N
    have h₀ := abs_le.1 (hB s₀)
    have hN' := abs_le.1 (abs_stateMean_le M hM π s₀ h N)
    rw [le_div_iff₀ (hpos hN), sub_mul, div_mul_cancel₀ _ (hpos hN).ne']
    linarith
  have ht : Tendsto (fun N : ℕ => 2 * B / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  refine ⟨fun π s₀ => ?_, fun σ hσ π hπ s₀ => ?_⟩
  · refine le_of_forall_sub_le fun ε hε => le_liminf_of_le (hcobdd π s₀) ?_
    filter_upwards [eventually_ge_atTop 1, (tendsto_order.1 ht).2 ε hε] with N hN hε'
    linarith [hlower π s₀ hN]
  · -- After `N ≥ 1` steps the average is within `2 B / N` of `g`.
    have hclose {N : ℕ} (hN : 1 ≤ N) :
        g - 2 * B / N ≤ (∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t) / N ∧
          (∑ t ∈ Finset.range N, π.expectedReward M hM s₀ t) / N ≤ g + 2 * B / N := by
      have key := mul_add_eq_sum M hM π s₀ hσ hπ N
      have h₀ := abs_le.1 (hB s₀)
      have hN' := abs_le.1 (abs_stateMean_le M hM π s₀ h N)
      rw [le_div_iff₀ (hpos hN), div_le_iff₀ (hpos hN), sub_mul, add_mul,
        div_mul_cancel₀ _ (hpos hN).ne']
      constructor <;> linarith
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using tendsto_const_nhds.sub ht)
      (by simpa using tendsto_const_nhds.add ht) ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hclose hN).1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (hclose hN).2

end Cslib.Algorithms.Lean.MarkovDecision
