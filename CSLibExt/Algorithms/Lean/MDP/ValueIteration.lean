/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Topology.MetricSpace.Pseudo.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Value iteration for finite discounted Markov decision processes

A finite Markov decision process (`MDP S A K`) has finitely many states `S` and actions `A`, a
reward `reward s a` and transition probabilities `prob s a s'` (`Stochastic`: nonnegative, each
row summing to `1`), with values in an ordered field `K`. For a discount factor `γ`, the Bellman
optimality operator is

  `bellman M γ V s = max_a (reward s a + γ * ∑ s', prob s a s' * V s')`,

and value iteration applies it repeatedly (`valueIteration M γ n V = (bellman M γ)^[n] V`, the
mathematical iterate; `valueIterationVec` is the tabulated program on `Fin m` states, equal to it by
`valueIterationVec_get`). For a
deterministic stationary policy `π : S → A`, `policyBellman M γ π` evaluates `π` instead of
maximizing.

Main results, for `0 ≤ γ < 1` and real values (Puterman, *Markov Decision Processes*,
Section 6.3; Bellman 1957):

* `abs_bellman_sub_le` (any ordered field): if `|V s - W s| ≤ d` for all `s`, then
  `|bellman M γ V s - bellman M γ W s| ≤ γ * d`; so `bellman_contracting`: the operator is
  `ContractingWith γ.toNNReal` in the sup metric on `S → ℝ`, and has a unique fixed point
  `optimalValue` (`bellman_optimalValue`, `eq_optimalValue_of_bellman_eq`).
* `tendsto_valueIteration`: value iteration converges to `optimalValue` from any start, with the
  a priori bound `dist (valueIteration M γ n V) (optimalValue ..) ≤ dist V (bellman M γ V) * γ ^ n
  / (1 - γ)` (`dist_valueIteration_le`) and the stopping test `dist_optimalValue_le`.
* The value of a policy, `policyValue`, is the unique fixed point of `policyBellman`
  (`policyBellman_policyValue`, `eq_policyValue_of_policyBellman_eq`); no policy beats
  `optimalValue` (`policyValue_le_optimalValue`), and a policy greedy with respect to
  `optimalValue` attains it (`policyValue_greedy`).

Values are defined by their Bellman equations; their identification with expected discounted
returns of the induced Markov chain (Puterman, Theorem 6.1.1) is not formalized here.

## Cost model

No `TimeM` cost model: these are mathematical statements about the operators.
`valueIterationVec` stores each update, so one update reads `|S| |A| |S|` stored values (one
multiplication each), and `dist_valueIteration_le` bounds how many updates reach a given accuracy.
`valueIteration` itself is the mathematical iterate: evaluating it directly recomputes earlier
iterates and takes exponential time.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter Topology

/-- A finite Markov decision process: rewards and transition probabilities in `K`. -/
structure MDP (S A K : Type*) where
  /-- The reward for taking action `a` in state `s`. -/
  reward : S → A → K
  /-- The probability of moving from `s` to `s'` under action `a`. -/
  prob : S → A → S → K

variable {S A K : Type*} [Fintype S] [Fintype A] [Nonempty A]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Transition probabilities are nonnegative and each row sums to `1`. -/
def MDP.Stochastic (M : MDP S A K) : Prop :=
  (∀ s a s', 0 ≤ M.prob s a s') ∧ ∀ s a, ∑ s', M.prob s a s' = 1

/-- The value of action `a` in state `s` against the value estimate `V`. -/
def qValue (M : MDP S A K) (γ : K) (V : S → K) (s : S) (a : A) : K :=
  M.reward s a + γ * ∑ s', M.prob s a s' * V s'

/-- The Bellman optimality operator: the best action value in each state. -/
def bellman (M : MDP S A K) (γ : K) (V : S → K) : S → K :=
  fun s => Finset.univ.sup' Finset.univ_nonempty (qValue M γ V s)

/-- The Bellman operator of the deterministic stationary policy `π`. -/
def policyBellman (M : MDP S A K) (γ : K) (π : S → A) (V : S → K) : S → K :=
  fun s => qValue M γ V s (π s)

/-- Value iteration, as a mathematical iterate: `n` Bellman updates from `V`. Evaluating it
directly recomputes earlier iterates; `valueIterationVec` is the tabulated program. -/
def valueIteration (M : MDP S A K) (γ : K) (n : ℕ) (V : S → K) : S → K :=
  (bellman M γ)^[n] V

/-- Value iteration as a program on `Fin m` states: each update is tabulated in a vector, so
update `k + 1` reads the stored values of update `k`. -/
def valueIterationVec {m : ℕ} (M : MDP (Fin m) A K) (γ : K) : ℕ → Vector K m → Vector K m
  | 0, v => v
  | k + 1, v => valueIterationVec M γ k (Vector.ofFn (bellman M γ fun s => v.get s))

/-- A policy greedy with respect to `V`: in each state, an action of largest value. -/
noncomputable def greedy (M : MDP S A K) (γ : K) (V : S → K) (s : S) : A :=
  (Finset.univ.exists_max_image (qValue M γ V s) Finset.univ_nonempty).choose

variable {M : MDP S A K} {γ : K}

omit [Fintype S] [IsStrictOrderedRing K] in
/-- The tabulated program computes value iteration. -/
theorem valueIterationVec_get {m : ℕ} (M : MDP (Fin m) A K) (γ : K) :
    ∀ (n : ℕ) (v : Vector K m) (s : Fin m),
      (valueIterationVec M γ n v).get s = valueIteration M γ n (fun s => v.get s) s
  | 0, _, _ => rfl
  | n + 1, v, s => by
      have h : (fun s => (Vector.ofFn (bellman M γ fun s => v.get s)).get s) =
          bellman M γ fun s => v.get s := by
        funext s'
        change (Vector.ofFn _)[s'.val] = _
        rw [Vector.getElem_ofFn]
      rw [valueIterationVec, valueIterationVec_get M γ n, valueIteration, valueIteration,
        Function.iterate_succ_apply, h]

/-! ## Order and contraction facts, in any ordered field -/

omit [Fintype A] [Nonempty A] in
theorem qValue_mono (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} (h : V ≤ W) (s : S) (a : A) :
    qValue M γ V s a ≤ qValue M γ W s a := by
  unfold qValue
  gcongr with s'
  all_goals first | exact hM.1 s a s' | exact h s'

theorem bellman_mono (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} (h : V ≤ W) :
    bellman M γ V ≤ bellman M γ W := fun s =>
  Finset.sup'_le _ _ fun a _ => (qValue_mono hM hγ h s a).trans (Finset.le_sup' _ (by simp))

omit [Fintype A] [Nonempty A] in
theorem policyBellman_mono (hM : M.Stochastic) (hγ : 0 ≤ γ) (π : S → A) {V W : S → K}
    (h : V ≤ W) : policyBellman M γ π V ≤ policyBellman M γ π W := fun s =>
  qValue_mono hM hγ h s (π s)

omit [IsStrictOrderedRing K] in
/-- A policy's update never exceeds the optimal update. -/
theorem policyBellman_le_bellman (π : S → A) (V : S → K) :
    policyBellman M γ π V ≤ bellman M γ V := fun s =>
  Finset.le_sup' (qValue M γ V s) (Finset.mem_univ (π s))

omit [IsStrictOrderedRing K] in
/-- The greedy action attains the maximum. -/
theorem qValue_greedy (V : S → K) (s : S) :
    qValue M γ V s (greedy M γ V s) = bellman M γ V s := by
  have h := (Finset.univ.exists_max_image (qValue M γ V s) Finset.univ_nonempty).choose_spec
  exact le_antisymm (Finset.le_sup' _ h.1) (Finset.sup'_le _ _ fun a ha => h.2 a ha)

omit [IsStrictOrderedRing K] in
theorem policyBellman_greedy (V : S → K) : policyBellman M γ (greedy M γ V) V = bellman M γ V :=
  funext fun s => qValue_greedy V s

omit [Fintype A] [Nonempty A] in
theorem abs_qValue_sub_le (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} {d : K}
    (h : ∀ s, |V s - W s| ≤ d) (s : S) (a : A) :
    |qValue M γ V s a - qValue M γ W s a| ≤ γ * d := by
  have e : qValue M γ V s a - qValue M γ W s a = γ * ∑ s', M.prob s a s' * (V s' - W s') := by
    simp only [qValue, mul_sub, Finset.sum_sub_distrib]; ring
  rw [e, abs_mul, abs_of_nonneg hγ]
  refine mul_le_mul_of_nonneg_left ?_ hγ
  calc |∑ s', M.prob s a s' * (V s' - W s')|
      ≤ ∑ s', |M.prob s a s' * (V s' - W s')| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s', M.prob s a s' * |V s' - W s'| := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (hM.1 s a s')]
    _ ≤ ∑ s', M.prob s a s' * d :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (h s') (hM.1 s a s')
    _ = d := by rw [← Finset.sum_mul, hM.2 s a, one_mul]

/-- **The Bellman operator contracts by `γ`** in the sup norm. -/
theorem abs_bellman_sub_le (hM : M.Stochastic) (hγ : 0 ≤ γ) {V W : S → K} {d : K}
    (h : ∀ s, |V s - W s| ≤ d) (s : S) : |bellman M γ V s - bellman M γ W s| ≤ γ * d := by
  have hq := abs_qValue_sub_le hM hγ h s
  rw [abs_sub_le_iff]
  constructor
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun a _ => ?_
    have := (abs_sub_le_iff.1 (hq a)).1
    have := Finset.le_sup' (qValue M γ W s) (Finset.mem_univ a)
    unfold bellman; linarith
  · rw [sub_le_iff_le_add]
    refine Finset.sup'_le _ _ fun a _ => ?_
    have := (abs_sub_le_iff.1 (hq a)).2
    have := Finset.le_sup' (qValue M γ V s) (Finset.mem_univ a)
    unfold bellman; linarith

omit [Fintype A] [Nonempty A] in
theorem abs_policyBellman_sub_le (hM : M.Stochastic) (hγ : 0 ≤ γ) (π : S → A) {V W : S → K}
    {d : K} (h : ∀ s, |V s - W s| ≤ d) (s : S) :
    |policyBellman M γ π V s - policyBellman M γ π W s| ≤ γ * d :=
  abs_qValue_sub_le hM hγ h s (π s)

/-! ## Real values: contraction, value iteration, optimality -/

variable {M : MDP S A ℝ} {γ : ℝ}

/-- A pointwise `γ`-contraction in absolute value is `ContractingWith γ` in the sup metric. -/
private theorem contractingWith_of_abs_le {T : (S → ℝ) → S → ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (hT : ∀ (V W : S → ℝ) (d : ℝ), (∀ s, |V s - W s| ≤ d) → ∀ s, |T V s - T W s| ≤ γ * d) :
    ContractingWith γ.toNNReal T := by
  refine ⟨Real.toNNReal_lt_one.2 hγ1, LipschitzWith.of_dist_le_mul fun V W => ?_⟩
  rw [Real.coe_toNNReal γ hγ0, dist_pi_le_iff (by positivity)]
  intro s
  rw [Real.dist_eq]
  exact hT V W _ (fun s' => by rw [← Real.dist_eq]; exact dist_le_pi_dist V W s') s

/-- **Bellman's operator is a contraction** (Puterman, Theorem 6.2.3). -/
theorem bellman_contracting (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    ContractingWith γ.toNNReal (bellman M γ) :=
  contractingWith_of_abs_le hγ0 hγ1 fun _ _ _ h => abs_bellman_sub_le hM hγ0 h

omit [Fintype A] [Nonempty A] in
theorem policyBellman_contracting (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (π : S → A) : ContractingWith γ.toNNReal (policyBellman M γ π) :=
  contractingWith_of_abs_le hγ0 hγ1 fun _ _ _ h => abs_policyBellman_sub_le hM hγ0 π h

/-- The optimal value: the unique fixed point of the Bellman operator. -/
noncomputable def optimalValue (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) : S → ℝ :=
  ContractingWith.fixedPoint _ (bellman_contracting hM hγ0 hγ1)

/-- The value of the policy `π`: the unique fixed point of its Bellman operator. -/
noncomputable def policyValue (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A) : S → ℝ :=
  ContractingWith.fixedPoint _ (policyBellman_contracting hM hγ0 hγ1 π)

variable (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hM hγ0 hγ1

/-- The optimal value satisfies the Bellman optimality equation. -/
theorem bellman_optimalValue : bellman M γ (optimalValue M γ hM hγ0 hγ1) =
    optimalValue M γ hM hγ0 hγ1 :=
  ContractingWith.fixedPoint_isFixedPt (bellman_contracting hM hγ0 hγ1)

/-- The optimal value is the only solution of the Bellman optimality equation. -/
theorem eq_optimalValue_of_bellman_eq {V : S → ℝ} (h : bellman M γ V = V) :
    V = optimalValue M γ hM hγ0 hγ1 :=
  ContractingWith.fixedPoint_unique (bellman_contracting hM hγ0 hγ1) h

omit [Fintype A] [Nonempty A] in
/-- The value of a policy satisfies the policy's Bellman equation. -/
theorem policyBellman_policyValue (π : S → A) :
    policyBellman M γ π (policyValue M γ hM hγ0 hγ1 π) = policyValue M γ hM hγ0 hγ1 π :=
  ContractingWith.fixedPoint_isFixedPt (policyBellman_contracting hM hγ0 hγ1 π)

omit [Fintype A] [Nonempty A] in
/-- The value of a policy is the only solution of the policy's Bellman equation. -/
theorem eq_policyValue_of_policyBellman_eq (π : S → A) {V : S → ℝ}
    (h : policyBellman M γ π V = V) : V = policyValue M γ hM hγ0 hγ1 π :=
  ContractingWith.fixedPoint_unique (policyBellman_contracting hM hγ0 hγ1 π) h

/-- **Value iteration converges** to the optimal value from any start. -/
theorem tendsto_valueIteration (V : S → ℝ) :
    Tendsto (fun n => valueIteration M γ n V) atTop (𝓝 (optimalValue M γ hM hγ0 hγ1)) :=
  ContractingWith.tendsto_iterate_fixedPoint (bellman_contracting hM hγ0 hγ1) V

/-- **A priori error bound** for value iteration: geometric in `γ`. -/
theorem dist_valueIteration_le (V : S → ℝ) (n : ℕ) :
    dist (valueIteration M γ n V) (optimalValue M γ hM hγ0 hγ1) ≤
      dist V (bellman M γ V) * γ ^ n / (1 - γ) := by
  have := ContractingWith.apriori_dist_iterate_fixedPoint_le (bellman_contracting hM hγ0 hγ1) V n
  rwa [Real.coe_toNNReal γ hγ0] at this

/-- **Stopping test**: one update moving `V` by `ε` puts `V` within `ε / (1 - γ)` of the optimal
value. -/
theorem dist_optimalValue_le (V : S → ℝ) :
    dist V (optimalValue M γ hM hγ0 hγ1) ≤ dist V (bellman M γ V) / (1 - γ) := by
  have := ContractingWith.dist_fixedPoint_le (bellman_contracting hM hγ0 hγ1) V
  rwa [Real.coe_toNNReal γ hγ0] at this

/-- **No policy beats the optimal value.** -/
theorem policyValue_le_optimalValue (π : S → A) :
    policyValue M γ hM hγ0 hγ1 π ≤ optimalValue M γ hM hγ0 hγ1 := by
  set V := optimalValue M γ hM hγ0 hγ1
  have hle : ∀ n, (policyBellman M γ π)^[n] V ≤ V := by
    intro n
    induction n with
    | zero => exact le_refl V
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        calc policyBellman M γ π ((policyBellman M γ π)^[n] V)
            ≤ policyBellman M γ π V := policyBellman_mono hM hγ0 π ih
          _ ≤ bellman M γ V := policyBellman_le_bellman π V
          _ = V := bellman_optimalValue hM hγ0 hγ1
  have ht := ContractingWith.tendsto_iterate_fixedPoint (policyBellman_contracting hM hγ0 hγ1 π) V
  intro s
  exact le_of_tendsto' ((continuous_apply s).continuousAt.tendsto.comp ht) fun n => hle n s

/-- **A greedy policy for the optimal value is optimal.** -/
theorem policyValue_greedy :
    policyValue M γ hM hγ0 hγ1 (greedy M γ (optimalValue M γ hM hγ0 hγ1)) =
      optimalValue M γ hM hγ0 hγ1 := by
  refine (eq_policyValue_of_policyBellman_eq hM hγ0 hγ1 _ ?_).symm
  rw [policyBellman_greedy, bellman_optimalValue hM hγ0 hγ1]

end Cslib.Algorithms.Lean.MarkovDecision
