/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ValueIteration
public import Mathlib.Probability.ProbabilityMassFunction.Basic

/-!
# Stochastic policies, discounted occupancy and the performance difference lemma

For the finite MDPs of `CSLibExt.Algorithms.Lean.MDP.ValueIteration` (`MDP S A ℝ`, `Stochastic`),
a stationary stochastic policy is a row-stochastic matrix `π s a` (`IsRowStochastic`; `ofPMF`
turns `S → PMF A` into one). Under `π` the states form a Markov chain with transition matrix
`stateKernel M π s s' = ∑ a, π s a * prob s a s'` and reward `policyReward M π s`.

The value of a chain with state reward `f` and discount `0 ≤ γ < 1` is `chainValue`, the unique
solution of `V = f + γ P V`. It is the existing `policyValue` of the one-action MDP `chain P f`,
so no new contraction argument is needed. Then:

* `stochPolicyValue M γ .. π hπ`: the value of `π`, the unique solution of the Bellman
  expectation equation `V s = ∑ a, π s a * qValue M γ V s a` (`stochPolicyValue_eq`,
  `eq_stochPolicyValue`); for a deterministic policy it is `policyValue`
  (`stochPolicyValue_detPolicy`).
* `occupancy M γ .. π hπ μ`: the normalized discounted state-action occupancy measure from the
  initial distribution `μ`, `(1 - γ) * ∑ n, γ ^ n * Pr(S n = s, A n = a)`, defined through the
  values of state-indicator rewards. It is nonnegative (`occupancy_nonneg`) and sums to `1`
  (`sum_occupancy`), and the expected value is `(1 - γ)⁻¹` times the expected reward under it
  (`sum_mul_stochPolicyValue`).
* `performance_difference`: for stochastic policies `π'` and `π`,
  `∑ s, μ s * V^π' s - ∑ s, μ s * V^π s = (1 - γ)⁻¹ * ∑ p, d^π'_μ p * A^π p`, where `A^π` is the
  advantage of `π` (Kakade and Langford 2002, Lemma 6.1; Agarwal, Jiang, Kakade and Sun,
  *Reinforcement Learning: Theory and Algorithms*, Lemma 1.16).

## Relation to LMLExplore

LMLExplore (`LeanMachineLearning/LMLExplore`, `LMLExplore/MarkovDecisionProcess/`) proves the
general form, `Learning.MDP.runValue_sub_integral_value`, for measurable state and action spaces,
reward kernels and history-dependent algorithms, on a different Lean toolchain. This file states
its stationary-policy, finite-space specialization against the Atlas MDP API, with the same
normalization: the occupancy measure carries the factor `1 - γ` and the identity the factor
`(1 - γ)⁻¹`. The finite statement is reached here through the uniqueness of Bellman fixed points
rather than through trajectory laws.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

variable {S A : Type*} [Fintype S] [Fintype A]

/-! ## Row-stochastic matrices, stochastic policies and the induced chain -/

/-- A row-stochastic matrix: nonnegative entries, each row summing to `1`. A stationary stochastic
policy is a row-stochastic `π : S → A → ℝ`. -/
def IsRowStochastic {X Y : Type*} [Fintype Y] (P : X → Y → ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ ∀ x, ∑ y, P x y = 1

/-- The deterministic policy `π` as a stochastic policy. -/
def detPolicy [DecidableEq A] (π : S → A) : S → A → ℝ :=
  fun s a => if a = π s then 1 else 0

omit [Fintype S] in
theorem isRowStochastic_detPolicy [DecidableEq A] (π : S → A) :
    IsRowStochastic (detPolicy π) :=
  ⟨fun s a => by unfold detPolicy; split_ifs <;> norm_num, fun s => by simp [detPolicy]⟩

/-- The stochastic policy with action laws `p s : PMF A`. -/
noncomputable def ofPMF (p : S → PMF A) : S → A → ℝ :=
  fun s a => (p s a).toReal

omit [Fintype S] in
theorem isRowStochastic_ofPMF (p : S → PMF A) : IsRowStochastic (ofPMF p) := by
  refine ⟨fun s a => ENNReal.toReal_nonneg, fun s => ?_⟩
  unfold ofPMF
  rw [← ENNReal.toReal_sum fun a _ => PMF.apply_ne_top (p s) a,
    ← tsum_fintype (L := .unconditional _), PMF.tsum_coe, ENNReal.toReal_one]

/-- The one-action MDP of the chain with transition matrix `P` and state reward `f`. -/
def chain (P : S → S → ℝ) (f : S → ℝ) : MDP S Unit ℝ where
  reward s _ := f s
  prob s _ s' := P s s'

/-- The transition matrix of the states of `M` under the stochastic policy `π`. -/
def stateKernel (M : MDP S A ℝ) (π : S → A → ℝ) (s s' : S) : ℝ :=
  ∑ a, π s a * M.prob s a s'

/-- The expected reward of `M` in state `s` under the stochastic policy `π`. -/
def policyReward (M : MDP S A ℝ) (π : S → A → ℝ) (s : S) : ℝ :=
  ∑ a, π s a * M.reward s a

/-- The state reward `1` at `t` and `0` elsewhere. -/
def indicatorReward [DecidableEq S] (t : S) : S → ℝ :=
  fun s => if s = t then 1 else 0

theorem chain_stochastic {P : S → S → ℝ} (hP : IsRowStochastic P) (f : S → ℝ) :
    (chain P f).Stochastic :=
  ⟨fun s _ s' => hP.1 s s', fun s _ => hP.2 s⟩

theorem isRowStochastic_stateKernel {M : MDP S A ℝ} {π : S → A → ℝ} (hM : M.Stochastic)
    (hπ : IsRowStochastic π) : IsRowStochastic (stateKernel M π) := by
  refine ⟨fun s s' => Finset.sum_nonneg fun a _ => mul_nonneg (hπ.1 s a) (hM.1 s a s'),
    fun s => ?_⟩
  unfold stateKernel
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hM.2, mul_one]
  exact hπ.2 s

/-- The policy average of action values is the chain's one-step value:
`∑ a, π s a * qValue M γ V s a = policyReward M π s + γ * ∑ s', stateKernel M π s s' * V s'`. -/
theorem sum_mul_qValue (M : MDP S A ℝ) (γ : ℝ) (π : S → A → ℝ) (V : S → ℝ) (s : S) :
    ∑ a, π s a * qValue M γ V s a =
      policyReward M π s + γ * ∑ s', stateKernel M π s s' * V s' := by
  simp only [qValue, policyReward, stateKernel, mul_add, Finset.sum_add_distrib, Finset.mul_sum,
    Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-! ## Values of a chain -/

section Chain

variable {P : S → S → ℝ} (hP : IsRowStochastic P) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- The discounted value of the chain `P` with state reward `f`: the unique solution of
`V = f + γ P V`, the `policyValue` of the one-action MDP `chain P f`. -/
noncomputable def chainValue (P : S → S → ℝ) (hP : IsRowStochastic P) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (f : S → ℝ) : S → ℝ :=
  policyValue (chain P f) γ (chain_stochastic hP f) hγ0 hγ1 fun _ => ()

include hP hγ0 hγ1

theorem chainValue_eq (f : S → ℝ) (s : S) :
    chainValue P hP γ hγ0 hγ1 f s = f s + γ * ∑ s', P s s' * chainValue P hP γ hγ0 hγ1 f s' :=
  (congrFun (policyBellman_policyValue (chain_stochastic hP f) hγ0 hγ1 fun _ => ()) s).symm

theorem eq_chainValue {f V : S → ℝ} (h : ∀ s, V s = f s + γ * ∑ s', P s s' * V s') :
    V = chainValue P hP γ hγ0 hγ1 f :=
  eq_policyValue_of_policyBellman_eq (chain_stochastic hP f) hγ0 hγ1 _
    (funext fun s => (h s).symm)

/-- A constant reward `c` has the constant value `c / (1 - γ)`. -/
theorem chainValue_const (c : ℝ) :
    chainValue P hP γ hγ0 hγ1 (fun _ => c) = fun _ => c / (1 - γ) := by
  refine (eq_chainValue hP hγ0 hγ1 fun s => ?_).symm
  rw [← Finset.sum_mul, hP.2 s, one_mul]
  have h1 : (1 - γ) ≠ 0 := by linarith
  field_simp
  ring

/-- Values are linear in the reward: the value of `f` is the `f`-weighted sum of the values of
the state indicators. -/
theorem chainValue_eq_sum [DecidableEq S] (f : S → ℝ) (s₀ : S) :
    chainValue P hP γ hγ0 hγ1 f s₀ =
      ∑ t, f t * chainValue P hP γ hγ0 hγ1 (indicatorReward t) s₀ := by
  refine (congrFun (eq_chainValue hP hγ0 hγ1 (f := f)
    (V := fun s₀ => ∑ t, f t * chainValue P hP γ hγ0 hγ1 (indicatorReward t) s₀)
    fun s => ?_) s₀).symm
  have hs : ∀ t, chainValue P hP γ hγ0 hγ1 (indicatorReward t) s = indicatorReward t s +
      γ * ∑ s', P s s' * chainValue P hP γ hγ0 hγ1 (indicatorReward t) s' :=
    fun t => chainValue_eq hP hγ0 hγ1 _ s
  simp_rw [hs, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp [indicatorReward]
  · simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Nonnegative rewards have nonnegative values. -/
theorem chainValue_nonneg {f : S → ℝ} (hf : ∀ s, 0 ≤ f s) (s : S) :
    0 ≤ chainValue P hP γ hγ0 hγ1 f s := by
  have hT : ∀ n, (0 : S → ℝ) ≤ (policyBellman (chain P f) γ fun _ => ())^[n] 0 := by
    intro n
    induction n with
    | zero => exact le_refl _
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        intro s
        exact add_nonneg (hf s)
          (mul_nonneg hγ0 (Finset.sum_nonneg fun s' _ => mul_nonneg (hP.1 s s') (ih s')))
  have ht := ContractingWith.tendsto_iterate_fixedPoint
    (policyBellman_contracting (chain_stochastic hP f) hγ0 hγ1 fun _ => ()) (0 : S → ℝ)
  exact ge_of_tendsto' ((continuous_apply s).continuousAt.tendsto.comp ht) fun n => hT n s

end Chain

/-! ## Discounted state occupancy of a chain -/

section ChainOccupancy

variable [DecidableEq S] {P : S → S → ℝ} (hP : IsRowStochastic P) {γ : ℝ} (hγ0 : 0 ≤ γ)
  (hγ1 : γ < 1)

/-- The normalized discounted state occupancy of the chain `P` from the initial distribution
`μ`: `(1 - γ) * ∑ s₀, μ s₀ * V_t s₀`, where `V_t` is the value of the indicator reward of `t`,
that is `(1 - γ) * ∑ n, γ ^ n * Pr(S n = t)`. -/
noncomputable def chainOccupancy (P : S → S → ℝ) (hP : IsRowStochastic P) (γ : ℝ) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (μ : S → ℝ) (t : S) : ℝ :=
  (1 - γ) * ∑ s₀, μ s₀ * chainValue P hP γ hγ0 hγ1 (indicatorReward t) s₀

include hP hγ0 hγ1

/-- The expected value of the reward `f` is `(1 - γ)⁻¹` times the expected reward under the
occupancy measure. -/
theorem sum_mul_chainValue (μ f : S → ℝ) :
    ∑ s₀, μ s₀ * chainValue P hP γ hγ0 hγ1 f s₀ =
      (1 - γ)⁻¹ * ∑ t, chainOccupancy P hP γ hγ0 hγ1 μ t * f t := by
  have h1 : (1 - γ) ≠ 0 := by linarith
  have hL : ∑ s₀, μ s₀ * chainValue P hP γ hγ0 hγ1 f s₀ =
      ∑ t, ∑ s₀, μ s₀ * (f t * chainValue P hP γ hγ0 hγ1 (indicatorReward t) s₀) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s₀ _ => by rw [chainValue_eq_sum hP hγ0 hγ1 f s₀, Finset.mul_sum]
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [chainOccupancy, mul_assoc (1 - γ), inv_mul_cancel_left₀ h1, Finset.sum_mul]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem chainOccupancy_nonneg {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) (t : S) :
    0 ≤ chainOccupancy P hP γ hγ0 hγ1 μ t :=
  mul_nonneg (by linarith) (Finset.sum_nonneg fun s₀ _ => mul_nonneg (hμ s₀)
    (chainValue_nonneg hP hγ0 hγ1 (fun s => by unfold indicatorReward; split_ifs <;> norm_num) s₀))

/-- From an initial distribution, the occupancy measure has total mass `1`. -/
theorem sum_chainOccupancy {μ : S → ℝ} (hμ : ∑ s, μ s = 1) :
    ∑ t, chainOccupancy P hP γ hγ0 hγ1 μ t = 1 := by
  have h := sum_mul_chainValue hP hγ0 hγ1 μ fun _ => 1
  rw [chainValue_const hP hγ0 hγ1] at h
  simp only [mul_one] at h
  rw [← Finset.sum_mul, hμ, one_mul, one_div] at h
  have h1 : (1 - γ)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  exact mul_left_cancel₀ h1 (h.symm.trans (mul_one _).symm)

end ChainOccupancy

/-! ## Stochastic policies: value, occupancy, performance difference -/

section Policy

variable {M : MDP S A ℝ} {γ : ℝ} (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
  {π : S → A → ℝ} (hπ : IsRowStochastic π)

/-- The discounted value of the stochastic policy `π`: the value of its chain of states. -/
noncomputable def stochPolicyValue (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A → ℝ) (hπ : IsRowStochastic π) : S → ℝ :=
  chainValue (stateKernel M π) (isRowStochastic_stateKernel hM hπ) γ hγ0 hγ1 (policyReward M π)

/-- The advantage `A^π (s, a) = Q^π (s, a) - V^π s` of the stochastic policy `π`. -/
noncomputable def advantage (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : S → A → ℝ) (hπ : IsRowStochastic π) (p : S × A) : ℝ :=
  qValue M γ (stochPolicyValue M γ hM hγ0 hγ1 π hπ) p.1 p.2 -
    stochPolicyValue M γ hM hγ0 hγ1 π hπ p.1

/-- The normalized discounted state-action occupancy measure of `π` from `μ`:
`(1 - γ) * ∑ n, γ ^ n * Pr(S n = s, A n = a)`. -/
noncomputable def occupancy [DecidableEq S] (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic)
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (π : S → A → ℝ) (hπ : IsRowStochastic π) (μ : S → ℝ)
    (p : S × A) : ℝ :=
  chainOccupancy (stateKernel M π) (isRowStochastic_stateKernel hM hπ) γ hγ0 hγ1 μ p.1 *
    π p.1 p.2

include hM hγ0 hγ1 hπ

/-- The **Bellman expectation equation** for a stochastic policy. -/
theorem stochPolicyValue_eq (s : S) :
    stochPolicyValue M γ hM hγ0 hγ1 π hπ s =
      ∑ a, π s a * qValue M γ (stochPolicyValue M γ hM hγ0 hγ1 π hπ) s a := by
  rw [sum_mul_qValue]
  exact chainValue_eq _ hγ0 hγ1 _ s

/-- The value of a stochastic policy is the only solution of its Bellman expectation equation. -/
theorem eq_stochPolicyValue {V : S → ℝ} (h : ∀ s, V s = ∑ a, π s a * qValue M γ V s a) :
    V = stochPolicyValue M γ hM hγ0 hγ1 π hπ :=
  eq_chainValue _ hγ0 hγ1 fun s => (h s).trans (sum_mul_qValue M γ π V s)

theorem occupancy_nonneg [DecidableEq S] {μ : S → ℝ} (hμ : ∀ s, 0 ≤ μ s) (p : S × A) :
    0 ≤ occupancy M γ hM hγ0 hγ1 π hπ μ p :=
  mul_nonneg (chainOccupancy_nonneg _ hγ0 hγ1 hμ p.1) (hπ.1 p.1 p.2)

/-- From an initial distribution, the state-action occupancy measure has total mass `1`. -/
theorem sum_occupancy [DecidableEq S] {μ : S → ℝ} (hμ : ∑ s, μ s = 1) :
    ∑ p : S × A, occupancy M γ hM hγ0 hγ1 π hπ μ p = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [occupancy, ← Finset.mul_sum, hπ.2, mul_one]
  exact sum_chainOccupancy _ hγ0 hγ1 hμ

/-- The expected value of `π` is `(1 - γ)⁻¹` times the expected reward under its occupancy
measure. -/
theorem sum_mul_stochPolicyValue [DecidableEq S] (μ : S → ℝ) :
    ∑ s, μ s * stochPolicyValue M γ hM hγ0 hγ1 π hπ s =
      (1 - γ)⁻¹ * ∑ p : S × A, occupancy M γ hM hγ0 hγ1 π hπ μ p * M.reward p.1 p.2 := by
  rw [stochPolicyValue, sum_mul_chainValue _ hγ0 hγ1, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [occupancy, policyReward, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit hπ in
/-- **Deterministic embedding**: the value of a deterministic policy as a stochastic policy is
its `policyValue`. -/
theorem stochPolicyValue_detPolicy [DecidableEq A] (π : S → A) :
    stochPolicyValue M γ hM hγ0 hγ1 (detPolicy π) (isRowStochastic_detPolicy π) =
      policyValue M γ hM hγ0 hγ1 π := by
  refine eq_policyValue_of_policyBellman_eq hM hγ0 hγ1 π (funext fun s => ?_)
  rw [policyBellman, stochPolicyValue_eq hM hγ0 hγ1 (isRowStochastic_detPolicy π) s]
  simp [detPolicy]

/-- **Performance difference lemma** (Kakade and Langford 2002, Lemma 6.1; Agarwal, Jiang, Kakade
and Sun, Lemma 1.16): for stochastic policies `π'` and `π` and an initial weighting `μ`, the
difference of expected values is `(1 - γ)⁻¹` times the expected advantage of `π` under the
occupancy measure of `π'`. -/
theorem performance_difference [DecidableEq S] {π' : S → A → ℝ} (hπ' : IsRowStochastic π')
    (μ : S → ℝ) :
    ∑ s, μ s * stochPolicyValue M γ hM hγ0 hγ1 π' hπ' s -
        ∑ s, μ s * stochPolicyValue M γ hM hγ0 hγ1 π hπ s =
      (1 - γ)⁻¹ * ∑ p : S × A,
        occupancy M γ hM hγ0 hγ1 π' hπ' μ p * advantage M γ hM hγ0 hγ1 π hπ p := by
  have hW : (fun s => stochPolicyValue M γ hM hγ0 hγ1 π' hπ' s -
        stochPolicyValue M γ hM hγ0 hγ1 π hπ s) =
      chainValue (stateKernel M π') (isRowStochastic_stateKernel hM hπ') γ hγ0 hγ1
        (fun s => ∑ a, π' s a * advantage M γ hM hγ0 hγ1 π hπ (s, a)) := by
    refine eq_chainValue _ hγ0 hγ1 fun s => ?_
    have h' := stochPolicyValue_eq hM hγ0 hγ1 hπ' s
    rw [sum_mul_qValue] at h'
    have hg : ∑ a, π' s a * advantage M γ hM hγ0 hγ1 π hπ (s, a) =
        policyReward M π' s +
          γ * ∑ s', stateKernel M π' s s' * stochPolicyValue M γ hM hγ0 hγ1 π hπ s' -
          stochPolicyValue M γ hM hγ0 hγ1 π hπ s := by
      simp only [advantage, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ'.2 s, one_mul]
      rw [sum_mul_qValue]
    rw [hg, h']
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  have hμ := sum_mul_chainValue (isRowStochastic_stateKernel hM hπ') hγ0 hγ1 μ
    (fun s => ∑ a, π' s a * advantage M γ hM hγ0 hγ1 π hπ (s, a))
  rw [← hW] at hμ
  rw [hμ, Fintype.sum_prod_type]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [occupancy, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

end Policy

end Cslib.Algorithms.Lean.MarkovDecision
