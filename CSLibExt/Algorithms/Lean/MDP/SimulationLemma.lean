/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.MarkovRewardProcess

/-!
# The simulation lemma

Two finite MDPs `M` and `M̂` on the same states and actions, with the same rewards but different
transition probabilities, give a stochastic policy `π` two values `V^π` and `V̂^π`. The
**simulation lemma** (Agarwal, Jiang, Kakade and Sun, *Reinforcement Learning: Theory and
Algorithms*, Lemma 2.2, stated there for action values) writes their difference as a value in the
model `M̂`:

  `V^π - V̂^π = (I - γ P̂^π)⁻¹ (γ (P^π - P̂^π) V^π)` (`stochValue_sub_stochValue_eq`).

With rewards in `[0, 1]` and transition rows within `ε` in `ℓ¹`,
`|V^π(s) - V̂^π(s)| ≤ γ ε / (1 - γ)²` (`abs_stochValue_sub_stochValue_le`, the value-accuracy step
of AJKS Proposition 2.1 and of model-based sample-complexity bounds such as AJKS Theorem 2.6). An
estimated model whose transitions are accurate therefore evaluates every policy accurately.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Finset Matrix StochasticPolicy

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
  {M M' : MDP S A ℝ} {γ : ℝ} (hM : M.Stochastic) (hM' : M'.Stochastic) (hγ0 : 0 ≤ γ)
  (hγ1 : γ < 1)

include hM hM' hγ0 hγ1

/-- **The simulation lemma** (AJKS Lemma 2.2, for state values): if the MDPs `M` and `M'` have
the same rewards, then for every stochastic policy `π`, `V^π_M - V^π_{M'}` is the value, in the
Markov chain of `π` under `M'`, of the reward `s ↦ γ ∑ s', (P^π_M - P^π_{M'})(s, s') V^π_M(s')`. -/
theorem stochValue_sub_stochValue_eq (hr : M.reward = M'.reward) (π : StochasticPolicy S A) :
    stochValue M γ hM hγ0 hγ1 π - stochValue M' γ hM' hγ0 hγ1 π =
      mrpValue (policyKernel M' π) (policyKernel_mem hM' π) hγ0 hγ1 (fun s =>
        γ * ∑ s', (policyKernel M π s s' - policyKernel M' π s s') *
          stochValue M γ hM hγ0 hγ1 π s') := by
  refine eq_mrpValue _ hγ0 hγ1 fun s => ?_
  have e : stochValue M γ hM hγ0 hγ1 π s = policyReward M π s +
      γ * ∑ s', policyKernel M π s s' * stochValue M γ hM hγ0 hγ1 π s' :=
    mrpValue_eq _ hγ0 hγ1 _ s
  have e' : stochValue M' γ hM' hγ0 hγ1 π s = policyReward M' π s +
      γ * ∑ s', policyKernel M' π s s' * stochValue M' γ hM' hγ0 hγ1 π s' :=
    mrpValue_eq _ hγ0 hγ1 _ s
  have hrr : policyReward M π s = policyReward M' π s := by simp only [policyReward, hr]
  have s1 : ∑ s', (policyKernel M π s s' - policyKernel M' π s s') *
      stochValue M γ hM hγ0 hγ1 π s' = ∑ s', policyKernel M π s s' *
        stochValue M γ hM hγ0 hγ1 π s' - ∑ s', policyKernel M' π s s' *
          stochValue M γ hM hγ0 hγ1 π s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have s2 : ∑ s', policyKernel M' π s s' * (stochValue M γ hM hγ0 hγ1 π - stochValue M' γ hM'
      hγ0 hγ1 π) s' = ∑ s', policyKernel M' π s s' * stochValue M γ hM hγ0 hγ1 π s' -
        ∑ s', policyKernel M' π s s' * stochValue M' γ hM' hγ0 hγ1 π s' := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun _ _ => by simp only [Pi.sub_apply]; ring
  rw [s1, s2, Pi.sub_apply]
  linear_combination e - e' + hrr

/-- **Model accuracy gives value accuracy** (AJKS Lemma 2.2 with Lemma 2.3, as in the proof of
Proposition 2.1): if `M` and `M'` have the same rewards, all in `[0, 1]`, and
`∑ s', |P(s, a, s') - P'(s, a, s')| ≤ ε` for all `s, a`, then for every stochastic policy `π` and
state `s`, `|V^π_M(s) - V^π_{M'}(s)| ≤ γ ε / (1 - γ)²`. -/
theorem abs_stochValue_sub_stochValue_le (hr : M.reward = M'.reward)
    (hr01 : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1) {ε : ℝ}
    (hε : ∀ s a, ∑ s', |M.prob s a s' - M'.prob s a s'| ≤ ε) (π : StochasticPolicy S A) (s : S) :
    |stochValue M γ hM hγ0 hγ1 π s - stochValue M' γ hM' hγ0 hγ1 π s| ≤
      γ * ε / (1 - γ) ^ 2 := by
  have h1γ : 0 < 1 - γ := by linarith
  set V := stochValue M γ hM hγ0 hγ1 π
  have hV : ∀ s', |V s'| ≤ 1 / (1 - γ) := fun s' => by
    have h := stochValue_mem_Icc hM hγ0 hγ1 hr01 π s'
    rw [abs_le]
    constructor
    · have : 0 ≤ 1 / (1 - γ) := by positivity
      linarith [h.1]
    · exact h.2
  have hrow : ∀ s, |γ * ∑ s', (policyKernel M π s s' - policyKernel M' π s s') * V s'| ≤
      γ * (ε / (1 - γ)) := by
    intro s
    rw [abs_mul, abs_of_nonneg hγ0]
    refine mul_le_mul_of_nonneg_left ?_ hγ0
    have hk : ∀ s', policyKernel M π s s' - policyKernel M' π s s' =
        ∑ a, π.prob s a * (M.prob s a s' - M'.prob s a s') := fun s' => by
      simp only [policyKernel, ← Finset.sum_sub_distrib, mul_sub]
    calc |∑ s', (policyKernel M π s s' - policyKernel M' π s s') * V s'|
        ≤ ∑ s', |(policyKernel M π s s' - policyKernel M' π s s') * V s'| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', (∑ a, π.prob s a * |M.prob s a s' - M'.prob s a s'|) * (1 / (1 - γ)) := by
          refine Finset.sum_le_sum fun s' _ => ?_
          rw [abs_mul, hk]
          refine mul_le_mul ?_ (hV s') (abs_nonneg _) (Finset.sum_nonneg fun a _ =>
            mul_nonneg (π.prob_nonneg s a) (abs_nonneg _))
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [abs_mul, abs_of_nonneg (π.prob_nonneg s a)]
      _ = (∑ a, π.prob s a * ∑ s', |M.prob s a s' - M'.prob s a s'|) * (1 / (1 - γ)) := by
          rw [← Finset.sum_mul, Finset.sum_comm]
          simp only [Finset.mul_sum]
      _ ≤ (∑ a, π.prob s a * ε) * (1 / (1 - γ)) := by
          refine mul_le_mul_of_nonneg_right (Finset.sum_le_sum fun a _ =>
            mul_le_mul_of_nonneg_left (hε s a) (π.prob_nonneg s a)) (by positivity)
      _ = ε / (1 - γ) := by rw [← Finset.sum_mul, π.sum_prob]; ring
  have h := abs_mrpValue_le (policyKernel_mem hM' π) hγ0 hγ1 hrow s
  rw [← stochValue_sub_stochValue_eq hM hM' hγ0 hγ1 hr π, Pi.sub_apply] at h
  calc |V s - stochValue M' γ hM' hγ0 hγ1 π s| ≤ γ * (ε / (1 - γ)) / (1 - γ) := h
    _ = γ * ε / (1 - γ) ^ 2 := by field_simp

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
