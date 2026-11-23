/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.FiniteHorizon
import Mathlib.Algebra.Order.Group.Finset

/-!
# Finite-horizon optimality with terminal values

For a finite Markov decision process with real rewards and a terminal (salvage)
value `g : S → ℝ`, the finite-horizon terminal value with `k` steps remaining is
`k` steps of the existing value iteration from `g`, `valueIteration M γ k g`; no
new backward-recursion value is defined. A nonstationary policy `π : ℕ → S → A`
(`π k s` is the action taken with `k` steps remaining) earns the terminal return
`finiteHorizonPolicyValueTerminal M γ g π`: `R 0 = g` and one `qValue` step at
the policy's action per additional step
(`finiteHorizonPolicyValueTerminal_zero`,
`finiteHorizonPolicyValueTerminal_succ`), agreeing with the existing
zero-terminal `finiteHorizonPolicyValue` when `g = 0`.

The terminal value is transported to an equivalent zero-terminal problem by
reward shaping. With the shaped reward
`r_g s a = r s a + γ * ∑ s', p s a s' * g s' - g s` and unchanged transition
probabilities (private `terminalShapedMDP`), value iteration from `g` is
pointwise `g` plus the shaped model's zero-terminal `finiteHorizonValue`, and
likewise for every policy return (private transport identities). These are
algebraic identities for every `γ` and every `M`, including non-stochastic `M`.
Domination and optimality for the terminal problem then follow from the existing
zero-terminal results on the shaped model: no policy beats
`valueIteration M γ k g`
(`finiteHorizonPolicyValueTerminal_le_valueIteration`), and one remaining-step
policy attains it at every horizon and state while dominating every competitor
(`exists_finiteHorizonTerminalOptimalPolicy`). No `γ < 1` is needed: the horizon
is finite.

## Main results

* `Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon.finiteHorizonPolicyValueTerminal`:
  terminal return of a nonstationary policy.
* `finiteHorizonPolicyValueTerminal_le_valueIteration`:
  the terminal value dominates every policy.
* `Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon.exists_finiteHorizonTerminalOptimalPolicy`:
  an optimal policy exists for the terminal-value problem.

## References

DP-001 source contract (finite-horizon optimality with terminal values).
Puterman, *Markov Decision Processes* (finite-horizon backward induction);
terminal-potential reward shaping. The zero-terminal optimality results
`finiteHorizonGreedy_value`, `finiteHorizonValue_ge_policy` and
`exists_finiteHorizonOptimalPolicy` are cited from
`CSLibExt/Algorithms/Lean/MDP/FiniteHorizon.lean`, not reproved.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

namespace FiniteHorizon

/-- Terminal return of a nonstationary policy `π`, where `π k s` is the action
taken with `k` steps remaining in state `s` (contract C1). With `0` steps
remaining the return is the terminal value `g`; with `k + 1` steps remaining it
is one `qValue` step at the policy's action `π (k + 1) s`. Evaluating a given
policy needs no maximization, so the action type may be infinite. The optimal
terminal value needs no new definition: it is the existing
`valueIteration M γ k g`. -/
noncomputable def finiteHorizonPolicyValueTerminal {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (π : ℕ → S → A) : ℕ → S → ℝ
  | 0 => g
  | k + 1 => fun s => qValue M γ (finiteHorizonPolicyValueTerminal M γ g π k) s (π (k + 1) s)

/-- Zero equation for the terminal policy return (contract C1): with `0` steps
remaining, the return is the terminal value. -/
theorem finiteHorizonPolicyValueTerminal_zero {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (π : ℕ → S → A) :
    finiteHorizonPolicyValueTerminal M γ g π 0 = g := rfl

/-- Successor equation for the terminal policy return (contract C1): with
`k + 1` steps remaining, one `qValue` step at action `π (k + 1) s`. -/
theorem finiteHorizonPolicyValueTerminal_succ {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (π : ℕ → S → A) (k : ℕ) :
    finiteHorizonPolicyValueTerminal M γ g π (k + 1)
      = fun s => qValue M γ (finiteHorizonPolicyValueTerminal M γ g π k) s (π (k + 1) s) := rfl

/-- The terminal policy return agrees with the existing zero-terminal
`finiteHorizonPolicyValue` when `g = 0` (contract C1). -/
theorem finiteHorizonPolicyValueTerminal_agrees_zero {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (π : ℕ → S → A) :
    ∀ (k : ℕ) (s : S),
      finiteHorizonPolicyValueTerminal M γ (fun _ => 0) π k s
        = finiteHorizonPolicyValue M γ π k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    have hfun : finiteHorizonPolicyValueTerminal M γ (fun _ => 0) π k
        = finiteHorizonPolicyValue M γ π k := funext ih
    change qValue M γ (finiteHorizonPolicyValueTerminal M γ (fun _ => 0) π k) s (π (k + 1) s)
      = qValue M γ (finiteHorizonPolicyValue M γ π k) s (π (k + 1) s)
    rw [hfun]

/-- Terminal-potential shaped model (contract C2, proof-only): the shaped reward
`r_g s a = r s a + γ * ∑ s', p s a s' * g s' - g s` with unchanged transition
probabilities. Private: no public definition depends on it. -/
private def terminalShapedMDP {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) : MDP S A ℝ where
  reward := fun s a => M.reward s a + γ * (∑ s', M.prob s a s' * g s') - g s
  prob := M.prob

/-- Shaped `qValue` unfolds to the original `qValue` at `g + V` minus `g`. -/
private theorem terminalShaped_qValue {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (V : S → ℝ) (s : S) (a : A) :
    qValue (terminalShapedMDP M γ g) γ V s a
      = qValue M γ (fun s' => g s' + V s') s a - g s := by
  unfold qValue terminalShapedMDP
  simp only
  have hsum : (∑ s', M.prob s a s' * (g s' + V s'))
      = (∑ s', M.prob s a s' * g s') + ∑ s', M.prob s a s' * V s' := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s' _
    ring
  rw [hsum, mul_add]
  ring

/-- Shaped Bellman update commutes with adding `g`. -/
private theorem terminalShaped_bellman {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (V : S → ℝ) (s : S) :
    bellman M γ (fun s' => g s' + V s') s
      = g s + bellman (terminalShapedMDP M γ g) γ V s := by
  have hq : ∀ a : A, qValue M γ (fun s' => g s' + V s') s a
      = g s + qValue (terminalShapedMDP M γ g) γ V s a := by
    intro a
    have h := terminalShaped_qValue M γ g V s a
    rw [h]
    ring
  have hfun : qValue M γ (fun s' => g s' + V s') s
      = fun a => g s + qValue (terminalShapedMDP M γ g) γ V s a := funext hq
  unfold bellman
  rw [hfun]
  exact (Finset.add_sup' Finset.univ (qValue (terminalShapedMDP M γ g) γ V s) (g s)
    Finset.univ_nonempty).symm

/-- Shaping preserves stochasticity since probabilities are unchanged. -/
private theorem terminalShaped_stochastic {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (hM : M.Stochastic) :
    (terminalShapedMDP M γ g).Stochastic := by
  unfold MDP.Stochastic terminalShapedMDP at *
  simpa using hM

/-- Terminal-potential transport for value iteration (contract C2, proof-only
algebraic identity): for every `γ` and every `M`, including non-stochastic `M`,
value iteration from `g` is pointwise `g` plus the shaped model's existing
zero-terminal `finiteHorizonValue`. -/
private theorem terminalShaped_valueIteration {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) :
    ∀ (k : ℕ) (s : S),
      valueIteration M γ k g s
        = g s + finiteHorizonValue (terminalShapedMDP M γ g) γ k s := by
  intro k
  induction k with
  | zero =>
    intro s
    change g s = g s + finiteHorizonValue (terminalShapedMDP M γ g) γ 0 s
    rw [finiteHorizonValue_zero]
    ring
  | succ k ih =>
    intro s
    have hfun : valueIteration M γ k g
        = fun s' => g s' + finiteHorizonValue (terminalShapedMDP M γ g) γ k s' := funext ih
    have hVI : valueIteration M γ (k + 1) g
        = bellman M γ (valueIteration M γ k g) :=
      Function.iterate_succ_apply' (bellman M γ) k g
    rw [hVI, hfun, finiteHorizonValue_succ]
    exact terminalShaped_bellman M γ g _ s

/-- Terminal-potential transport for policy returns (contract C2, proof-only
algebraic identity): for every `γ`, every `M` (including non-stochastic `M`) and
every policy, the terminal return is pointwise `g` plus the shaped model's
existing zero-terminal policy value. -/
private theorem terminalShaped_policyReturn {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (π : ℕ → S → A) :
    ∀ (k : ℕ) (s : S),
      finiteHorizonPolicyValueTerminal M γ g π k s
        = g s + finiteHorizonPolicyValue (terminalShapedMDP M γ g) γ π k s := by
  intro k
  induction k with
  | zero =>
    intro s
    change g s = g s + finiteHorizonPolicyValue (terminalShapedMDP M γ g) γ π 0 s
    change g s = g s + 0
    ring
  | succ k ih =>
    intro s
    have hfun : finiteHorizonPolicyValueTerminal M γ g π k
        = fun s' => g s' + finiteHorizonPolicyValue (terminalShapedMDP M γ g) γ π k s' :=
      funext ih
    change qValue M γ (finiteHorizonPolicyValueTerminal M γ g π k) s (π (k + 1) s)
      = g s + qValue (terminalShapedMDP M γ g) γ
        (finiteHorizonPolicyValue (terminalShapedMDP M γ g) γ π k) s (π (k + 1) s)
    rw [hfun]
    have h := terminalShaped_qValue M γ g
      (finiteHorizonPolicyValue (terminalShapedMDP M γ g) γ π k) s (π (k + 1) s)
    rw [h]
    ring

/-- **Terminal value dominates every policy (contract C3).** For a stochastic MDP
and `0 ≤ γ`, no nonstationary policy's terminal return exceeds
`valueIteration M γ k g` at any horizon and state. Follows from the transport
identity (C2) and `finiteHorizonValue_ge_policy` on the shaped model. No
`γ < 1` is needed: the horizon is finite. -/
theorem finiteHorizonPolicyValueTerminal_le_valueIteration {S A : Type*} [Fintype S]
    [Fintype A] [Nonempty A] (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (hM : M.Stochastic)
    (hγ : 0 ≤ γ) (π : ℕ → S → A) :
    ∀ (k : ℕ) (s : S),
      finiteHorizonPolicyValueTerminal M γ g π k s ≤ valueIteration M γ k g s := by
  have hM' : (terminalShapedMDP M γ g).Stochastic :=
    terminalShaped_stochastic M γ g hM
  intro k s
  have hT := terminalShaped_policyReturn M γ g π k s
  have hV := terminalShaped_valueIteration M γ g k s
  have hle := finiteHorizonValue_ge_policy (terminalShapedMDP M γ g) γ hM' hγ π k s
  rw [hT, hV]
  gcongr

/-- **An optimal policy exists for the terminal-value finite-horizon problem
(contract C4).** For a stochastic MDP and `0 ≤ γ`, one remaining-step policy
attains `valueIteration M γ k g` at every horizon and state and dominates every
competing policy. Follows from `finiteHorizonGreedy_value` /
`exists_finiteHorizonOptimalPolicy` on the shaped model. This is finite-horizon
optimality, not an infinite-horizon claim. -/
theorem exists_finiteHorizonTerminalOptimalPolicy {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] (M : MDP S A ℝ) (γ : ℝ) (g : S → ℝ) (hM : M.Stochastic) (hγ : 0 ≤ γ) :
    ∃ π : ℕ → S → A,
      (∀ (k : ℕ) (s : S),
        finiteHorizonPolicyValueTerminal M γ g π k s = valueIteration M γ k g s) ∧
      ∀ (π' : ℕ → S → A) (k : ℕ) (s : S),
        finiteHorizonPolicyValueTerminal M γ g π' k s ≤ valueIteration M γ k g s := by
  have hM' : (terminalShapedMDP M γ g).Stochastic :=
    terminalShaped_stochastic M γ g hM
  obtain ⟨π, h_eq, _⟩ := exists_finiteHorizonOptimalPolicy (terminalShapedMDP M γ g) γ hM' hγ
  refine ⟨π, ?_, ?_⟩
  · intro k s
    have hT := terminalShaped_policyReturn M γ g π k s
    have hV := terminalShaped_valueIteration M γ g k s
    have he := h_eq k s
    rw [hT, hV, he]
  · intro π' k s
    exact finiteHorizonPolicyValueTerminal_le_valueIteration M γ g hM hγ π' k s

end FiniteHorizon

end Cslib.Algorithms.Lean.MarkovDecision
