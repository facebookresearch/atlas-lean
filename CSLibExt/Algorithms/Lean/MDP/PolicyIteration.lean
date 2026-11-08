/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ValueIteration
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Card

/-!
# Policy iteration for finite discounted Markov decision processes

Policy iteration (Howard, *Dynamic Programming and Markov Processes*, 1960) alternates policy
evaluation (the value `policyValue π` of the current policy) and policy improvement (a policy
greedy for that value, `improve π`). Over the setting of `ValueIteration.lean` (finite states and
actions, discount `0 ≤ γ < 1`, real values), the main results are (Puterman, *Markov Decision
Processes*, Theorems 6.4.1 and 6.4.2):

* `policyValue_le_policyValue_improve` (policy improvement theorem): the improved policy is at
  least as good in every state.
* `policyValue_improve_eq_iff`: improvement leaves the value unchanged exactly when the current
  policy is optimal (`policyValue π = optimalValue`); otherwise the value strictly improves
  (`policyValue_improve_ne`).
* `policyValue_policyIteration`: after `Fintype.card (S → A)` improvement steps (at most
  `|A| ^ |S|`) the policy is optimal, from any starting policy. The proof: while the policy is not
  optimal the values strictly increase (`policyValue_improve_ne`,
  `policyValue_policyIteration_mono`), so the policies visited are pairwise distinct, and there are
  only `Fintype.card (S → A)` of them.

## Cost model

No `TimeM` cost model: policy evaluation is exact (the fixed point of the policy's Bellman
operator, a linear system), so these are statements about the iteration count only; the bound is
`Fintype.card (S → A)` improvement steps.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter Topology

variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] {M : MDP S A ℝ} {γ : ℝ}
  (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- Policy improvement: a policy greedy for the value of `π`. -/
noncomputable def improve (π : S → A) : S → A :=
  greedy M γ (policyValue M γ hM hγ0 hγ1 π)

/-- Policy iteration: `n` improvement steps from `π`. -/
noncomputable def policyIteration (n : ℕ) (π : S → A) : S → A :=
  (improve hM hγ0 hγ1)^[n] π

include hM hγ0 hγ1

omit [Fintype A] [Nonempty A] in
/-- Iterating a policy's Bellman operator from a value it does not decrease converges to the
policy's value from below. -/
theorem le_policyValue_of_le_policyBellman (π : S → A) {V : S → ℝ}
    (h : V ≤ policyBellman M γ π V) : V ≤ policyValue M γ hM hγ0 hγ1 π := by
  have hle : ∀ n, V ≤ (policyBellman M γ π)^[n] V := by
    intro n
    induction n with
    | zero => exact le_refl V
    | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact h.trans (policyBellman_mono hM hγ0 π ih)
  have ht := ContractingWith.tendsto_iterate_fixedPoint (policyBellman_contracting hM hγ0 hγ1 π) V
  intro s
  exact ge_of_tendsto' ((continuous_apply s).continuousAt.tendsto.comp ht) fun n => hle n s

/-- **Policy improvement theorem**: the improved policy is at least as good everywhere. -/
theorem policyValue_le_policyValue_improve (π : S → A) :
    policyValue M γ hM hγ0 hγ1 π ≤ policyValue M γ hM hγ0 hγ1 (improve hM hγ0 hγ1 π) := by
  refine le_policyValue_of_le_policyBellman hM hγ0 hγ1 _ ?_
  rw [improve, policyBellman_greedy]
  calc policyValue M γ hM hγ0 hγ1 π
      = policyBellman M γ π (policyValue M γ hM hγ0 hγ1 π) :=
        (policyBellman_policyValue hM hγ0 hγ1 π).symm
    _ ≤ bellman M γ (policyValue M γ hM hγ0 hγ1 π) := policyBellman_le_bellman π _

/-- **Improvement stalls exactly at optimal policies.** -/
theorem policyValue_improve_eq_iff (π : S → A) :
    policyValue M γ hM hγ0 hγ1 (improve hM hγ0 hγ1 π) = policyValue M γ hM hγ0 hγ1 π ↔
      policyValue M γ hM hγ0 hγ1 π = optimalValue M γ hM hγ0 hγ1 := by
  constructor
  · intro h
    refine eq_optimalValue_of_bellman_eq hM hγ0 hγ1 ?_
    have h1 := policyBellman_policyValue hM hγ0 hγ1 (improve hM hγ0 hγ1 π)
    rw [h, improve, policyBellman_greedy] at h1
    exact h1
  · intro h
    refine le_antisymm ?_ (policyValue_le_policyValue_improve hM hγ0 hγ1 π)
    rw [h]
    exact policyValue_le_optimalValue hM hγ0 hγ1 _

/-- Away from optimality the value strictly improves somewhere. -/
theorem policyValue_improve_ne (π : S → A)
    (h : policyValue M γ hM hγ0 hγ1 π ≠ optimalValue M γ hM hγ0 hγ1) :
    policyValue M γ hM hγ0 hγ1 (improve hM hγ0 hγ1 π) ≠ policyValue M γ hM hγ0 hγ1 π :=
  fun he => h ((policyValue_improve_eq_iff hM hγ0 hγ1 π).1 he)

/-- The values along policy iteration never decrease. -/
theorem policyValue_policyIteration_mono (π : S → A) {i j : ℕ} (hij : i ≤ j) :
    policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 i π) ≤
      policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 j π) := by
  induction hij with
  | refl => exact le_refl _
  | step _ ih =>
      refine ih.trans ?_
      simp only [policyIteration, Function.iterate_succ_apply']
      exact policyValue_le_policyValue_improve hM hγ0 hγ1 _

/-- Once optimal, policy iteration stays optimal. -/
theorem policyValue_policyIteration_of_eq (π : S → A) {i j : ℕ} (hij : i ≤ j)
    (h : policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 i π) =
      optimalValue M γ hM hγ0 hγ1) :
    policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 j π) =
      optimalValue M γ hM hγ0 hγ1 :=
  le_antisymm (policyValue_le_optimalValue hM hγ0 hγ1 _)
    (h ▸ policyValue_policyIteration_mono hM hγ0 hγ1 π hij)

/-- **Policy iteration terminates**: after `Fintype.card (S → A)` steps (at most `|A| ^ |S|`), the
policy is optimal. -/
theorem policyValue_policyIteration [DecidableEq S] (π : S → A) :
    policyValue M γ hM hγ0 hγ1 (policyIteration hM hγ0 hγ1 (Fintype.card (S → A)) π) =
      optimalValue M γ hM hγ0 hγ1 := by
  set N := Fintype.card (S → A)
  set P : ℕ → S → A := fun k => policyIteration hM hγ0 hγ1 k π
  set V : ℕ → S → ℝ := fun k => policyValue M γ hM hγ0 hγ1 (P k)
  by_contra hN
  -- every step up to `N` is strictly improving
  have hne : ∀ k ≤ N, V k ≠ optimalValue M γ hM hγ0 hγ1 := fun k hk hk' =>
    hN (policyValue_policyIteration_of_eq hM hγ0 hγ1 π hk hk')
  have hstep : ∀ k < N, V (k + 1) ≠ V k := by
    intro k hk
    have := policyValue_improve_ne hM hγ0 hγ1 (P k) (hne k hk.le)
    simpa [V, P, policyIteration, Function.iterate_succ_apply'] using this
  -- so the policies `P 0, …, P N` are pairwise distinct
  have hinj : Function.Injective fun k : Fin (N + 1) => P k := by
    intro a b hab
    simp only at hab
    by_contra hne'
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne') with h | h
    · have h1 : V a ≤ V (a + 1) := policyValue_policyIteration_mono hM hγ0 hγ1 π (by omega)
      have h2 : V (a + 1) ≤ V b := policyValue_policyIteration_mono hM hγ0 hγ1 π (by omega)
      have h3 : V b = V a := by simp only [V]; rw [hab]
      exact hstep a (by omega) (le_antisymm (h3 ▸ h2) h1)
    · have h1 : V b ≤ V (b + 1) := policyValue_policyIteration_mono hM hγ0 hγ1 π (by omega)
      have h2 : V (b + 1) ≤ V a := policyValue_policyIteration_mono hM hγ0 hγ1 π (by omega)
      have h3 : V a = V b := by simp only [V]; rw [hab]
      exact hstep b (by omega) (le_antisymm (h3 ▸ h2) h1)
  have := Fintype.card_le_of_injective _ hinj
  simp only [Fintype.card_fin] at this
  omega

end Cslib.Algorithms.Lean.MarkovDecision
