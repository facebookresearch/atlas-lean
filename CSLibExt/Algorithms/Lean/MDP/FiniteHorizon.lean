/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ValueIteration

/-!
# Finite-horizon Bellman problems

For a finite Markov decision process, the finite-horizon value with `k` steps
remaining is `k` steps of value iteration from the zero terminal value,
`valueIteration M γ k (fun _ => 0)`: backward recursion with value `0` at `0`
steps remaining and one Bellman optimality update per additional step
(`finiteHorizonValue_zero`, `finiteHorizonValue_succ`). A nonstationary
policy `π : ℕ → S → A` (`π k s` is the action taken with `k` steps remaining)
has an expected discounted return defined by the same recursion with `qValue`
at the policy's action. This supplies the finite-horizon return semantics
that the infinite-horizon MDP module explicitly does not formalize, and proves
by induction that the greedy backward-recursion policy attains the value and
no policy beats it. No contraction and no discount `< 1` is needed: the horizon is finite.

## Main results

* `Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon.finiteHorizonGreedy_value`:
  the greedy policy's return equals the backward-recursion value.
* `Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon.finiteHorizonValue_ge_policy`:
  no policy earns more than the finite-horizon value.
* `Cslib.Algorithms.Lean.MarkovDecision.FiniteHorizon.exists_finiteHorizonOptimalPolicy`:
  an optimal policy exists for the finite-horizon problem.

## References

Atlas roadmap target MA08.T01. Puterman, *Markov Decision Processes*
(finite-horizon backward induction); the one-step greedy attainment
`qValue_greedy` and monotonicity `qValue_mono` are cited from
`CSLibExt/Algorithms/Lean/MDP/ValueIteration.lean`, not reproved.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

namespace FiniteHorizon

/-- Finite-horizon value: `k` steps of value iteration from the zero terminal
value. With `0` steps remaining the value is `0` (no terminal reward); with
`k + 1` steps remaining it is one Bellman optimality update of the `k`-step
value (`finiteHorizonValue_succ`). -/
noncomputable def finiteHorizonValue {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (γ : ℝ) (k : ℕ) : S → ℝ :=
  valueIteration M γ k (fun _ => 0)

theorem finiteHorizonValue_zero {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (γ : ℝ) : finiteHorizonValue M γ 0 = fun _ => 0 :=
  rfl

theorem finiteHorizonValue_succ {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (γ : ℝ) (k : ℕ) :
    finiteHorizonValue M γ (k + 1) = bellman M γ (finiteHorizonValue M γ k) :=
  Function.iterate_succ_apply' (bellman M γ) k (fun _ => 0)

/-- Expected discounted return of a nonstationary policy `π`, where `π k s` is
the action taken with `k` steps remaining in state `s`. Evaluating a given
policy needs no maximization, so the action type may be infinite. -/
noncomputable def finiteHorizonPolicyValue {S A : Type*} [Fintype S]
    (M : MDP S A ℝ) (γ : ℝ) (π : ℕ → S → A) : ℕ → S → ℝ
  | 0 => fun _ => 0
  | k + 1 => fun s => qValue M γ (finiteHorizonPolicyValue M γ π k) s (π (k + 1) s)

/-- Backward-recursion (greedy) policy: with `k + 1` steps remaining, act
greedily with respect to the `k`-step finite-horizon value. At `k = 0` the
action is irrelevant (no reward is collected); an arbitrary action is used. -/
noncomputable def finiteHorizonGreedy {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (γ : ℝ) : ℕ → S → A
  | 0 => fun _ => (inferInstance : Nonempty A).some
  | k + 1 => greedy M γ (finiteHorizonValue M γ k)

/-- **Backward recursion attains the finite-horizon value (MA08.T01).** The
greedy policy's return equals the value obtained by backward recursion, at
every horizon and state. No contraction / discount `< 1` is needed: the
horizon is finite. -/
theorem finiteHorizonGreedy_value {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (γ : ℝ) :
    ∀ (k : ℕ) (s : S),
      finiteHorizonPolicyValue M γ (finiteHorizonGreedy M γ) k s =
        finiteHorizonValue M γ k s := by
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    have hfun : finiteHorizonPolicyValue M γ (finiteHorizonGreedy M γ) k
        = finiteHorizonValue M γ k := funext ih
    rw [finiteHorizonValue_succ]
    change qValue M γ (finiteHorizonPolicyValue M γ (finiteHorizonGreedy M γ) k) s
        (greedy M γ (finiteHorizonValue M γ k) s)
      = bellman M γ (finiteHorizonValue M γ k) s
    rw [hfun]
    exact qValue_greedy _ s

/-- **Backward-recursion value dominates every policy.** For a stochastic MDP
and `0 ≤ γ`, no nonstationary policy earns more than the finite-horizon value
at any horizon and state. Uses `qValue_mono` (cited, not reproved). -/
theorem finiteHorizonValue_ge_policy {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ : 0 ≤ γ) (π : ℕ → S → A) :
    ∀ (k : ℕ) (s : S),
      finiteHorizonPolicyValue M γ π k s ≤ finiteHorizonValue M γ k s := by
  intro k
  induction k with
  | zero => intro s; exact le_rfl
  | succ k ih =>
    intro s
    have hle : finiteHorizonPolicyValue M γ π k ≤ finiteHorizonValue M γ k := ih
    rw [finiteHorizonValue_succ]
    change qValue M γ (finiteHorizonPolicyValue M γ π k) s (π (k + 1) s)
      ≤ bellman M γ (finiteHorizonValue M γ k) s
    have hmono : qValue M γ (finiteHorizonPolicyValue M γ π k) s (π (k + 1) s)
        ≤ qValue M γ (finiteHorizonValue M γ k) s (π (k + 1) s) :=
      qValue_mono hM hγ hle s (π (k + 1) s)
    refine hmono.trans ?_
    exact Finset.le_sup' _ (Finset.mem_univ (π (k + 1) s))

/-- **An optimal policy exists for the finite-horizon problem.** The
backward-recursion policy attains the value and no policy beats it. -/
theorem exists_finiteHorizonOptimalPolicy {S A : Type*} [Fintype S] [Fintype A]
    [Nonempty A] (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ : 0 ≤ γ) :
    ∃ π : ℕ → S → A,
      (∀ (k : ℕ) (s : S),
        finiteHorizonPolicyValue M γ π k s = finiteHorizonValue M γ k s) ∧
      ∀ (π' : ℕ → S → A) (k : ℕ) (s : S),
        finiteHorizonPolicyValue M γ π' k s ≤ finiteHorizonValue M γ k s := by
  exact ⟨finiteHorizonGreedy M γ, finiteHorizonGreedy_value M γ,
    fun π' k s => finiteHorizonValue_ge_policy M γ hM hγ π' k s⟩

end FiniteHorizon

end Cslib.Algorithms.Lean.MarkovDecision
