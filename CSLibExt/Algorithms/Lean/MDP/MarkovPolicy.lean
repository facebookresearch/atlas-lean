/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.ValueIteration
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Markov policies and the optimality of stationary policies

A (deterministic) *Markov policy* is a sequence `π = (π 0, π 1, …)` of decision rules
`π k : S → A`, one per stage; a stationary policy uses the same rule at every stage. Following
Bertsekas (*Abstract Dynamic Programming*, 3rd ed., Athena Scientific 2022, Section 1.2.1), the
`N`-stage value of `π` with terminal value `V` is the composition of the policies' Bellman
operators,

  `nStageValue M γ π N V = T_{π 0} (T_{π 1} ( ⋯ (T_{π (N - 1)} V)))`,

and its infinite-horizon value is the limit as `N → ∞`. Over the setting of `ValueIteration.lean`
(finite states and actions, stochastic transitions, real rewards, `0 ≤ γ < 1` unless stated):

* `isGreatest_nStageValue`: over a finite horizon `N`, the value iterate `T^N V` is the greatest
  `N`-stage value of a Markov policy, attained by the dynamic programming policy `dpPolicy`, which
  acts greedily for `T^(N - 1 - k) V` at stage `k` (the finite-horizon DP algorithm, Bertsekas,
  *A Course in Reinforcement Learning*, 2nd ed., Section 1.3.1). This needs only `γ ≥ 0`, in any
  ordered field.
* `tendsto_nStageValue`: the `N`-stage values converge, to a limit `markovValue π` that does not
  depend on the terminal value `V` (`dist_nStageValue_le`: two terminal values are forgotten at
  rate `γ ^ N`).
* `markovValue_const`: for a stationary policy the limit is `policyValue`.
* `markovValue_le_optimalValue`: no Markov policy beats `optimalValue`, because its `N`-stage
  value is below the `N`-th value iterate (`nStageValue_le_iterate`).
* `isGreatest_markovValue`: the optimal value is the greatest value of a Markov policy, and it is
  attained by the stationary policy greedy for it: optimal policies may be taken stationary (the
  results (a)-(b) listed in Section 1.2.2 of *Abstract Dynamic Programming*, here for deterministic
  Markov policies of a finite discounted MDP).

Randomized and history-dependent policies are not treated here; stationary randomized policies are
in `StochasticPolicy.lean`.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter Topology

variable {S A K : Type*} [Fintype S] [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **N-stage value of a Markov policy.** The `N`-stage value of the Markov policy `π` with
terminal value `V`:
`T_{π 0} (T_{π 1} ( ⋯ (T_{π (N - 1)} V)))`, where `T_μ` is the Bellman operator of the decision
rule `μ`. -/
def nStageValue (M : MDP S A K) (γ : K) : (ℕ → S → A) → ℕ → (S → K) → S → K
  | _, 0, V => V
  | π, N + 1, V => policyBellman M γ (π 0) (nStageValue M γ (fun k => π (k + 1)) N V)

/-- **Value of a Markov policy.** The value of the Markov policy `π`: the limit of its `N`-stage
values with terminal value `0`. For a stochastic MDP and `0 ≤ γ < 1` the limit exists, and any
terminal value gives the same limit (`tendsto_nStageValue`). -/
noncomputable def markovValue (M : MDP S A ℝ) (γ : ℝ) (π : ℕ → S → A) : S → ℝ :=
  limUnder atTop fun N => nStageValue M γ π N 0

variable {M : MDP S A K} {γ : K}

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **Appending a stage at the end**: the `(N + 1)`-stage value is the `N`-stage value with the
terminal value replaced by `T_{π N} V`. -/
theorem nStageValue_succ (π : ℕ → S → A) (N : ℕ) (V : S → K) :
    nStageValue M γ π (N + 1) V = nStageValue M γ π N (policyBellman M γ (π N) V) := by
  induction N generalizing π with
  | zero => rfl
  | succ N ih => rw [nStageValue, ih]; rfl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- **N-stage values of a stationary policy**: the `N`-stage value of the stationary policy `μ` is
the `N`-th iterate of `T_μ`. -/
theorem nStageValue_const (μ : S → A) (N : ℕ) (V : S → K) :
    nStageValue M γ (fun _ => μ) N V = (policyBellman M γ μ)^[N] V := by
  induction N with
  | zero => rfl
  | succ N ih => rw [nStageValue, ih, Function.iterate_succ_apply']

/-- **A Markov policy does no better than value iteration over `N` stages**: for a stochastic MDP
and `γ ≥ 0`, `nStageValue M γ π N V ≤ (bellman M γ)^[N] V` for every Markov policy `π`. -/
theorem nStageValue_le_iterate [Fintype A] [Nonempty A] (hM : M.Stochastic) (hγ : 0 ≤ γ)
    (π : ℕ → S → A) (N : ℕ) (V : S → K) : nStageValue M γ π N V ≤ (bellman M γ)^[N] V := by
  induction N generalizing π with
  | zero => exact le_refl V
  | succ N ih =>
      rw [nStageValue, Function.iterate_succ_apply']
      exact (policyBellman_mono hM hγ _ (ih _)).trans (policyBellman_le_bellman _ _)

/-- **The dynamic programming policy**: for horizon `N` and terminal value `V`, the Markov policy
that at stage `k < N` acts greedily for the value iterate `T^(N - 1 - k) V`. -/
noncomputable def dpPolicy [Fintype A] [Nonempty A] (M : MDP S A K) (γ : K) (N : ℕ)
    (V : S → K) : ℕ → S → A :=
  fun k => greedy M γ ((bellman M γ)^[N - 1 - k] V)

omit [IsStrictOrderedRing K] in
/-- **The dynamic programming policy attains the value iterate**: its `N`-stage value with
terminal value `V` is `T^N V`. -/
theorem nStageValue_dpPolicy [Fintype A] [Nonempty A] (N : ℕ) (V : S → K) :
    nStageValue M γ (dpPolicy M γ N V) N V = (bellman M γ)^[N] V := by
  induction N with
  | zero => rfl
  | succ N ih =>
      have hshift : (fun k => dpPolicy M γ (N + 1) V (k + 1)) = dpPolicy M γ N V := by
        funext k
        simp only [dpPolicy]
        congr 2
        omega
      rw [nStageValue, hshift, ih, Function.iterate_succ_apply']
      simp only [dpPolicy, Nat.add_sub_cancel, Nat.sub_zero]
      exact policyBellman_greedy _

/-- **Optimality of the dynamic programming algorithm** (finite horizon; Bertsekas, *A Course in
Reinforcement Learning*, 2nd ed., Section 1.3.1, the DP algorithm (1.15), here with stationary
data and discount `γ ≥ 0`): for a stochastic MDP, a horizon `N` and a terminal value `V`, the
value iterate `T^N V` is the greatest `N`-stage value of a Markov policy, in every state at once,
and the dynamic programming policy `dpPolicy M γ N V` attains it. -/
theorem isGreatest_nStageValue [Fintype A] [Nonempty A] (hM : M.Stochastic) (hγ : 0 ≤ γ)
    (N : ℕ) (V : S → K) :
    IsGreatest (Set.range fun π => nStageValue M γ π N V) ((bellman M γ)^[N] V) :=
  ⟨⟨dpPolicy M γ N V, nStageValue_dpPolicy N V⟩, by
    rintro _ ⟨π, rfl⟩
    exact nStageValue_le_iterate hM hγ π N V⟩

variable {M : MDP S A ℝ} {γ : ℝ} (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hM hγ0 hγ1

/-- **The terminal value is forgotten geometrically**: for all terminal values `V`, `W`,
`dist (nStageValue M γ π N V) (nStageValue M γ π N W) ≤ γ ^ N * dist V W` in the sup metric. -/
theorem dist_nStageValue_le (π : ℕ → S → A) (N : ℕ) (V W : S → ℝ) :
    dist (nStageValue M γ π N V) (nStageValue M γ π N W) ≤ γ ^ N * dist V W := by
  induction N generalizing π with
  | zero => simp [nStageValue]
  | succ N ih =>
      simp only [nStageValue]
      have h := (policyBellman_contracting hM hγ0 hγ1 (π 0)).dist_le_mul
        (nStageValue M γ (fun k => π (k + 1)) N V) (nStageValue M γ (fun k => π (k + 1)) N W)
      rw [Real.coe_toNNReal γ hγ0] at h
      calc _ ≤ γ * dist (nStageValue M γ (fun k => π (k + 1)) N V)
            (nStageValue M γ (fun k => π (k + 1)) N W) := h
        _ ≤ γ * (γ ^ N * dist V W) := by gcongr; exact ih _
        _ = γ ^ (N + 1) * dist V W := by ring

/-- The `N`-stage values of a Markov policy form a Cauchy sequence. -/
private theorem cauchySeq_nStageValue [Finite A] (π : ℕ → S → A) (V : S → ℝ) :
    CauchySeq fun N => nStageValue M γ π N V := by
  have := Fintype.ofFinite A
  set C := ∑ s, ∑ a, |V s - qValue M γ V s a|
  have hC : ∀ μ : S → A, dist V (policyBellman M γ μ V) ≤ C := by
    intro μ
    refine (dist_pi_le_iff (Finset.sum_nonneg fun s _ =>
      Finset.sum_nonneg fun a _ => abs_nonneg _)).2 fun s => ?_
    rw [Real.dist_eq]
    calc |V s - policyBellman M γ μ V s| ≤ ∑ a, |V s - qValue M γ V s a| :=
          Finset.single_le_sum (f := fun a => |V s - qValue M γ V s a|)
            (fun a _ => abs_nonneg _) (Finset.mem_univ (μ s))
      _ ≤ C := Finset.single_le_sum (f := fun s => ∑ a, |V s - qValue M γ V s a|)
            (fun s _ => Finset.sum_nonneg fun a _ => abs_nonneg _) (Finset.mem_univ s)
  refine cauchySeq_of_le_geometric γ C hγ1 fun N => ?_
  rw [nStageValue_succ]
  calc _ ≤ γ ^ N * dist V (policyBellman M γ (π N) V) := dist_nStageValue_le hM hγ0 hγ1 π N _ _
    _ ≤ γ ^ N * C := by gcongr; exact hC _
    _ = C * γ ^ N := mul_comm _ _

/-- **The `N`-stage values of a Markov policy converge**, from every terminal value `V`, to
`markovValue π`. -/
theorem tendsto_nStageValue [Finite A] (π : ℕ → S → A) (V : S → ℝ) :
    Tendsto (fun N => nStageValue M γ π N V) atTop (𝓝 (markovValue M γ π)) := by
  have h0 : Tendsto (fun N => nStageValue M γ π N 0) atTop (𝓝 (markovValue M γ π)) :=
    tendsto_nhds_limUnder (cauchySeq_tendsto_of_complete (cauchySeq_nStageValue hM hγ0 hγ1 π 0))
  refine h0.congr_dist (squeeze_zero (fun _ => dist_nonneg)
    (fun N => dist_nStageValue_le hM hγ0 hγ1 π N 0 V) ?_)
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (dist (0 : S → ℝ) V)

/-- **The value of a stationary policy**, as a Markov policy, is its `policyValue`. -/
theorem markovValue_const [Finite A] (μ : S → A) :
    markovValue M γ (fun _ => μ) = policyValue M γ hM hγ0 hγ1 μ := by
  refine tendsto_nhds_unique (tendsto_nStageValue hM hγ0 hγ1 (fun _ => μ) 0) ?_
  simp only [nStageValue_const]
  exact ContractingWith.tendsto_iterate_fixedPoint (policyBellman_contracting hM hγ0 hγ1 μ) 0

/-- **No Markov policy beats the optimal value**: `markovValue π ≤ optimalValue` in every state. -/
theorem markovValue_le_optimalValue [Fintype A] [Nonempty A] (π : ℕ → S → A) :
    markovValue M γ π ≤ optimalValue M γ hM hγ0 hγ1 := by
  intro s
  have h1 := (continuous_apply s).continuousAt.tendsto.comp (tendsto_nStageValue hM hγ0 hγ1 π 0)
  have h2 := (continuous_apply s).continuousAt.tendsto.comp (tendsto_valueIteration hM hγ0 hγ1 0)
  exact le_of_tendsto_of_tendsto' h1 h2 fun N => nStageValue_le_iterate hM hγ0 π N 0 s

/-- **Optimality of stationary policies** (Bertsekas, *Abstract Dynamic Programming*, 3rd ed.,
Section 1.2.2, results (a)-(b), for deterministic Markov policies of a finite discounted MDP): the
optimal value is the greatest value of a Markov policy, and the stationary policy greedy for the
optimal value attains it. -/
theorem isGreatest_markovValue [Fintype A] [Nonempty A] :
    IsGreatest (Set.range (markovValue M γ)) (optimalValue M γ hM hγ0 hγ1) := by
  refine ⟨⟨fun _ => greedy M γ (optimalValue M γ hM hγ0 hγ1), ?_⟩, ?_⟩
  · rw [markovValue_const, policyValue_greedy]
  · rintro _ ⟨π, rfl⟩
    exact markovValue_le_optimalValue hM hγ0 hγ1 π

end Cslib.Algorithms.Lean.MarkovDecision
