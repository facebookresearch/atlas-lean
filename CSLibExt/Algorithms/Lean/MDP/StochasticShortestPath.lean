/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.MarkovRewardProcess
public import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Stochastic shortest path problems: proper policies

A *stochastic shortest path* (SSP) problem (Bertsekas, *Abstract Dynamic Programming*, 3rd ed.,
Athena Scientific 2022, Example 1.2.6; Bertsekas and Tsitsiklis, Math. Oper. Res. 16 (1991)) is an
undiscounted (`γ = 1`) Markov decision process with a cost-free absorbing termination state `t`.
We keep only the nonterminal states `S`: the transition probabilities `M.prob s a s'` among them
are *substochastic* (`MDP.Substochastic`: nonnegative, each row summing to at most `1`), the
missing mass `1 - ∑ s', M.prob s a s'` being the probability of terminating. As everywhere in
this library rewards are maximized: Bertsekas's cost per stage `g(x, u)` is `-M.reward x u`, and
his `T_μ` and `T` are `policyBellman M 1 μ` and `bellman M 1` up to this sign change. Every action
is allowed in every state.

A stationary policy `μ` is *proper* (`MDP.Proper`) if, from every initial state, termination has
positive probability within `n = |S|` stages: every row sum of `P_μ ^ n` is `< 1`, where
`P_μ = transitionMatrix M μ`. Main results, for a proper policy:

* `policyBellman_iterate_sub`: `T_μ^k J - T_μ^k J' = P_μ^k (J - J')`, and
  `contractingWith_policyBellman_iterate`: `T_μ^n` is a contraction in the sup norm, i.e. `T_μ` is
  an `n`-stage contraction (Example 1.2.6 of *Abstract Dynamic Programming*).
* `policyBellman_sspValue`, `eq_sspValue_of_policyBellman_eq`: `T_μ` has a unique fixed point
  `sspValue M μ`, and `tendsto_policyBellman_iterate`: value iteration `T_μ^k J` converges to it
  from every `J`.
* `tendsto_sum_pow_mulVec`: `sspValue M μ` is the total expected reward until termination,
  `∑_{k ≥ 0} P_μ^k r_μ`.

A discounted problem is an SSP in which the system terminates with probability `1 - γ` at every
stage (`MDP.toSSP`; Bertsekas, *A Course in Reinforcement Learning*, 2nd ed., Section 1.4,
item (b)): every policy is then proper (`proper_toSSP`) and its SSP value is its discounted value
(`sspValue_toSSP`).

The `bellman_ssp` theorem below gives Bellman's equation and convergence of value iteration under
the strong SSP conditions, with optimality among deterministic stationary policies.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision

open Filter Topology Matrix Simplex

variable {S A : Type*} [Fintype S] [DecidableEq S]

/-- **Substochastic transitions.** Transition probabilities among the nonterminal states are
nonnegative and each row sums to at
most `1`; the missing mass is the probability of moving to the termination state. -/
def MDP.Substochastic (M : MDP S A ℝ) : Prop :=
  (∀ s a s', 0 ≤ M.prob s a s') ∧ ∀ s a, ∑ s', M.prob s a s' ≤ 1

/-- **Transition matrix of a stationary policy.** The transition matrix of `μ` among the nonterminal
states: `P_μ s s' = M.prob s (μ s) s'`. -/
def transitionMatrix (M : MDP S A ℝ) (μ : S → A) : Matrix S S ℝ :=
  Matrix.of fun s s' => M.prob s (μ s) s'

/-- **Proper policy.** A stationary policy is proper if from every initial state termination has
positive probability within `|S|` stages: every row sum of `P_μ ^ |S|` is less than `1`. -/
def MDP.Proper (M : MDP S A ℝ) (μ : S → A) : Prop :=
  ∀ s, ∑ s', (transitionMatrix M μ ^ Fintype.card S) s s' < 1

/-- **Value of a stationary policy in a stochastic shortest path problem**: the limit of its
`N`-stage total rewards `T_μ^N 0`. For a proper policy of a substochastic MDP the limit exists
(`tendsto_policyBellman_iterate`) and is the unique fixed point of `T_μ`. -/
noncomputable def sspValue (M : MDP S A ℝ) (μ : S → A) : S → ℝ :=
  limUnder atTop fun N => (policyBellman M 1 μ)^[N] 0

variable {M : MDP S A ℝ}

omit [Fintype S] [DecidableEq S] in
private theorem transitionMatrix_apply (μ : S → A) (s s' : S) :
    transitionMatrix M μ s s' = M.prob s (μ s) s' := rfl

omit [Fintype S] [DecidableEq S] in
/-- **The transition matrix of a deterministic policy is its policy kernel**: for the Dirac policy
`StochasticPolicy.ofDet μ`, the kernel `policyKernel M (ofDet μ)` of `StochasticPolicy.lean` is
`transitionMatrix M μ`. (`policyKernel` is row-stochastic for stochastic MDPs; `transitionMatrix`
is used here because SSP transitions are only substochastic.) -/
theorem policyKernel_ofDet [Fintype A] (μ : S → A) :
    policyKernel M (StochasticPolicy.ofDet μ) = transitionMatrix M μ := by
  classical
  ext s s'
  simp [policyKernel, StochasticPolicy.ofDet_prob, transitionMatrix_apply]

omit [DecidableEq S] in
/-- **Undiscounted Bellman operators are affine**: with `γ = 1`, `T_μ J = r_μ + P_μ J`. -/
theorem policyBellman_one_eq (μ : S → A) (J : S → ℝ) :
    policyBellman M 1 μ J = (fun s => M.reward s (μ s)) + transitionMatrix M μ *ᵥ J := by
  funext s
  simp [policyBellman, qValue, mulVec, dotProduct, transitionMatrix_apply]

/-- **Iterates of `T_μ` differ by powers of `P_μ`**: `T_μ^k J - T_μ^k J' = P_μ^k (J - J')`. -/
theorem policyBellman_iterate_sub (μ : S → A) (k : ℕ) (J J' : S → ℝ) :
    (policyBellman M 1 μ)^[k] J - (policyBellman M 1 μ)^[k] J' =
      (transitionMatrix M μ ^ k) *ᵥ (J - J') := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', policyBellman_one_eq,
        policyBellman_one_eq, add_sub_add_left_eq_sub, ← mulVec_sub, ih, mulVec_mulVec, ← pow_succ']

/-- **The `N`-stage total reward**: `T_μ^N 0 = ∑_{k < N} P_μ^k r_μ`. -/
theorem policyBellman_iterate_zero (μ : S → A) (N : ℕ) :
    (policyBellman M 1 μ)^[N] 0 =
      ∑ k ∈ Finset.range N, (transitionMatrix M μ ^ k) *ᵥ fun s => M.reward s (μ s) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, policyBellman_one_eq, Finset.sum_range_succ',
        mulVec_sum, pow_zero, one_mulVec, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mulVec_mulVec, ← pow_succ']

/-- **Powers of a substochastic matrix are substochastic**: the powers of the transition matrix of
a policy in a substochastic MDP are nonnegative with row sums at most `1`. -/
theorem transitionMatrix_pow_nonneg_and_sum_le (hM : M.Substochastic) (μ : S → A) (k : ℕ) :
    (∀ s s', 0 ≤ (transitionMatrix M μ ^ k) s s') ∧
      ∀ s, ∑ s', (transitionMatrix M μ ^ k) s s' ≤ 1 := by
  classical
  induction k with
  | zero =>
      refine ⟨fun s s' => ?_, fun s => ?_⟩
      · rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
      · simp only [pow_zero, Matrix.one_apply]
        rw [Finset.sum_ite_eq]; simp
  | succ k ih =>
      refine ⟨fun s s' => ?_, fun s => ?_⟩
      · rw [pow_succ', Matrix.mul_apply]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hM.1 _ _ _) (ih.1 j s')
      · simp only [pow_succ', Matrix.mul_apply]
        rw [Finset.sum_comm]
        calc ∑ j, ∑ s', transitionMatrix M μ s j * (transitionMatrix M μ ^ k) j s'
            = ∑ j, transitionMatrix M μ s j * ∑ s', (transitionMatrix M μ ^ k) j s' := by
              simp only [Finset.mul_sum]
          _ ≤ ∑ j, transitionMatrix M μ s j * 1 :=
              Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih.2 j) (hM.1 _ _ _)
          _ ≤ 1 := by simpa [transitionMatrix_apply] using hM.2 s (μ s)

omit [DecidableEq S] in
/-- A nonnegative matrix moves a vector bounded by `d` by at most its row sum times `d`. -/
private theorem abs_mulVec_le {Q : Matrix S S ℝ} (hQ : ∀ s s', 0 ≤ Q s s') {v : S → ℝ} {d : ℝ}
    (hv : ∀ s', |v s'| ≤ d) (s : S) : |(Q *ᵥ v) s| ≤ (∑ s', Q s s') * d := by
  rw [Finset.sum_mul]
  calc |(Q *ᵥ v) s| = |∑ s', Q s s' * v s'| := rfl
    _ ≤ ∑ s', |Q s s' * v s'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', Q s s' * d := Finset.sum_le_sum fun s' _ => by
        rw [abs_mul, abs_of_nonneg (hQ s s')]
        exact mul_le_mul_of_nonneg_left (hv s') (hQ s s')

/-- The contraction modulus of `T_μ^|S|`: the largest row sum of `P_μ ^ |S|` (zero if there are no
states). -/
private noncomputable def modulus (hM : M.Substochastic) (μ : S → A) : NNReal :=
  Finset.univ.sup fun s => ⟨∑ s', (transitionMatrix M μ ^ Fintype.card S) s s',
    Finset.sum_nonneg fun s' _ => (transitionMatrix_pow_nonneg_and_sum_le hM μ _).1 s s'⟩

private theorem dist_iterate_le (hM : M.Substochastic) (μ : S → A) (k : ℕ) (J J' : S → ℝ)
    {c : ℝ} (hc : 0 ≤ c) (hrow : ∀ s, ∑ s', (transitionMatrix M μ ^ k) s s' ≤ c) :
    dist ((policyBellman M 1 μ)^[k] J) ((policyBellman M 1 μ)^[k] J') ≤ c * dist J J' := by
  refine (dist_pi_le_iff (by positivity)).2 fun s => ?_
  rw [Real.dist_eq, ← Pi.sub_apply, policyBellman_iterate_sub]
  refine (abs_mulVec_le (transitionMatrix_pow_nonneg_and_sum_le hM μ k).1 (d := dist J J')
    (fun s' => by rw [Pi.sub_apply, ← Real.dist_eq]; exact dist_le_pi_dist J J' s') s).trans ?_
  exact mul_le_mul_of_nonneg_right (hrow s) dist_nonneg

/-- **A proper policy's Bellman operator is an `|S|`-stage contraction** in the sup norm
(Bertsekas, *Abstract Dynamic Programming*, 3rd ed., Example 1.2.6): `T_μ^|S|` is a contraction
for some modulus `K < 1` (the proof takes the largest row sum of `P_μ ^ |S|`). -/
theorem contractingWith_policyBellman_iterate (hM : M.Substochastic) {μ : S → A}
    (hμ : M.Proper μ) :
    ∃ K : NNReal, ContractingWith K (policyBellman M 1 μ)^[Fintype.card S] := by
  refine ⟨modulus hM μ, ?_, LipschitzWith.of_dist_le_mul fun J J' => ?_⟩
  · refine (Finset.sup_lt_iff
      (show (⊥ : NNReal) < 1 by rw [bot_eq_zero]; exact one_pos)).2 fun s _ => ?_
    exact (show (⟨_, _⟩ : NNReal) < 1 from NNReal.coe_lt_coe.1 (hμ s))
  · refine dist_iterate_le hM μ _ J J' (modulus hM μ).2 fun s => ?_
    have : (⟨∑ s', (transitionMatrix M μ ^ Fintype.card S) s s',
        Finset.sum_nonneg fun s' _ => (transitionMatrix_pow_nonneg_and_sum_le hM μ _).1 s s'⟩ :
          NNReal) ≤ modulus hM μ :=
      Finset.le_sup (f := fun s => (⟨∑ s', (transitionMatrix M μ ^ Fintype.card S) s s',
        Finset.sum_nonneg fun s' _ =>
          (transitionMatrix_pow_nonneg_and_sum_le hM μ _).1 s s'⟩ : NNReal)) (Finset.mem_univ s)
    exact this

section Proper

variable (hM : M.Substochastic) {μ : S → A} (hμ : M.Proper μ)
include hM hμ

/-- **Value iteration for a proper policy converges**, from every `J`, to a fixed point of `T_μ`. -/
private theorem exists_tendsto_iterate :
    ∃ V : S → ℝ, policyBellman M 1 μ V = V ∧ (∀ W, policyBellman M 1 μ W = W → W = V) ∧
      ∀ J, Tendsto (fun k => (policyBellman M 1 μ)^[k] J) atTop (𝓝 V) := by
  obtain ⟨K, hK⟩ := contractingWith_policyBellman_iterate hM hμ
  set n := Fintype.card S
  set T := policyBellman M 1 μ
  set V := ContractingWith.fixedPoint _ hK
  have hV : T^[n] V = V := ContractingWith.fixedPoint_isFixedPt hK
  have hTV : T V = V := by
    refine ContractingWith.fixedPoint_unique hK ?_
    change T^[n] (T V) = T V
    rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hV]
  have huniq : ∀ W, T W = W → W = V := fun W hW =>
    ContractingWith.fixedPoint_unique hK (Function.iterate_fixed hW n)
  refine ⟨V, hTV, huniq, fun J => ?_⟩
  rcases isEmpty_or_nonempty S with hS | hS
  · have : ∀ W W' : S → ℝ, W = W' := fun W W' => funext fun s => (IsEmpty.false s).elim
    simp only [this _ V]
    exact tendsto_const_nhds
  have hn : 0 < n := Fintype.card_pos
  -- `dist (T^k J) V ≤ K ^ (k / n) * dist J V`
  have hbound : ∀ k, dist (T^[k] J) V ≤ (K : ℝ) ^ (k / n) * dist J V := by
    intro k
    have hk : T^[k] J = (T^[n])^[k / n] (T^[k % n] J) := by
      rw [← Function.iterate_mul, ← Function.iterate_add_apply, Nat.div_add_mod]
    rw [hk]
    calc dist ((T^[n])^[k / n] (T^[k % n] J)) V
        = dist ((T^[n])^[k / n] (T^[k % n] J)) ((T^[n])^[k / n] V) := by
          rw [Function.iterate_fixed hV]
      _ ≤ (K : ℝ) ^ (k / n) * dist (T^[k % n] J) V := by
          have := (hK.toLipschitzWith.iterate (k / n)).dist_le_mul (T^[k % n] J) V
          simpa using this
      _ ≤ (K : ℝ) ^ (k / n) * dist J V := by
          gcongr
          have h := dist_iterate_le hM μ (k % n) J V zero_le_one
            (transitionMatrix_pow_nonneg_and_sum_le hM μ _).2
          rwa [Function.iterate_fixed hTV, one_mul] at h
  have hdiv : Tendsto (fun k => k / n) atTop atTop :=
    tendsto_atTop_atTop.2 fun q => ⟨n * q, fun k hk => (Nat.le_div_iff_mul_le hn).2 (by
      rw [mul_comm]; exact hk)⟩
  have hK1 : (K : ℝ) < 1 := hK.1
  have hpow : Tendsto (fun k => (K : ℝ) ^ (k / n) * dist J V) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one K.2 hK1).comp hdiv).mul_const (dist J V)
  exact tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) hbound hpow)

/-- **Value iteration for a proper policy converges** to `sspValue M μ`, from every `J`. -/
theorem tendsto_policyBellman_iterate (J : S → ℝ) :
    Tendsto (fun k => (policyBellman M 1 μ)^[k] J) atTop (𝓝 (sspValue M μ)) := by
  obtain ⟨V, -, -, hV⟩ := exists_tendsto_iterate hM hμ
  have hlim : sspValue M μ = V := tendsto_nhds_unique (tendsto_nhds_limUnder ⟨V, hV 0⟩) (hV 0)
  rw [hlim]
  exact hV J

/-- **The value of a proper policy solves its Bellman equation** `T_μ V = V`. -/
theorem policyBellman_sspValue : policyBellman M 1 μ (sspValue M μ) = sspValue M μ := by
  obtain ⟨V, hTV, -, hV⟩ := exists_tendsto_iterate hM hμ
  rwa [tendsto_nhds_unique (tendsto_policyBellman_iterate hM hμ 0) (hV 0)]

/-- **Uniqueness of the value of a proper policy**: it is the only solution of `T_μ V = V`. -/
theorem eq_sspValue_of_policyBellman_eq {V : S → ℝ} (h : policyBellman M 1 μ V = V) :
    V = sspValue M μ := by
  obtain ⟨W, -, huniq, hW⟩ := exists_tendsto_iterate hM hμ
  rw [huniq V h, tendsto_nhds_unique (tendsto_policyBellman_iterate hM hμ 0) (hW 0)]

/-- **The value of a proper policy is its total expected reward until termination**:
`∑_{k < N} P_μ^k r_μ → sspValue M μ` as `N → ∞`. -/
theorem tendsto_sum_pow_mulVec :
    Tendsto (fun N => ∑ k ∈ Finset.range N, (transitionMatrix M μ ^ k) *ᵥ
      fun s => M.reward s (μ s)) atTop (𝓝 (sspValue M μ)) := by
  simpa only [policyBellman_iterate_zero] using tendsto_policyBellman_iterate hM hμ 0

end Proper

section Optimal

/-! ## Bellman's equation under the strong SSP conditions -/

omit [DecidableEq S] in
private theorem qValue_one_mono (hM : M.Substochastic) {U V : S → ℝ} (h : U ≤ V)
    (s : S) (a : A) : qValue M 1 U s a ≤ qValue M 1 V s a := by
  simp only [qValue, one_mul]
  exact add_le_add_right (Finset.sum_le_sum fun s' _ =>
    mul_le_mul_of_nonneg_left (h s') (hM.1 s a s')) _

omit [DecidableEq S] in
private theorem monotone_sspPolicyBellman (hM : M.Substochastic) (μ : S → A) :
    Monotone (policyBellman M 1 μ) := fun _ _ h s => qValue_one_mono hM h s (μ s)

-- A policy that improves an estimate has iterates bounded below from that
-- estimate, and substochasticity transfers the bound to iterates from zero.
private theorem proper_of_le_sspPolicyBellman (hM : M.Substochastic) {μ : S → A}
    (himproper : ¬ M.Proper μ →
      ∃ s, ¬ BddBelow (Set.range fun N : ℕ => (policyBellman M 1 μ)^[N] 0 s))
    {V : S → ℝ} (hV : V ≤ policyBellman M 1 μ V) : M.Proper μ := by
  by_contra hμ
  obtain ⟨s, hs⟩ := himproper hμ
  apply hs
  refine ⟨V s - dist V 0, ?_⟩
  rintro _ ⟨n, rfl⟩
  have hmono := (monotone_sspPolicyBellman hM μ).monotone_iterate_of_le_map hV
  have hlow : V s ≤ (policyBellman M 1 μ)^[n] V s := hmono (Nat.zero_le n) s
  have hdist := (dist_le_pi_dist ((policyBellman M 1 μ)^[n] V)
    ((policyBellman M 1 μ)^[n] 0) s).trans
      (dist_iterate_le hM μ n V 0 zero_le_one
        (transitionMatrix_pow_nonneg_and_sum_le hM μ n).2)
  rw [Real.dist_eq, one_mul] at hdist
  linarith [le_abs_self ((policyBellman M 1 μ)^[n] V s - (policyBellman M 1 μ)^[n] 0 s)]

variable [Fintype A] [Nonempty A]

omit [DecidableEq S] in
private theorem monotone_sspBellman (hM : M.Substochastic) : Monotone (bellman M 1) :=
  fun _ _ h s => Finset.sup'_le _ _ fun a ha =>
    (qValue_one_mono hM h s a).trans (Finset.le_sup' _ ha)

omit [DecidableEq S] in
private theorem continuous_sspBellman : Continuous (bellman M 1) := by
  refine continuous_pi fun s => Continuous.finset_sup'_apply Finset.univ_nonempty fun a _ => ?_
  unfold qValue
  fun_prop

-- Raising a fixed point by a nonnegative constant gives a supersolution.
omit [DecidableEq S] in
private theorem sspBellman_add_const_le (hM : M.Substochastic) (V : S → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : bellman M 1 (fun s => V s + c) ≤ fun s => bellman M 1 V s + c := by
  intro s
  refine Finset.sup'_le _ _ fun a ha =>
    le_trans ?_ (add_le_add_left (Finset.le_sup' (qValue M 1 V s) ha) c)
  have hrow : (∑ s', M.prob s a s') * c ≤ c := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (hM.2 s a) hc
  simp only [qValue, one_mul, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  linarith

/-- **Bellman's equation for stochastic shortest path problems** (Bertsekas, *Abstract Dynamic
Programming*, 3rd ed., Example 1.2.6, after Bertsekas and Tsitsiklis 1991). Let `M` have finitely
many nonterminal states, finitely many actions (at least one, all available in every state) and
substochastic transitions. Assume the strong SSP conditions: (a) some deterministic stationary
policy is proper; (b) for every improper deterministic stationary policy `μ` there is a state `s`
from which the `N`-stage total rewards `(T_μ^N 0)(s)` are unbounded below. With cost equal to
negative reward, this is infinite limsup cost, not a requirement that the costs tend to infinity.
Then there is `V*` such that

* `V*` is the unique solution of Bellman's equation `T V* = V*` (`T = bellman M 1`);
* value iteration `T^k J` converges to `V*` from every `J`;
* no deterministic stationary policy does better than `V*`: for every such `μ` (proper or not)
  and every state `s`, the `N`-stage total rewards `(T_μ^N 0)(s)` are frequently at most
  `V*(s) + ε`, for every `ε > 0`; that is, `liminf_N (T_μ^N 0)(s) ≤ V*(s)`, the reward form of
  Bertsekas's `J*(s) ≤ J_μ(s) = limsup_N` (`N`-stage cost);
* in particular `sspValue M μ ≤ V*` for every proper `μ`;
* a deterministic stationary policy `μ` satisfies `T_μ V* = T V*` exactly when it is proper and
  `sspValue M μ = V*`, i.e. exactly when it is optimal among deterministic stationary policies.

The source compares more general policies and allows the available actions to depend on the
state. -/
theorem bellman_ssp {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]
    {M : MDP S A ℝ} (hM : M.Substochastic) (hproper : ∃ μ : S → A, M.Proper μ)
    (himproper : ∀ μ : S → A, ¬ M.Proper μ →
      ∃ s, ¬ BddBelow (Set.range fun N : ℕ => (policyBellman M 1 μ)^[N] 0 s)) :
    ∃ V : S → ℝ, bellman M 1 V = V ∧ (∀ W, bellman M 1 W = W → W = V) ∧
      (∀ J, Tendsto (fun k => (bellman M 1)^[k] J) atTop (𝓝 V)) ∧
      (∀ (μ : S → A) (s : S), ∀ ε > 0, ∃ᶠ N in atTop, (policyBellman M 1 μ)^[N] 0 s ≤ V s + ε) ∧
      (∀ μ, M.Proper μ → sspValue M μ ≤ V) ∧
      ∀ μ, policyBellman M 1 μ V = bellman M 1 V ↔ M.Proper μ ∧ sspValue M μ = V := by
  classical
  have hmono := monotone_sspBellman hM
  have hiter (μ : S → A) (n : ℕ) (J : S → ℝ) :
      (policyBellman M 1 μ)^[n] J ≤ (bellman M 1)^[n] J :=
    (monotone_sspPolicyBellman hM μ).iterate_le_of_le (policyBellman_le_bellman μ) n J
  -- The pointwise maximum over proper policy values is a subsolution.
  let ps : Finset (S → A) := Finset.univ.filter fun μ => M.Proper μ
  have hps : ps.Nonempty := by
    obtain ⟨μ, hμ⟩ := hproper
    exact ⟨μ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hμ⟩⟩
  let V : S → ℝ := fun s => ps.sup' hps fun μ => sspValue M μ s
  have hp_le (μ : S → A) (hμ : M.Proper μ) : sspValue M μ ≤ V := fun s =>
    Finset.le_sup' (fun π => sspValue M π s) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hμ⟩)
  have hsub : V ≤ bellman M 1 V := fun s => Finset.sup'_le _ _ fun μ hμ => by
    have hp := (Finset.mem_filter.1 hμ).2
    calc sspValue M μ s = policyBellman M 1 μ (sspValue M μ) s :=
          (congrFun (policyBellman_sspValue hM hp) s).symm
      _ ≤ policyBellman M 1 μ V s := monotone_sspPolicyBellman hM μ (hp_le μ hp) s
      _ ≤ bellman M 1 V s := policyBellman_le_bellman μ V s
  -- A greedy policy at the subsolution is proper; its limit bounds the next iterate.
  let μ := greedy M 1 V
  have hg : policyBellman M 1 μ V = bellman M 1 V := policyBellman_greedy V
  have himprove : V ≤ policyBellman M 1 μ V := hg ▸ hsub
  have hμ := proper_of_le_sspPolicyBellman hM (himproper μ) himprove
  have hinc := (monotone_sspPolicyBellman hM μ).monotone_iterate_of_le_map himprove
  have hstep : policyBellman M 1 μ V ≤ sspValue M μ :=
    ge_of_tendsto (tendsto_policyBellman_iterate hM hμ V) <|
      (eventually_ge_atTop 1).mono fun n hn => by simpa only [Function.iterate_one] using hinc hn
  have hV : bellman M 1 V = V := le_antisymm (hg ▸ hstep.trans (hp_le μ hμ)) hsub
  -- Any fixed point is the value of its own proper greedy policy and dominates
  -- every proper policy value.
  have huniq (W : S → ℝ) (hW : bellman M 1 W = W) : W = V := by
    have hgreedy : policyBellman M 1 (greedy M 1 W) W = W := (policyBellman_greedy W).trans hW
    have hp := proper_of_le_sspPolicyBellman hM (himproper _) hgreedy.ge
    refine le_antisymm ((eq_sspValue_of_policyBellman_eq hM hp hgreedy).le.trans (hp_le _ hp)) ?_
    intro s
    refine Finset.sup'_le _ _ fun ν hν => ?_
    have hlim := tendsto_policyBellman_iterate hM (Finset.mem_filter.1 hν).2 W
    have hbound := (monotone_sspPolicyBellman hM ν).antitone_iterate_of_map_le
      ((policyBellman_le_bellman ν W).trans_eq hW)
    exact (le_of_tendsto' hlim fun n => by
      simpa only [Function.iterate_zero_apply] using hbound (Nat.zero_le n)) s
  -- For any start, squeeze between the greedy policy iterates and the decreasing
  -- Bellman iterates from a supersolution. The latter limit is a fixed point.
  have hconv (J : S → ℝ) : Tendsto (fun k => (bellman M 1)^[k] J) atTop (𝓝 V) := by
    let U : S → ℝ := fun s => V s + dist J V
    have hJU : J ≤ U := fun s => sub_le_iff_le_add'.1
      ((le_abs_self (J s - V s)).trans (by simpa only [Real.dist_eq] using dist_le_pi_dist J V s))
    have hVU : V ≤ U := fun s => le_add_of_nonneg_right dist_nonneg
    have hU : bellman M 1 U ≤ U := (sspBellman_add_const_le hM V dist_nonneg).trans_eq (by rw [hV])
    have hdec := hmono.antitone_iterate_of_map_le hU
    let L : S → ℝ := fun s => ⨅ n : ℕ, (bellman M 1)^[n] U s
    have hlim : Tendsto (fun n => (bellman M 1)^[n] U) atTop (𝓝 L) :=
      tendsto_pi_nhds.2 fun s => tendsto_atTop_ciInf (fun _ _ h => hdec h s) ⟨V s, by
        rintro _ ⟨n, rfl⟩
        simpa only [Function.iterate_fixed hV] using (hmono.iterate n hVU) s⟩
    have hnext : Tendsto (fun n => (bellman M 1)^[n + 1] U) atTop (𝓝 L) :=
      (tendsto_add_atTop_iff_nat 1).2 hlim
    have hL : bellman M 1 L = L := tendsto_nhds_unique
      ((continuous_sspBellman (M := M)).tendsto L |>.comp hlim) (by
        simpa only [Function.iterate_succ_apply', Function.comp_def] using hnext)
    rw [huniq L hL] at hlim
    have hμV : sspValue M μ = V := (eq_sspValue_of_policyBellman_eq hM hμ (hg.trans hV)).symm
    have hlower := tendsto_policyBellman_iterate hM hμ J
    rw [hμV] at hlower
    exact tendsto_pi_nhds.2 fun s => tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_pi_nhds.1 hlower s) (tendsto_pi_nhds.1 hlim s)
      (fun n => hiter μ n J s) (fun n => hmono.iterate n hJU s)
  refine ⟨V, hV, huniq, hconv, ?_, hp_le, ?_⟩
  · intro ν s ε hε
    have hlim := ((continuous_apply s).tendsto V).comp (hconv 0)
    exact ((hlim.eventually_lt_const (lt_add_of_pos_right _ hε)).mono
      fun n hn => ((hiter ν n 0) s).trans hn.le).frequently
  · intro ν
    constructor
    · intro h
      have hfix := h.trans hV
      have hp := proper_of_le_sspPolicyBellman hM (himproper ν) hfix.ge
      exact ⟨hp, (eq_sspValue_of_policyBellman_eq hM hp hfix).symm⟩
    · rintro ⟨hp, hval⟩
      rw [hV, ← hval]
      exact policyBellman_sspValue hM hp

end Optimal

section Discounted

variable {γ : ℝ}

/-! ## Discounted problems as stochastic shortest path problems -/

/-- **A discounted MDP as a stochastic shortest path problem.** The MDP with the same rewards and
transition weights `γ * M.prob s a s'`. For a stochastic `M` and `0 ≤ γ ≤ 1` these are transition
probabilities (`MDP.toSSP_substochastic`): at every stage the system terminates with probability
`1 - γ`, and otherwise moves as in `M`. Like `MDP` itself, which is a data container whose
normalisation is imposed by the predicates `MDP.Stochastic` and `MDP.Substochastic`, the
construction is defined for every `γ`, and the Bellman identity `policyBellman_toSSP` holds for
every `γ`; for `γ > 1` or `γ < 0` the result is not substochastic (the "termination probability"
`1 - γ` would be negative, or the transition weights negative). -/
def MDP.toSSP (M : MDP S A ℝ) (γ : ℝ) : MDP S A ℝ where
  reward := M.reward
  prob s a s' := γ * M.prob s a s'


omit [DecidableEq S] in
/-- **The SSP of a discounted MDP is substochastic**: for a stochastic MDP and `0 ≤ γ ≤ 1`, the
transition probabilities `γ * M.prob s a s'` are nonnegative with row sums `γ ≤ 1`. -/
theorem MDP.toSSP_substochastic (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) :
    (M.toSSP γ).Substochastic := by
  refine ⟨fun s a s' => mul_nonneg hγ0 (hM.1 s a s'), fun s a => ?_⟩
  simp only [MDP.toSSP, ← Finset.mul_sum, hM.2 s a, mul_one]
  exact hγ1

omit [DecidableEq S] in
/-- **The undiscounted Bellman operator of the SSP is the discounted one**:
`policyBellman (M.toSSP γ) 1 μ = policyBellman M γ μ`. -/
theorem policyBellman_toSSP (μ : S → A) :
    policyBellman (M.toSSP γ) 1 μ = policyBellman M γ μ := by
  funext V s
  simp only [policyBellman, qValue, MDP.toSSP, one_mul, Finset.mul_sum, mul_assoc]

/-- **Every policy of a discounted MDP is proper in its SSP**: for a stochastic MDP and
`0 ≤ γ < 1`, termination has probability at least `1 - γ ^ |S| > 0` within `|S|` stages. -/
theorem proper_toSSP (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → A) :
    (M.toSSP γ).Proper μ := by
  intro s
  have hn : 0 < Fintype.card S := Fintype.card_pos_iff.2 ⟨s⟩
  have hP : transitionMatrix (M.toSSP γ) μ = γ • transitionMatrix M μ := by
    ext i j; simp [transitionMatrix, MDP.toSSP]
  have hsub : M.Substochastic := ⟨hM.1, fun s a => (hM.2 s a).le⟩
  rw [hP, smul_pow]
  simp only [Matrix.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  calc γ ^ Fintype.card S * ∑ s', (transitionMatrix M μ ^ Fintype.card S) s s'
      ≤ γ ^ Fintype.card S * 1 :=
        mul_le_mul_of_nonneg_left ((transitionMatrix_pow_nonneg_and_sum_le hsub μ _).2 s)
          (pow_nonneg hγ0 _)
    _ < 1 := by rw [mul_one]; exact pow_lt_one₀ hγ0 hγ1 hn.ne'

omit [DecidableEq S] in
/-- **The SSP value of a discounted MDP's policy is its discounted value**: for a stochastic MDP
and `0 ≤ γ < 1`, `sspValue (M.toSSP γ) μ = policyValue M γ μ`. -/
theorem sspValue_toSSP (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (μ : S → A) :
    sspValue (M.toSSP γ) μ = policyValue M γ hM hγ0 hγ1 μ := by
  classical
  refine (eq_sspValue_of_policyBellman_eq (M.toSSP_substochastic hM hγ0 hγ1.le)
    (proper_toSSP hM hγ0 hγ1 μ) ?_).symm
  rw [policyBellman_toSSP]
  exact policyBellman_policyValue hM hγ0 hγ1 μ

end Discounted

end Cslib.Algorithms.Lean.MarkovDecision
