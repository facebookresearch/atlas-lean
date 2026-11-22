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

Bellman's equation for the optimal value under the strong SSP conditions is recorded in
`WantedExt.ComputerScience.StochasticShortestPathWanted`.
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
      · rw [pow_zero, one_apply]; split_ifs <;> norm_num
      · simp only [pow_zero, one_apply]
        rw [Finset.sum_ite_eq]; simp
  | succ k ih =>
      refine ⟨fun s s' => ?_, fun s => ?_⟩
      · rw [pow_succ', mul_apply]
        exact Finset.sum_nonneg fun j _ => mul_nonneg (hM.1 _ _ _) (ih.1 j s')
      · simp only [pow_succ', mul_apply]
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
