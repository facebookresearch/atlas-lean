/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.PolicyIteration
public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Stochastic policies, Markov reward processes and discounted state visitation

This file adds stationary *stochastic* policies to the finite discounted MDPs of
`CSLibExt.Algorithms.Lean.MDP.ValueIteration`, which only treats deterministic policies
`π : S → A`. The development follows Agarwal, Jiang, Kakade and Sun, *Reinforcement Learning:
Theory and Algorithms* (the AJKS book, online draft at rltheorybook.github.io, Chapter 1).

* A **Markov reward process** is a row-stochastic matrix `P` (`Matrix.rowStochastic`) with a
  reward vector `c`. For `0 ≤ γ < 1` its value `mrpValue P hP hγ0 hγ1 c` is the unique solution of
  `V s = c s + γ * ∑ s', P s s' * V s'`. It is the value of a one-action MDP (`mrpMDP`), so it
  reuses `policyValue`. It is linear (`mrpValue_add`, `mrpValue_smul`), monotone
  (`mrpValue_mono`), sends a constant `k` to `k / (1 - γ)` (`mrpValue_const`), and is bounded by
  `sup |c| / (1 - γ)` (`abs_mrpValue_le`). `tendsto_mrpValue` identifies it with the
  discounted series `∑ₜ γᵗ Pᵗ c` (AJKS Corollary 1.5 and Lemma 1.6, as a limit of partial sums).
* The **discounted state visitation** `visitation hP hγ0 hγ1 s₀ s` is
  `(1 - γ) ∑ₜ γᵗ Pr(sₜ = s | s₀)` (`tendsto_visitation`; AJKS equation (0.9)). It is a probability
  vector (`visitation_nonneg`, `sum_visitation`), at least `1 - γ` at its start
  (`one_sub_le_visitation_self`), and it turns discounted sums into averages:
  `∑ s, d(s₀, s) f s = (1 - γ) * mrpValue f s₀` (`sum_visitation_mul`, AJKS equation (0.10)).
* A **stochastic policy** (`StochasticPolicy S A`) maps each state to a probability vector
  `Convexity.StdSimplex ℝ A` on the actions. A deterministic policy embeds as Dirac masses
  (`StochasticPolicy.ofDet`),
  and two policies mix state by state (`StochasticPolicy.mix`, the conservative update of
  Kakade and Langford).
* A stochastic policy `π` induces the Markov reward process `policyKernel M π`,
  `policyReward M π`. Its value `stochValue` is the unique solution of the Bellman consistency
  equation `V s = ∑ a, π(a | s) * qValue M γ V s a` (`stochValue_eq`, `eq_stochValue`; AJKS
  Lemma 1.4). For a deterministic policy it is the existing `policyValue`
  (`stochValue_ofDet`), no stochastic policy beats `optimalValue`
  (`stochValue_le_optimalValue`; AJKS Theorem 1.7 for stationary policies), and rewards in
  `[0, 1]` give values in `[0, 1 / (1 - γ)]` (`stochValue_mem_Icc`).

Values are defined by their Bellman equations, as in `ValueIteration`; `tendsto_mrpValue` is
the link to discounted sums of expected rewards.

**Relation to `CSLibExt.Algorithms.Lean.MDP.StochasticPolicy`.** That module treats the same
objects with a policy given as a row-stochastic matrix `π s a`: its `chainValue`, `occupancy` and
`performance_difference` correspond to `mrpValue`, `visitation` and the `performance_difference` of
`CSLibExt.Algorithms.Lean.MDP.PerformanceDifference`. This file and the modules built on it
(`PerformanceDifference`, `SimulationLemma`, `NaturalPolicyGradient`)
use the namespace `Cslib.Algorithms.Lean.MarkovDecision.Simplex`, after their policies with values
in the probability simplex, so that both developments can be imported together.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Finset Matrix Filter Topology Convexity

variable {S A : Type*}

section MarkovRewardProcess

variable [Fintype S] [DecidableEq S]

/-! ## Markov reward processes -/

/-- The one-action MDP of the Markov reward process with transition matrix `P` and reward `c`. -/
def mrpMDP (P : Matrix S S ℝ) (c : S → ℝ) : MDP S Unit ℝ where
  reward s _ := c s
  prob s _ s' := P s s'

/-- The one-action MDP of a row-stochastic matrix is stochastic. -/
theorem mrpMDP_stochastic {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) (c : S → ℝ) :
    (mrpMDP P c).Stochastic :=
  ⟨fun _ _ _ => nonneg_of_mem_rowStochastic hP, fun s _ => sum_row_of_mem_rowStochastic hP s⟩

/-- The value of the Markov reward process with row-stochastic transition matrix `P`, reward `c`
and discount `0 ≤ γ < 1`: the unique solution of `V s = c s + γ * ∑ s', P s s' * V s'`. -/
noncomputable def mrpValue (P : Matrix S S ℝ) (hP : P ∈ rowStochastic ℝ S) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (c : S → ℝ) : S → ℝ :=
  policyValue (mrpMDP P c) γ (mrpMDP_stochastic hP c) hγ0 hγ1 fun _ => ()

section MRP

variable {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hP hγ0 hγ1

/-- The value of a Markov reward process satisfies its Bellman equation. -/
theorem mrpValue_eq (c : S → ℝ) (s : S) :
    mrpValue P hP hγ0 hγ1 c s = c s + γ * ∑ s', P s s' * mrpValue P hP hγ0 hγ1 c s' :=
  (congrFun (policyBellman_policyValue (mrpMDP_stochastic hP c) hγ0 hγ1 fun _ => ()) s).symm

/-- The value of a Markov reward process is the only solution of its Bellman equation. -/
theorem eq_mrpValue {c V : S → ℝ} (h : ∀ s, V s = c s + γ * ∑ s', P s s' * V s') :
    V = mrpValue P hP hγ0 hγ1 c :=
  eq_policyValue_of_policyBellman_eq (mrpMDP_stochastic hP c) hγ0 hγ1 _
    (funext fun s => (h s).symm)

/-- A function below its Bellman image lies below the value. -/
theorem le_mrpValue {c V : S → ℝ} (h : ∀ s, V s ≤ c s + γ * ∑ s', P s s' * V s') :
    V ≤ mrpValue P hP hγ0 hγ1 c :=
  le_policyValue_of_le_policyBellman (mrpMDP_stochastic hP c) hγ0 hγ1 _ h

/-- The value is additive in the reward. -/
theorem mrpValue_add (c d : S → ℝ) :
    mrpValue P hP hγ0 hγ1 (c + d) = mrpValue P hP hγ0 hγ1 c + mrpValue P hP hγ0 hγ1 d := by
  refine (eq_mrpValue hP hγ0 hγ1 fun s => ?_).symm
  simp only [Pi.add_apply]
  rw [mrpValue_eq hP hγ0 hγ1 c s, mrpValue_eq hP hγ0 hγ1 d s]
  simp only [mul_add, Finset.sum_add_distrib]
  ring

/-- The value is homogeneous in the reward. -/
theorem mrpValue_smul (k : ℝ) (c : S → ℝ) :
    mrpValue P hP hγ0 hγ1 (k • c) = k • mrpValue P hP hγ0 hγ1 c := by
  refine (eq_mrpValue hP hγ0 hγ1 fun s => ?_).symm
  simp only [Pi.smul_apply, smul_eq_mul]
  have h := mrpValue_eq hP hγ0 hγ1 c s
  have h2 : ∑ s', P s s' * (k * mrpValue P hP hγ0 hγ1 c s') =
      k * ∑ s', P s s' * mrpValue P hP hγ0 hγ1 c s' := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [h2]
  linear_combination k * h

/-- Negating the reward negates the value. -/
theorem mrpValue_neg (c : S → ℝ) :
    mrpValue P hP hγ0 hγ1 (-c) = -mrpValue P hP hγ0 hγ1 c := by
  simpa using mrpValue_smul hP hγ0 hγ1 (-1) c

/-- The value of a difference of rewards is the difference of their values. -/
theorem mrpValue_sub (c d : S → ℝ) :
    mrpValue P hP hγ0 hγ1 (c - d) = mrpValue P hP hγ0 hγ1 c - mrpValue P hP hγ0 hγ1 d := by
  rw [sub_eq_add_neg, mrpValue_add, mrpValue_neg, ← sub_eq_add_neg]

/-- A constant reward `k` has value `k / (1 - γ)` everywhere. -/
theorem mrpValue_const (k : ℝ) :
    mrpValue P hP hγ0 hγ1 (fun _ => k) = fun _ => k / (1 - γ) := by
  refine (eq_mrpValue hP hγ0 hγ1 fun s => ?_).symm
  rw [← Finset.sum_mul, sum_row_of_mem_rowStochastic hP s]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp
  ring

/-- A nonnegative reward has a nonnegative value. -/
theorem mrpValue_nonneg {c : S → ℝ} (hc : 0 ≤ c) : 0 ≤ mrpValue P hP hγ0 hγ1 c :=
  le_mrpValue hP hγ0 hγ1 fun s => by simpa using hc s

/-- The value is monotone in the reward. -/
theorem mrpValue_mono {c d : S → ℝ} (h : c ≤ d) :
    mrpValue P hP hγ0 hγ1 c ≤ mrpValue P hP hγ0 hγ1 d := by
  have := mrpValue_nonneg hP hγ0 hγ1 (sub_nonneg.2 h)
  rw [mrpValue_sub] at this
  exact sub_nonneg.1 this

/-- A function above its Bellman image lies above the value. -/
theorem mrpValue_le {c V : S → ℝ} (h : ∀ s, c s + γ * ∑ s', P s s' * V s' ≤ V s) :
    mrpValue P hP hγ0 hγ1 c ≤ V := by
  have h' : -V ≤ mrpValue P hP hγ0 hγ1 (-c) := le_mrpValue hP hγ0 hγ1 fun s => by
    have := h s
    simp only [Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    linarith
  rw [mrpValue_neg] at h'
  exact neg_le_neg_iff.1 h'

/-- **Value bound**: a reward bounded by `C` in absolute value has value bounded by
`C / (1 - γ)` (AJKS Lemma 2.3). -/
theorem abs_mrpValue_le {c : S → ℝ} {C : ℝ} (hc : ∀ s, |c s| ≤ C) (s : S) :
    |mrpValue P hP hγ0 hγ1 c s| ≤ C / (1 - γ) := by
  have hu := mrpValue_mono hP hγ0 hγ1 (c := c) (d := fun _ => C)
    fun s => (le_abs_self _).trans (hc s)
  have hl := mrpValue_mono hP hγ0 hγ1 (c := fun _ => -C) (d := c)
    fun s => neg_le.1 ((neg_le_abs _).trans (hc s))
  rw [mrpValue_const] at hu hl
  rw [abs_le]
  refine ⟨?_, hu s⟩
  have := hl s
  rwa [neg_div] at this

/-- **Discounted series**: the value is the limit of the partial sums `∑ₜ<n γᵗ Pᵗ c`
(AJKS Corollary 1.5: `V = (I - γ P)⁻¹ c`). -/
theorem tendsto_mrpValue (c : S → ℝ) :
    Tendsto (fun n => ∑ t ∈ range n, γ ^ t • (P ^ t *ᵥ c)) atTop
      (𝓝 (mrpValue P hP hγ0 hγ1 c)) := by
  set T := policyBellman (mrpMDP P c) γ fun _ => ()
  have hT : ∀ V : S → ℝ, T V = c + γ • (P *ᵥ V) := fun V => rfl
  have hiter : ∀ n, T^[n] 0 = ∑ t ∈ range n, γ ^ t • (P ^ t *ᵥ c) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hT, Finset.sum_range_succ', mulVec_sum,
        Finset.smul_sum, pow_zero, one_smul, pow_zero, one_mulVec, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [mulVec_smul, mulVec_mulVec, smul_smul, pow_succ, pow_succ']
      ring_nf
  exact (ContractingWith.tendsto_iterate_fixedPoint
    (policyBellman_contracting (mrpMDP_stochastic hP c) hγ0 hγ1 fun _ => ()) 0).congr hiter

end MRP

/-- The perturbation identity for Markov reward processes: `V_Q - V_P` is the value, in the chain
`Q`, of the reward `s ↦ γ ∑ s', (Q - P)(s, s') V_P(s')`. -/
private theorem mrpValue_sub_mrpValue {P Q : Matrix S S ℝ} (hP : P ∈ Matrix.rowStochastic ℝ S)
    (hQ : Q ∈ Matrix.rowStochastic ℝ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (c : S → ℝ) :
    mrpValue Q hQ hγ0 hγ1 c - mrpValue P hP hγ0 hγ1 c =
      mrpValue Q hQ hγ0 hγ1
        (fun s => γ * ∑ s', (Q s s' - P s s') * mrpValue P hP hγ0 hγ1 c s') := by
  refine eq_mrpValue hQ hγ0 hγ1 fun s => ?_
  have eQ := mrpValue_eq hQ hγ0 hγ1 c s
  have eP := mrpValue_eq hP hγ0 hγ1 c s
  simp only [Pi.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
  linear_combination eQ - eP

/-- The value of a Markov reward process depends continuously on its transition matrix. -/
theorem tendsto_mrpValue_of_tendsto {ι : Type*} {l : Filter ι} {P : ι → Matrix S S ℝ}
    (hP : ∀ i, P i ∈ Matrix.rowStochastic ℝ S) {P₀ : Matrix S S ℝ}
    (hP₀ : P₀ ∈ Matrix.rowStochastic ℝ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (h : ∀ s s', Tendsto (fun i => P i s s') l (𝓝 (P₀ s s'))) (c : S → ℝ) (s₀ : S) :
    Tendsto (fun i => mrpValue (P i) (hP i) hγ0 hγ1 c s₀) l
      (𝓝 (mrpValue P₀ hP₀ hγ0 hγ1 c s₀)) := by
  set V := mrpValue P₀ hP₀ hγ0 hγ1 c
  -- `E i` bounds the reward of the perturbation identity in every state
  set E : ι → ℝ := fun i => ∑ s, |γ * ∑ s', (P i s s' - P₀ s s') * V s'|
  have hE : Tendsto E l (𝓝 0) := by
    have : Tendsto E l (𝓝 (∑ s : S, |γ * ∑ s' : S, (P₀ s s' - P₀ s s') * V s'|)) := by
      refine tendsto_finsetSum _ fun s _ => ?_
      refine ((tendsto_finsetSum _ fun s' _ => ?_).const_mul γ).abs
      exact ((h s s').sub tendsto_const_nhds).mul_const _
    simpa using this
  have hle : ∀ i, ‖mrpValue (P i) (hP i) hγ0 hγ1 c s₀ - V s₀‖ ≤ E i / (1 - γ) := by
    intro i
    have hb : ∀ s, |γ * ∑ s', (P i s s' - P₀ s s') * V s'| ≤ E i := fun s =>
      Finset.single_le_sum (f := fun s => |γ * ∑ s', (P i s s' - P₀ s s') * V s'|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    have := abs_mrpValue_le (hP i) hγ0 hγ1 hb s₀
    rw [← mrpValue_sub_mrpValue hP₀ (hP i) hγ0 hγ1 c, Pi.sub_apply] at this
    simpa [Real.norm_eq_abs] using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) hle ?_
  simpa using hE.div_const (1 - γ)

/-! ## Discounted state visitation -/

/-- The discounted state visitation of the Markov chain `P` from `s₀`:
`d(s₀, s) = (1 - γ) ∑ₜ γᵗ Pr(sₜ = s | s₀)` (AJKS equation (0.9)), defined as `1 - γ` times the
value of the indicator reward of `s` (see `tendsto_visitation`). -/
noncomputable def visitation {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {γ : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) (s₀ s : S) : ℝ :=
  (1 - γ) * mrpValue P hP hγ0 hγ1 (Pi.single s 1) s₀

section Visitation

variable {P : Matrix S S ℝ} (hP : P ∈ rowStochastic ℝ S) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hP hγ0 hγ1

/-- The visitation is `(1 - γ) ∑ₜ γᵗ (Pᵗ) s₀ s`, as a limit of partial sums. -/
theorem tendsto_visitation (s₀ s : S) :
    Tendsto (fun n => (1 - γ) * ∑ t ∈ range n, γ ^ t * (P ^ t) s₀ s) atTop
      (𝓝 (visitation hP hγ0 hγ1 s₀ s)) := by
  have h := ((continuous_apply s₀).tendsto _).comp (tendsto_mrpValue hP hγ0 hγ1 (Pi.single s 1))
  refine (h.const_mul (1 - γ)).congr fun n => ?_
  simp [Finset.sum_apply]

/-- The discounted visitation is nonnegative. -/
theorem visitation_nonneg (s₀ s : S) : 0 ≤ visitation hP hγ0 hγ1 s₀ s :=
  mul_nonneg (by linarith) (mrpValue_nonneg hP hγ0 hγ1 (fun s' => by
    simp only [Pi.zero_apply, Pi.single_apply]; split_ifs <;> norm_num) s₀)

/-- **Occupancy averages**: `∑ s, d(s₀, s) f s = (1 - γ) * mrpValue f s₀`, the discounted sum
of `f` along the chain (AJKS equation (0.10)). -/
theorem sum_visitation_mul (f : S → ℝ) (s₀ : S) :
    ∑ s, visitation hP hγ0 hγ1 s₀ s * f s = (1 - γ) * mrpValue P hP hγ0 hγ1 f s₀ := by
  have key : (fun s₀ => ∑ s, mrpValue P hP hγ0 hγ1 (Pi.single s 1) s₀ * f s) =
      mrpValue P hP hγ0 hγ1 f := by
    refine eq_mrpValue hP hγ0 hγ1 fun s₀ => ?_
    simp_rw [mrpValue_eq hP hγ0 hγ1 (Pi.single _ 1) s₀, add_mul, Finset.sum_add_distrib]
    congr 1
    · simp [Pi.single_apply]
    · simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun s _ => ?_
      ring
  rw [← key]
  simp_rw [visitation, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- The visitation from `s₀` is a probability vector. -/
theorem sum_visitation (s₀ : S) : ∑ s, visitation hP hγ0 hγ1 s₀ s = 1 := by
  have := sum_visitation_mul hP hγ0 hγ1 (fun _ => 1) s₀
  simp only [mul_one] at this
  rw [this, mrpValue_const]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp

/-- The visitation puts mass at least `1 - γ` on its starting state. -/
theorem one_sub_le_visitation_self (s₀ : S) : 1 - γ ≤ visitation hP hγ0 hγ1 s₀ s₀ := by
  have h1 := mrpValue_eq hP hγ0 hγ1 (Pi.single s₀ 1) s₀
  have h2 : 0 ≤ γ * ∑ s', P s₀ s' * mrpValue P hP hγ0 hγ1 (Pi.single s₀ 1) s' :=
    mul_nonneg hγ0 (Finset.sum_nonneg fun s' _ => mul_nonneg (nonneg_of_mem_rowStochastic hP)
      (mrpValue_nonneg hP hγ0 hγ1 (fun s => by
        simp only [Pi.zero_apply, Pi.single_apply]; split_ifs <;> norm_num) s'))
  rw [Pi.single_eq_same] at h1
  unfold visitation
  nlinarith

end Visitation

end MarkovRewardProcess

/-! ## Stochastic policies -/

/-- A stationary stochastic policy: in each state, a probability vector over the actions. -/
abbrev StochasticPolicy (S A : Type*) := S → StdSimplex ℝ A

namespace StochasticPolicy

/-- The probability `π(a | s)` that `π` takes action `a` in state `s`. -/
def prob (π : StochasticPolicy S A) (s : S) (a : A) : ℝ := (π s).weights a

/-- Action probabilities are nonnegative. -/
theorem prob_nonneg (π : StochasticPolicy S A) (s : S) (a : A) : 0 ≤ π.prob s a :=
  (π s).weights_nonneg a

/-- In each state, the action probabilities sum to one. -/
theorem sum_prob [Fintype A] (π : StochasticPolicy S A) (s : S) : ∑ a, π.prob s a = 1 :=
  (π s).total_of_fintype

/-- A deterministic policy as a stochastic one: the Dirac mass at `π s` in each state `s`. -/
noncomputable def ofDet (π : S → A) : StochasticPolicy S A := fun s => StdSimplex.single (π s)

/-- The Dirac policy of `π` takes action `π s` in state `s` with probability one. -/
theorem ofDet_prob [DecidableEq A] (π : S → A) (s : S) (a : A) :
    (ofDet π).prob s a = if a = π s then 1 else 0 := by
  simp [ofDet, prob, StdSimplex.single, Finsupp.single_apply, eq_comm]

/-- The state-wise mixture `(1 - α) π + α π'` of two stochastic policies, for `0 ≤ α ≤ 1`: the
conservative policy update of Kakade and Langford (2002). -/
noncomputable def mix [Fintype A] (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (π π' : StochasticPolicy S A) : StochasticPolicy S A :=
  fun s =>
    { weights := (1 - α) • (π s).weights + α • (π' s).weights
      nonneg := fun a => by
        simpa using add_nonneg (mul_nonneg (sub_nonneg.2 hα1) ((π s).weights_nonneg a))
          (mul_nonneg hα0 ((π' s).weights_nonneg a))
      total := by
        rw [Finsupp.sum_fintype _ _ (by simp)]
        simp [Finset.sum_add_distrib, ← Finset.mul_sum] }

/-- The mixture takes action `a` in state `s` with probability
`(1 - α) π(a | s) + α π'(a | s)`. -/
theorem mix_prob [Fintype A] (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (π π' : StochasticPolicy S A)
    (s : S) (a : A) : (mix α hα0 hα1 π π').prob s a = (1 - α) * π.prob s a + α * π'.prob s a := by
  simp [mix, prob]

end StochasticPolicy

open StochasticPolicy

variable [Fintype S] [DecidableEq S] [Fintype A]

/-- The transition matrix `P^π(s, s') = ∑ a, π(a | s) P(s, a, s')` of the Markov chain induced
by the stochastic policy `π`. -/
def policyKernel (M : MDP S A ℝ) (π : StochasticPolicy S A) : Matrix S S ℝ :=
  fun s s' => ∑ a, π.prob s a * M.prob s a s'

/-- The expected one-step reward `r^π(s) = ∑ a, π(a | s) r(s, a)` of the stochastic policy `π`. -/
def policyReward (M : MDP S A ℝ) (π : StochasticPolicy S A) : S → ℝ :=
  fun s => ∑ a, π.prob s a * M.reward s a

/-- A stochastic policy on a stochastic MDP induces a row-stochastic transition matrix. -/
theorem policyKernel_mem {M : MDP S A ℝ} (hM : M.Stochastic) (π : StochasticPolicy S A) :
    policyKernel M π ∈ rowStochastic ℝ S := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun s s' => Finset.sum_nonneg fun a _ => mul_nonneg (π.prob_nonneg s a) (hM.1 s a s'),
    fun s => ?_⟩
  simp only [policyKernel]
  rw [Finset.sum_comm]
  simp [← Finset.mul_sum, hM.2, π.sum_prob]

/-- The value `V^π` of a stochastic policy `π`: the value of the Markov reward process it
induces. -/
noncomputable def stochValue (M : MDP S A ℝ) (γ : ℝ) (hM : M.Stochastic) (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) (π : StochasticPolicy S A) : S → ℝ :=
  mrpValue (policyKernel M π) (policyKernel_mem hM π) hγ0 hγ1 (policyReward M π)

variable {M : MDP S A ℝ} {γ : ℝ}

omit [DecidableEq S] in
/-- Averaging action values under `π` gives the induced Markov reward process's Bellman
update. -/
theorem sum_prob_mul_qValue (π : StochasticPolicy S A) (V : S → ℝ) (s : S) :
    ∑ a, π.prob s a * qValue M γ V s a =
      policyReward M π s + γ * ∑ s', policyKernel M π s s' * V s' := by
  simp only [qValue, policyReward, policyKernel, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s' _ => Finset.sum_congr rfl fun a _ => ?_
  ring

section Value

variable (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
include hM hγ0 hγ1

/-- **Bellman consistency** for a stochastic policy (AJKS Lemma 1.4):
`V^π(s) = ∑ a, π(a | s) (r(s, a) + γ ∑ s', P(s, a, s') V^π(s'))`. -/
theorem stochValue_eq (π : StochasticPolicy S A) (s : S) :
    stochValue M γ hM hγ0 hγ1 π s =
      ∑ a, π.prob s a * qValue M γ (stochValue M γ hM hγ0 hγ1 π) s a := by
  rw [sum_prob_mul_qValue]
  exact mrpValue_eq _ hγ0 hγ1 _ s

/-- The value of a stochastic policy is the only solution of its Bellman consistency equation. -/
theorem eq_stochValue (π : StochasticPolicy S A) {V : S → ℝ}
    (h : ∀ s, V s = ∑ a, π.prob s a * qValue M γ V s a) : V = stochValue M γ hM hγ0 hγ1 π :=
  eq_mrpValue _ hγ0 hγ1 fun s => by rw [h s, sum_prob_mul_qValue]

/-- **Compatibility with deterministic policies**: the stochastic value of the Dirac policy of
`π : S → A` is the deterministic value `policyValue π`. -/
theorem stochValue_ofDet (π : S → A) :
    stochValue M γ hM hγ0 hγ1 (ofDet π) = policyValue M γ hM hγ0 hγ1 π := by
  classical
  refine (eq_stochValue hM hγ0 hγ1 _ fun s => ?_).symm
  have h := congrFun (policyBellman_policyValue hM hγ0 hγ1 π) s
  simp only [ofDet_prob, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  exact h.symm

/-- **No stochastic policy beats the optimal value**: `V^π ≤ V*` for every stationary stochastic
policy (AJKS Theorem 1.7, for stationary policies). -/
theorem stochValue_le_optimalValue [Nonempty A] (π : StochasticPolicy S A) :
    stochValue M γ hM hγ0 hγ1 π ≤ optimalValue M γ hM hγ0 hγ1 := by
  refine mrpValue_le _ hγ0 hγ1 fun s => ?_
  rw [← sum_prob_mul_qValue]
  conv_rhs => rw [← bellman_optimalValue hM hγ0 hγ1]
  calc ∑ a, π.prob s a * qValue M γ (optimalValue M γ hM hγ0 hγ1) s a
      ≤ ∑ a, π.prob s a * bellman M γ (optimalValue M γ hM hγ0 hγ1) s :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left
          (Finset.le_sup' (qValue M γ _ s) (Finset.mem_univ a)) (π.prob_nonneg s a)
    _ = bellman M γ (optimalValue M γ hM hγ0 hγ1) s := by
        rw [← Finset.sum_mul, π.sum_prob, one_mul]

/-- **Values of bounded rewards are bounded**: if all rewards lie in `[0, 1]`, then
`0 ≤ V^π(s) ≤ 1 / (1 - γ)` (AJKS Section 1.1.1). -/
theorem stochValue_mem_Icc (hr : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1)
    (π : StochasticPolicy S A) (s : S) :
    stochValue M γ hM hγ0 hγ1 π s ∈ Set.Icc 0 (1 / (1 - γ)) := by
  have hr0 : ∀ s, 0 ≤ policyReward M π s := fun s =>
    Finset.sum_nonneg fun a _ => mul_nonneg (π.prob_nonneg s a) (hr s a).1
  have hr1 : ∀ s, policyReward M π s ≤ 1 := fun s => by
    calc policyReward M π s ≤ ∑ a, π.prob s a * 1 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hr s a).2 (π.prob_nonneg s a)
      _ = 1 := by simp [π.sum_prob]
  refine ⟨mrpValue_nonneg _ hγ0 hγ1 (fun s => hr0 s) s, ?_⟩
  have := mrpValue_mono (policyKernel_mem hM π) hγ0 hγ1 (c := policyReward M π)
    (d := fun _ => 1) hr1 s
  rwa [mrpValue_const] at this

end Value

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
