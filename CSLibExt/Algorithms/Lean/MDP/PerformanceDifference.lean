/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.MarkovRewardProcess

/-!
# The performance difference lemma and conservative policy iteration

For a finite discounted MDP and stationary stochastic policies (`StochasticPolicy`), this file
defines the action-value function `Q^π` (`stochQValue`), the advantage
`A^π(s, a) = Q^π(s, a) - V^π(s)` (`advantage`) and the discounted state occupancy
`d^π_{s₀}` (`occupancy`), and proves:

* `sum_prob_mul_advantage`: `∑ a, π(a | s) A^π(s, a) = 0`.
* `performance_difference`: **the performance difference lemma** (Kakade and Langford, 2002;
  Agarwal, Jiang, Kakade and Sun, *Reinforcement Learning: Theory and Algorithms*,
  Lemma 1.16; Agarwal, Kakade, Lee and Mahajan, JMLR 2021, Lemma 3.2): for all stochastic
  policies `π, π'` and states `s₀`,
  `V^{π'}(s₀) - V^π(s₀) = (1 - γ)⁻¹ ∑ s, d^{π'}_{s₀}(s) ∑ a, π'(a | s) A^π(s, a)`;
  `performance_difference_initial` averages it over an initial distribution `μ`.
* `stochValue_le_of_sum_prob_mul_advantage_nonneg`: the **policy improvement theorem** for
  stochastic policies, as a corollary.
* `abs_sum_occupancy_mix_sub_le`: **similar policies have similar occupancies** (AJKS Lemma 14.1):
  for the mixture `π_α = (1 - α) π + α π'` and `|f| ≤ C`,
  `|∑ s, (d^{π_α}_{s₀}(s) - d^π_{s₀}(s)) f s| ≤ 2 α γ C / (1 - γ)`.
* `cpi_improvement`: **the conservative policy iteration improvement bound** (AJKS
  Theorem 14.2; cf. Kakade and Langford 2002, Theorem 4.1, which is sharper: it replaces one
  factor `1 - γ` of the penalty's denominator `(1 - γ)²` by `1 - γ (1 - α)`): if
  `|∑ a, π'(a | s) A^π(s, a)| ≤ ε` for all `s`, then
  `V^{π_α}(s₀) - V^π(s₀) ≥ α / (1 - γ) * 𝔸 - 2 α² γ ε / (1 - γ)²`, where
  `𝔸 = ∑ s, d^π_{s₀}(s) ∑ a, π'(a | s) A^π(s, a)` is the policy advantage of `π'` over `π`.

The proofs are algebraic: the difference of two values solves a Bellman equation whose reward
is the averaged advantage, and `sum_visitation_mul` converts its value into an occupancy average.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open Finset Matrix Filter Topology StochasticPolicy

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
  {M : MDP S A ℝ} {γ : ℝ} (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- The action value `Q^π(s, a) = r(s, a) + γ ∑ s', P(s, a, s') V^π(s')` of a stochastic
policy. -/
noncomputable def stochQValue (π : StochasticPolicy S A) (s : S) (a : A) : ℝ :=
  qValue M γ (stochValue M γ hM hγ0 hγ1 π) s a

/-- The advantage `A^π(s, a) = Q^π(s, a) - V^π(s)` of action `a` over the policy `π` in
state `s`. -/
noncomputable def advantage (π : StochasticPolicy S A) (s : S) (a : A) : ℝ :=
  stochQValue hM hγ0 hγ1 π s a - stochValue M γ hM hγ0 hγ1 π s

/-- The discounted state occupancy `d^π_{s₀}(s) = (1 - γ) ∑ₜ γᵗ Pr^π(sₜ = s | s₀)` of the
stochastic policy `π` (AJKS equation (0.9)): the discounted visitation of the Markov chain
`policyKernel M π`. -/
noncomputable def occupancy (π : StochasticPolicy S A) (s₀ s : S) : ℝ :=
  visitation (policyKernel_mem hM π) hγ0 hγ1 s₀ s

include hM hγ0 hγ1

/-- The discounted occupancy depends continuously on the policy probabilities. -/
theorem tendsto_occupancy_of_tendsto
    {ι : Type*} {l : Filter ι} {π : ι → StochasticPolicy S A} {π₀ : StochasticPolicy S A}
    (h : ∀ s a, Tendsto (fun i => (π i).prob s a) l (𝓝 (π₀.prob s a))) (s₀ s : S) :
    Tendsto (fun i => occupancy hM hγ0 hγ1 (π i) s₀ s) l
      (𝓝 (occupancy hM hγ0 hγ1 π₀ s₀ s)) := by
  unfold occupancy visitation
  refine (tendsto_mrpValue_of_tendsto (fun i => policyKernel_mem hM (π i))
    (policyKernel_mem hM π₀) hγ0 hγ1 (fun s s' => ?_) _ s₀).const_mul _
  exact tendsto_finsetSum _ fun a _ => (h s a).mul_const _

/-- The advantage of a policy averages to zero under the policy itself. -/
theorem sum_prob_mul_advantage (π : StochasticPolicy S A) (s : S) :
    ∑ a, π.prob s a * advantage hM hγ0 hγ1 π s a = 0 := by
  simp only [advantage, stochQValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    π.sum_prob, one_mul]
  rw [← stochValue_eq hM hγ0 hγ1 π s, sub_self]

/-- The discounted state occupancy is nonnegative. -/
theorem occupancy_nonneg (π : StochasticPolicy S A) (s₀ s : S) :
    0 ≤ occupancy hM hγ0 hγ1 π s₀ s :=
  visitation_nonneg _ hγ0 hγ1 s₀ s

/-- The occupancy from `s₀` is a probability vector. -/
theorem sum_occupancy (π : StochasticPolicy S A) (s₀ : S) :
    ∑ s, occupancy hM hγ0 hγ1 π s₀ s = 1 :=
  sum_visitation _ hγ0 hγ1 s₀

/-- The averaged advantage of `π'` over `π` is the Bellman residual of `V^π` under `π'`. -/
theorem sum_prob_mul_advantage_eq (π π' : StochasticPolicy S A) (s : S) :
    ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a =
      policyReward M π' s + γ * ∑ s', policyKernel M π' s s' * stochValue M γ hM hγ0 hγ1 π s' -
        stochValue M γ hM hγ0 hγ1 π s := by
  simp only [advantage, stochQValue, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    π'.sum_prob, one_mul]
  rw [sum_prob_mul_qValue]

/-- The value difference `V^{π'} - V^π` is the value, under `π'`, of the averaged advantage of
`π'` over `π`. -/
theorem stochValue_sub_eq_mrpValue (π π' : StochasticPolicy S A) :
    stochValue M γ hM hγ0 hγ1 π' - stochValue M γ hM hγ0 hγ1 π =
      mrpValue (policyKernel M π') (policyKernel_mem hM π') hγ0 hγ1
        (fun s => ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a) := by
  refine eq_mrpValue _ hγ0 hγ1 fun s => ?_
  have h' : stochValue M γ hM hγ0 hγ1 π' s = policyReward M π' s +
      γ * ∑ s', policyKernel M π' s s' * stochValue M γ hM hγ0 hγ1 π' s' :=
    mrpValue_eq _ hγ0 hγ1 _ s
  rw [sum_prob_mul_advantage_eq]
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  rw [h']
  ring

/-- **The performance difference lemma** (Kakade and Langford 2002; AJKS Lemma 1.16;
Agarwal, Kakade, Lee and Mahajan 2021, Lemma 3.2): for stochastic policies `π, π'` and a start
state `s₀`,
`V^{π'}(s₀) - V^π(s₀) = (1 - γ)⁻¹ ∑ s, d^{π'}_{s₀}(s) ∑ a, π'(a | s) A^π(s, a)`. -/
theorem performance_difference (π π' : StochasticPolicy S A) (s₀ : S) :
    stochValue M γ hM hγ0 hγ1 π' s₀ - stochValue M γ hM hγ0 hγ1 π s₀ =
      (1 - γ)⁻¹ * ∑ s, occupancy hM hγ0 hγ1 π' s₀ s *
        ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a := by
  have h := congrFun (stochValue_sub_eq_mrpValue hM hγ0 hγ1 π π') s₀
  rw [Pi.sub_apply] at h
  unfold occupancy
  rw [h, sum_visitation_mul]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp

/-- **The performance difference lemma** for an initial distribution `μ`:
`V^{π'}(μ) - V^π(μ) = (1 - γ)⁻¹ ∑ s, d^{π'}_μ(s) ∑ a, π'(a | s) A^π(s, a)`, where
`V(μ) = ∑ s₀, μ s₀ V(s₀)` and `d^{π'}_μ(s) = ∑ s₀, μ s₀ d^{π'}_{s₀}(s)`. -/
theorem performance_difference_initial (π π' : StochasticPolicy S A) (μ : S → ℝ) :
    ∑ s₀, μ s₀ * stochValue M γ hM hγ0 hγ1 π' s₀ - ∑ s₀, μ s₀ * stochValue M γ hM hγ0 hγ1 π s₀ =
      (1 - γ)⁻¹ * ∑ s, (∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 π' s₀ s) *
        ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a := by
  have key : ∀ g : S → ℝ, ∑ s₀, μ s₀ * ((1 - γ)⁻¹ * ∑ s, occupancy hM hγ0 hγ1 π' s₀ s * g s) =
      (1 - γ)⁻¹ * ∑ s, (∑ s₀, μ s₀ * occupancy hM hγ0 hγ1 π' s₀ s) * g s := by
    intro g
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [← Finset.sum_sub_distrib]
  refine Eq.trans ?_ (key fun s => ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a)
  refine Finset.sum_congr rfl fun s₀ _ => ?_
  rw [← mul_sub, performance_difference hM hγ0 hγ1 π π' s₀]

/-- **Policy improvement for stochastic policies**: if `π'` has nonnegative averaged advantage
over `π` in every state, then `V^π ≤ V^{π'}` everywhere. -/
theorem stochValue_le_of_sum_prob_mul_advantage_nonneg (π π' : StochasticPolicy S A)
    (h : ∀ s, 0 ≤ ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a) :
    stochValue M γ hM hγ0 hγ1 π ≤ stochValue M γ hM hγ0 hγ1 π' := fun s₀ => by
  have hd := performance_difference hM hγ0 hγ1 π π' s₀
  have : 0 ≤ (1 - γ)⁻¹ * ∑ s, occupancy hM hγ0 hγ1 π' s₀ s *
      ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a :=
    mul_nonneg (inv_nonneg.2 (by linarith)) (Finset.sum_nonneg fun s _ =>
      mul_nonneg (occupancy_nonneg hM hγ0 hγ1 π' s₀ s) (h s))
  linarith

/-! ## Conservative policy iteration -/

omit [Fintype S] [DecidableEq S] hM hγ0 hγ1 in
/-- The mixture's transition matrix is the mixture of the transition matrices. -/
theorem policyKernel_mix (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (π π' : StochasticPolicy S A)
    (s s' : S) : policyKernel M (mix α hα0 hα1 π π') s s' =
      (1 - α) * policyKernel M π s s' + α * policyKernel M π' s s' := by
  simp only [policyKernel, mix_prob, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

/-- The averaged advantage of the mixture `(1 - α) π + α π'` over `π` is `α` times that of
`π'`. -/
theorem sum_mix_prob_mul_advantage (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (π π' : StochasticPolicy S A) (s : S) :
    ∑ a, (mix α hα0 hα1 π π').prob s a * advantage hM hγ0 hγ1 π s a =
      α * ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a := by
  have h0 := sum_prob_mul_advantage hM hγ0 hγ1 π s
  simp only [mix_prob, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum, h0,
    mul_zero, zero_add]

/-- **Similar policies have similar occupancies** (AJKS Lemma 14.1, in dual form): for the
mixture `π_α = (1 - α) π + α π'` with `0 ≤ α ≤ 1` and a function `f` with `|f| ≤ C`,
`|∑ s, (d^{π_α}_{s₀}(s) - d^π_{s₀}(s)) f s| ≤ 2 α γ C / (1 - γ)`. -/
theorem abs_sum_occupancy_mix_sub_le (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (π π' : StochasticPolicy S A) {f : S → ℝ} {C : ℝ} (hf : ∀ s, |f s| ≤ C) (s₀ : S) :
    |∑ s, (occupancy hM hγ0 hγ1 (mix α hα0 hα1 π π') s₀ s - occupancy hM hγ0 hγ1 π s₀ s) * f s|
      ≤ 2 * α * γ * C / (1 - γ) := by
  set πα := mix α hα0 hα1 π π'
  set P := policyKernel M π
  set Pα := policyKernel M πα
  set P' := policyKernel M π'
  have hP := policyKernel_mem hM π
  have hPα := policyKernel_mem hM πα
  have hP' := policyKernel_mem hM π'
  set W := mrpValue P hP hγ0 hγ1 f
  set Wα := mrpValue Pα hPα hγ0 hγ1 f
  have h1γ : 0 < 1 - γ := by linarith
  have hC : 0 ≤ C := (abs_nonneg _).trans (hf s₀)
  have hW : ∀ s, |W s| ≤ C / (1 - γ) := abs_mrpValue_le hP hγ0 hγ1 hf
  -- the occupancy gap is `(1 - γ) (Wα - W)(s₀)`
  have hgap : ∑ s, (occupancy hM hγ0 hγ1 πα s₀ s - occupancy hM hγ0 hγ1 π s₀ s) * f s =
      (1 - γ) * (Wα s₀ - W s₀) := by
    simp only [sub_mul, Finset.sum_sub_distrib, occupancy]
    rw [sum_visitation_mul, sum_visitation_mul]
    ring
  -- `Wα - W` is the value under `πα` of the reward `h s = γ α ∑ s', (P' - P)(s, s') W(s')`
  set h : S → ℝ := fun s => γ * α * ∑ s', (P' s s' - P s s') * W s'
  have hD : Wα - W = mrpValue Pα hPα hγ0 hγ1 h := by
    refine eq_mrpValue hPα hγ0 hγ1 fun s => ?_
    have eα : Wα s = f s + γ * ∑ s', Pα s s' * Wα s' := mrpValue_eq hPα hγ0 hγ1 f s
    have e : W s = f s + γ * ∑ s', P s s' * W s' := mrpValue_eq hP hγ0 hγ1 f s
    have hk : ∀ s', Pα s s' = (1 - α) * P s s' + α * P' s s' := policyKernel_mix α hα0 hα1 π π' s
    have s1 : ∑ x, Pα s x * (Wα x - W x) = ∑ x, Pα s x * Wα x - ∑ x, Pα s x * W x := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have s2 : ∑ x, Pα s x * W x = ∑ x, P s x * W x + α * ∑ x, (P' s x - P s x) * W x := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by linear_combination (W x) * hk x
    simp only [Pi.sub_apply, h]
    linear_combination eα - e - γ * s1 + γ * s2
  have hh : ∀ s, |h s| ≤ γ * (2 * α * C / (1 - γ)) := by
    intro s
    have hsum : |∑ s', (P' s s' - P s s') * W s'| ≤ 2 * (C / (1 - γ)) := by
      calc |∑ s', (P' s s' - P s s') * W s'|
          ≤ ∑ s', |(P' s s' - P s s') * W s'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ s', (P' s s' + P s s') * (C / (1 - γ)) := by
            refine Finset.sum_le_sum fun s' _ => ?_
            rw [abs_mul]
            have h1 : |P' s s' - P s s'| ≤ P' s s' + P s s' := by
              have := nonneg_of_mem_rowStochastic hP (i := s) (j := s')
              have := nonneg_of_mem_rowStochastic hP' (i := s) (j := s')
              rw [abs_le]; constructor <;> linarith
            exact mul_le_mul h1 (hW s') (abs_nonneg _) (add_nonneg
              (nonneg_of_mem_rowStochastic hP') (nonneg_of_mem_rowStochastic hP))
        _ = 2 * (C / (1 - γ)) := by
            rw [← Finset.sum_mul, Finset.sum_add_distrib, sum_row_of_mem_rowStochastic hP',
              sum_row_of_mem_rowStochastic hP]
            ring
    simp only [h, abs_mul, abs_of_nonneg hγ0, abs_of_nonneg hα0]
    calc γ * α * |∑ s', (P' s s' - P s s') * W s'| ≤ γ * α * (2 * (C / (1 - γ))) :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg hγ0 hα0)
      _ = γ * (2 * α * C / (1 - γ)) := by ring
  have hDs := abs_mrpValue_le hPα hγ0 hγ1 hh s₀
  rw [← hD, Pi.sub_apply] at hDs
  rw [hgap, abs_mul, abs_of_pos h1γ]
  calc (1 - γ) * |Wα s₀ - W s₀| ≤ (1 - γ) * (γ * (2 * α * C / (1 - γ)) / (1 - γ)) :=
        mul_le_mul_of_nonneg_left hDs h1γ.le
    _ = 2 * α * γ * C / (1 - γ) := by field_simp

/-- **Conservative policy iteration improves the policy** (AJKS Theorem 14.2; cf. Kakade and
Langford 2002, Theorem 4.1, which replaces one factor `1 - γ` of the penalty's denominator by
`1 - γ (1 - α)`): let
`π_α = (1 - α) π + α π'` with `0 ≤ α ≤ 1` and suppose `|∑ a, π'(a | s) A^π(s, a)| ≤ ε` for
every state `s`. Then
`V^{π_α}(s₀) - V^π(s₀) ≥ α / (1 - γ) * 𝔸 - 2 α² γ ε / (1 - γ)²`, where
`𝔸 = ∑ s, d^π_{s₀}(s) ∑ a, π'(a | s) A^π(s, a)` is the policy advantage of `π'`. -/
theorem cpi_improvement (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (π π' : StochasticPolicy S A)
    {ε : ℝ} (hε : ∀ s, |∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a| ≤ ε) (s₀ : S) :
    α / (1 - γ) * ∑ s, occupancy hM hγ0 hγ1 π s₀ s *
        ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a -
      2 * α ^ 2 * γ * ε / (1 - γ) ^ 2 ≤
    stochValue M γ hM hγ0 hγ1 (mix α hα0 hα1 π π') s₀ - stochValue M γ hM hγ0 hγ1 π s₀ := by
  set g : S → ℝ := fun s => ∑ a, π'.prob s a * advantage hM hγ0 hγ1 π s a
  have h1γ : 0 < 1 - γ := by linarith
  rw [performance_difference hM hγ0 hγ1 π (mix α hα0 hα1 π π') s₀]
  simp_rw [sum_mix_prob_mul_advantage hM hγ0 hγ1 α hα0 hα1 π π']
  have hgap := abs_sum_occupancy_mix_sub_le hM hγ0 hγ1 α hα0 hα1 π π' hε s₀
  have hsplit : ∑ s, occupancy hM hγ0 hγ1 (mix α hα0 hα1 π π') s₀ s * (α * g s) =
      α * (∑ s, occupancy hM hγ0 hγ1 π s₀ s * g s +
        ∑ s, (occupancy hM hγ0 hγ1 (mix α hα0 hα1 π π') s₀ s -
          occupancy hM hγ0 hγ1 π s₀ s) * g s) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [hsplit]
  have hlow := neg_abs_le (∑ s, (occupancy hM hγ0 hγ1 (mix α hα0 hα1 π π') s₀ s -
    occupancy hM hγ0 hγ1 π s₀ s) * g s)
  set X := ∑ s, occupancy hM hγ0 hγ1 π s₀ s * g s
  set Y := ∑ s, (occupancy hM hγ0 hγ1 (mix α hα0 hα1 π π') s₀ s -
    occupancy hM hγ0 hγ1 π s₀ s) * g s
  have hY : -(2 * α * γ * ε / (1 - γ)) ≤ Y := by linarith
  have key : α / (1 - γ) * X - 2 * α ^ 2 * γ * ε / (1 - γ) ^ 2 =
      (1 - γ)⁻¹ * (α * (X + -(2 * α * γ * ε / (1 - γ)))) := by
    field_simp
    ring
  rw [key]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hα0)
    (inv_nonneg.2 h1γ.le)

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
