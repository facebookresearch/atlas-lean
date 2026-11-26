/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.StochasticPolicy

/-!
# Linear programs for finite discounted Markov decision processes

The value program minimises a positive weighted sum over Bellman upper bounds. Its dual
maximises the reward of a nonnegative state-action table subject to discounted flow balance.
The policy space here is the subtype of `IsRowStochastic` rows: the dual table of such a policy
is its existing `occupancy` divided by `1 - γ`. The initial weights need not sum to one.

Jefferson Huang, *Recent Progress on the Complexity of Solving Markov Decision Processes*,
§1.3.5, pp. 8–9, gives the programs (Dβ) and (Pβ) with all-ones weights and the deterministic
policy bases in (10). Here the weights are arbitrary strictly positive reals, and row
normalization identifies **all** dual feasible points, not just the basic feasible solutions.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.MarkovDecision.DiscountedLP

variable {S A : Type*} [Fintype S] [Fintype A] {M : MDP S A ℝ} {γ : ℝ}
  {w V : S → ℝ} {d : S × A → ℝ}

/-- A value table satisfies the primal constraints if it bounds the one-step value of every
state-action pair, with no sign restriction on either rewards or values. -/
def PrimalFeasible (M : MDP S A ℝ) (γ : ℝ) (V : S → ℝ) : Prop :=
  ∀ s a, qValue M γ V s a ≤ V s

/-- A dual feasible table is nonnegative and has outgoing mass minus discounted incoming mass
at each state equal to its initial weight. This definition makes no reference to a policy. -/
def DualFeasible (M : MDP S A ℝ) (γ : ℝ) (w : S → ℝ) (d : S × A → ℝ) : Prop :=
  (∀ p, 0 ≤ d p) ∧ ∀ t, (∑ a, d (t, a)) - γ * ∑ p, M.prob p.1 p.2 t * d p = w t

/-- Testing the flow equations against a value table moves the transition operator onto values. -/
private theorem sum_flow_mul (d : S × A → ℝ) (V : S → ℝ) :
    ∑ t, ((∑ a, d (t, a)) - γ * ∑ p, M.prob p.1 p.2 t * d p) * V t =
      ∑ p, d p * (V p.1 - γ * ∑ t, M.prob p.1 p.2 t * V t) := by
  simp only [sub_mul, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · rw [Fintype.sum_prod_type]
    simp only [Finset.sum_mul]
  · simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private theorem flow_iff_pairing :
    (∀ t, (∑ a, d (t, a)) - γ * ∑ p, M.prob p.1 p.2 t * d p = w t) ↔
      ∀ V : S → ℝ, ∑ s, w s * V s = ∑ p, d p * (V p.1 - γ * ∑ t, M.prob p.1 p.2 t * V t) := by
  constructor
  · intro h V
    simpa only [h] using sum_flow_mul (M := M) (γ := γ) d V
  · classical
    intro h t
    have ht := h (indicatorReward t)
    rw [← sum_flow_mul] at ht
    simpa [indicatorReward] using ht.symm

/-- Weak duality for any feasible tables: the total dual reward cannot exceed the weighted
primal objective. -/
theorem weak_duality (hV : PrimalFeasible M γ V) (hd : DualFeasible M γ w d) :
    ∑ p, d p * M.reward p.1 p.2 ≤ ∑ s, w s * V s := by
  rw [flow_iff_pairing.mp hd.2 V]
  refine Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left ?_ (hd.1 p)
  exact le_sub_iff_add_le.mpr (hV p.1 p.2)

/-- The outgoing mass at a state covers its initial weight. Thus strictly positive initial
weights make the row sum nonzero at every state, including when the discount is zero. -/
theorem DualFeasible.weight_le_row (hd : DualFeasible M γ w d) (hM : M.Stochastic)
    (hγ0 : 0 ≤ γ) (t : S) : w t ≤ ∑ a, d (t, a) := by
  rw [← hd.2 t]
  exact sub_le_self _ (mul_nonneg hγ0 (Finset.sum_nonneg fun p _ =>
    mul_nonneg (hM.1 p.1 p.2 t) (hd.1 p)))

/-- Every feasible dual table has mass `∑ s, w s` divided by `1 - γ`. -/
theorem DualFeasible.total_mass (hd : DualFeasible M γ w d) (hM : M.Stochastic) (hγ1 : γ < 1) :
    ∑ p, d p = (∑ s, w s) / (1 - γ) := by
  have h := flow_iff_pairing.mp hd.2 (fun _ => 1)
  simp only [mul_one, hM.2, ← Finset.sum_mul] at h
  exact (eq_div_iff (sub_ne_zero.mpr hγ1.ne')).mpr h.symm

section Correspondence

variable [DecidableEq S] (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
  {π : S → A → ℝ} (hπ : IsRowStochastic π)

/-- The linear pairing of a test reward with the rescaled occupancy is the sum of its policy
values weighted by the initial weights `w`. Changing the reward leaves the occupancy unchanged. -/
private theorem pair_occupancy (w : S → ℝ) (g : S → A → ℝ) :
    ∑ p, occupancy M γ hM hγ0 hγ1 π hπ w p / (1 - γ) * g p.1 p.2 =
      ∑ s, w s * stochPolicyValue { M with reward := g } γ hM hγ0 hγ1 π hπ s := by
  rw [sum_mul_stochPolicyValue (M := { M with reward := g }) hM hγ0 hγ1 hπ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  change _ = (1 - γ)⁻¹ * (occupancy M γ hM hγ0 hγ1 π hπ w p * g p.1 p.2)
  ring

/-- The existing normalized occupancy, divided by `1 - γ`, satisfies the dual flow equations. -/
theorem dualFeasible_occupancy_div (hw : ∀ s, 0 ≤ w s) :
    DualFeasible M γ w (fun p => occupancy M γ hM hγ0 hγ1 π hπ w p / (1 - γ)) := by
  refine ⟨fun p => div_nonneg (occupancy_nonneg hM hγ0 hγ1 hπ hw p) (sub_nonneg.mpr hγ1.le),
    ?_⟩
  apply (flow_iff_pairing (M := M) (γ := γ) (w := w)
    (d := fun p => occupancy M γ hM hγ0 hγ1 π hπ w p / (1 - γ))).mpr
  intro V
  let g s a := V s - γ * ∑ t, M.prob s a t * V t
  have hV : V = stochPolicyValue { M with reward := g } γ hM hγ0 hγ1 π hπ := by
    apply eq_stochPolicyValue
    intro s
    simp [qValue, g, ← Finset.sum_mul, hπ.2]
  exact (congrArg (fun U : S → ℝ => ∑ s, w s * U s) hV).trans
    (pair_occupancy hM hγ0 hγ1 hπ w g).symm

/-- If a feasible flow factors into state masses and policy rows, it is the rescaled occupancy
of that policy. The proof tests arbitrary state-action rewards before selecting single entries. -/
theorem occupancy_div_eq_of_factor (hd : DualFeasible M γ w d) (x : S → ℝ)
    (hx : ∀ s a, d (s, a) = x s * π s a) (p : S × A) :
    occupancy M γ hM hγ0 hγ1 π hπ w p / (1 - γ) = d p := by
  have pair (g : S → A → ℝ) :
      ∑ q, occupancy M γ hM hγ0 hγ1 π hπ w q / (1 - γ) * g q.1 q.2 =
        ∑ q, d q * g q.1 q.2 := by
    let N : MDP S A ℝ := { M with reward := g }
    let U := stochPolicyValue N γ hM hγ0 hγ1 π hπ
    rw [pair_occupancy]
    change ∑ s, w s * U s = _
    rw [flow_iff_pairing.mp hd.2 U, Fintype.sum_prod_type, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [hx, mul_assoc, ← Finset.mul_sum]
    congr 1
    have hb := stochPolicyValue_eq (M := N) hM hγ0 hγ1 hπ s
    change U s = ∑ a, π s a * (g s a + γ * ∑ t, M.prob s a t * U t) at hb
    simp only [mul_add, Finset.sum_add_distrib] at hb
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hπ.2, one_mul]
    linarith
  classical
  simpa using pair (fun s a => if (s, a) = p then 1 else 0)

private theorem occupancy_div_factor (w : S → ℝ) (s : S) (a : A) :
    occupancy M γ hM hγ0 hγ1 π hπ w (s, a) / (1 - γ) =
      (∑ b, occupancy M γ hM hγ0 hγ1 π hπ w (s, b) / (1 - γ)) * π s a := by
  simp only [occupancy, div_eq_mul_inv, ← Finset.sum_mul, ← Finset.mul_sum, hπ.2, mul_one]
  ring

/-- Stationary randomized policies, represented by `IsRowStochastic` rows, correspond bijectively
to **all** nonnegative solutions of the discounted flow equations with positive initial weights.
The forward map divides the normalized occupancy by `1 - γ`; the inverse divides each entry by
its row sum. -/
noncomputable def occupancyEquiv (hw : ∀ s, 0 < w s) :
    {π : S → A → ℝ // IsRowStochastic π} ≃ {d : S × A → ℝ // DualFeasible M γ w d} where
  toFun π := ⟨_, dualFeasible_occupancy_div hM hγ0 hγ1 π.property (fun s => (hw s).le)⟩
  invFun d := ⟨fun s a => d.val (s, a) / ∑ b, d.val (s, b), by
    have hpos s := (hw s).trans_le (d.property.weight_le_row hM hγ0 s)
    exact ⟨fun s a => div_nonneg (d.property.1 _) (hpos s).le, fun s => by
      simp only [div_eq_mul_inv, ← Finset.sum_mul, mul_inv_cancel₀ (hpos s).ne']⟩⟩
  left_inv π := by
    apply Subtype.ext
    funext s a
    have hd := dualFeasible_occupancy_div hM hγ0 hγ1 π.property (fun s => (hw s).le)
    exact (div_eq_iff ((hw s).trans_le (hd.weight_le_row hM hγ0 s)).ne').mpr
      ((occupancy_div_factor hM hγ0 hγ1 π.property w s a).trans (mul_comm _ _))
  right_inv d := by
    apply Subtype.ext
    funext p
    apply occupancy_div_eq_of_factor hM hγ0 hγ1 _ d.property (fun s => ∑ a, d.val (s, a)) _ p
    intro s a
    exact (mul_div_cancel₀ _ ((hw s).trans_le (d.property.weight_le_row hM hγ0 s)).ne').symm

end Correspondence

section Optima

variable [Nonempty A] (hM : M.Stochastic) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)

/-- The Bellman fixed point is the pointwise least feasible value table. -/
theorem isLeast_primalFeasible :
    IsLeast {V | PrimalFeasible M γ V} (optimalValue M γ hM hγ0 hγ1) := by
  constructor
  · intro s a
    exact (Finset.le_sup' _ (Finset.mem_univ a)).trans_eq
      (congrFun (bellman_optimalValue hM hγ0 hγ1) s)
  · intro V hV
    have hT : bellman M γ V ≤ V := fun s => Finset.sup'_le _ _ fun a _ => hV s a
    have hle (n : ℕ) : (bellman M γ)^[n] V ≤ V := by
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact (bellman_mono hM hγ0 ih).trans hT
    intro s
    exact le_of_tendsto' ((continuous_apply s).continuousAt.tendsto.comp
      (tendsto_valueIteration hM hγ0 hγ1 V)) fun n => hle n s

/-- A strictly positive weighting makes each feasible table other than the Bellman fixed point
strictly more costly, even when the rewards are signed. -/
theorem lt_primal_cost (hw : ∀ s, 0 < w s) (hV : PrimalFeasible M γ V)
    (hne : V ≠ optimalValue M γ hM hγ0 hγ1) :
    ∑ s, w s * optimalValue M γ hM hγ0 hγ1 s < ∑ s, w s * V s := by
  have hle := (isLeast_primalFeasible hM hγ0 hγ1).2 hV
  obtain ⟨t, ht⟩ : ∃ t, optimalValue M γ hM hγ0 hγ1 t < V t := by
    by_contra! h
    exact hne (le_antisymm h hle)
  exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hle s) (hw s).le)
    ⟨t, Finset.mem_univ t, mul_lt_mul_of_pos_left ht (hw t)⟩

/-- **Weighted discounted LP duality.** The optimal value is feasible and strictly minimises
weighted cost. Row-stochastic policies are in bijection with the nonnegative flow solutions,
by scaled occupancy forward and row normalization backward. The maximum reward over the entire
dual feasible set is attained and equals the optimal weighted cost. -/
theorem weighted_duality [DecidableEq S] (hw : ∀ s, 0 < w s) :
    let Vstar := optimalValue M γ hM hγ0 hγ1
    PrimalFeasible M γ Vstar ∧
    (∀ V, PrimalFeasible M γ V → V ≠ Vstar → ∑ s, w s * Vstar s < ∑ s, w s * V s) ∧
    (∃ e : {π : S → A → ℝ // IsRowStochastic π} ≃ {d // DualFeasible M γ w d},
      (∀ π p, (e π).val p = occupancy M γ hM hγ0 hγ1 π.val π.property w p / (1 - γ)) ∧
      ∀ d s, w s ≤ ∑ a, d.val (s, a) ∧ ∀ a, (e.symm d).val s a = d.val (s, a) / ∑ b, d.val (s, b)) ∧
    IsGreatest ((fun d => ∑ p : S × A, d p * M.reward p.1 p.2) '' {d | DualFeasible M γ w d})
      (∑ s, w s * Vstar s) := by
  classical
  let Vstar := optimalValue M γ hM hγ0 hγ1
  have hV := (isLeast_primalFeasible hM hγ0 hγ1).1
  refine ⟨hV, fun _ => lt_primal_cost hM hγ0 hγ1 hw, ⟨occupancyEquiv hM hγ0 hγ1 hw,
    fun _ _ => rfl, fun d s => ⟨d.property.weight_le_row hM hγ0 s, fun _ => rfl⟩⟩, ?_, ?_⟩
  · let π := greedy M γ Vstar
    have hπ := isRowStochastic_detPolicy π
    refine ⟨_, dualFeasible_occupancy_div hM hγ0 hγ1 hπ (fun s => (hw s).le), ?_⟩
    dsimp only
    rw [pair_occupancy hM hγ0 hγ1 hπ w M.reward, stochPolicyValue_detPolicy, policyValue_greedy]
  · rintro _ ⟨d, hd, rfl⟩
    exact weak_duality hV hd

end Optima

/-- Multiplying a feasible table and its initial weights by the same nonnegative scalar
preserves flow feasibility. -/
theorem DualFeasible.scale (hd : DualFeasible M γ w d) {c : ℝ} (hc : 0 ≤ c) :
    DualFeasible M γ (fun s => c * w s) (fun p => c * d p) := by
  refine ⟨fun p => mul_nonneg hc (hd.1 p), fun t => ?_⟩
  simp only [mul_left_comm (M.prob _ _ _) c, ← Finset.mul_sum]
  rw [← hd.2 t]
  ring

/-- Dividing positive weights by their sum gives a probability distribution. The feasible
tables for the original weights are precisely the total weight times the feasible tables for
this distribution; both primal costs and dual rewards scale by that same factor. -/
theorem normalize_weights [Nonempty S] (M : MDP S A ℝ) (γ : ℝ) (hw : ∀ s, 0 < w s) :
    let W := ∑ s, w s
    let μ := fun s => w s / W
    (∀ s, 0 < μ s) ∧ (∑ s, μ s) = 1 ∧
    (∀ d, DualFeasible M γ w d ↔ ∃ e, DualFeasible M γ μ e ∧ d = fun p => W * e p) ∧
    (∀ V : S → ℝ, (∑ s, w s * V s) = W * ∑ s, μ s * V s) ∧
    (∀ e : S × A → ℝ, (∑ p, W * e p * M.reward p.1 p.2) = W * ∑ p, e p * M.reward p.1 p.2) := by
  let W := ∑ s, w s
  have hW : 0 < W := Finset.sum_pos (fun s _ => hw s) Finset.univ_nonempty
  let μ := fun s => w s / W
  have hμ (s : S) : W * μ s = w s := mul_div_cancel₀ _ hW.ne'
  refine ⟨fun s => div_pos (hw s) hW, ?_, fun d => ⟨fun hd => ?_, ?_⟩, fun V => ?_, fun e => ?_⟩
  · simp only [div_eq_mul_inv, ← Finset.sum_mul]
    exact mul_inv_cancel₀ hW.ne'
  · refine ⟨fun p => W⁻¹ * d p, ?_, funext fun p => (mul_inv_cancel_left₀ hW.ne' (d p)).symm⟩
    simpa only [div_eq_inv_mul] using hd.scale (inv_nonneg.mpr hW.le)
  · rintro ⟨e, he, rfl⟩
    have h := he.scale hW.le
    change DualFeasible M γ (fun s => W * μ s) (fun p => W * e p) at h
    simpa only [hμ] using h
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by change _ = W * (μ s * V s); rw [← mul_assoc, hμ]
  · simp only [Finset.mul_sum, mul_assoc]

end Cslib.Algorithms.Lean.MarkovDecision.DiscountedLP
