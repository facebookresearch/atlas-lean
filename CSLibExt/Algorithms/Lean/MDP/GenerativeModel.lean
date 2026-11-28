/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.MDP.SimulationLemma
public import MathlibExt.Probability.HoeffdingBounded
public import MathlibExt.Probability.LearningTheory.EmpiricalDistribution
import Mathlib.Data.Fintype.Powerset
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # A finite generative-model sample bound for discounted MDPs -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace Cslib.Algorithms.Lean.MarkovDecision.Simplex

open StochasticPolicy

variable {S A : Type*} [Fintype S] [Fintype A]

section Simulation

variable [Nonempty A] {M M' : MDP S A ℝ} {γ η : ℝ}
  (hM : M.Stochastic) (hM' : M'.Stochastic) (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
  (hr : M.reward = M'.reward) (hr₀₁ : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1)
  (hrow : ∀ s a, ∑ y, |M.prob s a y - M'.prob s a y| ≤ η)

include hr hr₀₁ hrow

/-- With common rewards in `[0,1]` and transition-row `L¹` error at most `η`, the optimal
state values differ pointwise by at most `γη / (1-γ)²`. Apply the simulation lemma to each
model's optimal stationary policy and use its value as a lower bound in the other model. -/
theorem abs_optimalValue_sub_optimalValue_le (s : S) :
    |optimalValue M γ hM hγ₀ hγ₁ s - optimalValue M' γ hM' hγ₀ hγ₁ s| ≤
      γ * η / (1 - γ) ^ 2 := by
  classical
  let π := greedy M γ (optimalValue M γ hM hγ₀ hγ₁)
  let π' := greedy M' γ (optimalValue M' γ hM' hγ₀ hγ₁)
  have hπ : stochValue M γ hM hγ₀ hγ₁ (ofDet π) = optimalValue M γ hM hγ₀ hγ₁ :=
    (stochValue_ofDet hM hγ₀ hγ₁ π).trans (policyValue_greedy hM hγ₀ hγ₁)
  have hπ' : stochValue M' γ hM' hγ₀ hγ₁ (ofDet π') = optimalValue M' γ hM' hγ₀ hγ₁ :=
    (stochValue_ofDet hM' hγ₀ hγ₁ π').trans (policyValue_greedy hM' hγ₀ hγ₁)
  have e := abs_stochValue_sub_stochValue_le hM hM' hγ₀ hγ₁ hr hr₀₁ hrow (ofDet π) s
  have e' := abs_stochValue_sub_stochValue_le hM hM' hγ₀ hγ₁ hr hr₀₁ hrow (ofDet π') s
  rw [hπ] at e
  rw [hπ'] at e'
  rw [abs_le]
  exact ⟨(abs_le.mp e').1.trans (sub_le_sub_right
    (stochValue_le_optimalValue hM hγ₀ hγ₁ (ofDet π') s) _),
    (sub_le_sub_left (stochValue_le_optimalValue hM' hγ₀ hγ₁ (ofDet π) s) _).trans (abs_le.mp e).2⟩

/-- With common rewards in `[0,1]` and transition-row `L¹` error at most `η`, the optimal
action-value error is at most `γη / (1-γ)²`, at every state and action. -/
theorem abs_optimalQ_sub_optimalQ_le (s : S) (a : A) :
    |qValue M γ (optimalValue M γ hM hγ₀ hγ₁) s a -
      qValue M' γ (optimalValue M' γ hM' hγ₀ hγ₁) s a| ≤ γ * η / (1 - γ) ^ 2 := by
  classical
  let V := optimalValue M γ hM hγ₀ hγ₁
  let V' := optimalValue M' γ hM' hγ₀ hγ₁
  let π := greedy M γ V
  have hπ : stochValue M γ hM hγ₀ hγ₁ (ofDet π) = V :=
    (stochValue_ofDet hM hγ₀ hγ₁ π).trans (policyValue_greedy hM hγ₀ hγ₁)
  have hγ : 0 < 1 - γ := sub_pos.mpr hγ₁
  have hV (y : S) : |V y| ≤ 1 / (1 - γ) := by
    rw [← hπ]
    have h := stochValue_mem_Icc hM hγ₀ hγ₁ hr₀₁ (ofDet π) y
    exact (abs_of_nonneg h.1).symm ▸ h.2
  have hfirst : |qValue M γ V s a - qValue M' γ V s a| ≤ γ * (η / (1 - γ)) := by
    have he : qValue M γ V s a - qValue M' γ V s a =
        γ * ∑ y, (M.prob s a y - M'.prob s a y) * V y := by
      simp only [qValue, hr, sub_mul, Finset.sum_sub_distrib]
      ring
    rw [he, abs_mul, abs_of_nonneg hγ₀]
    apply mul_le_mul_of_nonneg_left _ hγ₀
    calc
      |∑ y, (M.prob s a y - M'.prob s a y) * V y|
          ≤ ∑ y, |(M.prob s a y - M'.prob s a y) * V y| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ y, |M.prob s a y - M'.prob s a y| * (1 / (1 - γ)) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hV y) (abs_nonneg _)
      _ ≤ η / (1 - γ) := by
        rw [← Finset.sum_mul, div_eq_mul_inv η, one_div]
        exact mul_le_mul_of_nonneg_right (hrow s a) (inv_nonneg.mpr hγ.le)
  have hsecond : |qValue M' γ V s a - qValue M' γ V' s a| ≤
      γ * (γ * η / (1 - γ) ^ 2) :=
    abs_qValue_sub_le hM' hγ₀ (abs_optimalValue_sub_optimalValue_le hM hM' hγ₀ hγ₁ hr hr₀₁ hrow) s a
  calc
    |qValue M γ V s a - qValue M' γ V' s a| ≤
        |qValue M γ V s a - qValue M' γ V s a| + |qValue M' γ V s a - qValue M' γ V' s a| :=
      abs_sub_le _ _ _
    _ ≤ γ * (η / (1 - γ)) + γ * (γ * η / (1 - γ) ^ 2) := add_le_add hfirst hsecond
    _ = γ * η / (1 - γ) ^ 2 := by field_simp; ring

end Simulation

section Sampling

variable [DecidableEq S] {n : ℕ}

omit [Fintype S] in
private theorem empFreq_eq_avg (x : Fin n → S) (y : S) :
    empFreq x y = (1 / (n : ℝ)) * ∑ i, if x i = y then (1 : ℝ) else 0 := by
  rw [empFreq, Finset.natCast_card_filter, one_div, div_eq_mul_inv, mul_comm]

/-- The empirical MDP has the original rewards and empirical next-state frequencies in each row. -/
noncomputable def empiricalMDP (M : MDP S A ℝ) (x : S → A → Fin n → S) : MDP S A ℝ where
  reward := M.reward
  prob s a := empFreq (x s a)

omit [Fintype A] in
/-- A positive sample count gives stochastic empirical transition rows. -/
theorem empiricalMDP_stochastic (M : MDP S A ℝ) (x : S → A → Fin n → S) (hn : 0 < n) :
    (empiricalMDP M x).Stochastic := by
  constructor
  · intro s a y
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · intro s a
    change ∑ y, empFreq (x s a) y = 1
    simp_rw [empFreq_eq_avg]
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, one_div]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne')

omit [Fintype S] in
private theorem sum_empFreq (x : Fin n → S) (B : Finset S) :
    ∑ y ∈ B, empFreq x y = (1 / (n : ℝ)) * ∑ i, if x i ∈ B then (1 : ℝ) else 0 := by
  simp_rw [empFreq_eq_avg]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [Finset.sum_ite_eq]

-- For a signed mass of total zero, the positive coordinates carry half its L¹ mass.
omit [DecidableEq S] in
private theorem exists_subset_sum_eq_half_l1 (f : S → ℝ) (h : ∑ y, f y = 0) :
    ∃ B : Finset S, (∑ y, |f y|) = 2 * ∑ y ∈ B, f y := by
  classical
  let B := Finset.univ.filter fun y => 0 ≤ f y
  let C := Finset.univ.filter fun y => ¬ 0 ≤ f y
  refine ⟨B, ?_⟩
  have hsum : (∑ y ∈ B, f y) + (∑ y ∈ C, f y) = 0 :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => 0 ≤ f y) f).trans h
  have hp : (∑ y ∈ B, |f y|) = ∑ y ∈ B, f y := by
    apply Finset.sum_congr rfl
    intro y hy
    exact abs_of_nonneg (Finset.mem_filter.mp hy).2
  have hc : (∑ y ∈ C, |f y|) = -(∑ y ∈ C, f y) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    exact abs_of_neg (lt_of_not_ge (Finset.mem_filter.mp hy).2)
  have habs : (∑ y ∈ B, |f y|) + (∑ y ∈ C, |f y|) = ∑ y, |f y| :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun y => 0 ≤ f y) (fun y => |f y|)
  rw [hp, hc] at habs
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  [MeasurableSpace S] [MeasurableSingletonClass S]

omit [Fintype S] in
private theorem measurable_empFreq (X : Fin n → Ω → S) (hX : ∀ i, Measurable (X i)) (y : S) :
    Measurable fun ω => empFreq (fun i => X i ω) y := by
  simp_rw [empFreq_eq_avg]
  refine measurable_const.mul (Finset.measurable_fun_sum _ fun i _ => ?_)
  exact measurable_const.ite ((measurableSet_singleton y).preimage (hX i)) measurable_const

omit [Fintype S] in
private theorem measureReal_empFreq_subset_tail (X : Fin n → Ω → S)
    (hX : ∀ i, Measurable (X i)) (hI : iIndepFun X μ) (p : S → ℝ)
    (hp : ∀ i y, μ.real (X i ⁻¹' {y}) = p y) (B : Finset S) (hn : 0 < n)
    {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ y ∈ B, (empFreq (fun i => X i ω) y - p y)} ≤
      Real.exp (-2 * (n : ℝ) * t ^ 2) := by
  let z : S → ℝ := fun y => if y ∈ B then 1 else 0
  have hz : Measurable z := measurable_const.ite B.measurableSet measurable_const
  have hzmean (i : Fin n) : ∫ ω, z (X i ω) ∂μ = ∑ y ∈ B, p y := by
    have he : (fun ω => z (X i ω)) = (X i ⁻¹' (↑B : Set S)).indicator (1 : Ω → ℝ) := by
      funext ω
      by_cases hb : X i ω ∈ B
      · rw [Set.indicator_of_mem (show ω ∈ X i ⁻¹' (↑B : Set S) from hb)]
        simp [z, hb]
      · rw [Set.indicator_of_notMem (show ω ∉ X i ⁻¹' (↑B : Set S) from hb)]
        simp [z, hb]
    rw [he, integral_indicator_one (B.measurableSet.preimage (hX i)),
      ← sum_measureReal_preimage_singleton B (fun y _ => (measurableSet_singleton y).preimage
        (hX i))]
    exact Finset.sum_congr rfl fun y _ => hp i y
  have h := MathlibExt.Probability.HoeffdingBounded.measureReal_avg_sub_ge_le
    (hI.comp (fun _ => z) (fun _ => hz)) (fun i => (hz.comp (hX i)).aemeasurable)
    (a := 0) (b := 1) (fun i => Filter.Eventually.of_forall fun ω => by
      change z (X i ω) ∈ Set.Icc (0 : ℝ) 1
      dsimp only [z]
      split <;> norm_num) ht
  have hm : (1 / (n : ℝ)) * ∑ _i : Fin n, ∑ y ∈ B, p y = ∑ y ∈ B, p y := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    field_simp
  simp only [Function.comp_apply, hzmean, hm, sub_zero, one_pow, div_one] at h
  simp only [Finset.sum_sub_distrib, sum_empFreq]
  exact h

/-- Union bound for empirical transition rows. There are `|S||A|` rows and `2^|S|` subsets of
next states. Only the `n` samples *within* each row are required to be independent. -/
theorem measureReal_empiricalMDP_largeRowError (M : MDP S A ℝ) (hM : M.Stochastic)
    (X : S → A → Fin n → Ω → S) (hX : ∀ s a i, Measurable (X s a i))
    (hI : ∀ s a, iIndepFun (X s a) μ)
    (hp : ∀ s a i y, μ.real (X s a i ⁻¹' {y}) = M.prob s a y)
    (hn : 0 < n) {η : ℝ} (hη : 0 ≤ η) :
    μ.real {ω | ∃ s a, η < ∑ y, |empFreq (fun i => X s a i ω) y - M.prob s a y|} ≤
      (Fintype.card S : ℝ) * Fintype.card A * (2 : ℝ) ^ Fintype.card S *
        Real.exp (-(n : ℝ) * η ^ 2 / 2) := by
  let E (s : S) (a : A) (B : Finset S) : Set Ω :=
    {ω | η / 2 ≤ ∑ y ∈ B, (empFreq (fun i => X s a i ω) y - M.prob s a y)}
  let U (j : S × A × Finset S) := E j.1 j.2.1 j.2.2
  have hsub : {ω | ∃ s a, η < ∑ y, |empFreq (fun i => X s a i ω) y - M.prob s a y|} ⊆
      ⋃ j, U j := by
    intro ω hω
    obtain ⟨s, a, h⟩ := hω
    let f := fun y => empFreq (fun i => X s a i ω) y - M.prob s a y
    have hzero : ∑ y, f y = 0 := by
      unfold f
      rw [Finset.sum_sub_distrib, hM.2 s a,
        show (∑ y, empFreq (fun i => X s a i ω) y) = 1 from
          (empiricalMDP_stochastic M (fun s a i => X s a i ω) hn).2 s a, sub_self]
    obtain ⟨B, hB⟩ := exists_subset_sum_eq_half_l1 f hzero
    apply Set.mem_iUnion.mpr
    refine ⟨(s, a, B), ?_⟩
    change η / 2 ≤ ∑ y ∈ B, f y
    change η < ∑ y, |f y| at h
    linarith
  have htail (j : S × A × Finset S) : μ.real (U j) ≤
      Real.exp (-(n : ℝ) * η ^ 2 / 2) := by
    have h := measureReal_empFreq_subset_tail (X j.1 j.2.1) (hX j.1 j.2.1)
      (hI j.1 j.2.1) (M.prob j.1 j.2.1) (hp j.1 j.2.1) j.2.2 hn
      (t := η / 2) (by positivity)
    convert h using 1
    congr 1
    ring
  calc
    _ ≤ μ.real (⋃ j, U j) := measureReal_mono hsub
    _ ≤ ∑ j, μ.real (U j) := measureReal_iUnion_fintype_le U
    _ ≤ ∑ _j : S × A × Finset S, Real.exp (-(n : ℝ) * η ^ 2 / 2) :=
      Finset.sum_le_sum fun j _ => htail j
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_finset,
        nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      ring

variable [Nonempty S] [Nonempty A]

/-- **Generative-model sample bound (restricted, non-minimax).** For each state-action pair,
take `n > 0` independent samples with the true next-state law. With rewards in `[0,1]`, if
`n ≥ 2 (|S| + log (|S||A|/δ)) / η²`, then with probability at least `1 - δ` every empirical
row has `L¹` error at most `η`, and the optimal action values differ by at most `γη/(1-γ)²`.
The two conclusions hold on the same event. Neither cross-row independence nor an upper bound
on `η` is needed. The proof unions over subsets of next states and then uses the simulation
lemma. It does not give the minimax sample complexity.

Source: Agarwal, Brantley, Jiang, Kakade, and Sun, *Reinforcement Learning: Theory and Algorithms*,
June 27, 2026 draft, Proposition 2.1 and Lemmas 2.2–2.3. The subset union bound gives the
additive sample threshold. -/
theorem measureReal_empiricalMDP_accurate (M : MDP S A ℝ) (hM : M.Stochastic)
    (X : S → A → Fin n → Ω → S) (hX : ∀ s a i, Measurable (X s a i))
    (hI : ∀ s a, iIndepFun (X s a) μ)
    (hp : ∀ s a i y, μ.real (X s a i ⁻¹' {y}) = M.prob s a y)
    (hn : 0 < n) {γ η δ : ℝ} (hγ₀ : 0 ≤ γ) (hγ₁ : γ < 1)
    (hr₀₁ : ∀ s a, 0 ≤ M.reward s a ∧ M.reward s a ≤ 1)
    (hη : 0 < η) (hδ : 0 < δ)
    (hsize : 2 * ((Fintype.card S : ℝ) +
      Real.log ((Fintype.card S : ℝ) * Fintype.card A / δ)) / η ^ 2 ≤ (n : ℝ)) :
    1 - δ ≤ μ.real {ω |
      let x := fun s a i => X s a i ω
      let M' := empiricalMDP M x
      let hM' : M'.Stochastic := empiricalMDP_stochastic M x hn
      (∀ s a, ∑ y, |M'.prob s a y - M.prob s a y| ≤ η) ∧
      ∀ s a, |qValue M' γ (optimalValue M' γ hM' hγ₀ hγ₁) s a -
        qValue M γ (optimalValue M γ hM hγ₀ hγ₁) s a| ≤ γ * η / (1 - γ) ^ 2} := by
  let k : ℝ := Fintype.card S
  let m : ℝ := Fintype.card S * Fintype.card A
  have hk : 0 ≤ k := Nat.cast_nonneg _
  have hm : 0 < m := by
    exact mul_pos (Nat.cast_pos.mpr Fintype.card_pos) (Nat.cast_pos.mpr Fintype.card_pos)
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    norm_num at h ⊢
    exact h
  have hthreshold : Real.log (m * (2 : ℝ) ^ Fintype.card S / δ) ≤ (n : ℝ) * η ^ 2 / 2 := by
    rw [show m * (2 : ℝ) ^ Fintype.card S / δ =
      (m / δ) * (2 : ℝ) ^ Fintype.card S by ring,
      Real.log_mul (div_pos hm hδ).ne' (by positivity), Real.log_pow]
    have hh := (div_le_iff₀ (pow_pos hη 2)).mp hsize
    change 2 * (k + Real.log (m / δ)) ≤ (n : ℝ) * η ^ 2 at hh
    change Real.log (m / δ) + k * Real.log 2 ≤ (n : ℝ) * η ^ 2 / 2
    linarith [mul_le_mul_of_nonneg_left hlog hk]
  have hconst : m * (2 : ℝ) ^ Fintype.card S * Real.exp (-(n : ℝ) * η ^ 2 / 2) ≤ δ := by
    let c : ℝ := m * (2 : ℝ) ^ Fintype.card S
    have hc : 0 < c := mul_pos hm (by positivity)
    have he := Real.exp_le_exp.mpr (show -(n : ℝ) * η ^ 2 / 2 ≤ -Real.log (c / δ) by
      linarith only [hthreshold])
    rw [Real.exp_neg, Real.exp_log (div_pos hc hδ), inv_div] at he
    calc
      c * Real.exp (-(n : ℝ) * η ^ 2 / 2) ≤ c * (δ / c) := mul_le_mul_of_nonneg_left he hc.le
      _ = δ := by field_simp
  let G : Set Ω := {ω | ∀ s a, ∑ y, |empFreq (fun i => X s a i ω) y - M.prob s a y| ≤ η}
  have hG : MeasurableSet G := by
    have he : G = ⋂ s : S, ⋂ a : A,
        {ω | ∑ y, |empFreq (fun i => X s a i ω) y - M.prob s a y| ≤ η} := by
      ext ω
      simp [G]
    rw [he]
    refine MeasurableSet.iInter fun s => MeasurableSet.iInter fun a =>
      measurableSet_le (Finset.measurable_fun_sum _ fun y _ => ?_) measurable_const
    exact continuous_abs.measurable.comp
      ((measurable_empFreq (X s a) (hX s a) y).sub
        (measurable_const (a := M.prob s a y)))
  have hbad : μ.real Gᶜ ≤ δ := by
    have he : Gᶜ = {ω | ∃ s a, η < ∑ y, |empFreq (fun i => X s a i ω) y - M.prob s a y|} := by
      ext ω
      simp [G, not_le]
    rw [he]
    exact (measureReal_empiricalMDP_largeRowError M hM X hX hI hp hn hη.le).trans hconst
  rw [measureReal_compl hG, probReal_univ] at hbad
  refine (show 1 - δ ≤ μ.real G by linarith).trans (measureReal_mono ?_)
  intro ω hω
  refine ⟨hω, fun s a => ?_⟩
  let x := fun s a i => X s a i ω
  let M' := empiricalMDP M x
  have hM' := empiricalMDP_stochastic M x hn
  have hrow : ∀ s a, ∑ y, |M.prob s a y - M'.prob s a y| ≤ η := by
    intro s a
    change (∑ y, |M.prob s a y - empFreq (fun i => X s a i ω) y|) ≤ η
    simp_rw [abs_sub_comm (M.prob s a _)]
    exact hω s a
  have h := abs_optimalQ_sub_optimalQ_le hM hM' hγ₀ hγ₁ rfl hr₀₁ hrow s a
  rw [abs_sub_comm] at h
  exact h

end Sampling

end Cslib.Algorithms.Lean.MarkovDecision.Simplex
