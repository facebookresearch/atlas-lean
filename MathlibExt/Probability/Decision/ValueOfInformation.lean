/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Value of information for finite decisions

Compare the best fixed action with the best action chosen after a finite observation.
The difference is nonnegative for any real weights. If the weights are nonnegative, equality
holds exactly when one feasible action is optimal for every observation of positive total weight.

See H. Raiffa and R. Schlaifer, *Applied Statistical Decision Theory* (1961), ch. 4, §5.
-/

@[expose] public section

namespace MathlibExt.Probability.Decision.ValueOfInformation

/-- The (unnormalized) expected utility of committing to action `a` when the
joint weight of state `ω` and evidence `e` is `w ω e`: sum over all states and
evidence outcomes. This weighted sum is defined even for signed or unnormalized weights. -/
noncomputable def commitValue {α Ω ε : Type*} [Fintype Ω] [Fintype ε]
    (w : Ω → ε → ℝ) (U : α → Ω → ℝ) (a : α) : ℝ :=
  ∑ ω, ∑ e, w ω e * U a ω

/-- The (unnormalized) expected utility of acting after seeing the evidence:
for each evidence outcome, take the best action under the joint weights for
that outcome. `actions` must be nonempty so the maxima exist. -/
noncomputable def informedValue {α Ω ε : Type*} [Fintype Ω] [Fintype ε]
    (actions : Finset α) (hne : actions.Nonempty)
    (w : Ω → ε → ℝ) (U : α → Ω → ℝ) : ℝ :=
  ∑ e, actions.sup' hne (fun a => ∑ ω, w ω e * U a ω)

/-- The expected value of imperfect information (times the total weight, in
this unnormalized formulation): the informed value minus the best committed
value. -/
noncomputable def evii {α Ω ε : Type*} [Fintype Ω] [Fintype ε]
    (actions : Finset α) (hne : actions.Nonempty)
    (w : Ω → ε → ℝ) (U : α → Ω → ℝ) : ℝ :=
  informedValue actions hne w U - actions.sup' hne (fun a => commitValue w U a)

/-- **Value of information is nonnegative.** For arbitrary real weights, choosing an
optimal action for each observation is worth at least as much as any fixed action. -/
theorem evii_nonneg {α Ω ε : Type*} [Fintype Ω] [Fintype ε]
    {actions : Finset α} {hne : actions.Nonempty} {w : Ω → ε → ℝ} {U : α → Ω → ℝ} :
    0 ≤ evii actions hne w U := by
  rw [evii, sub_nonneg]
  obtain ⟨a_star, ha_mem, ha_eq⟩ := Finset.exists_mem_eq_sup' hne (fun a => commitValue w U a)
  rw [ha_eq]
  simp only [commitValue, informedValue]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro e _
  exact Finset.le_sup' (fun a => ∑ ω, w ω e * U a ω) ha_mem

/-- **Equality condition for the value of information.** The value is zero
if and only if some single feasible action is optimal under every evidence
outcome in the support (every outcome of positive total weight). -/
theorem evii_eq_zero_iff {α Ω ε : Type*} [Fintype Ω] [Fintype ε]
    {actions : Finset α} {hne : actions.Nonempty}
    {w : Ω → ε → ℝ} (hw : ∀ ω e, 0 ≤ w ω e) {U : α → Ω → ℝ} :
    evii actions hne w U = 0 ↔
      ∃ a ∈ actions, ∀ e, (0 < ∑ ω, w ω e) →
        ∀ a' ∈ actions, (∑ ω, w ω e * U a' ω) ≤ ∑ ω, w ω e * U a ω := by
  constructor
  · intro h0
    obtain ⟨a_star, ha_mem, ha_eq⟩ := Finset.exists_mem_eq_sup' hne (fun a => commitValue w U a)
    refine ⟨a_star, ha_mem, ?_⟩
    have h_evii : informedValue actions hne w U - commitValue w U a_star = 0 := by
      have h : evii actions hne w U = informedValue actions hne w U - commitValue w U a_star := by
        rw [evii, ha_eq]
      rw [h] at h0
      exact h0
    have h_commit_swap : commitValue w U a_star = ∑ e, ∑ ω, w ω e * U a_star ω := by
      simp only [commitValue]
      rw [Finset.sum_comm]
    rw [h_commit_swap] at h_evii
    simp only [informedValue] at h_evii
    rw [← Finset.sum_sub_distrib] at h_evii
    have h_nonneg : ∀ e ∈ Finset.univ,
      0 ≤ actions.sup' hne (fun a => ∑ ω, w ω e * U a ω) -
        ∑ ω, w ω e * U a_star ω := by
      intro e _
      apply sub_nonneg.mpr
      exact Finset.le_sup' (fun a => ∑ ω, w ω e * U a ω) ha_mem
    rw [Finset.sum_eq_zero_iff_of_nonneg h_nonneg] at h_evii
    intro e _he_pos a' ha'
    have h_e := h_evii e (Finset.mem_univ e)
    have h_eq : actions.sup' hne (fun a => ∑ ω, w ω e * U a ω) = ∑ ω, w ω e * U a_star ω :=
      sub_eq_zero.mp h_e
    rw [← h_eq]
    exact Finset.le_sup' (fun a => ∑ ω, w ω e * U a ω) ha'
  · intro h
    obtain ⟨a, ha_mem, ha_opt⟩ := h
    have h_nonneg : 0 ≤ evii actions hne w U := evii_nonneg
    apply le_antisymm _ h_nonneg
    rw [evii, sub_nonpos]
    have h_le_sup : commitValue w U a ≤ actions.sup' hne (fun a => commitValue w U a) :=
      Finset.le_sup' (fun a => commitValue w U a) ha_mem
    have h_swap : commitValue w U a = ∑ e, ∑ ω, w ω e * U a ω := by
      simp only [commitValue]
      rw [Finset.sum_comm]
    simp only [informedValue]
    apply le_trans _ h_le_sup
    rw [h_swap]
    apply Finset.sum_le_sum
    intro e _
    apply Finset.sup'_le
    intro a' ha'
    by_cases he : 0 < ∑ ω, w ω e
    · exact ha_opt e he a' ha'
    · have he' : ∑ ω, w ω e ≤ 0 := not_lt.mp he
      have h_sum_nonneg : 0 ≤ ∑ ω, w ω e := Finset.sum_nonneg (fun ω _ => hw ω e)
      have h_sum_zero : ∑ ω, w ω e = 0 := le_antisymm he' h_sum_nonneg
      have h_each_zero : ∀ ω ∈ Finset.univ, w ω e = 0 := by
        have h := (Finset.sum_eq_zero_iff_of_nonneg (fun ω _ => hw ω e)).mp h_sum_zero
        exact h
      have h_post_a' : (∑ ω, w ω e * U a' ω) = 0 := by
        apply Finset.sum_eq_zero
        intro ω _
        rw [h_each_zero ω (Finset.mem_univ ω), zero_mul]
      have h_post_a : (∑ ω, w ω e * U a ω) = 0 := by
        apply Finset.sum_eq_zero
        intro ω _
        rw [h_each_zero ω (Finset.mem_univ ω), zero_mul]
      rw [h_post_a', h_post_a]

end MathlibExt.Probability.Decision.ValueOfInformation
