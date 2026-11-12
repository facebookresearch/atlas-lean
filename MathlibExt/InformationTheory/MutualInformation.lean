/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

/-! # Mutual information on finite types

Mutual information of a joint PMF (in nats): nonnegativity
(Gibbs), vanishing on independent products, and symmetry under
swapping the coordinates. This is the information-calculus core
of roadmap package QCI-32 of the Atlas TCS canon roadmap; the
operational channel-coding statements built on it are follow-ups.

Source: Cover and Thomas, Elements of Information Theory (2006),
Chapter 2.
-/

open Finset

/-- Mutual information (nats) of a joint PMF on a finite product
type: `∑ x y, p (x, y) log (p (x, y) / (pX x * pY y))`, where the
marginals are the finite sums. Real-arithmetic conventions make
terms with `p (x, y) = 0` contribute `0`. -/
noncomputable def mutualInfo {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : ℝ :=
  ∑ x, ∑ y, (p (x, y)).toReal *
    Real.log ((p (x, y)).toReal /
      ((∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal)))

/-- The product (independent) joint law of two PMFs. -/
noncomputable def prodJoint {α β : Type*} (p : PMF α) (q : PMF β) :
    PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

private lemma toReal_sum_one {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a, (p a).toReal) = 1 := by
  have h1 : (∑' a : α, p a).toReal = (1 : ENNReal).toReal := by
    rw [PMF.tsum_coe]
  rw [ENNReal.tsum_toReal_eq (fun a => PMF.apply_ne_top p a),
    ENNReal.toReal_one, tsum_fintype] at h1
  exact h1

private lemma toReal_sum_prod {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : (∑ x, ∑ y, (p (x, y)).toReal) = 1 := by
  have h : (∑ z : α × β, (p z).toReal) = 1 := toReal_sum_one p
  rwa [Fintype.sum_prod_type] at h

private lemma toReal_sum_swap {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : (∑ y, ∑ x, (p (x, y)).toReal) = 1 := by
  rw [Finset.sum_comm]
  exact toReal_sum_prod p

private lemma marg_prod_sum {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) :
    (∑ x, ∑ y, (∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal)) = 1 := by
  have hY : ∀ x : α, (∑ y, (∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal))
      = (∑ y', (p (x, y')).toReal) := by
    intro x
    rw [← Finset.mul_sum, toReal_sum_swap, mul_one]
  simp only [hY]
  exact toReal_sum_prod p

private lemma support_zero {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) (x : α) (y : β)
    (h : (∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal) = 0) :
    (p (x, y)).toReal = 0 := by
  have hnn : ∀ z : α × β, 0 ≤ (p z).toReal := fun z => ENNReal.toReal_nonneg
  rcases mul_eq_zero.mp h with hX | hY
  · have hle : (p (x, y)).toReal ≤ ∑ y', (p (x, y')).toReal :=
      Finset.single_le_sum (fun y' _ => hnn (x, y')) (Finset.mem_univ y)
    rw [hX] at hle
    exact le_antisymm hle (hnn (x, y))
  · have hle : (p (x, y)).toReal ≤ ∑ x', (p (x', y)).toReal :=
      Finset.single_le_sum (fun x' _ => hnn (x', y)) (Finset.mem_univ x)
    rw [hY] at hle
    exact le_antisymm hle (hnn (x, y))

private lemma gibbs_pointwise {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : b = 0 → a = 0) : a - b ≤ a * Real.log (a / b) := by
  by_cases ha0 : a = 0
  · subst ha0
    simp only [zero_sub, zero_mul]
    linarith
  · by_cases hb0 : b = 0
    · exact absurd (h hb0) ha0
    · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
      have hlog : Real.log (b / a) ≤ b / a - 1 :=
        Real.log_le_sub_one_of_pos (div_pos hbp hap)
      have hdiv : Real.log (a / b) = -Real.log (b / a) := by
        rw [Real.log_div (ne_of_gt hap) (ne_of_gt hbp),
          Real.log_div (ne_of_gt hbp) (ne_of_gt hap), neg_sub]
      have ha0' : a ≠ 0 := ne_of_gt hap
      have h2 : a * Real.log (b / a) ≤ b - a := by
        have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hap)
        have heq : a * (b / a - 1) = b - a := by field_simp
        rwa [heq] at hmul
      rw [hdiv]
      have h3 : a * -Real.log (b / a) = -(a * Real.log (b / a)) := by ring
      rw [h3]
      linarith

private lemma prodJoint_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) (x : α) (y : β) :
    (prodJoint p q) (x, y) = p x * q y := by
  unfold prodJoint
  rw [PMF.bind_apply, tsum_fintype]
  have h1 : ∀ a ∈ (Finset.univ : Finset α), a ≠ x →
      p a * ((q.map fun b => (a, b)) (x, y)) = 0 := by
    intro a _ hax
    have h0 : (q.map fun b => (a, b)) (x, y) = 0 := by
      rw [PMF.map_apply, tsum_fintype]
      apply Finset.sum_eq_zero
      intro b _
      have hne : (x, y) ≠ (a, b) := by
        intro h
        simp only [Prod.mk.injEq] at h
        exact hax h.1.symm
      simp [hne]
    rw [h0, mul_zero]
  have h2 : x ∉ (Finset.univ : Finset α) →
      p x * ((q.map fun b => (x, b)) (x, y)) = 0 := by
    intro hx
    simp at hx
  have hsum : (∑ a : α, p a * ((q.map fun b => (a, b)) (x, y)))
      = p x * ((q.map fun b => (x, b)) (x, y)) :=
    Finset.sum_eq_single x h1 h2
  rw [hsum]
  congr 1
  rw [PMF.map_apply]
  have h0 : ∀ b : β, b ≠ y →
      (@ite ENNReal ((x, y) = (x, b)) (Classical.propDecidable _) (q b) 0) = 0 := by
    intro b hby
    have hne : (x, y) ≠ (x, b) := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact hby h.2.symm
    simp [hne]
  rw [tsum_eq_single y h0]
  simp

private lemma map_swap_apply {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) (c : β) (d : α) :
    ((p.map fun z => (z.2, z.1)) (c, d)) = p (d, c) := by
  rw [PMF.map_apply]
  have h0 : ∀ a : α × β, a ≠ (d, c) →
      (@ite ENNReal ((c, d) = (a.2, a.1)) (Classical.propDecidable _) (p a) 0) = 0 := by
    intro a ha
    have hne : (c, d) ≠ (a.2, a.1) := by
      intro h
      simp only [Prod.mk.injEq] at h
      exact ha (Prod.ext h.2.symm h.1.symm)
    simp [hne]
  rw [tsum_eq_single (d, c) h0]
  simp

/-- Mutual information is nonnegative (Gibbs' inequality). -/
theorem mutualInfo_nonneg {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) : 0 ≤ mutualInfo p := by
  have hpt : ∀ x : α, ∀ y : β, (p (x, y)).toReal -
      (∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal)
      ≤ (p (x, y)).toReal * Real.log ((p (x, y)).toReal /
        ((∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal))) := by
    intro x y
    refine gibbs_pointwise ENNReal.toReal_nonneg ?_ (support_zero p x y)
    apply mul_nonneg <;> apply Finset.sum_nonneg <;> intro _ _ <;>
      exact ENNReal.toReal_nonneg
  have hle : (∑ x, ∑ y, ((p (x, y)).toReal -
      (∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal)))
      ≤ mutualInfo p := by
    unfold mutualInfo
    apply Finset.sum_le_sum
    intro x _
    apply Finset.sum_le_sum
    intro y _
    exact hpt x y
  have heq : (∑ x, ∑ y, ((p (x, y)).toReal -
      (∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal))) = 0 := by
    simp only [Finset.sum_sub_distrib]
    rw [toReal_sum_prod p, marg_prod_sum p, sub_self]
  calc (0 : ℝ) = (∑ x, ∑ y, ((p (x, y)).toReal -
      (∑ y', (p (x, y')).toReal) * (∑ x', (p (x', y)).toReal))) := heq.symm
    _ ≤ mutualInfo p := hle

/-- Independent coordinates have zero mutual information. -/
theorem mutualInfo_prodJoint {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (q : PMF β) : mutualInfo (prodJoint p q) = 0 := by
  have hval : ∀ x : α, ∀ y : β, ((prodJoint p q) (x, y)).toReal
      = (p x).toReal * (q y).toReal := by
    intro x y
    rw [prodJoint_apply]
    exact ENNReal.toReal_mul
  have hX : ∀ x : α, (∑ y', ((prodJoint p q) (x, y')).toReal) = (p x).toReal := by
    intro x
    simp only [hval]
    rw [← Finset.mul_sum]
    have hq : (∑ y' : β, (q y').toReal) = 1 := toReal_sum_one q
    rw [hq, mul_one]
  have hY : ∀ y : β, (∑ x', ((prodJoint p q) (x', y)).toReal) = (q y).toReal := by
    intro y
    simp only [hval]
    rw [← Finset.sum_mul]
    have hp : (∑ x' : α, (p x').toReal) = 1 := toReal_sum_one p
    rw [hp, one_mul]
  unfold mutualInfo
  apply Finset.sum_eq_zero
  intro x _
  apply Finset.sum_eq_zero
  intro y _
  rw [hX, hY, hval]
  by_cases h0 : (p x).toReal * (q y).toReal = 0
  · rw [h0, zero_mul]
  · rw [div_self h0, Real.log_one, mul_zero]

/-- Mutual information is symmetric under swapping the
coordinates. -/
theorem mutualInfo_swap {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF (α × β)) :
    mutualInfo (p.map (fun z => (z.2, z.1))) = mutualInfo p := by
  have hmass : ∀ c : β, ∀ d : α, ((p.map fun z => (z.2, z.1)) (c, d)).toReal
      = (p (d, c)).toReal := by
    intro c d
    rw [map_swap_apply]
  have hterm : ∀ c : β, ∀ d : α,
      ((p.map fun z => (z.2, z.1)) (c, d)).toReal * Real.log (
        ((p.map fun z => (z.2, z.1)) (c, d)).toReal /
        ((∑ d', ((p.map fun z => (z.2, z.1)) (c, d')).toReal) *
          (∑ c', ((p.map fun z => (z.2, z.1)) (c', d)).toReal)))
      = (p (d, c)).toReal * Real.log ((p (d, c)).toReal /
        ((∑ y', (p (d, y')).toReal) * (∑ x', (p (x', c)).toReal))) := by
    intro c d
    simp only [hmass]
    congr 1
    congr 1
    congr 1
    exact mul_comm _ _
  unfold mutualInfo
  simp only [hterm]
  exact Finset.sum_comm
