/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Topology.MetricSpace.Basic

import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Path coupling

If a one-step coupling contracts the expected distance by `β`,
then the total variation between the chains after `t` steps is at
most `β^t * dist x y / δ`, where `δ` is the least nonzero distance
in the space. This is roadmap package ML-27 of the Atlas TCS canon
roadmap.

Source: Levin and Peres, Markov Chains and Mixing Times (2017),
Chapter 13.
-/

open Finset
open scoped Classical ENNReal

/-- Total variation distance between two PMFs on a finite type:
half the `L1` distance. -/
noncomputable def tvDist {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  (1 / 2) * ∑ a, |(p a).toReal - (q a).toReal|

/-- The distribution of a Markov chain after `t` steps started from
`x`, where `K` is the one-step kernel. -/
noncomputable def chainDist {α : Type*} (K : α → PMF α) (x : α) : ℕ → PMF α
  | 0 => PMF.pure x
  | t + 1 => (chainDist K x t).bind K

private noncomputable def JCoupling {α : Type*} (C : α → α → PMF (α × α))
    (x y : α) : ℕ → PMF (α × α)
  | 0 => PMF.pure (x, y)
  | t + 1 => (JCoupling C x y t).bind (fun z => C z.1 z.2)

private theorem chainDist_zero {α : Type*} (K : α → PMF α) (x : α) :
    chainDist K x 0 = PMF.pure x := rfl

private theorem chainDist_succ {α : Type*} (K : α → PMF α) (x : α) (t : ℕ) :
    chainDist K x (t + 1) = (chainDist K x t).bind K := rfl

private theorem JCoupling_zero {α : Type*} (C : α → α → PMF (α × α))
    (x y : α) : JCoupling C x y 0 = PMF.pure (x, y) := rfl

private theorem JCoupling_succ {α : Type*} (C : α → α → PMF (α × α))
    (x y : α) (t : ℕ) :
    JCoupling C x y (t + 1)
      = (JCoupling C x y t).bind (fun z => C z.1 z.2) := rfl

private theorem JCoupling_map_fst {α : Type*} (K : α → PMF α)
    (C : α → α → PMF (α × α))
    (hC_fst : ∀ x y, (C x y).map Prod.fst = K x) (x y : α) (t : ℕ) :
    (JCoupling C x y t).map Prod.fst = chainDist K x t := by
  induction t with
  | zero => rw [JCoupling_zero, chainDist_zero, PMF.pure_map]
  | succ t ih =>
      rw [JCoupling_succ, PMF.map_bind]
      simp only [hC_fst]
      have hcomp : (fun z : α × α => K z.1) = K ∘ Prod.fst := rfl
      rw [hcomp, ← PMF.bind_map, ih, chainDist_succ]

private theorem JCoupling_map_snd {α : Type*} (K : α → PMF α)
    (C : α → α → PMF (α × α))
    (hC_snd : ∀ x y, (C x y).map Prod.snd = K y) (x y : α) (t : ℕ) :
    (JCoupling C x y t).map Prod.snd = chainDist K y t := by
  induction t with
  | zero => rw [JCoupling_zero, chainDist_zero, PMF.pure_map]
  | succ t ih =>
      rw [JCoupling_succ, PMF.map_bind]
      simp only [hC_snd]
      have hcomp : (fun z : α × α => K z.2) = K ∘ Prod.snd := rfl
      rw [hcomp, ← PMF.bind_map, ih, chainDist_succ]

private theorem JCoupling_dist_le {α : Type*} [PseudoMetricSpace α]
    [Fintype α] (C : α → α → PMF (α × α)) {β : ℝ}
    (hcontract : ∀ x y, ∑ z, (C x y z).toReal * dist z.1 z.2 ≤
      β * dist x y) (x y : α) (t : ℕ) :
    ∑ z, ((JCoupling C x y t) z).toReal * dist z.1 z.2 ≤
      β ^ t * dist x y := by
  by_cases hβ0 : 0 ≤ β
  · induction t with
    | zero =>
        rw [JCoupling_zero]
        have hterm : ∀ z : α × α, ((PMF.pure (x, y)) z).toReal * dist z.1 z.2
            = if z = (x, y) then dist x y else 0 := by
          intro z
          by_cases h : z = (x, y)
          · subst h
            rw [PMF.pure_apply_self, ENNReal.toReal_one, one_mul,
              ite_eq_left rfl]
          · simp [h, PMF.pure_apply_of_ne _ _ h]
        have h1 : ∑ z, ((PMF.pure (x, y)) z).toReal * dist z.1 z.2
            = dist x y := by
          simp_rw [hterm]
          rw [Finset.sum_ite_eq']
          simp
        rw [h1, pow_zero, one_mul]
    | succ t ih =>
        rw [JCoupling_succ]
        have hside : ∀ z : α × α, ∀ a ∈ (univ : Finset (α × α)),
            ((JCoupling C x y t) a * (C a.1 a.2) z) ≠ ∞ := by
          intro z a _
          exact ENNReal.mul_ne_top ((JCoupling C x y t).apply_ne_top a)
            ((C a.1 a.2).apply_ne_top z)
        have hexpand : ∀ z : α × α,
            (((JCoupling C x y t).bind (fun w => C w.1 w.2)) z).toReal
              = ∑ w, ((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal := by
          intro z
          rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum (hside z)]
          refine Finset.sum_congr rfl fun w _ => ?_
          show (((JCoupling C x y t) w) * ((C w.1 w.2) z)).toReal
            = ((JCoupling C x y t) w).toReal * (((C w.1 w.2) z)).toReal
          rw [ENNReal.toReal_mul]
        simp_rw [hexpand, Finset.sum_mul]
        have hswap : (∑ z, ∑ w, (((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal) * dist z.1 z.2)
            = ∑ w, ∑ z, (((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal) * dist z.1 z.2 :=
          Finset.sum_comm
        rw [hswap]
        have hfactor : ∀ w : α × α,
            (∑ z, (((JCoupling C x y t) w).toReal
                * ((C w.1 w.2) z).toReal) * dist z.1 z.2)
              = ((JCoupling C x y t) w).toReal
                * (∑ z, ((C w.1 w.2) z).toReal * dist z.1 z.2) := by
          intro w
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun z _ => ?_
          show (((JCoupling C x y t) w).toReal * ((C w.1 w.2) z).toReal)
              * dist z.1 z.2
            = ((JCoupling C x y t) w).toReal
              * (((C w.1 w.2) z).toReal * dist z.1 z.2)
          ring
        simp_rw [hfactor]
        calc ∑ w, ((JCoupling C x y t) w).toReal
                * (∑ z, ((C w.1 w.2) z).toReal * dist z.1 z.2)
            ≤ ∑ w, ((JCoupling C x y t) w).toReal * (β * dist w.1 w.2) := by
              apply Finset.sum_le_sum
              intro w _
              exact mul_le_mul_of_nonneg_left (hcontract w.1 w.2)
                ENNReal.toReal_nonneg
          _ = β * (∑ w, ((JCoupling C x y t) w).toReal * dist w.1 w.2) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun w _ => ?_
              show ((JCoupling C x y t) w).toReal * (β * dist w.1 w.2)
                = β * (((JCoupling C x y t) w).toReal * dist w.1 w.2)
              ring
          _ ≤ β * (β ^ t * dist x y) := mul_le_mul_of_nonneg_left ih hβ0
          _ = β ^ (t + 1) * dist x y := by
              rw [pow_succ]
              ring
  · have hneg : β < 0 := lt_of_not_ge hβ0
    have hdist0 : ∀ a b : α, dist a b = 0 := by
      intro a b
      have hsum : 0 ≤ ∑ z, (C a b z).toReal * dist z.1 z.2 :=
        Finset.sum_nonneg fun z _ =>
          mul_nonneg ENNReal.toReal_nonneg dist_nonneg
      have hle : 0 ≤ β * dist a b := le_trans hsum (hcontract a b)
      have hle' : dist a b ≤ 0 := nonpos_of_mul_nonneg_right hle hneg
      exact le_antisymm hle' dist_nonneg
    simp [hdist0]

private theorem map_fst_toReal {α : Type*} [Fintype α] (J : PMF (α × α))
    (a : α) : ((J.map Prod.fst) a).toReal = ∑ b, (J (a, b)).toReal := by
  have hne : ∀ w ∈ (univ : Finset (α × α)),
      (if a = w.1 then J w else 0) ≠ ∞ := by
    intro w _
    split_ifs with h
    · exact J.apply_ne_top w
    · exact ENNReal.zero_ne_top
  have hinner : ∀ x : α, (∑ y : α, (if a = x then J (x, y) else 0).toReal)
      = if a = x then (∑ y, (J (x, y)).toReal) else 0 := by
    intro x
    by_cases h : a = x <;> simp [h]
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum hne,
    Fintype.sum_prod_type]
  simp only []
  show (∑ x : α, ∑ y : α, (if a = x then J (x, y) else 0).toReal)
    = ∑ b, (J (a, b)).toReal
  simp_rw [hinner]
  rw [Finset.sum_ite_eq]
  simp

private theorem map_snd_toReal {α : Type*} [Fintype α] (J : PMF (α × α))
    (a : α) : ((J.map Prod.snd) a).toReal = ∑ b, (J (b, a)).toReal := by
  have hne : ∀ w ∈ (univ : Finset (α × α)),
      (if a = w.2 then J w else 0) ≠ ∞ := by
    intro w _
    split_ifs with h
    · exact J.apply_ne_top w
    · exact ENNReal.zero_ne_top
  have hpush : ∀ x y : α, (if a = y then J (x, y) else 0).toReal
      = if a = y then (J (x, y)).toReal else 0 := by
    intro x y
    by_cases h : a = y <;> simp [h]
  have hinner : ∀ x : α, (∑ y : α, (if a = y then J (x, y) else 0).toReal)
      = (J (x, a)).toReal := by
    intro x
    simp_rw [hpush]
    rw [Finset.sum_ite_eq]
    simp
  rw [PMF.map_apply, tsum_fintype, ENNReal.toReal_sum hne,
    Fintype.sum_prod_type]
  simp only []
  show (∑ x : α, ∑ y : α, (if a = y then J (x, y) else 0).toReal)
    = ∑ b, (J (b, a)).toReal
  simp_rw [hinner]

private theorem tvDist_map_le {α : Type*} [Fintype α] (J : PMF (α × α)) :
    tvDist (J.map Prod.fst) (J.map Prod.snd)
      ≤ ∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) := by
  have hfst : ∀ a : α, ((J.map Prod.fst) a).toReal
      = ∑ b, (J (a, b)).toReal := fun a => map_fst_toReal J a
  have hsnd : ∀ a : α, ((J.map Prod.snd) a).toReal
      = ∑ b, (J (b, a)).toReal := fun a => map_snd_toReal J a
  have hterm : ∀ a b : α, |(J (a, b)).toReal - (J (b, a)).toReal|
      ≤ (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1)
        + (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1) := by
    intro a b
    by_cases h : a = b
    · subst h
      simp
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_one, mul_one]
      calc |(J (a, b)).toReal - (J (b, a)).toReal|
          ≤ |(J (a, b)).toReal| + |(J (b, a)).toReal| := abs_sub _ _
        _ = (J (a, b)).toReal + (J (b, a)).toReal := by
            rw [abs_of_nonneg ENNReal.toReal_nonneg,
              abs_of_nonneg ENNReal.toReal_nonneg]
  have hper : ∀ a : α, |((J.map Prod.fst) a).toReal
        - ((J.map Prod.snd) a).toReal|
      ≤ (∑ b, (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1))
        + (∑ b, (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1)) := by
    intro a
    have hsub : (∑ b, (J (a, b)).toReal) - (∑ b, (J (b, a)).toReal)
        = ∑ b, ((J (a, b)).toReal - (J (b, a)).toReal) :=
      (Finset.sum_sub_distrib _ _).symm
    rw [hfst a, hsnd a, hsub]
    have habs : ∀ g : α → ℝ, |∑ b, g b| ≤ ∑ b, |g b| := by
      intro g
      have h := norm_sum_le (univ : Finset α) g
      simpa only [Real.norm_eq_abs] using h
    calc |∑ b, ((J (a, b)).toReal - (J (b, a)).toReal)|
        ≤ ∑ b, |(J (a, b)).toReal - (J (b, a)).toReal| := habs _
      _ ≤ ∑ b, ((J (a, b)).toReal * (if a = b then (0 : ℝ) else 1)
          + (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1)) := by
          apply Finset.sum_le_sum
          intro b _
          exact hterm a b
      _ = (∑ b, (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1))
          + (∑ b, (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1)) :=
          Finset.sum_add_distrib
  have hsum : (∑ a, |((J.map Prod.fst) a).toReal
        - ((J.map Prod.snd) a).toReal|)
      ≤ 2 * (∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1)) := by
    have hA : (∑ a : α, ∑ b : α, (J (a, b)).toReal
            * (if a = b then (0 : ℝ) else 1))
        = ∑ z : α × α, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) :=
      (Fintype.sum_prod_type' _).symm
    have hB : (∑ a : α, ∑ b : α, (J (b, a)).toReal
            * (if b = a then (0 : ℝ) else 1))
        = ∑ z : α × α, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) :=
      (Fintype.sum_prod_type_right' _).symm
    calc (∑ a, |((J.map Prod.fst) a).toReal - ((J.map Prod.snd) a).toReal|)
        ≤ ∑ a, ((∑ b, (J (a, b)).toReal * (if a = b then (0 : ℝ) else 1))
          + (∑ b, (J (b, a)).toReal * (if b = a then (0 : ℝ) else 1))) := by
          apply Finset.sum_le_sum
          intro a _
          exact hper a
      _ = (∑ a : α, ∑ b : α, (J (a, b)).toReal
              * (if a = b then (0 : ℝ) else 1))
          + (∑ a : α, ∑ b : α, (J (b, a)).toReal
              * (if b = a then (0 : ℝ) else 1)) :=
          Finset.sum_add_distrib
      _ = 2 * (∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1)) := by
          rw [hA, hB]
          ring
  unfold tvDist
  calc (1 / 2) * (∑ a, |((J.map Prod.fst) a).toReal
          - ((J.map Prod.snd) a).toReal|)
      ≤ (1 / 2) * (2 * (∑ z, (J z).toReal
        * (if z.1 = z.2 then (0 : ℝ) else 1))) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = ∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1) := by ring

private theorem mass_le_dist_div {α : Type*} [PseudoMetricSpace α]
    [Fintype α] (J : PMF (α × α)) {δ : ℝ} (hδ : 0 < δ)
    (hdist : ∀ x y : α, x ≠ y → δ ≤ dist x y) :
    (∑ z, (J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1))
      ≤ (∑ z, (J z).toReal * dist z.1 z.2) / δ := by
  rw [le_div_iff₀ hδ, Finset.sum_mul]
  refine Finset.sum_le_sum fun z _ => ?_
  show ((J z).toReal * (if z.1 = z.2 then (0 : ℝ) else 1)) * δ
    ≤ (J z).toReal * dist z.1 z.2
  by_cases h : z.1 = z.2
  · rw [ite_eq_left h, mul_zero, zero_mul]
    exact mul_nonneg ENNReal.toReal_nonneg dist_nonneg
  · rw [ite_eq_right h, mul_one]
    exact mul_le_mul_of_nonneg_left (hdist z.1 z.2 h)
      ENNReal.toReal_nonneg

/-- Path coupling bound: suppose `C x y` is a one-step coupling of
`K` (its marginals are `K x` and `K y`), and the coupled distance
contracts in expectation by `β ≤ 1` for every pair. On a finite
metric space whose nonzero distances are at least `δ > 0`, the
chains started at `x`, `y` satisfy
`tvDist ≤ β^t * dist x y / δ` after `t` steps. -/
theorem path_coupling_tv {α : Type*} [PseudoMetricSpace α] [Fintype α]
    (K : α → PMF α) (C : α → α → PMF (α × α))
    (hC_fst : ∀ x y, (C x y).map Prod.fst = K x)
    (hC_snd : ∀ x y, (C x y).map Prod.snd = K y)
    {β δ : ℝ} (hβ : β ≤ 1) (hδ : 0 < δ)
    (hdist : ∀ x y : α, x ≠ y → δ ≤ dist x y)
    (hcontract : ∀ x y, ∑ z, (C x y z).toReal * dist z.1 z.2 ≤
      β * dist x y)
    (x y : α) (t : ℕ) :
    tvDist (chainDist K x t) (chainDist K y t) ≤ β ^ t * dist x y / δ := by
  have hfst : (JCoupling C x y t).map Prod.fst = chainDist K x t :=
    JCoupling_map_fst K C hC_fst x y t
  have hsnd : (JCoupling C x y t).map Prod.snd = chainDist K y t :=
    JCoupling_map_snd K C hC_snd x y t
  have hdecay : ∑ z, ((JCoupling C x y t) z).toReal * dist z.1 z.2
      ≤ β ^ t * dist x y :=
    JCoupling_dist_le C hcontract x y t
  have hcouple := tvDist_map_le (JCoupling C x y t)
  rw [hfst, hsnd] at hcouple
  have hmass := mass_le_dist_div (JCoupling C x y t) hδ hdist
  calc tvDist (chainDist K x t) (chainDist K y t)
      ≤ ∑ z, ((JCoupling C x y t) z).toReal
        * (if z.1 = z.2 then (0 : ℝ) else 1) := hcouple
    _ ≤ (∑ z, ((JCoupling C x y t) z).toReal * dist z.1 z.2) / δ := hmass
    _ ≤ β ^ t * dist x y / δ := (div_le_div_iff_of_pos_right hδ).mpr hdecay
