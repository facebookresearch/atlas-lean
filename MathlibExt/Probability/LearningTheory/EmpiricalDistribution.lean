/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Probability.ProbabilityMassFunction.Basic

@[expose] public section

/-! # Learning a discrete distribution in total variation

For `n` i.i.d. samples from a distribution on a `k`-element type,
the expected `L1` distance between the empirical frequencies and
the true distribution is at most `√(k / n)`. This is the upper
bound of roadmap package ML-33 of the Atlas TCS canon roadmap.

Source: Devroye, Gyorfi and Lugosi, A Probabilistic Theory of
Pattern Recognition (1996), Chapter 7.
-/

open Finset

/-- The empirical frequency of value `a` in a sample tuple. -/
noncomputable def empFreq {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ} (x : Fin n → α)
    (a : α) : ℝ :=
  ((Finset.univ.filter (fun i => x i = a)).card : ℝ) / n

private theorem mass_sum {α : Type*} [Fintype α] (p : PMF α) :
    ∑ a, (p a).toReal = 1 := by
  have h1 := p.tsum_coe
  have h2 := ENNReal.tsum_toReal_eq (fun a => p.apply_ne_top a)
  rw [h1, ENNReal.toReal_one, tsum_fintype] at h2
  exact h2.symm

private theorem sum_prod_univ {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (g : Fin n → α → ℝ) :
    (∑ x : Fin n → α, ∏ k, g k (x k)) = ∏ k, ∑ b, g k b := by
  have hh := Finset.sum_prod_piFinset (Finset.univ : Finset α) g
  rwa [Fintype.piFinset_univ] at hh

private theorem weight_sum {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ} :
    ∑ x : Fin n → α, ∏ i, (p (x i)).toReal = 1 := by
  have h := sum_prod_univ (fun _ : Fin n => fun b => (p b).toReal)
  calc ∑ x : Fin n → α, ∏ i, (p (x i)).toReal
      = ∏ i, ∑ b, (p b).toReal := h
    _ = ∏ _ : Fin n, 1 := Finset.prod_congr rfl (fun _ _ => mass_sum p)
    _ = 1 := Finset.prod_const_one

private theorem weight_nonneg {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ}
    (x : Fin n → α) : 0 ≤ ∏ i, (p (x i)).toReal :=
  Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)

private theorem sum_weighted_factor {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (f : Fin n → α → ℝ) (j : Fin n) (h : α → ℝ) :
    ∑ x : Fin n → α, (∏ k, f k (x k)) * h (x j)
      = (∑ b, f j b * h b) * ∏ k ∈ Finset.univ.erase j, (∑ b, f k b) := by
  have step1 : ∀ x : Fin n → α, (∏ k, f k (x k)) * h (x j)
      = ∏ k, (if k = j then f k (x k) * h (x k) else f k (x k)) := by
    intro x
    have e2 : (∏ k ∈ Finset.univ.erase j,
        (if k = j then f k (x k) * h (x k) else f k (x k)))
        = ∏ k ∈ Finset.univ.erase j, f k (x k) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hkj : k ≠ j := Finset.ne_of_mem_erase hk
      simp [hkj]
    calc (∏ k, f k (x k)) * h (x j)
        = (f j (x j) * ∏ k ∈ Finset.univ.erase j, f k (x k)) * h (x j) := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
      _ = (f j (x j) * h (x j)) * ∏ k ∈ Finset.univ.erase j, f k (x k) := by ring
      _ = (if j = j then f j (x j) * h (x j) else f j (x j))
          * ∏ k ∈ Finset.univ.erase j, f k (x k) := by simp
      _ = (if j = j then f j (x j) * h (x j) else f j (x j))
          * ∏ k ∈ Finset.univ.erase j,
            (if k = j then f k (x k) * h (x k) else f k (x k)) := by rw [e2]
      _ = ∏ k, (if k = j then f k (x k) * h (x k) else f k (x k)) := by
          exact Finset.mul_prod_erase (Finset.univ)
            (fun k => if k = j then f k (x k) * h (x k) else f k (x k))
            (Finset.mem_univ j)
  have h2 := sum_prod_univ (fun k b => if k = j then f k b * h b else f k b)
  calc ∑ x : Fin n → α, (∏ k, f k (x k)) * h (x j)
      = ∑ x : Fin n → α, ∏ k,
          (if k = j then f k (x k) * h (x k) else f k (x k)) :=
        Finset.sum_congr rfl (fun x _ => step1 x)
    _ = ∏ k, ∑ b, (if k = j then f k b * h b else f k b) := h2
    _ = (∑ b, f j b * h b) * ∏ k ∈ Finset.univ.erase j, (∑ b, f k b) := by
        calc ∏ k, ∑ b, (if k = j then f k b * h b else f k b)
            = (∑ b, (if j = j then f j b * h b else f j b))
              * ∏ k ∈ Finset.univ.erase j,
                (∑ b, (if k = j then f k b * h b else f k b)) := by
              exact (Finset.mul_prod_erase (Finset.univ)
                (fun k => ∑ b, (if k = j then f k b * h b else f k b))
                (Finset.mem_univ j)).symm
          _ = (∑ b, f j b * h b) * ∏ k ∈ Finset.univ.erase j, (∑ b, f k b) := by
              congr 1
              · exact Finset.sum_congr rfl (fun b _ => by simp)
              · exact Finset.prod_congr rfl (fun k hk => Finset.sum_congr rfl (fun b _ => by
                  have hkj : k ≠ j := Finset.ne_of_mem_erase hk
                  simp [hkj]))

private theorem ind_single {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) (a : α) :
    ∑ b, (p b).toReal * (if b = a then (1:ℝ) else 0) = (p a).toReal := by
  calc ∑ b, (p b).toReal * (if b = a then (1:ℝ) else 0)
      = ∑ b, (if b = a then (p b).toReal else 0) := by
        apply Finset.sum_congr rfl
        intro b _
        by_cases hb : b = a <;> simp [hb]
    _ = (p a).toReal := Fintype.sum_ite_eq' a (fun b => (p b).toReal)

private theorem moment1 {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ}
    (i : Fin n) (a : α) :
    ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (if x i = a then (1:ℝ) else 0)
      = (p a).toReal := by
  have h := sum_weighted_factor (fun _ : Fin n => fun b => (p b).toReal) i
    (fun b => if b = a then (1:ℝ) else 0)
  have eB : (∏ k ∈ Finset.univ.erase i, (∑ b, (p b).toReal)) = 1 := by
    calc (∏ k ∈ Finset.univ.erase i, (∑ b, (p b).toReal))
        = ∏ k ∈ Finset.univ.erase i, 1 :=
          Finset.prod_congr rfl (fun k _ => mass_sum p)
      _ = 1 := Finset.prod_const_one
  calc ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (if x i = a then (1:ℝ) else 0)
      = (∑ b, (p b).toReal * (if b = a then (1:ℝ) else 0))
        * ∏ k ∈ Finset.univ.erase i, (∑ b, (p b).toReal) := h
    _ = (p a).toReal * 1 := by rw [ind_single p a, eB]
    _ = (p a).toReal := mul_one _

private theorem moment2 {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ}
    (i j : Fin n) (hij : i ≠ j) (a : α) :
    ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0))
      = (p a).toReal ^ 2 := by
  have h := sum_weighted_factor
    (fun k b => if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0) else (p b).toReal)
    j (fun b => if b = a then (1:ℝ) else 0)
  have perx : ∀ x : Fin n → α,
      (∏ k, (p (x k)).toReal) * ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0))
      = (∏ k, (if k = i then (p (x k)).toReal * (if x k = a then (1:ℝ) else 0)
          else (p (x k)).toReal))
        * (if x j = a then (1:ℝ) else 0) := by
    intro x
    have e2 : (∏ k ∈ Finset.univ.erase i, (p (x k)).toReal)
        = ∏ k ∈ Finset.univ.erase i, (if k = i then (p (x k)).toReal
          * (if x k = a then (1:ℝ) else 0) else (p (x k)).toReal) := by
      apply Finset.prod_congr rfl
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      simp [hki]
    calc (∏ k, (p (x k)).toReal)
          * ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0))
        = ((p (x i)).toReal * ∏ k ∈ Finset.univ.erase i, (p (x k)).toReal)
          * ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0)) := by
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      _ = ((p (x i)).toReal * (if x i = a then (1:ℝ) else 0))
          * ((∏ k ∈ Finset.univ.erase i, (p (x k)).toReal)
            * (if x j = a then (1:ℝ) else 0)) := by ring
      _ = (if i = i then (p (x i)).toReal * (if x i = a then (1:ℝ) else 0)
            else (p (x i)).toReal)
          * ((∏ k ∈ Finset.univ.erase i, (p (x k)).toReal)
            * (if x j = a then (1:ℝ) else 0)) := by simp
      _ = ((if i = i then (p (x i)).toReal * (if x i = a then (1:ℝ) else 0)
            else (p (x i)).toReal)
          * (∏ k ∈ Finset.univ.erase i, (if k = i then (p (x k)).toReal
            * (if x k = a then (1:ℝ) else 0) else (p (x k)).toReal)))
          * (if x j = a then (1:ℝ) else 0) := by rw [e2]; ring
      _ = (∏ k, (if k = i then (p (x k)).toReal * (if x k = a then (1:ℝ) else 0)
            else (p (x k)).toReal))
          * (if x j = a then (1:ℝ) else 0) := by
          congr 1
          exact Finset.mul_prod_erase (Finset.univ)
            (fun k => if k = i then (p (x k)).toReal * (if x k = a then (1:ℝ) else 0)
              else (p (x k)).toReal)
            (Finset.mem_univ i)
  have hji : j ≠ i := Ne.symm hij
  have eA : (∑ b, (if j = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
        else (p b).toReal) * (if b = a then (1:ℝ) else 0)) = (p a).toReal := by
    calc (∑ b, (if j = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
          else (p b).toReal) * (if b = a then (1:ℝ) else 0))
        = ∑ b, (p b).toReal * (if b = a then (1:ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          simp [hji]
      _ = (p a).toReal := ind_single p a
  have hmem : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  have eB1 : (∑ b, (if i = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
      else (p b).toReal)) = (p a).toReal := by
    calc (∑ b, (if i = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
          else (p b).toReal))
        = ∑ b, (p b).toReal * (if b = a then (1:ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro b _
          simp
      _ = (p a).toReal := ind_single p a
  have eB2 : (∏ k ∈ (Finset.univ.erase j).erase i,
      (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
        else (p b).toReal))) = 1 := by
    have e : ∀ k ∈ (Finset.univ.erase j).erase i,
        (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
          else (p b).toReal)) = 1 := by
      intro k hk
      have hki : k ≠ i := Finset.ne_of_mem_erase hk
      calc (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
            else (p b).toReal))
          = ∑ b, (p b).toReal := by
            apply Finset.sum_congr rfl
            intro b _
            simp [hki]
        _ = 1 := mass_sum p
    calc (∏ k ∈ (Finset.univ.erase j).erase i,
          (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
            else (p b).toReal)))
        = ∏ k ∈ (Finset.univ.erase j).erase i, 1 := Finset.prod_congr rfl e
      _ = 1 := Finset.prod_const_one
  have eB : (∏ k ∈ Finset.univ.erase j,
      (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
        else (p b).toReal))) = (p a).toReal := by
    calc (∏ k ∈ Finset.univ.erase j,
          (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
            else (p b).toReal)))
        = (∑ b, (if i = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
            else (p b).toReal))
          * ∏ k ∈ (Finset.univ.erase j).erase i,
            (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
              else (p b).toReal)) := by
          exact (Finset.mul_prod_erase (Finset.univ.erase j)
            (fun k => ∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
              else (p b).toReal))
            hmem).symm
      _ = (p a).toReal * 1 := by rw [eB1, eB2]
      _ = (p a).toReal := mul_one _
  calc ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0))
      = ∑ x : Fin n → α, (∏ k, (if k = i then (p (x k)).toReal
          * (if x k = a then (1:ℝ) else 0) else (p (x k)).toReal))
        * (if x j = a then (1:ℝ) else 0) :=
        Finset.sum_congr rfl (fun x _ => perx x)
    _ = (∑ b, (if j = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
          else (p b).toReal) * (if b = a then (1:ℝ) else 0))
        * ∏ k ∈ Finset.univ.erase j,
          (∑ b, (if k = i then (p b).toReal * (if b = a then (1:ℝ) else 0)
            else (p b).toReal)) := h
    _ = (p a).toReal * (p a).toReal := by rw [eA, eB]
    _ = (p a).toReal ^ 2 := by ring

private theorem moment_count {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ}
    (a : α) :
    ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (∑ i, (if x i = a then (1:ℝ) else 0))
      = (n : ℝ) * (p a).toReal := by
  calc ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (∑ i, (if x i = a then (1:ℝ) else 0))
      = ∑ i, ∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
        * (if x i = a then (1:ℝ) else 0) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
    _ = ∑ i : Fin n, (p a).toReal := Finset.sum_congr rfl (fun i _ => moment1 p i a)
    _ = (n : ℝ) * (p a).toReal := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private theorem moment_count_sq {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ}
    (a : α) :
    ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2
      = (n : ℝ) ^ 2 * (p a).toReal ^ 2 + (n : ℝ) * ((p a).toReal - (p a).toReal ^ 2) := by
  have hsq : ∀ x : Fin n → α, (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2
      = ∑ i, ∑ j, ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0)) := by
    intro x
    rw [pow_two, Finset.sum_mul_sum]
  have hswap : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (∑ i, ∑ j,
      ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0))))
      = ∑ i, ∑ j, ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0)) := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm.trans (Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
  have perij : ∀ i j : Fin n,
      (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0)))
      = (p a).toReal ^ 2
        + (if i = j then ((p a).toReal - (p a).toReal ^ 2) else 0) := by
    intro i j
    by_cases hij : i = j
    · have esq : ∀ x : Fin n → α,
          ((if x i = a then (1:ℝ) else 0) * (if x i = a then (1:ℝ) else 0))
          = (if x i = a then (1:ℝ) else 0) := by
        intro x
        by_cases hx : x i = a <;> simp [hx]
      calc (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
            ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0)))
          = ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
            ((if x i = a then (1:ℝ) else 0) * (if x i = a then (1:ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [hij]
        _ = ∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
            * (if x i = a then (1:ℝ) else 0) :=
            Finset.sum_congr rfl (fun x _ => by rw [esq x])
        _ = (p a).toReal := moment1 p i a
        _ = (p a).toReal ^ 2
            + (if i = j then ((p a).toReal - (p a).toReal ^ 2) else 0) := by
            simp [hij]
    · calc (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
            ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0)))
          = (p a).toReal ^ 2 := moment2 p i j hij a
        _ = (p a).toReal ^ 2
            + (if i = j then ((p a).toReal - (p a).toReal ^ 2) else 0) := by
            simp [hij]
  have inner : ∀ i : Fin n, (∑ j, ((p a).toReal ^ 2
      + (if i = j then ((p a).toReal - (p a).toReal ^ 2) else 0)))
      = (n : ℝ) * (p a).toReal ^ 2 + ((p a).toReal - (p a).toReal ^ 2) := by
    intro i
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    · exact Fintype.sum_ite_eq i (fun _ => ((p a).toReal - (p a).toReal ^ 2))
  calc ∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
        * (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2
      = ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (∑ i, ∑ j,
        ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0))) :=
        Finset.sum_congr rfl (fun x _ => by rw [hsq x])
    _ = ∑ i, ∑ j, ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((if x i = a then (1:ℝ) else 0) * (if x j = a then (1:ℝ) else 0)) := hswap
    _ = ∑ i, ∑ j, ((p a).toReal ^ 2
        + (if i = j then ((p a).toReal - (p a).toReal ^ 2) else 0)) :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => perij i j))
    _ = (n : ℝ) ^ 2 * (p a).toReal ^ 2
        + (n : ℝ) * ((p a).toReal - (p a).toReal ^ 2) := by
        calc ∑ i, ∑ j, ((p a).toReal ^ 2
              + (if i = j then ((p a).toReal - (p a).toReal ^ 2) else 0))
            = ∑ i : Fin n, ((n : ℝ) * (p a).toReal ^ 2
              + ((p a).toReal - (p a).toReal ^ 2)) :=
              Finset.sum_congr rfl (fun i _ => inner i)
          _ = (∑ i : Fin n, ((n : ℝ) * (p a).toReal ^ 2))
              + ∑ i : Fin n, ((p a).toReal - (p a).toReal ^ 2) := by
              rw [Finset.sum_add_distrib]
          _ = (n : ℝ) ^ 2 * (p a).toReal ^ 2
              + (n : ℝ) * ((p a).toReal - (p a).toReal ^ 2) := by
              rw [Finset.sum_const, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
                nsmul_eq_mul, nsmul_eq_mul]
              ring

private theorem var_bound {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ}
    (hn : 0 < n) (a : α) :
    ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2
      ≤ (p a).toReal / n := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hE1 := moment_count (n := n) p a
  have hE2 := moment_count_sq (n := n) p a
  have hw1 := weight_sum p (n := n)
  have hexpand : ∀ x : Fin n → α,
      ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2
      = (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2 / (n : ℝ) ^ 2
        - (2 * (p a).toReal / (n : ℝ)) * (∑ i, (if x i = a then (1:ℝ) else 0))
        + (p a).toReal ^ 2 := by
    intro x
    ring
  have f1 : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
      ((∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2 / (n : ℝ) ^ 2))
      = (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
        * (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2) / (n : ℝ) ^ 2 := by
    calc (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          ((∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2 / (n : ℝ) ^ 2))
        = ∑ x : Fin n → α, ((∏ k, (p (x k)).toReal)
          * (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2) / (n : ℝ) ^ 2 := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
          * (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2) / (n : ℝ) ^ 2 :=
          (Finset.sum_div _ _ _).symm
  have f2 : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
      ((2 * (p a).toReal / (n : ℝ)) * (∑ i, (if x i = a then (1:ℝ) else 0))))
      = (2 * (p a).toReal / (n : ℝ)) * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
        * (∑ i, (if x i = a then (1:ℝ) else 0))) := by
    calc (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          ((2 * (p a).toReal / (n : ℝ)) * (∑ i, (if x i = a then (1:ℝ) else 0))))
        = ∑ x : Fin n → α, (2 * (p a).toReal / (n : ℝ)) * ((∏ k, (p (x k)).toReal)
          * (∑ i, (if x i = a then (1:ℝ) else 0))) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (2 * (p a).toReal / (n : ℝ)) * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
          * (∑ i, (if x i = a then (1:ℝ) else 0))) := (Finset.mul_sum _ _ _).symm
  have f3 : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (p a).toReal ^ 2)
      = (p a).toReal ^ 2 * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)) := by
    calc (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (p a).toReal ^ 2)
        = ∑ x : Fin n → α, (p a).toReal ^ 2 * (∏ k, (p (x k)).toReal) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
      _ = (p a).toReal ^ 2 * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)) :=
          (Finset.mul_sum _ _ _).symm
  have hE : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2)
      = (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
        * (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2) / (n : ℝ) ^ 2
        - (2 * (p a).toReal / (n : ℝ)) * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
          * (∑ i, (if x i = a then (1:ℝ) else 0)))
        + (p a).toReal ^ 2 * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)) := by
    calc (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2)
        = ∑ x : Fin n → α, ((((∏ k, (p (x k)).toReal) *
            ((∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2 / (n : ℝ) ^ 2))
          - ((∏ k, (p (x k)).toReal)) *
            ((2 * (p a).toReal / (n : ℝ)) * (∑ i, (if x i = a then (1:ℝ) else 0))))
          + (∏ k, (p (x k)).toReal) * (p a).toReal ^ 2) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [hexpand x]
          ring
      _ = (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
            ((∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2 / (n : ℝ) ^ 2))
          - (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
            ((2 * (p a).toReal / (n : ℝ)) * (∑ i, (if x i = a then (1:ℝ) else 0))))
          + (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) * (p a).toReal ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
          * (∑ i, (if x i = a then (1:ℝ) else 0)) ^ 2) / (n : ℝ) ^ 2
          - (2 * (p a).toReal / (n : ℝ)) * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)
            * (∑ i, (if x i = a then (1:ℝ) else 0)))
          + (p a).toReal ^ 2 * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal)) := by
          rw [f1, f2, f3]
  have hfin : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2)
      = (p a).toReal * (1 - (p a).toReal) / n := by
    rw [hE, hE1, hE2, hw1]
    field_simp
    ring
  rw [hfin, div_le_div_iff_of_pos_right hnR]
  nlinarith [sq_nonneg ((p a).toReal)]

private theorem jensen_coord {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α) {n : ℕ}
    (hn : 0 < n) (a : α) :
    ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|
      ≤ Real.sqrt ((p a).toReal / n) := by
  have hvar : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2)
      ≤ (p a).toReal / n := var_bound p hn a
  have hcs : (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|) ^ 2
      ≤ ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin n → α))
      (fun x => Real.sqrt (∏ k, (p (x k)).toReal))
      (fun x => Real.sqrt (∏ k, (p (x k)).toReal) *
        |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|)
    have e_fg : (∑ x : Fin n → α, Real.sqrt (∏ k, (p (x k)).toReal) *
        (Real.sqrt (∏ k, (p (x k)).toReal) *
          |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|))
        = ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal| := by
      apply Finset.sum_congr rfl
      intro x _
      have hw : 0 ≤ ∏ k, (p (x k)).toReal := weight_nonneg p x
      calc Real.sqrt (∏ k, (p (x k)).toReal) *
            (Real.sqrt (∏ k, (p (x k)).toReal) *
              |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|)
          = (Real.sqrt (∏ k, (p (x k)).toReal) * Real.sqrt (∏ k, (p (x k)).toReal))
            * |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal| := by ring
        _ = (∏ k, (p (x k)).toReal) *
            |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal| := by
            rw [Real.mul_self_sqrt hw]
    have e_f2 : (∑ x : Fin n → α, (Real.sqrt (∏ k, (p (x k)).toReal)) ^ 2) = 1 := by
      calc (∑ x : Fin n → α, (Real.sqrt (∏ k, (p (x k)).toReal)) ^ 2)
          = ∑ x : Fin n → α, ∏ k, (p (x k)).toReal := by
            apply Finset.sum_congr rfl
            intro x _
            exact Real.sq_sqrt (weight_nonneg p x)
        _ = 1 := weight_sum p
    have e_g2 : (∑ x : Fin n → α, (Real.sqrt (∏ k, (p (x k)).toReal) *
          |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|) ^ 2)
        = ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2 := by
      apply Finset.sum_congr rfl
      intro x _
      have hw : 0 ≤ ∏ k, (p (x k)).toReal := weight_nonneg p x
      calc (Real.sqrt (∏ k, (p (x k)).toReal) *
            |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|) ^ 2
          = (Real.sqrt (∏ k, (p (x k)).toReal)) ^ 2 *
            (|(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|) ^ 2 := by ring
        _ = (∏ k, (p (x k)).toReal) *
            ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2 := by
            rw [Real.sq_sqrt hw, sq_abs]
    calc (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|) ^ 2
        = (∑ x : Fin n → α, Real.sqrt (∏ k, (p (x k)).toReal) *
          (Real.sqrt (∏ k, (p (x k)).toReal) *
            |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|)) ^ 2 := by
          rw [e_fg]
      _ ≤ (∑ x : Fin n → α, (Real.sqrt (∏ k, (p (x k)).toReal)) ^ 2) *
          (∑ x : Fin n → α, (Real.sqrt (∏ k, (p (x k)).toReal) *
            |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|) ^ 2) := h
      _ = 1 * (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2) := by
          rw [e_f2, e_g2]
      _ = ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
          ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2 := one_mul _
  calc ∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|
      ≤ Real.sqrt (∑ x : Fin n → α, (∏ k, (p (x k)).toReal) *
        ((∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal) ^ 2) :=
        Real.le_sqrt_of_sq_le hcs
    _ ≤ Real.sqrt ((p a).toReal / n) := Real.sqrt_le_sqrt hvar

private theorem count_eq_sum {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
    (x : Fin n → α) (a : α) :
    (((Finset.univ.filter (fun i => x i = a)).card : ℕ) : ℝ)
      = ∑ i, (if x i = a then (1:ℝ) else 0) :=
  Finset.natCast_card_filter (fun i => x i = a) (Finset.univ : Finset (Fin n))

/-- Learning a discrete distribution in total variation (expectation
form): for `n ≥ 1` i.i.d. samples from `p` on a finite type, the
expected `L1` distance between the empirical frequencies and `p`
is at most `√(k / n)`, where `k` is the alphabet size. The
expectation is over all sample tuples weighted by their
probability under `p`. -/
theorem empFreq_l1_expectation {α : Type*} [Fintype α] [DecidableEq α] (p : PMF α)
    {n : ℕ} (hn : 0 < n) :
    (∑ x : Fin n → α, (∏ i, (p (x i)).toReal) *
      ∑ a, |empFreq x a - (p a).toReal|) ≤
    Real.sqrt (Fintype.card α / n) := by
  have hswap : (∑ x : Fin n → α, (∏ i, (p (x i)).toReal) * ∑ a, |empFreq x a - (p a).toReal|)
      = ∑ a, ∑ x : Fin n → α, (∏ i, (p (x i)).toReal) * |empFreq x a - (p a).toReal| := by
    simp_rw [Finset.mul_sum]
    exact Finset.sum_comm
  rw [hswap]
  have emp_eq : ∀ x : Fin n → α, ∀ a : α, empFreq x a
      = (∑ i, (if x i = a then (1:ℝ) else 0)) / n := by
    intro x a
    unfold empFreq
    rw [count_eq_sum x a]
  simp_rw [emp_eq]
  have hcoord : ∀ a : α, (∑ x : Fin n → α, (∏ i, (p (x i)).toReal) *
      |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|)
      ≤ Real.sqrt ((p a).toReal / n) := fun a => jensen_coord p hn a
  have hsum : (∑ a, (Real.sqrt ((p a).toReal / n)) ^ 2) = 1 / (n : ℝ) := by
    have e : ∀ a : α, (Real.sqrt ((p a).toReal / n)) ^ 2 = (p a).toReal / n := by
      intro a
      apply Real.sq_sqrt
      apply div_nonneg ENNReal.toReal_nonneg
      exact Nat.cast_nonneg n
    calc (∑ a, (Real.sqrt ((p a).toReal / n)) ^ 2)
        = ∑ a, ((p a).toReal / n) := Finset.sum_congr rfl (fun a _ => e a)
      _ = (∑ a, (p a).toReal) / n := (Finset.sum_div _ _ _).symm
      _ = 1 / (n : ℝ) := by rw [mass_sum p]
  have hcs : (∑ a, Real.sqrt ((p a).toReal / n)) ^ 2
      ≤ (Fintype.card α : ℝ) * (∑ a, (Real.sqrt ((p a).toReal / n)) ^ 2) := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset α))
      (f := fun a => Real.sqrt ((p a).toReal / n))
    rw [Finset.card_univ] at h
    exact h
  calc (∑ a, ∑ x : Fin n → α, (∏ i, (p (x i)).toReal) *
        |(∑ i, (if x i = a then (1:ℝ) else 0)) / n - (p a).toReal|)
      ≤ ∑ a, Real.sqrt ((p a).toReal / n) :=
        Finset.sum_le_sum (fun a _ => hcoord a)
    _ ≤ Real.sqrt (Fintype.card α / n) := by
        apply Real.le_sqrt_of_sq_le
        calc (∑ a, Real.sqrt ((p a).toReal / n)) ^ 2
            ≤ (Fintype.card α : ℝ) * (∑ a, (Real.sqrt ((p a).toReal / n)) ^ 2) := hcs
          _ = (Fintype.card α : ℝ) * (1 / (n : ℝ)) := by rw [hsum]
          _ = (Fintype.card α : ℝ) / n := by ring
