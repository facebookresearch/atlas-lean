/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OptimalStopping.Secretary
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# The secretary problem in the random-order model

The applicants are interviewed at times `0, …, n - 1` and `σ i` is the quality of the applicant
interviewed at time `i` (larger is better), for a uniformly random permutation `σ` of `Fin n`.
This file proves Ferguson's equation (3) (*Optimal Stopping and Applications*, Chapter 2, §2.1):
the threshold rule `N_r`, which rejects the applicants interviewed before time `r - 1` and then
selects the first applicant who is best so far, selects the best applicant for a proportion
`winProb n r` of the permutations.

The proof follows Ferguson's computation. The rule wins exactly when the best applicant comes at
a time `m ≥ r - 1` and the best of the applicants interviewed before time `m` comes before time
`r - 1`. Exchanging two positions is a bijection of the permutations, so the position of the best
applicant is uniform on `Fin n`, and, given that it is `m ≥ 1`, the position of the best of the
first `m` applicants is uniform on `{0, …, m - 1}`.
-/

@[expose] public section

open Finset Equiv

namespace MathlibExt.Probability.Secretary

variable {α : Type*} [Fintype α] [DecidableEq α]


variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem card_filter_mul_right (g : Perm α) (p : Perm α → Prop) [DecidablePred p] :
    #{σ : Perm α | p (σ * g)} = #{σ : Perm α | p σ} := by
  refine Finset.card_bij (fun σ _ => σ * g) (fun σ hσ => by simpa using hσ)
    (fun a _ b _ h => mul_right_cancel h) (fun b hb => ⟨b * g⁻¹, by simpa using hb, by simp⟩)

omit [Fintype α] [DecidableEq α] in
private theorem symm_mul_apply (σ g : Perm α) (v : α) : (σ * g).symm v = g.symm (σ.symm v) := by
  simp [Perm.mul_def]

private theorem card_symm_eq (v m m' : α) :
    #{σ : Perm α | σ.symm v = m} = #{σ : Perm α | σ.symm v = m'} := by
  rw [← card_filter_mul_right (swap m m') (fun σ => σ.symm v = m')]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, symm_mul_apply, Equiv.symm_swap]
  constructor
  · intro h; rw [h, swap_apply_left]
  · intro h
    have := congrArg (swap m m') h
    rwa [swap_apply_self, swap_apply_right] at this

private theorem card_symm_eq_factorial (k : ℕ) (v m : Fin (k + 1)) :
    #{σ : Perm (Fin (k + 1)) | σ.symm v = m} = k.factorial := by
  have hsum : ∑ m' : Fin (k + 1), #{σ : Perm (Fin (k + 1)) | σ.symm v = m'} =
      (k + 1).factorial := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin (k + 1)) => σ.symm v)
      (fun _ _ => mem_univ _)]
    simp [Fintype.card_perm]
  simp_rw [card_symm_eq v _ m] at hsum
  simp only [sum_const, card_univ, Fintype.card_fin, smul_eq_mul] at hsum
  rw [Nat.factorial_succ] at hsum
  exact Nat.eq_of_mul_eq_mul_left (Nat.succ_pos k) hsum


variable {k : ℕ}

-- Position of the best of the applicants interviewed before time `m` (any position if `m = 0`).
private noncomputable def prefMax (σ : Perm (Fin (k + 1))) (m : Fin (k + 1)) : Fin (k + 1) :=
  if h : ((Iio m).image σ).Nonempty then σ.symm (((Iio m).image σ).max' h) else 0

private theorem prefMax_spec (σ : Perm (Fin (k + 1))) {m : Fin (k + 1)} (hm : 0 < m) :
    prefMax σ m < m ∧ ∀ i, i < m → σ i ≤ σ (prefMax σ m) := by
  have hne : ((Iio m).image σ).Nonempty := ⟨σ 0, mem_image_of_mem _ (by simpa using hm)⟩
  have hmem := ((Iio m).image σ).max'_mem hne
  obtain ⟨j, hj, hjv⟩ := mem_image.mp hmem
  have hpm : prefMax σ m = j := by
    simp only [prefMax, hne, ↓reduceDIte, ← hjv, Equiv.symm_apply_apply]
  rw [hpm]
  refine ⟨by simpa using hj, fun i hi => ?_⟩
  rw [hjv]
  exact le_max' _ _ (mem_image_of_mem _ (by simpa using hi))

private theorem prefMax_unique (σ : Perm (Fin (k + 1))) {m j : Fin (k + 1)} (hj : j < m)
    (hmax : ∀ i, i < m → σ i ≤ σ j) : prefMax σ m = j := by
  have hm : 0 < m := lt_of_le_of_lt (Fin.zero_le _) hj
  obtain ⟨h1, h2⟩ := prefMax_spec σ hm
  exact σ.injective (le_antisymm (hmax _ h1) (h2 _ hj))

private theorem swap_lt_of_lt {m j j' x : Fin (k + 1)} (hj : j < m) (hj' : j' < m) (hx : x < m) :
    swap j j' x < m := by
  rw [swap_apply_def]
  split_ifs <;> assumption

private theorem prefMax_mul_swap (σ : Perm (Fin (k + 1))) {m j j' : Fin (k + 1)} (hj : j < m)
    (hj' : j' < m) : prefMax (σ * swap j j') m = swap j j' (prefMax σ m) := by
  have hm : 0 < m := lt_of_le_of_lt (Fin.zero_le _) hj
  obtain ⟨h1, h2⟩ := prefMax_spec σ hm
  refine prefMax_unique _ (swap_lt_of_lt hj hj' h1) fun i hi => ?_
  simp only [Perm.coe_mul, Function.comp_apply, swap_apply_self]
  exact h2 _ (swap_lt_of_lt hj hj' hi)

private theorem card_prefMax_eq (top m j j' : Fin (k + 1)) (hj : j < m) (hj' : j' < m) :
    #{σ : Perm (Fin (k + 1)) | σ.symm top = m ∧ prefMax σ m = j} =
      #{σ : Perm (Fin (k + 1)) | σ.symm top = m ∧ prefMax σ m = j'} := by
  rw [← card_filter_mul_right (swap j j') (fun σ => σ.symm top = m ∧ prefMax σ m = j')]
  congr 1
  ext σ
  simp only [mem_filter, mem_univ, true_and, symm_mul_apply, Equiv.symm_swap,
    prefMax_mul_swap σ hj hj']
  have hmj : m ≠ j := ne_of_gt hj
  have hmj' : m ≠ j' := ne_of_gt hj'
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [h1, swap_apply_of_ne_of_ne hmj hmj'], by rw [h2, swap_apply_left]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := congrArg (swap j j') h1
      rwa [swap_apply_self, swap_apply_of_ne_of_ne hmj hmj'] at this
    · have := congrArg (swap j j') h2
      rwa [swap_apply_self, swap_apply_right] at this

private theorem card_prefMax_mul (top m j : Fin (k + 1)) (hj : j < m) :
    (m : ℕ) * #{σ : Perm (Fin (k + 1)) | σ.symm top = m ∧ prefMax σ m = j} = k.factorial := by
  have hm : 0 < m := lt_of_le_of_lt (Fin.zero_le _) hj
  have hsum : ∑ j' ∈ Iio m, #{σ : Perm (Fin (k + 1)) | σ.symm top = m ∧ prefMax σ m = j'} =
      k.factorial := by
    rw [← card_symm_eq_factorial k top m]
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ => prefMax σ m) (t := Iio m)
      (s := {σ : Perm (Fin (k + 1)) | σ.symm top = m})
      (fun σ _ => by simpa using (prefMax_spec σ hm).1)]
    refine sum_congr rfl fun j' _ => ?_
    congr 1
    ext σ
    simp
  rw [sum_congr rfl (fun j' hj' => card_prefMax_eq top m j' j (by simpa using hj') hj)] at hsum
  simpa [Fin.card_Iio] using hsum


private theorem win_iff (r : ℕ) (σ : Perm (Fin (k + 1))) :
    (∃ i : Fin (k + 1), r - 1 ≤ (i : ℕ) ∧ (∀ j, j < i → σ j < σ i) ∧
        (∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < i → ∃ j, j < k' ∧ σ k' < σ j) ∧
        ∀ j, σ j ≤ σ i) ↔
      r - 1 ≤ (σ.symm (Fin.last k) : ℕ) ∧
        ∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < σ.symm (Fin.last k) →
          ∃ j, j < k' ∧ σ k' < σ j := by
  constructor
  · rintro ⟨i, hri, -, hnot, hmax⟩
    have hi : σ i = Fin.last k := by
      have := hmax (σ.symm (Fin.last k))
      rw [Equiv.apply_symm_apply] at this
      exact Fin.last_le_iff.mp this
    have : σ.symm (Fin.last k) = i := by rw [← hi, Equiv.symm_apply_apply]
    rw [this]
    exact ⟨hri, hnot⟩
  · rintro ⟨hr, hnot⟩
    refine ⟨σ.symm (Fin.last k), hr, fun j hj => ?_, hnot, fun j => ?_⟩
    · rw [Equiv.apply_symm_apply, Fin.lt_last_iff_ne_last]
      intro h
      have : j = σ.symm (Fin.last k) := by rw [← h, Equiv.symm_apply_apply]
      exact absurd this (ne_of_lt hj)
    · rw [Equiv.apply_symm_apply]
      exact Fin.le_last _

private theorem cond_iff_prefMax {r : ℕ} (σ : Perm (Fin (k + 1))) {m : Fin (k + 1)}
    (hrm : r - 1 < (m : ℕ)) :
    (∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < m → ∃ j, j < k' ∧ σ k' < σ j) ↔
      ((prefMax σ m : Fin (k + 1)) : ℕ) < r - 1 := by
  have hm : 0 < m := by
    rw [Fin.lt_def]; simp only [Fin.val_zero]; omega
  obtain ⟨h1, h2⟩ := prefMax_spec σ hm
  constructor
  · intro h
    by_contra hc
    push Not at hc
    obtain ⟨j, hj, hlt⟩ := h _ hc h1
    exact absurd (h2 j (hj.trans h1)) (not_le.mpr hlt)
  · intro h k' hk' hk'm
    refine ⟨prefMax σ m, ?_, ?_⟩
    · rw [Fin.lt_def]; omega
    · refine lt_of_le_of_ne (h2 k' hk'm) fun heq => ?_
      have := σ.injective heq
      rw [this] at hk'
      omega


private theorem card_fiber_cast {r : ℕ} (hr : 1 ≤ r) (m : Fin (k + 1)) :
    ((#{σ : Perm (Fin (k + 1)) | σ.symm (Fin.last k) = m ∧
        (r - 1 ≤ (m : ℕ) ∧ ∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < m →
          ∃ j, j < k' ∧ σ k' < σ j)} : ℕ) : ℝ) =
      if (m : ℕ) < r - 1 then 0 else if (m : ℕ) = r - 1 then (k.factorial : ℝ)
      else ((r : ℝ) - 1) * k.factorial / m := by
  split_ifs with h h'
  · norm_cast
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro σ _ ⟨_, hr, _⟩
    omega
  · norm_cast
    rw [← card_symm_eq_factorial k (Fin.last k) m]
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and, and_iff_left_iff_imp]
    intro _
    refine ⟨by omega, fun k' hk' hk'm => ?_⟩
    rw [Fin.lt_def] at hk'm
    omega
  · replace h : r - 1 < (m : ℕ) := by omega
    have hm : (0 : Fin (k + 1)) < m := by rw [Fin.lt_def]; simp only [Fin.val_zero]; omega
    have hr1 : r - 1 < k + 1 := h.trans m.isLt
    set j₀ : Fin (k + 1) := ⟨r - 1, hr1⟩ with hj₀
    have hset : #{σ : Perm (Fin (k + 1)) | σ.symm (Fin.last k) = m ∧
        (r - 1 ≤ (m : ℕ) ∧ ∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < m →
          ∃ j, j < k' ∧ σ k' < σ j)} =
        ∑ j ∈ Iio j₀, #{σ : Perm (Fin (k + 1)) | σ.symm (Fin.last k) = m ∧ prefMax σ m = j} := by
      rw [Finset.card_eq_sum_card_fiberwise (f := fun σ => prefMax σ m) (t := Iio j₀)]
      · refine sum_congr rfl fun j hj => ?_
        congr 1
        ext σ
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨⟨h1, -⟩, h2⟩; exact ⟨h1, h2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, h.le, ?_⟩, h2⟩
          rw [cond_iff_prefMax σ h, h2]
          simpa [hj₀, Fin.lt_def] using hj
      · intro σ hσ
        simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hσ
        obtain ⟨-, -, hc⟩ := hσ
        rw [cond_iff_prefMax σ h] at hc
        simpa [hj₀, Fin.lt_def] using hc
    have hjm : ∀ j ∈ Iio j₀, j < m := fun j hj => by
      simp only [mem_Iio, Fin.lt_def, hj₀] at hj
      rw [Fin.lt_def]; omega
    rw [sum_congr rfl (fun j hj => card_prefMax_eq (Fin.last k) m j 0 (hjm j hj) hm), sum_const,
      Fin.card_Iio, smul_eq_mul] at hset
    have hmul := card_prefMax_mul (Fin.last k) m 0 hm
    have hm0 : (0 : ℝ) < (m : ℕ) := by exact_mod_cast (show 0 < (m : ℕ) by omega)
    rw [hset]
    push_cast
    rw [eq_div_iff hm0.ne']
    have : ((m : ℕ) : ℝ) * (#{σ : Perm (Fin (k + 1)) | σ.symm (Fin.last k) = m ∧
        prefMax σ m = 0} : ℝ) = k.factorial := by exact_mod_cast hmul
    have hr' : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    simp only [hj₀, hr']
    linear_combination ((r : ℝ) - 1) * this


private theorem card_win_cast {r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ k + 1) :
    ((#{σ : Perm (Fin (k + 1)) | ∃ i : Fin (k + 1), r - 1 ≤ (i : ℕ) ∧ (∀ j, j < i → σ j < σ i) ∧
        (∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < i → ∃ j, j < k' ∧ σ k' < σ j) ∧
        ∀ j, σ j ≤ σ i} : ℕ) : ℝ) / (k + 1).factorial = winProb (k + 1) r := by
  have hfib : #{σ : Perm (Fin (k + 1)) | ∃ i : Fin (k + 1), r - 1 ≤ (i : ℕ) ∧
        (∀ j, j < i → σ j < σ i) ∧
        (∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < i → ∃ j, j < k' ∧ σ k' < σ j) ∧
        ∀ j, σ j ≤ σ i} =
      ∑ m : Fin (k + 1), #{σ : Perm (Fin (k + 1)) | σ.symm (Fin.last k) = m ∧
        (r - 1 ≤ (m : ℕ) ∧ ∀ k' : Fin (k + 1), r - 1 ≤ (k' : ℕ) → k' < m →
          ∃ j, j < k' ∧ σ k' < σ j)} := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin (k + 1)) => σ.symm (Fin.last k))
      (t := univ) (fun _ _ => by simp)]
    refine sum_congr rfl fun m _ => ?_
    congr 1
    ext σ
    simp only [mem_filter, mem_univ, true_and, win_iff]
    constructor
    · rintro ⟨h, hm⟩; subst hm; exact ⟨rfl, h⟩
    · rintro ⟨hm, h⟩; subst hm; exact ⟨h, rfl⟩
  rw [hfib]
  push_cast
  simp_rw [card_fiber_cast hr]
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < r - 1 then (0 : ℝ) else if i = r - 1 then
    (k.factorial : ℝ) else ((r : ℝ) - 1) * k.factorial / i) (k + 1)]
  have hsplit : ∑ i ∈ range (k + 1), (if i < r - 1 then (0 : ℝ) else if i = r - 1 then
      (k.factorial : ℝ) else ((r : ℝ) - 1) * k.factorial / i) =
      k.factorial * (1 + ((r : ℝ) - 1) * harmonicTail (k + 1) r) := by
    rw [range_eq_Ico, ← sum_Ico_consecutive _ (Nat.zero_le (r - 1)) (by omega : r - 1 ≤ k + 1),
      sum_eq_sum_Ico_succ_bot (by omega : r - 1 < k + 1), show r - 1 + 1 = r by omega]
    have h0 : ∑ i ∈ Ico 0 (r - 1), (if i < r - 1 then (0 : ℝ) else if i = r - 1 then
        (k.factorial : ℝ) else ((r : ℝ) - 1) * k.factorial / i) = 0 :=
      sum_eq_zero fun i hi => by simp only [(mem_Ico.mp hi).2, ↓reduceIte]
    have h1 : ∑ i ∈ Ico r (k + 1), (if i < r - 1 then (0 : ℝ) else if i = r - 1 then
        (k.factorial : ℝ) else ((r : ℝ) - 1) * k.factorial / i) =
        ((r : ℝ) - 1) * k.factorial * harmonicTail (k + 1) r := by
      unfold harmonicTail
      rw [mul_sum]
      refine sum_congr rfl fun i hi => ?_
      have hi' := (mem_Ico.mp hi).1
      simp only [show ¬i < r - 1 by omega, show i ≠ r - 1 by omega, ↓reduceIte]
      ring
    rw [h0, h1]
    simp only [lt_irrefl, ↓reduceIte, zero_add]
    ring
  rw [hsplit, winProb, Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := by positivity
  field_simp


/-- **Win probability of a threshold rule in the random-order model** (Ferguson, *Optimal
Stopping and Applications*, Chapter 2, equation (3)). For `1 ≤ r ≤ n`, the rule `N_r` rejects
the applicants interviewed at times `0, …, r - 2` and selects the first later applicant who is
best so far. The proportion of permutations for which the selected applicant is the best of
all equals `winProb n r`. -/
theorem card_thresholdRule_wins_div_factorial {n r : ℕ} (hr : 1 ≤ r) (hrn : r ≤ n) :
    ((Finset.univ.filter fun σ : Equiv.Perm (Fin n) =>
        ∃ i : Fin n, r - 1 ≤ (i : ℕ) ∧ (∀ j, j < i → σ j < σ i) ∧
          (∀ k : Fin n, r - 1 ≤ (k : ℕ) → k < i → ∃ j, j < k ∧ σ k < σ j) ∧
          ∀ j, σ j ≤ σ i).card : ℝ) / n.factorial = winProb n r := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact card_win_cast hr hrn

end MathlibExt.Probability.Secretary
