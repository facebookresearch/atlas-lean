/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

/-
Modified for Atlas by Meta Platforms, Inc.: generalized the balanced weighted-colouring
existence theorem to finite index and colour types and exposed it through matrices and fibers.
-/
module

public import MathlibExt.Data.Fintype.PrescribedFunctions
public import MathlibExt.Data.Finset.MomentBounds
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-! # Balanced weighted colorings

A sufficiently large finite symmetric matrix with bounded row sums admits a coloring whose
fibers are balanced and whose ordered color blocks have bounded total weight. The main theorem
also has an off-diagonal form in which diagonal entries are ignored.

The proof is adapted from `Groundwork.Colouring.exists_colouring_core` and
`Groundwork.Colouring.exists_colouring_fintype` in
`eth/proof/networks/Groundwork/Net/Colouring.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth: a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Matrix

section Core

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

local notation "K" => Fintype.card κ
local notation "g" => Fintype.card ι
local notation "N" => Fintype.card κ ^ Fintype.card ι

private theorem card_prescribed (S : Finset ι) (f : ι → κ) :
    #{χ : ι → κ | ∀ a ∈ S, χ a = f a} * K ^ #S = N := by
  have h := Fintype.card_filter_univ_eqOn_mul_pow_card S (fun a => f a.1)
  have heq : (univ.filter fun χ : ι → κ => ∀ a : {a // a ∈ S}, χ a.1 = f a.1) =
      (univ.filter fun χ : ι → κ => ∀ a ∈ S, χ a = f a) := by
    apply Finset.ext
    intro χ
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · intro hχ a ha
      exact hχ ⟨a, ha⟩
    · intro hχ a
      exact hχ a.1 a.2
  rwa [heq] at h

private theorem card_one (a : ι) (γ : κ) :
    #{χ : ι → κ | χ a = γ} * K = N := by
  have h := card_prescribed (κ := κ) {a} (fun _ => γ)
  simpa using h

private theorem card_two {a b : ι} (hab : a ≠ b) (γ γ' : κ) :
    #{χ : ι → κ | χ a = γ ∧ χ b = γ'} * K ^ 2 = N := by
  have h := card_prescribed (κ := κ) {a, b} (fun x => if x = a then γ else γ')
  rw [card_pair hab] at h
  simpa [hab.symm] using h

private theorem card_four {a b a' b' : ι} (hab : a ≠ b) (h1 : a ≠ a')
    (h2 : a ≠ b') (h3 : b ≠ a') (h4 : b ≠ b') (h5 : a' ≠ b') (γ γ' : κ) :
    #{χ : ι → κ | (χ a = γ ∧ χ b = γ') ∧ (χ a' = γ ∧ χ b' = γ')} * K ^ 4 = N := by
  have h := card_prescribed (κ := κ) {a, b, a', b'}
    (fun x => if x = a ∨ x = a' then γ else γ')
  have hc : #({a, b, a', b'} : Finset ι) = 4 := by
    rw [card_insert_of_notMem (by simp [hab, h1, h2]),
      card_insert_of_notMem (by simp [h3, h4]), card_pair h5]
  rw [hc] at h
  simpa [hab.symm, h1.symm, h2.symm, h3, h3.symm, h4.symm, h5.symm, and_assoc] using h

private def classSize (γ : κ) (χ : ι → κ) : ℕ :=
  ∑ a : ι, if χ a = γ then 1 else 0

omit [DecidableEq ι] [Fintype κ] in
private theorem classSize_eq (γ : κ) (χ : ι → κ) :
    classSize γ χ = #{a | χ a = γ} := by
  simp [classSize]

private theorem sum_classSize (γ : κ) :
    (∑ χ : ι → κ, classSize γ χ) * K = g * N := by
  unfold classSize
  rw [sum_comm, sum_mul]
  have h : ∀ a : ι, (∑ χ : ι → κ, if χ a = γ then 1 else 0) * K = N := by
    intro a
    rw [← card_one a γ]
    simp
  rw [sum_congr rfl fun a _ => h a]
  simp

private theorem sum_classSize_sq (γ : κ) :
    (∑ χ : ι → κ, classSize γ χ ^ 2) * K ^ 2 ≤ g ^ 2 * N + g * K * N := by
  have h0 : ∀ χ : ι → κ, classSize γ χ ^ 2 =
      ∑ a : ι, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0 := by
    intro χ
    unfold classSize
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    split_ifs <;> simp_all
  simp only [h0]
  rw [sum_comm, sum_mul]
  have h1 : ∀ a : ι,
      (∑ χ : ι → κ, ∑ b : ι, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2 ≤
        g * N + K * N := by
    intro a
    rw [sum_comm, sum_mul]
    have h2 : ∀ b : ι,
        (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2 ≤
          N + if b = a then K * N else 0 := by
      intro b
      by_cases hab : b = a
      · subst hab
        have h := card_one (κ := κ) b γ
        simp only [and_self, ite_true]
        have heq : (∑ χ : ι → κ, if χ b = γ then 1 else 0) =
            #{χ : ι → κ | χ b = γ} := by simp
        rw [heq]
        calc
          #{χ : ι → κ | χ b = γ} * K ^ 2 = (#{χ : ι → κ | χ b = γ} * K) * K := by
            ring
          _ = K * N := by rw [h]; ring
          _ ≤ N + K * N := Nat.le_add_left _ _
      · have h := card_two (κ := κ) (Ne.symm hab) γ γ
        have heq : (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0) =
            #{χ : ι → κ | χ a = γ ∧ χ b = γ} := by simp
        rw [heq, h]
        simp [hab]
    calc
      ∑ b : ι, (∑ χ : ι → κ, if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2 ≤
          ∑ b : ι, (N + if b = a then K * N else 0) := sum_le_sum fun b _ => h2 b
      _ = g * N + K * N := by simp [sum_add_distrib]
  calc
    ∑ a : ι, (∑ χ : ι → κ, ∑ b : ι,
        if χ a = γ ∧ χ b = γ then 1 else 0) * K ^ 2 ≤
        ∑ _a : ι, (g * N + K * N) := sum_le_sum fun a _ => h1 a
    _ = g ^ 2 * N + g * K * N := by simp; ring

private theorem card_badClass (γ : κ) :
    #{χ : ι → κ | 2 * g ≤ K * classSize γ χ} * g ≤ K * N := by
  rcases Nat.eq_zero_or_pos g with h0 | hpos
  · rw [h0]
    simp
  have hc := Finset.card_filter_mul_sq_le_of_moments_univ
    (fun χ : ι → κ => classSize γ χ) K g (g * K * N) 1 g
    (by rw [sum_classSize]; simp [mul_comm])
    (by simpa [mul_comm] using sum_classSize_sq (ι := ι) γ)
  have heq : ∀ χ : ι → κ,
      (1 * g + g ≤ 1 * (K * classSize γ χ)) ↔ (2 * g ≤ K * classSize γ χ) := by
    intro χ
    omega
  simp only [heq] at hc
  have h : (#{χ : ι → κ | 2 * g ≤ K * classSize γ χ} * g) * g ≤
      (K * N) * g := by
    calc
      _ = #{χ : ι → κ | 2 * g ≤ K * classSize γ χ} * g ^ 2 := by ring
      _ ≤ 1 ^ 2 * (g * K * N) := hc
      _ = (K * N) * g := by ring
  exact Nat.le_of_mul_le_mul_right h hpos

private def blockCapacity (c : Matrix ι ι ℕ) (γ γ' : κ) (χ : ι → κ) : ℕ :=
  ∑ p : ι × ι, if χ p.1 = γ ∧ χ p.2 = γ' then c p.1 p.2 else 0

private def totalCapacity (c : Matrix ι ι ℕ) : ℕ :=
  ∑ p : ι × ι, c p.1 p.2

omit [DecidableEq ι] [Fintype κ] in
private theorem blockCapacity_le_totalCapacity (c : Matrix ι ι ℕ) (γ γ' : κ)
    (χ : ι → κ) : blockCapacity c γ γ' χ ≤ totalCapacity c := by
  unfold blockCapacity totalCapacity
  refine sum_le_sum fun p _ => ?_
  split_ifs <;> simp

omit [DecidableEq ι] in
private theorem totalCapacity_le (c : Matrix ι ι ℕ) (P : ℕ)
    (hP : ∀ a, ∑ b, c a b ≤ P) : totalCapacity c ≤ g * P := by
  unfold totalCapacity
  rw [Fintype.sum_prod_type]
  calc
    ∑ a, ∑ b, c a b ≤ ∑ _a : ι, P := sum_le_sum fun a _ => hP a
    _ = g * P := by simp

private theorem sum_blockCapacity (c : Matrix ι ι ℕ) (hd : ∀ a, c a a = 0)
    (γ γ' : κ) :
    (∑ χ : ι → κ, blockCapacity c γ γ' χ) * K ^ 2 = N * totalCapacity c := by
  unfold blockCapacity totalCapacity
  rw [sum_comm, sum_mul, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [← sum_filter, sum_const, smul_eq_mul]
  by_cases hp : p.1 = p.2
  · rw [hp, hd]
    simp
  · rw [← card_two hp γ γ']
    ring

private def meet (p q : ι × ι) : ℕ :=
  (if q.1 = p.1 then 1 else 0) + (if q.1 = p.2 then 1 else 0) +
    (if q.2 = p.1 then 1 else 0) + (if q.2 = p.2 then 1 else 0)

private theorem card_pairs_le (γ γ' : κ) (p q : ι × ι) (hp : p.1 ≠ p.2)
    (hq : q.1 ≠ q.2) :
    #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧
      (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4 ≤ N + K ^ 2 * N * meet p q := by
  rcases Nat.eq_zero_or_pos (meet p q) with hm | hm
  · rw [hm]
    simp only [meet, Nat.add_eq_zero_iff, ite_eq_right_iff, one_ne_zero, imp_false] at hm
    obtain ⟨⟨⟨m1, m2⟩, m3⟩, m4⟩ := hm
    rw [card_four hp (Ne.symm m1) (Ne.symm m3) (Ne.symm m2) (Ne.symm m4) hq γ γ']
    simp
  · have hle : #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧
        (χ q.1 = γ ∧ χ q.2 = γ')} ≤
        #{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} := by
      refine card_le_card fun χ h => ?_
      simp only [mem_filter, mem_univ, true_and] at h ⊢
      exact h.1
    calc
      #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧
          (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4 ≤
          #{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} * K ^ 4 :=
            Nat.mul_le_mul_right _ hle
      _ = K ^ 2 * (#{χ : ι → κ | χ p.1 = γ ∧ χ p.2 = γ'} * K ^ 2) := by ring
      _ = K ^ 2 * N * 1 := by rw [card_two hp γ γ']; ring
      _ ≤ K ^ 2 * N * meet p q := Nat.mul_le_mul_left _ hm
      _ ≤ N + K ^ 2 * N * meet p q := Nat.le_add_left _ _

private theorem sum_meet (c : Matrix ι ι ℕ) (hs : ∀ a b, c a b = c b a) (P : ℕ)
    (hP : ∀ a, ∑ b, c a b ≤ P) (p : ι × ι) :
    ∑ q : ι × ι, c q.1 q.2 * meet p q ≤ 4 * P := by
  have r1 : ∀ x : ι,
      ∑ q : ι × ι, c q.1 q.2 * (if q.1 = x then 1 else 0) ≤ P := by
    intro x
    rw [Fintype.sum_prod_type, sum_comm]
    simpa using hP x
  have r2 : ∀ x : ι,
      ∑ q : ι × ι, c q.1 q.2 * (if q.2 = x then 1 else 0) ≤ P := by
    intro x
    rw [Fintype.sum_prod_type]
    have h := hP x
    simp only [hs x] at h
    simpa using h
  unfold meet
  simp only [mul_add, sum_add_distrib]
  have := r1 p.1
  have := r1 p.2
  have := r2 p.1
  have := r2 p.2
  omega

private theorem sum_blockCapacity_sq (c : Matrix ι ι ℕ) (hd : ∀ a, c a a = 0)
    (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P)
    (γ γ' : κ) :
    (∑ χ : ι → κ, blockCapacity c γ γ' χ ^ 2) * K ^ 4 ≤
      N * totalCapacity c ^ 2 + 4 * K ^ 2 * N * P * totalCapacity c := by
  have h0 : ∀ χ : ι → κ, blockCapacity c γ γ' χ ^ 2 =
      ∑ p : ι × ι, ∑ q : ι × ι,
        if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then
          c p.1 p.2 * c q.1 q.2 else 0 := by
    intro χ
    unfold blockCapacity
    rw [sq, sum_mul_sum]
    refine sum_congr rfl fun p _ => sum_congr rfl fun q _ => ?_
    split_ifs <;> simp_all
  simp only [h0]
  rw [sum_comm, sum_mul]
  have h1 : ∀ p : ι × ι,
      (∑ χ : ι → κ, ∑ q : ι × ι,
        if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then
          c p.1 p.2 * c q.1 q.2 else 0) * K ^ 4 ≤
        c p.1 p.2 * (N * totalCapacity c + K ^ 2 * N * (4 * P)) := by
    intro p
    rw [sum_comm, sum_mul]
    have h2 : ∀ q : ι × ι,
        (∑ χ : ι → κ,
          if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then
            c p.1 p.2 * c q.1 q.2 else 0) * K ^ 4 ≤
          c p.1 p.2 *
            (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) := by
      intro q
      rw [← sum_filter, sum_const, smul_eq_mul]
      by_cases hp : p.1 = p.2
      · rw [hp, hd]
        simp
      by_cases hq : q.1 = q.2
      · rw [hq, hd]
        simp
      calc
        #{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧
            (χ q.1 = γ ∧ χ q.2 = γ')} * (c p.1 p.2 * c q.1 q.2) * K ^ 4 =
            (c p.1 p.2 * c q.1 q.2) *
              (#{χ : ι → κ | (χ p.1 = γ ∧ χ p.2 = γ') ∧
                (χ q.1 = γ ∧ χ q.2 = γ')} * K ^ 4) := by ring
        _ ≤ (c p.1 p.2 * c q.1 q.2) * (N + K ^ 2 * N * meet p q) :=
          Nat.mul_le_mul_left _ (card_pairs_le γ γ' p q hp hq)
        _ = c p.1 p.2 *
            (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) := by ring
    calc
      ∑ q : ι × ι, (∑ χ : ι → κ,
          if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then
            c p.1 p.2 * c q.1 q.2 else 0) * K ^ 4 ≤
          ∑ q : ι × ι, c p.1 p.2 *
            (N * c q.1 q.2 + K ^ 2 * N * (c q.1 q.2 * meet p q)) :=
              sum_le_sum fun q _ => h2 q
      _ = c p.1 p.2 * (N * totalCapacity c +
          K ^ 2 * N * ∑ q : ι × ι, c q.1 q.2 * meet p q) := by
            simp only [← mul_sum, sum_add_distrib, totalCapacity]
      _ ≤ c p.1 p.2 * (N * totalCapacity c + K ^ 2 * N * (4 * P)) := by
        gcongr
        exact sum_meet c hs P hP p
  calc
    ∑ p : ι × ι, (∑ χ : ι → κ, ∑ q : ι × ι,
        if (χ p.1 = γ ∧ χ p.2 = γ') ∧ (χ q.1 = γ ∧ χ q.2 = γ') then
          c p.1 p.2 * c q.1 q.2 else 0) * K ^ 4 ≤
        ∑ p : ι × ι, c p.1 p.2 *
          (N * totalCapacity c + K ^ 2 * N * (4 * P)) :=
            sum_le_sum fun p _ => h1 p
    _ = totalCapacity c * (N * totalCapacity c + K ^ 2 * N * (4 * P)) := by
      rw [← sum_mul, totalCapacity]
    _ = N * totalCapacity c ^ 2 + 4 * K ^ 2 * N * P * totalCapacity c := by ring

private theorem card_badBlock (c : Matrix ι ι ℕ) (hd : ∀ a, c a a = 0)
    (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P)
    (γ γ' : κ) :
    #{χ : ι → κ | K * totalCapacity c + g * P < K ^ 3 * blockCapacity c γ γ' χ} * g ≤
      4 * K ^ 4 * N := by
  have hU := totalCapacity_le c P hP
  rcases Nat.eq_zero_or_pos (g * P) with h0 | hpos
  · have hU0 : totalCapacity c = 0 := by omega
    have hnone : ({χ : ι → κ |
        K * totalCapacity c + g * P < K ^ 3 * blockCapacity c γ γ' χ} :
          Finset (ι → κ)) = ∅ := by
      refine filter_false_of_mem fun χ _ => ?_
      have hY := blockCapacity_le_totalCapacity c γ γ' χ
      have hY0 : blockCapacity c γ γ' χ = 0 := by omega
      simp [hY0]
    rw [hnone]
    simp
  have hc := Finset.card_filter_mul_sq_le_of_moments_univ
    (fun χ : ι → κ => blockCapacity c γ γ' χ) (K ^ 2) (totalCapacity c)
    (4 * K ^ 2 * N * P * totalCapacity c) K (g * P)
    (by rw [sum_blockCapacity c hd]; simp)
    (by
      have h := sum_blockCapacity_sq c hd hs P hP γ γ'
      rw [← pow_mul]
      simpa using h)
  have hsub : #{χ : ι → κ |
      K * totalCapacity c + g * P < K ^ 3 * blockCapacity c γ γ' χ} ≤
      #{χ : ι → κ | K * totalCapacity c + g * P ≤
        K * (K ^ 2 * blockCapacity c γ γ' χ)} := by
    refine card_le_card fun χ h => ?_
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    calc
      K * totalCapacity c + g * P ≤ K ^ 3 * blockCapacity c γ γ' χ := h.le
      _ = K * (K ^ 2 * blockCapacity c γ γ' χ) := by ring
  have hPpos : 0 < P := Nat.pos_of_mul_pos_left hpos
  have h : (#{χ : ι → κ |
      K * totalCapacity c + g * P < K ^ 3 * blockCapacity c γ γ' χ} * g) *
        (g * P * P) ≤ (4 * K ^ 4 * N) * (g * P * P) := by
    calc
      _ = #{χ : ι → κ |
          K * totalCapacity c + g * P < K ^ 3 * blockCapacity c γ γ' χ} *
            (g * P) ^ 2 := by ring
      _ ≤ #{χ : ι → κ | K * totalCapacity c + g * P ≤
          K * (K ^ 2 * blockCapacity c γ γ' χ)} * (g * P) ^ 2 :=
            Nat.mul_le_mul_right _ hsub
      _ ≤ K ^ 2 * (4 * K ^ 2 * N * P * totalCapacity c) := hc
      _ = (4 * K ^ 4 * N * P) * totalCapacity c := by ring
      _ ≤ (4 * K ^ 4 * N * P) * (g * P) := Nat.mul_le_mul_left _ hU
      _ = (4 * K ^ 4 * N) * (g * P * P) := by ring
  exact Nat.le_of_mul_le_mul_right h (Nat.mul_pos hpos hPpos)

private theorem exists_balanced_coloring_aux (c : Matrix ι ι ℕ) (hd : ∀ a, c a a = 0)
    (hs : ∀ a b, c a b = c b a) (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P)
    (hK : 0 < K) (hg : 4 * K ^ 6 + K ^ 2 < g) :
    ∃ χ : ι → κ, (∀ γ, K * classSize γ χ < 2 * g) ∧
      ∀ γ γ', K ^ 3 * blockCapacity c γ γ' χ ≤ K * totalCapacity c + g * P := by
  by_contra hcon
  push Not at hcon
  have hcov : (univ : Finset (ι → κ)) ⊆
      (univ.biUnion fun γ : κ => {χ : ι → κ | 2 * g ≤ K * classSize γ χ}) ∪
      (univ.biUnion fun p : κ × κ => {χ : ι → κ |
        K * totalCapacity c + g * P < K ^ 3 * blockCapacity c p.1 p.2 χ}) := by
    intro χ _
    simp only [mem_union, mem_biUnion, mem_univ, mem_filter, true_and, Prod.exists]
    by_cases h : ∀ γ, K * classSize γ χ < 2 * g
    · right
      exact hcon χ h
    · left
      push Not at h
      exact h
  have h1 := card_le_card hcov
  have h2 := card_union_le
    (univ.biUnion fun γ : κ => ({χ : ι → κ | 2 * g ≤ K * classSize γ χ} :
      Finset (ι → κ)))
    (univ.biUnion fun p : κ × κ => ({χ : ι → κ |
      K * totalCapacity c + g * P < K ^ 3 * blockCapacity c p.1 p.2 χ} :
        Finset (ι → κ)))
  have h3 : #(univ.biUnion fun γ : κ =>
      ({χ : ι → κ | 2 * g ≤ K * classSize γ χ} : Finset (ι → κ))) * g ≤
        K * (K * N) := by
    calc
      _ ≤ (∑ γ : κ, #{χ : ι → κ | 2 * g ≤ K * classSize γ χ}) * g :=
        Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ γ : κ, #{χ : ι → κ | 2 * g ≤ K * classSize γ χ} * g :=
        sum_mul _ _ _
      _ ≤ ∑ _γ : κ, K * N := sum_le_sum fun γ _ => card_badClass γ
      _ = K * (K * N) := by simp
  have h4 : #(univ.biUnion fun p : κ × κ => ({χ : ι → κ |
      K * totalCapacity c + g * P < K ^ 3 * blockCapacity c p.1 p.2 χ} :
        Finset (ι → κ))) * g ≤ (K * K) * (4 * K ^ 4 * N) := by
    calc
      _ ≤ (∑ p : κ × κ, #{χ : ι → κ |
          K * totalCapacity c + g * P < K ^ 3 * blockCapacity c p.1 p.2 χ}) * g :=
            Nat.mul_le_mul_right _ card_biUnion_le
      _ = ∑ p : κ × κ, #{χ : ι → κ |
          K * totalCapacity c + g * P < K ^ 3 * blockCapacity c p.1 p.2 χ} * g :=
            sum_mul _ _ _
      _ ≤ ∑ _p : κ × κ, 4 * K ^ 4 * N :=
        sum_le_sum fun p _ => card_badBlock c hd hs P hP p.1 p.2
      _ = (K * K) * (4 * K ^ 4 * N) := by simp
  have h5 : #(univ : Finset (ι → κ)) = N := by simp
  rw [h5] at h1
  have h6 : N * g ≤ (4 * K ^ 6 + K ^ 2) * N := by
    calc
      N * g ≤ (_ + _) * g := Nat.mul_le_mul_right _ (h1.trans h2)
      _ = _ * g + _ * g := add_mul _ _ _
      _ ≤ K * (K * N) + (K * K) * (4 * K ^ 4 * N) := Nat.add_le_add h3 h4
      _ = (4 * K ^ 6 + K ^ 2) * N := by ring
  have hN : 0 < N := pow_pos hK g
  have hle : N * g ≤ N * (4 * K ^ 6 + K ^ 2) := by
    rw [mul_comm N (4 * K ^ 6 + K ^ 2)]
    exact h6
  exact absurd (Nat.le_of_mul_le_mul_left hle hN) (not_le.2 hg)

/-- A finite symmetric natural-valued matrix with zero diagonal and bounded row sums has a
coloring with balanced fibers and bounded weight in every ordered color block. -/
theorem exists_balanced_coloring (c : Matrix ι ι ℕ) (hd : ∀ a, c a a = 0)
    (hs : c.IsSymm) (P : ℕ) (hP : ∀ a, ∑ b, c a b ≤ P) (hK : 0 < K)
    (hg : 4 * K ^ 6 + K ^ 2 < g) :
    ∃ χ : ι → κ, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', K ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', c a b) ≤
        K * (∑ a, ∑ b, c a b) + g * P := by
  obtain ⟨χ, hclass, hblock⟩ := exists_balanced_coloring_aux c hd
    (fun a b => (hs.apply a b).symm) P hP hK hg
  refine ⟨χ, fun γ => by simpa only [classSize_eq] using hclass γ, fun γ γ' => ?_⟩
  have htotal : totalCapacity c = ∑ a, ∑ b, c a b := by
    unfold totalCapacity
    rw [Fintype.sum_prod_type]
  have hblock' : blockCapacity c γ γ' χ =
      ∑ a with χ a = γ, ∑ b with χ b = γ', c a b := by
    unfold blockCapacity
    rw [Fintype.sum_prod_type, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases ha : χ a = γ
    · simp only [ha, ite_true]
      rw [sum_filter]
      refine sum_congr rfl fun b _ => ?_
      by_cases hb : χ b = γ' <;> simp [hb]
    · simp [ha]
  simpa only [htotal, hblock'] using hblock γ γ'

/-- A finite symmetric natural-valued matrix with bounded off-diagonal row sums has a balanced
coloring whose blocks between distinct colors have bounded off-diagonal weight. Diagonal entries
are unrestricted and ignored. -/
theorem exists_balanced_coloring_offDiagonal (c : Matrix ι ι ℕ) (hK : 2 ≤ K)
    (hg : 3 * K ^ 8 ≤ g) (hs : c.IsSymm) (P : ℕ)
    (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : ι → κ, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' →
        K ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', c a b) ≤
          K * (∑ a, ∑ b with b ≠ a, c a b) + g * P := by
  have hg' : 4 * K ^ 6 + K ^ 2 < g := by
    have h4 : 4 ≤ K ^ 2 := by nlinarith
    have h6 : 4 * K ^ 6 ≤ K ^ 8 := by
      calc
        4 * K ^ 6 ≤ K ^ 2 * K ^ 6 := Nat.mul_le_mul_right _ h4
        _ = K ^ 8 := by ring
    have h2 : K ^ 2 ≤ K ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
    have h0 : 0 < K ^ 8 := pow_pos (by omega) 8
    omega
  let c' : Matrix ι ι ℕ := fun a b => if b ≠ a then c a b else 0
  have hs' : c'.IsSymm := by
    change c'ᵀ = c'
    ext a b
    change c' b a = c' a b
    by_cases hab : a = b
    · subst b
      rfl
    · have hba : b ≠ a := Ne.symm hab
      rw [show c' b a = c b a by simp [c', hab]]
      rw [show c' a b = c a b by simp [c', hba]]
      exact hs.apply a b
  obtain ⟨χ, hclass, hblock⟩ := exists_balanced_coloring c' (by simp [c']) hs' P
    (fun a => by
      simp only [c']
      rw [← sum_filter]
      exact hP a) (by omega) hg'
  refine ⟨χ, hclass, fun γ γ' hne => ?_⟩
  have htotal : (∑ a, ∑ b, c' a b) = ∑ a, ∑ b with b ≠ a, c a b := by
    apply sum_congr rfl
    intro a _
    rw [← sum_filter]
  have hblock' : (∑ a with χ a = γ, ∑ b with χ b = γ', c' a b) =
      ∑ a with χ a = γ, ∑ b with χ b = γ', c a b := by
    apply sum_congr rfl
    intro a ha
    simp only [mem_filter, mem_univ, true_and] at ha
    apply sum_congr rfl
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb
    have hba : b ≠ a := by
      rintro rfl
      exact hne (ha.symm.trans hb)
    simp [c', hba]
  simpa only [htotal, hblock'] using hblock γ γ'

end Core

/-- The `Fin`-indexed form of `Matrix.exists_balanced_coloring_offDiagonal`. -/
theorem exists_balanced_coloring_fin {K g : ℕ} (hK : 2 ≤ K) (hg : 3 * K ^ 8 ≤ g)
    (c : Matrix (Fin g) (Fin g) ℕ) (hs : c.IsSymm) (P : ℕ)
    (hP : ∀ a, ∑ b with b ≠ a, c a b ≤ P) :
    ∃ χ : Fin g → Fin K, (∀ γ, K * #{a | χ a = γ} < 2 * g) ∧
      ∀ γ γ', γ ≠ γ' →
        K ^ 3 * (∑ a with χ a = γ, ∑ b with χ b = γ', c a b) ≤
          K * (∑ a, ∑ b with b ≠ a, c a b) + g * P := by
  simpa only [Fintype.card_fin] using
    exists_balanced_coloring_offDiagonal (ι := Fin g) (κ := Fin K) c
      (by simpa using hK) (by simpa using hg) hs P hP

end Matrix
