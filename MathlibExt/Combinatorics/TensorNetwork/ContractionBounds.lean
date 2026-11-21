/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: ported exact shape and integer bounds for tensor-network contraction.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Contraction

/-! # Bounds for contraction of factored tensor networks

Contraction along a map whose fibers contain at most `m` vertices multiplies the shape parameter
by `m`. For integer-valued networks, it changes the absolute-value exponent from `B` to
`B * (m + m * m)`.

Adapted from `eth/proof/networks/Groundwork/Net/Net.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork.Factored

open Finset

variable {J J' σ τ : Type*}

private theorem abs_prod_le_two_pow {I : Type*} (s : Finset I) (f : I → ℤ) {B k : ℕ}
    (h : ∀ i ∈ s, |f i| ≤ 2 ^ B) (hk : s.card ≤ k) :
    |∏ i ∈ s, f i| ≤ 2 ^ (B * k) := by
  rw [Finset.abs_prod]
  calc
    ∏ i ∈ s, |f i| ≤ ∏ _i ∈ s, (2 : ℤ) ^ B :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) h
    _ = 2 ^ (B * s.card) := by rw [Finset.prod_const, pow_mul]
    _ ≤ 2 ^ (B * k) :=
      pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left B hk)

private theorem card_class_pairs_le [Fintype J] [DecidableEq J'] (chi : J → J') {m : ℕ}
    (hm : ∀ G, (univ.filter fun a => chi a = G).card ≤ m) (G G' : J') :
    (univ.filter fun p : J × J => chi p.1 = G ∧ chi p.2 = G').card ≤ m * m := by
  have h : (univ.filter fun p : J × J => chi p.1 = G ∧ chi p.2 = G') =
      (univ.filter fun a => chi a = G) ×ˢ (univ.filter fun b => chi b = G') := by
    ext p
    simp
  rw [h, Finset.card_product]
  exact Nat.mul_le_mul (hm G) (hm G')

/-- If every contraction class has at most `m` vertices, contraction multiplies the network's
shape parameter by `m`. -/
theorem merge_shaped [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Factored J σ τ) (chi : J → J') (defaultState : σ) (defaultLabel : τ) {P m : ℕ}
    (h : N.Shaped P) (hm : ∀ G, (univ.filter fun a => chi a = G).card ≤ m) :
    (N.merge chi defaultState defaultLabel).Shaped (P * m) := by
  have hc : ∀ G G', (N.merge chi defaultState defaultLabel).c G G' =
      (N.merge chi defaultState defaultLabel).c G' G := by
    intro G G'
    simp only [merge]
    exact Finset.sum_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm])
      (by intro p; simp [and_comm]) (by intro p; simp) (by intro p; simp)
      (by intro p _; exact h.c_symm _ _)
  have hlab : ∀ G G', G < G' →
      ((N.merge chi defaultState defaultLabel).labelSet G G').card ≤
        2 ^ (N.merge chi defaultState defaultLabel).c G G' := by
    intro G G' hlt
    simp only [labelSet, merge, min_eq_left hlt.le, max_eq_right hlt.le]
    rw [Fintype.card_piFinsetOn, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    exact h.card_labelSet _ _ (by rintro he; rw [he, h2] at h1; exact hlt.ne' h1)
  refine ⟨?_, hc, ?_, ?_⟩
  · intro G
    rw [card_merge_S]
    calc
      ∏ a with chi a = G, (N.S a).card ≤ ∏ _a with chi _a = G, 2 ^ P :=
        Finset.prod_le_prod fun a _ => h.card_S a
      _ = 2 ^ (P * (univ.filter fun a => chi a = G).card) := by
        rw [Finset.prod_const, pow_mul]
      _ ≤ 2 ^ (P * m) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left P (hm G))
  · intro G
    simp only [merge]
    calc
      ∑ G' ∈ univ.erase G,
          ∑ p : J × J with chi p.1 = G ∧ chi p.2 = G', N.c p.1 p.2 =
          ∑ p : J × J with chi p.1 = G ∧ chi p.2 ≠ G, N.c p.1 p.2 := by
        rw [← Finset.sum_fiberwise_of_maps_to
          (s := univ.filter fun p : J × J => chi p.1 = G ∧ chi p.2 ≠ G)
          (t := univ.erase G) (g := fun p => chi p.2) (by intro p; simp)]
        refine Finset.sum_congr rfl fun G' hG' => ?_
        have hne : G' ≠ G := by simpa using hG'
        rw [Finset.filter_filter]
        refine Finset.sum_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
        grind
      _ ≤ ∑ p : J × J with chi p.1 = G ∧ p.2 ≠ p.1, N.c p.1 p.2 := by
        refine Finset.sum_le_sum_of_subset fun p hp => ?_
        simp only [mem_filter, mem_univ, true_and] at hp ⊢
        grind
      _ = ∑ a with chi a = G, ∑ b ∈ univ.erase a, N.c a b :=
        Finset.sum_finset_product' _ _ _ (by intro p; simp)
      _ ≤ ∑ _a with chi _a = G, P := Finset.sum_le_sum fun a _ => h.sum_c a
      _ = P * (univ.filter fun a => chi a = G).card := by simp [mul_comm]
      _ ≤ P * m := Nat.mul_le_mul_left P (hm G)
  · intro G G' hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact hlab _ _ hlt
    · rw [labelSet_comm, hc]
      exact hlab _ _ hlt

/-- If every contraction class has at most `m` vertices, contraction multiplies the shape
parameter by `m` and changes the absolute-value exponent from `B` to `B * (m + m * m)`. -/
theorem merge_sized [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Factored J σ τ) (chi : J → J') (defaultState : σ) (defaultLabel : τ)
    {P B m : ℕ} (h : N.Sized P B)
    (hm : ∀ G, (univ.filter fun a => chi a = G).card ≤ m) :
    (N.merge chi defaultState defaultLabel).Sized (P * m) (B * (m + m * m)) := by
  have hmono : (2 : ℤ) ^ (B * (m * m)) ≤ 2 ^ (B * (m + m * m)) :=
    pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left B (Nat.le_add_left _ _))
  refine ⟨merge_shaped N chi defaultState defaultLabel h.toShaped hm, ?_, ?_, ?_⟩
  · intro G z
    simp only [merge]
    rw [abs_mul, mul_add, pow_add]
    refine mul_le_mul
      (abs_prod_le_two_pow _ _ (fun a _ => h.abs_W a _) (hm G)) ?_ (abs_nonneg _)
      (pow_nonneg (by norm_num) _)
    refine abs_prod_le_two_pow _ _ (fun p hp => h.abs_interaction _ _ _ _ ?_)
      ((Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.subset_univ _))).trans
          (card_class_pairs_le chi hm G G))
    have hp' : p.1 < p.2 := by simpa [orderedPairs] using (Finset.mem_filter.1 hp).1
    exact hp'.ne
  · intro G G' z t
    simp only [merge]
    exact (abs_prod_le_two_pow _ _ (fun p _ => h.abs_f _ _ _ _)
      (card_class_pairs_le chi hm G G')).trans hmono
  · intro G G' z z' hne
    rw [merge_interaction _ _ _ _ hne]
    refine (abs_prod_le_two_pow _ _ (fun p hp => h.abs_interaction _ _ _ _ ?_)
      (card_class_pairs_le chi hm G G')).trans hmono
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    rintro he
    rw [he, h2] at h1
    exact hne h1.symm

end TensorNetwork.Factored
