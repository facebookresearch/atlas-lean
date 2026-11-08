/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0

Modified for Atlas: ported exact value-preserving contraction to the shared factored
tensor-network and default-padded finite-product APIs.
-/
module

public import MathlibExt.Combinatorics.TensorNetwork.Basic

/-! # Contraction of factored tensor networks

Merging a finite network along an arbitrary map groups vertices into target classes. Empty target
classes are represented by their unique default-padded state. The construction preserves the
integer-valued network value without a surjectivity or shape hypothesis.

Adapted from `eth/proof/networks/Groundwork/Net/Defs.lean` and the merging section of
`eth/proof/networks/Groundwork/Net/Net.lean` at
https://github.com/anthropics/formal-math/tree/16a5ce41304fcdaea4e0be7c132e1c361dc26da5.

Attribution notice: eth, a Lean 4 formalization of "A 2^o(n) Time Algorithm for 3-SAT".
Copyright 2026 Anthropic, PBC. Licensed under Apache 2.0 (see LICENSE).
-/

@[expose] public section

namespace TensorNetwork.Factored

open Finset

variable {J J' σ τ : Type*}

/-- Merge vertices along `χ`, retaining source states and labels on their classes and padding all
other coordinates with the supplied defaults. -/
def merge [Fintype J] [LinearOrder J] [LinearOrder J'] (N : Factored J σ τ)
    (χ : J → J') (defaultState : σ) (defaultLabel : τ) :
    Factored J' (J → σ) (J × J → τ) where
  S G := Fintype.piFinsetOn (fun a => χ a = G) N.S defaultState
  W G z :=
    (∏ a with χ a = G, N.W a (z a)) *
      ∏ p ∈ orderedPairs J with χ p.1 = G ∧ χ p.2 = G,
        N.interaction p.1 p.2 (z p.1) (z p.2)
  Θ G G' := Fintype.piFinsetOn (fun p : J × J => χ p.1 = G ∧ χ p.2 = G')
    (fun p => N.labelSet p.1 p.2) defaultLabel
  f G G' z t :=
    ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G',
      N.f p.1 p.2 (z p.1) (t (if G < G' then p else p.swap))
  c G G' := ∑ p : J × J with χ p.1 = G ∧ χ p.2 = G', N.c p.1 p.2

/-- The interaction of two increasingly ordered classes is the product of all source interactions
crossing between them. -/
theorem merge_interaction_lt [Fintype J] [LinearOrder J] [LinearOrder J']
    (N : Factored J σ τ) (χ : J → J') (defaultState : σ) (defaultLabel : τ)
    {G G' : J'} (h : G < G') (z z' : J → σ) :
    (N.merge χ defaultState defaultLabel).interaction G G' z z' =
      ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G',
        N.interaction p.1 p.2 (z p.1) (z' p.2) := by
  have h2 : ∀ t : J × J → τ,
      ∏ q : J × J with χ q.1 = G' ∧ χ q.2 = G,
        N.f q.1 q.2 (z' q.1) (t q.swap) =
      ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G',
        N.f p.2 p.1 (z' p.2) (t p) := fun t =>
    Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm])
      (by intro p; simp [and_comm]) (by intro p; simp) (by intro p; simp)
      (by intro p; simp)
  simp only [interaction, labelSet, merge, h.le, min_eq_left, max_eq_right, h, ite_true,
    h.not_gt, ite_false, h2]
  rw [← Fintype.prod_sum_eq_sum_piFinsetOn_mul]

/-- The interaction of two distinct classes is the product of all source interactions crossing
between them, oriented from the first class to the second. -/
theorem merge_interaction [Fintype J] [LinearOrder J] [LinearOrder J']
    (N : Factored J σ τ) (χ : J → J') (defaultState : σ) (defaultLabel : τ)
    {G G' : J'} (h : G ≠ G') (z z' : J → σ) :
    (N.merge χ defaultState defaultLabel).interaction G G' z z' =
      ∏ p : J × J with χ p.1 = G ∧ χ p.2 = G',
        N.interaction p.1 p.2 (z p.1) (z' p.2) := by
  rcases lt_or_gt_of_ne h with h | h
  · exact merge_interaction_lt N χ defaultState defaultLabel h z z'
  · rw [interaction_comm, merge_interaction_lt N χ defaultState defaultLabel h z' z]
    exact Finset.prod_nbij' Prod.swap Prod.swap (by intro p; simp [and_comm])
      (by intro p; simp [and_comm]) (by intro p; simp) (by intro p; simp)
      (by intro p _; simp [interaction_comm])

private theorem prod_orient [Fintype J] [LinearOrder J] [LinearOrder J']
    (χ : J → J') (F : J × J → ℤ) (hF : ∀ p, F p.swap = F p) :
    ∏ p : J × J with χ p.1 < χ p.2, F p =
      ∏ p ∈ orderedPairs J with χ p.1 ≠ χ p.2, F p := by
  refine Finset.prod_nbij' (fun p => if p.1 < p.2 then p else p.swap)
    (fun p => if χ p.1 < χ p.2 then p else p.swap) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp only [orderedPairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs with hab <;> simp only [Prod.swap_prod_mk] <;> grind
  · rintro ⟨a, b⟩ h
    simp only [orderedPairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs with hab <;> simp only [Prod.swap_prod_mk] <;> grind
  · rintro ⟨a, b⟩ h
    simp only [mem_filter, mem_univ, true_and] at h ⊢
    split_ifs <;> simp_all
    grind
  · rintro ⟨a, b⟩ h
    simp only [orderedPairs, mem_filter, mem_univ, true_and] at h ⊢
    split_ifs <;> simp_all
    grind
  · rintro p _
    split_ifs
    · rfl
    · exact (hF p).symm

private theorem merge_summand [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Factored J σ τ) (χ : J → J') (defaultState : σ) (defaultLabel : τ)
    (z : J → σ) :
    (∏ a, N.W a (z a)) *
        ∏ p ∈ orderedPairs J, N.interaction p.1 p.2 (z p.1) (z p.2) =
      (∏ G, (N.merge χ defaultState defaultLabel).W G
        (fun a => if χ a = G then z a else defaultState)) *
      ∏ q ∈ orderedPairs J',
        (N.merge χ defaultState defaultLabel).interaction q.1 q.2
          (fun a => if χ a = q.1 then z a else defaultState)
          (fun a => if χ a = q.2 then z a else defaultState) := by
  set F : J × J → ℤ := fun p => N.interaction p.1 p.2 (z p.1) (z p.2) with hFdef
  have hW : ∀ G,
      (N.merge χ defaultState defaultLabel).W G
          (fun a => if χ a = G then z a else defaultState) =
        (∏ a with χ a = G, N.W a (z a)) *
          ∏ p ∈ orderedPairs J with χ p.1 = G ∧ χ p.2 = G, F p := by
    intro G
    simp only [merge]
    congr 1
    · refine Finset.prod_congr rfl fun a ha => ?_
      simp [(Finset.mem_filter.1 ha).2]
    · refine Finset.prod_congr rfl fun p hp => ?_
      obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
      simp [F, h1, h2]
  have hInteraction : ∀ q ∈ orderedPairs J',
      (N.merge χ defaultState defaultLabel).interaction q.1 q.2
          (fun a => if χ a = q.1 then z a else defaultState)
          (fun a => if χ a = q.2 then z a else defaultState) =
        ∏ p : J × J with χ p.1 = q.1 ∧ χ p.2 = q.2, F p := by
    intro q hq
    have hq' : q.1 < q.2 := by simpa [orderedPairs] using hq
    rw [merge_interaction_lt N χ defaultState defaultLabel hq']
    refine Finset.prod_congr rfl fun p hp => ?_
    obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
    simp [F, h1, h2]
  rw [Finset.prod_congr rfl hInteraction]
  simp only [hW, Finset.prod_mul_distrib]
  rw [Finset.prod_fiberwise univ χ (fun a => N.W a (z a))]
  have h1 :
      ∏ G, ∏ p ∈ orderedPairs J with χ p.1 = G ∧ χ p.2 = G, F p =
        ∏ p ∈ orderedPairs J with χ p.1 = χ p.2, F p := by
    rw [← Finset.prod_fiberwise
      ((orderedPairs J).filter fun p => χ p.1 = χ p.2) (fun p => χ p.1)]
    refine Finset.prod_congr rfl fun G _ => ?_
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
    grind
  have h2 :
      ∏ q ∈ orderedPairs J',
          ∏ p : J × J with χ p.1 = q.1 ∧ χ p.2 = q.2, F p =
        ∏ p : J × J with χ p.1 < χ p.2, F p := by
    rw [← Finset.prod_fiberwise_of_maps_to
      (s := univ.filter fun p : J × J => χ p.1 < χ p.2) (t := orderedPairs J')
      (g := fun p => (χ p.1, χ p.2)) (by intro p; simp [orderedPairs])]
    refine Finset.prod_congr rfl fun q hq => ?_
    have hq' : q.1 < q.2 := by simpa [orderedPairs] using hq
    rw [Finset.filter_filter]
    refine Finset.prod_congr (Finset.filter_congr fun p _ => ?_) fun _ _ => rfl
    rw [Prod.ext_iff]
    grind
  rw [h1, h2, prod_orient χ F (fun p => N.interaction_comm _ _ _ _), mul_assoc,
    Finset.prod_filter_mul_prod_filter_not]

/-- Merging along any map preserves the exact integer-valued network value. -/
theorem value_merge [Fintype J] [LinearOrder J] [Fintype J'] [LinearOrder J']
    (N : Factored J σ τ) (χ : J → J') (defaultState : σ) (defaultLabel : τ) :
    (N.merge χ defaultState defaultLabel).value = N.value := by
  unfold value
  symm
  refine Finset.sum_nbij' (fun z G a => if χ a = G then z a else defaultState)
    (fun Z a => Z (χ a) a) ?_ ?_ ?_ ?_ ?_
  · intro z hz
    rw [Fintype.mem_piFinset] at hz ⊢
    intro G
    exact (Fintype.mem_piFinsetOn _ _ _ _).2 fun a =>
      ⟨fun h => by simp [h, hz a], fun h => by simp [h]⟩
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ ⊢
    intro a
    exact ((Fintype.mem_piFinsetOn _ _ _ _).1 (hZ (χ a)) a).1 rfl
  · intro z _
    funext a
    simp
  · intro Z hZ
    rw [Fintype.mem_piFinset] at hZ
    funext G a
    by_cases h : χ a = G
    · subst h
      simp
    · simp [h, ((Fintype.mem_piFinsetOn _ _ _ _).1 (hZ G) a).2 h]
  · intro z _
    exact merge_summand N χ defaultState defaultLabel z

/-- The number of merged states is the product of the state-set sizes in the class. -/
theorem card_merge_S [Fintype J] [LinearOrder J] [LinearOrder J']
    (N : Factored J σ τ) (χ : J → J') (defaultState : σ) (defaultLabel : τ)
    (G : J') :
    ((N.merge χ defaultState defaultLabel).S G).card =
      ∏ a with χ a = G, (N.S a).card :=
  Fintype.card_piFinsetOn _ _ _

end TensorNetwork.Factored
