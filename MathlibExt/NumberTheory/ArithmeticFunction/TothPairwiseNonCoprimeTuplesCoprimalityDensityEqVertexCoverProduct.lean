/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ArithmeticFunction.TothPairwiseNonCoprimeTuples
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Vertex-cover Euler product for the coprimality density

This module proves `MetaMathlibExt.coprimalityDensity_eq_vertex_cover_product`:
for a graph with edge set `E` and a vertex cover `J`, the coprimality density
equals the Euler product over primes of the independent-set sums over `J`.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`).
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- Binomial expansion of `(a + b) ^ s.card` as a sum over the powerset of `s`. -/
private theorem add_pow_card {α : Type*} (a b : ℝ) (s : Finset α) :
    (a + b) ^ s.card = ∑ t ∈ s.powerset, a ^ t.card * b ^ (s.card - t.card) := by
  classical
  have h := Finset.prod_add (fun _ : α => a) (fun _ : α => b) s
  simp only [Finset.prod_const] at h
  rw [h]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [Finset.card_sdiff_of_subset (Finset.mem_powerset.mp ht)]

open scoped Classical in
/-- The alternating sum over a powerset detects the empty set. -/
private theorem sum_powerset_neg_one_pow {α : Type*} (s : Finset α) :
    ∑ t ∈ s.powerset, (-1 : ℝ) ^ t.card = if s = ∅ then 1 else 0 := by
  have h := add_pow_card (-1 : ℝ) 1 s
  simp only [neg_add_cancel, one_pow, mul_one] at h
  rw [← h]
  by_cases hs : s = ∅
  · subst hs
    simp
  · rw [ite_eq_right hs, zero_pow (mt Finset.card_eq_zero.mp hs)]

/-- The binomial distribution over a powerset sums to one. -/
private theorem sum_powerset_pow_mul_pow_sub (t : ℝ) {α : Type*}
    (s : Finset α) :
    ∑ u ∈ s.powerset, t ^ u.card * (1 - t) ^ (s.card - u.card) = 1 := by
  classical
  have h := add_pow_card t (1 - t) s
  have hadd : t + (1 - t) = 1 := by ring
  rw [hadd, one_pow] at h
  exact h.symm

/-- Expansion of `(1 - t) ^ s.card` over the powerset of `s`. -/
private theorem one_sub_pow_eq (t : ℝ) {α : Type*} (s : Finset α) :
    (1 - t) ^ s.card = ∑ u ∈ s.powerset, (-1 : ℝ) ^ u.card * t ^ u.card := by
  classical
  have h := add_pow_card (-t) 1 s
  have hneg : -t + 1 = 1 - t := by ring
  rw [hneg] at h
  rw [h]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [neg_pow, one_pow, mul_one]

/-- Each endpoint of an edge of `F` lies in the vertex set of `F`. -/
private theorem mem_vertexSet_of_mem {k : ℕ} (F : Finset (Fin k × Fin k))
    {e : Fin k × Fin k} (he : e ∈ F) :
    e.1 ∈ univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ∧
      e.2 ∈ univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) := by
  refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, Or.inl rfl⟩,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, Or.inr rfl⟩⟩

/-- The vertex set of `F` lies in `S` iff every edge of `F` has both endpoints in `S`. -/
private theorem vertexSet_subset_iff {k : ℕ} (F : Finset (Fin k × Fin k))
    (S : Finset (Fin k)) :
    univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S ↔
      ∀ e ∈ F, e.1 ∈ S ∧ e.2 ∈ S := by
  constructor
  · intro h e he
    exact ⟨h (mem_vertexSet_of_mem F he).1, h (mem_vertexSet_of_mem F he).2⟩
  · intro h i hi
    obtain ⟨-, e, he, heq | heq⟩ := Finset.mem_filter.mp hi
    · rw [← heq]
      exact (h e he).1
    · rw [← heq]
      exact (h e he).2

open scoped Classical in
/-- The alternating sum over vertex sets between `W` and `V` detects `W = V`. -/
private theorem sum_slice_neg_one_pow {k : ℕ} (V W : Finset (Fin k)) (hW : W ⊆ V) :
    ∑ S ∈ V.powerset.filter (fun S => W ⊆ S), (-1 : ℝ) ^ (V.card - S.card)
      = if W = V then 1 else 0 := by
  classical
  have hcancel : ∀ S : Finset (Fin k), S ⊆ V → S = V \ (V \ S) := by
    intro S hS
    ext x
    simp only [Finset.mem_sdiff]
    by_cases hxS : x ∈ S
    · simp [hxS, hS hxS]
    · simp [hxS]
  have hbij : ∑ S ∈ V.powerset.filter (fun S => W ⊆ S), (-1 : ℝ) ^ (V.card - S.card)
      = ∑ T ∈ (V \ W).powerset, (-1 : ℝ) ^ T.card :=
    Finset.sum_bij (fun S _ => V \ S)
      (fun S hS => by
        rw [Finset.mem_filter, Finset.mem_powerset] at hS
        rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hx.1, fun hxW => hx.2 (hS.2 hxW)⟩)
      (fun S₁ hS₁ S₂ hS₂ heq => by
        rw [Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
        rw [hcancel S₁ hS₁.1, hcancel S₂ hS₂.1, heq])
      (fun T hT => by
        rw [Finset.mem_powerset] at hT
        refine ⟨V \ T, ?_, ?_⟩
        · rw [Finset.mem_filter, Finset.mem_powerset]
          refine ⟨Finset.sdiff_subset, fun w hw => ?_⟩
          rw [Finset.mem_sdiff]
          exact ⟨hW hw, fun hwT => (Finset.mem_sdiff.mp (hT hwT)).2 hw⟩
        · exact (hcancel T (fun x hx => (Finset.mem_sdiff.mp (hT hx)).1)).symm)
      (fun S hS => by
        rw [Finset.mem_filter, Finset.mem_powerset] at hS
        rw [Finset.card_sdiff_of_subset hS.1])
  rw [hbij, sum_powerset_neg_one_pow]
  have heq : V \ W = ∅ ↔ W = V :=
    ⟨fun h => Subset.antisymm hW (Finset.sdiff_eq_empty_iff_subset.mp h),
      fun h => by rw [h, Finset.sdiff_self]⟩
  by_cases hWV : W = V
  · subst hWV
    simp
  · have hne : ¬(V \ W = ∅) := fun h => hWV (heq.mp h)
    rw [ite_eq_right hne, ite_eq_right hWV]

open scoped Classical in
/-- For a fixed vertex set `V`, the alternating edge-subset sum over the `F` with
vertex set `V` equals the alternating sum over independent subsets of `V`. -/
private theorem sum_edge_vertexSet_eq_sum_indep_slice {k : ℕ}
    (E : Finset (Fin k × Fin k)) (V : Finset (Fin k)) :
    ∑ F ∈ E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card =
      ∑ S ∈ V.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        (-1 : ℝ) ^ (V.card - S.card) := by
  classical
  have hRHS : ∑ S ∈ V.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        (-1 : ℝ) ^ (V.card - S.card)
      = ∑ S ∈ V.powerset, ∑ F ∈ (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).powerset,
        (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    have hind : (∑ F ∈ (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).powerset,
          (-1 : ℝ) ^ F.card)
        = if (∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)) then 1 else 0 := by
      rw [sum_powerset_neg_one_pow]
      by_cases hE : (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S) = ∅
      · have hI : ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S) :=
          Finset.filter_eq_empty_iff.mp hE
        rw [ite_eq_left hE, ite_eq_left hI]
      · have hI : ¬(∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)) :=
          fun h => hE (Finset.filter_eq_empty_iff.mpr h)
        rw [ite_eq_right hE, ite_eq_right hI]
    rw [← Finset.sum_mul, hind]
    by_cases hS : ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)
    · rw [ite_eq_left hS, ite_eq_left hS, one_mul]
    · rw [ite_eq_right hS, ite_eq_right hS, zero_mul]
  have hExtend : ∀ S ∈ V.powerset,
      (∑ F ∈ (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).powerset,
        (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card))
      = ∑ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset,
        (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S
          then (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card) else 0) := by
    intro S hS
    rw [Finset.mem_powerset] at hS
    have hguard : ∀ F ∈ (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).powerset,
        (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card)
        = (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S
          then (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card) else 0) := by
      intro F hF
      rw [Finset.mem_powerset] at hF
      have hVS : univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S :=
        (vertexSet_subset_iff F S).mpr (fun e he =>
          ⟨(Finset.mem_filter.mp (hF he)).2.1, (Finset.mem_filter.mp (hF he)).2.2⟩)
      rw [ite_eq_left hVS]
    trans ∑ F ∈ (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).powerset,
      (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S
        then (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card) else 0)
    · exact Finset.sum_congr rfl hguard
    · apply Finset.sum_subset
      · rw [Finset.powerset_mono]
        intro e he
        rw [Finset.mem_filter] at he ⊢
        exact ⟨he.1, hS he.2.1, hS he.2.2⟩
      · intro F hF hFn
        rw [Finset.mem_powerset] at hF hFn
        have hsub : ¬(univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i)
            ⊆ S) := by
          intro hVS
          apply hFn
          intro e he
          rw [Finset.mem_filter]
          have heE := (Finset.mem_filter.mp (hF he)).1
          have hends := (vertexSet_subset_iff F S).mp hVS e he
          exact ⟨heE, hends.1, hends.2⟩
        rw [ite_eq_right hsub]
  have hStep2 : (∑ S ∈ V.powerset, ∑ F ∈ (E.filter fun e => e.1 ∈ S ∧ e.2 ∈ S).powerset,
        (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card))
      = ∑ S ∈ V.powerset, ∑ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset,
        (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S
          then (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card) else 0) :=
    Finset.sum_congr rfl fun S hS => hExtend S hS
  have hInner : ∀ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset,
      (∑ S ∈ V.powerset, (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S
        then (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card) else 0))
      = (-1 : ℝ) ^ F.card *
        (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V then 1 else 0) := by
    intro F hF
    have hWV : univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ V := by
      rw [Finset.mem_powerset] at hF
      rw [vertexSet_subset_iff]
      intro e he
      exact ⟨(Finset.mem_filter.mp (hF he)).2.1, (Finset.mem_filter.mp (hF he)).2.2⟩
    rw [← Finset.sum_filter, ← Finset.mul_sum, sum_slice_neg_one_pow V _ hWV]
  have hStep5 : (∑ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset, ∑ S ∈ V.powerset,
        (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) ⊆ S
          then (-1 : ℝ) ^ F.card * (-1 : ℝ) ^ (V.card - S.card) else 0))
      = ∑ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset, (-1 : ℝ) ^ F.card *
        (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V then 1 else 0) :=
    Finset.sum_congr rfl fun F hF => hInner F hF
  have hIte : ∀ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset,
      (-1 : ℝ) ^ F.card *
          (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V then 1 else 0)
      = (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V
        then (-1 : ℝ) ^ F.card else 0) := by
    intro F _
    rw [mul_ite, mul_one, mul_zero]
  have hStep6 : (∑ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset, (-1 : ℝ) ^ F.card *
        (if univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V then 1 else 0))
      = ∑ F ∈ (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl hIte
  have hFib : (E.filter fun e => e.1 ∈ V ∧ e.2 ∈ V).powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V)
      = E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V) := by
    ext F
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro h
      exact ⟨fun e he => (Finset.mem_filter.mp (h.1 he)).1, h.2⟩
    · intro h
      refine ⟨fun e he => Finset.mem_filter.mpr ⟨h.1 he, ?_, ?_⟩, h.2⟩
      · rw [← h.2]
        exact (mem_vertexSet_of_mem F he).1
      · rw [← h.2]
        exact (mem_vertexSet_of_mem F he).2
  rw [hRHS, hStep2, Finset.sum_comm, hStep5, hStep6, hFib]

/-- Reindexing a sum over subsets of the complement by adjoining `S`. -/
private theorem sum_compl_powerset_eq_sum_superset {k : ℕ} (S : Finset (Fin k))
    (hS : S ⊆ univ) (t : ℝ) :
    (∑ T ∈ (univ \ S).powerset, (-1 : ℝ) ^ T.card * t ^ (S.card + T.card))
    = ∑ V ∈ univ.powerset.filter (fun V => S ⊆ V),
      (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card := by
  have hcancel : ∀ T : Finset (Fin k), T ⊆ univ \ S → T = (S ∪ T) \ S := by
    intro T hT
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · intro hxT
      exact ⟨Or.inr hxT, fun hxS => (Finset.mem_sdiff.mp (hT hxT)).2 hxS⟩
    · intro h
      rcases h.1 with hxS | hxT
      · exact absurd hxS h.2
      · exact hxT
  refine Finset.sum_bij (fun T _ => S ∪ T)
    (fun T hT => by
      rw [Finset.mem_powerset] at hT
      rw [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro x hx
        rw [Finset.mem_union] at hx
        rcases hx with hxS | hxT
        · exact hS hxS
        · exact (Finset.mem_sdiff.mp (hT hxT)).1
      · exact Finset.subset_union_left)
    (fun T₁ hT₁ T₂ hT₂ heq => by
      rw [Finset.mem_powerset] at hT₁ hT₂
      rw [hcancel T₁ hT₁, hcancel T₂ hT₂, heq])
    (fun V hV => by
      rw [Finset.mem_filter, Finset.mem_powerset] at hV
      refine ⟨V \ S, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro x hx
        rw [Finset.mem_sdiff] at hx ⊢
        exact ⟨hV.1 hx.1, hx.2⟩
      · rw [Finset.union_comm, Finset.sdiff_union_of_subset hV.2])
    (fun T hT => by
      rw [Finset.mem_powerset] at hT
      have hdisj : Disjoint S T := by
        rw [Finset.disjoint_left]
        intro x hxS hxT
        exact (Finset.mem_sdiff.mp (hT hxT)).2 hxS
      have hcard : (S ∪ T).card = S.card + T.card :=
        Finset.card_union_of_disjoint hdisj
      have hexp : S.card + T.card - S.card = T.card := by omega
      rw [hcard, hexp])

/-- The edge-subset sum equals the independent-set sum for every weight `t`. -/
private theorem sum_edge_subset_eq_sum_indep {k : ℕ} (E : Finset (Fin k × Fin k))
    (t : ℝ) :
    ∑ F ∈ E.powerset, (-1 : ℝ) ^ F.card *
        t ^ (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card =
      ∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        t ^ S.card * (1 - t) ^ (univ \ S).card := by
  have hExpand : ∀ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
      t ^ S.card * (1 - t) ^ (univ \ S).card
      = ∑ T ∈ (univ \ S).powerset, (-1 : ℝ) ^ T.card * t ^ (S.card + T.card) := by
    intro S _
    rw [one_sub_pow_eq t (univ \ S), Finset.mul_sum]
    refine Finset.sum_congr rfl fun T _ => ?_
    rw [pow_add]
    ring
  have hRHS : (∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        t ^ S.card * (1 - t) ^ (univ \ S).card)
      = ∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        ∑ T ∈ (univ \ S).powerset, (-1 : ℝ) ^ T.card * t ^ (S.card + T.card) :=
    Finset.sum_congr rfl fun S hS => hExpand S hS
  rw [hRHS]
  have hRe : ∀ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
      (∑ T ∈ (univ \ S).powerset, (-1 : ℝ) ^ T.card * t ^ (S.card + T.card))
      = ∑ V ∈ univ.powerset.filter (fun V => S ⊆ V),
        (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS
    exact sum_compl_powerset_eq_sum_superset S hS.1 t
  have hRHS2 : (∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        ∑ T ∈ (univ \ S).powerset, (-1 : ℝ) ^ T.card * t ^ (S.card + T.card))
      = ∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        ∑ V ∈ univ.powerset.filter (fun V => S ⊆ V),
          (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card :=
    Finset.sum_congr rfl fun S hS => hRe S hS
  rw [hRHS2]
  have hSwap : (∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        ∑ V ∈ univ.powerset.filter (fun V => S ⊆ V),
          (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card)
      = ∑ V ∈ univ.powerset, ∑ S ∈ V.powerset.filter
        (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card := by
    have hIf : ∀ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        (∑ V ∈ univ.powerset.filter (fun V => S ⊆ V),
          (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card)
        = ∑ V ∈ univ.powerset,
          (if S ⊆ V then (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card else 0) := by
      intro S _
      rw [Finset.sum_filter]
    trans ∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
      ∑ V ∈ univ.powerset,
        (if S ⊆ V then (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card else 0)
    · exact Finset.sum_congr rfl hIf
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun V hV => ?_
      rw [Finset.mem_powerset] at hV
      rw [← Finset.sum_filter]
      congr 1
      ext S
      simp only [Finset.mem_filter, Finset.mem_powerset]
      constructor
      · intro h
        exact ⟨h.2, h.1.2⟩
      · intro h
        exact ⟨⟨fun x hx => hV (h.1 hx), h.2⟩, h.1⟩
  rw [hSwap]
  have hPerV : ∀ V ∈ univ.powerset,
      (∑ S ∈ V.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card)
      = t ^ V.card * ∑ F ∈ E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card := by
    intro V _
    rw [← Finset.sum_mul, sum_edge_vertexSet_eq_sum_indep_slice E V]
    exact mul_comm _ _
  have hRHS3 : (∑ V ∈ univ.powerset, ∑ S ∈ V.powerset.filter
        (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        (-1 : ℝ) ^ (V.card - S.card) * t ^ V.card)
      = ∑ V ∈ univ.powerset, t ^ V.card * ∑ F ∈ E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card :=
    Finset.sum_congr rfl fun V hV => hPerV V hV
  rw [hRHS3]
  have hDist : ∀ V ∈ univ.powerset,
      t ^ V.card * ∑ F ∈ E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card
      = ∑ F ∈ E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card *
          t ^ (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card := by
    intro V _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun F hF => ?_
    rw [Finset.mem_filter] at hF
    rw [hF.2]
    exact mul_comm _ _
  have hRHS4 : (∑ V ∈ univ.powerset, t ^ V.card * ∑ F ∈ E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card)
      = ∑ V ∈ univ.powerset, ∑ F ∈ E.powerset.filter
        (fun F => univ.filter (fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i) = V),
        (-1 : ℝ) ^ F.card *
          t ^ (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card :=
    Finset.sum_congr rfl fun V hV => hDist V hV
  rw [hRHS4]
  exact (Finset.sum_fiberwise_of_maps_to
    (fun F _ => Finset.mem_powerset.mpr (Finset.filter_subset _ _)) _).symm

/-- The fiber over an independent `L ⊆ J` sums to the vertex-cover term. -/
private theorem fiber_sum_eq_vertex_cover_term {k : ℕ} (E : Finset (Fin k × Fin k))
    (J L : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J)
    (hLJ : L ⊆ J) (hLindep : ∀ e ∈ E, ¬(e.1 ∈ L ∧ e.2 ∈ L)) (t : ℝ) :
    (∑ S ∈ (univ.powerset.filter
        (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S))).filter (fun S => S ∩ J = L),
      t ^ S.card * (1 - t) ^ (univ \ S).card)
    = t ^ L.card * (1 - t) ^
      ((J \ L).card +
        ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card) := by
  have hW : J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E)
      = J ∪ ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  have hWdisj : Disjoint J
      ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J) := by
    rw [Finset.disjoint_left]
    intro x hxJ hxNJ
    exact (Finset.mem_sdiff.mp hxNJ).2 hxJ
  have hWcard : (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E)).card
      = J.card + ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card := by
    rw [hW, Finset.card_union_of_disjoint hWdisj]
  have hJcard : J.card = L.card + (J \ L).card := by
    have h := Finset.card_sdiff_of_subset hLJ
    have hle := Finset.card_le_card hLJ
    omega
  have hUcard' : (univ \ (J ∪
      (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).card
      = univ.card - (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E)).card :=
    Finset.card_sdiff_of_subset (Finset.subset_univ _)
  have hUniv : (univ : Finset (Fin k)).card = L.card + (J \ L).card +
      ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card +
      (univ \ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).card := by
    have hle := Finset.card_le_card
      (Finset.subset_univ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E)))
    omega
  have hFiberSub : ∀ S ∈ (univ.powerset.filter
      (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S))).filter (fun S => S ∩ J = L),
      S \ J ⊆ univ \ (J ∪
        (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E)) := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hS
    intro x hx
    rw [Finset.mem_sdiff] at hx
    rw [Finset.mem_sdiff, Finset.mem_union]
    refine ⟨hS.1.1 hx.1, ?_⟩
    intro hJN
    rcases hJN with hxJ | hxN
    · exact hx.2 hxJ
    · rw [Finset.mem_filter] at hxN
      obtain ⟨-, l, hlL, hor⟩ := hxN
      rw [← hS.2] at hlL
      have hlS := (Finset.mem_inter.mp hlL).1
      rcases hor with hor | hor
      · exact hS.1.2 (l, x) hor ⟨hlS, hx.1⟩
      · exact hS.1.2 (x, l) hor ⟨hx.1, hlS⟩
  have hbij : (∑ S ∈ (univ.powerset.filter
        (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S))).filter (fun S => S ∩ J = L),
      t ^ S.card * (1 - t) ^ (univ \ S).card)
      = ∑ T ∈ (univ \ (J ∪
        (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).powerset,
        t ^ (L.card + T.card) * (1 - t) ^ ((J \ L).card +
          ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card +
          ((univ \ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).card -
            T.card)) :=
    Finset.sum_nbij' (fun S => S \ J) (fun T => L ∪ T)
      (fun S hS => Finset.mem_powerset.mpr (hFiberSub S hS))
      (fun T hT => by
        rw [Finset.mem_powerset] at hT
        have hTsub : ∀ x ∈ T, x ∈ univ ∧ x ∉ J ∧
            x ∉ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) := by
          intro x hxT
          have hxU := hT hxT
          rw [Finset.mem_sdiff, Finset.mem_union] at hxU
          exact ⟨hxU.1, fun hxJ => hxU.2 (Or.inl hxJ), fun hxN => hxU.2 (Or.inr hxN)⟩
        change L ∪ T ∈ (univ.powerset.filter _).filter _
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · intro x hx
          rw [Finset.mem_union] at hx
          rcases hx with hxL | hxT
          · exact Finset.mem_univ x
          · exact (hTsub x hxT).1
        · intro e he hcon
          simp only [Finset.mem_union] at hcon
          obtain ⟨h1, h2⟩ := hcon
          rcases h1 with he1L | he1T <;> rcases h2 with he2L | he2T
          · exact hLindep e he ⟨he1L, he2L⟩
          · have he2N : e.2 ∈ (univ.filter
                fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.1, he1L, Or.inl he⟩
            exact (hTsub e.2 he2T).2.2 he2N
          · have he1N : e.1 ∈ (univ.filter
                fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) :=
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, e.2, he2L, Or.inr he⟩
            exact (hTsub e.1 he1T).2.2 he1N
          · rcases hJ e he with hJ1 | hJ2
            · exact (hTsub e.1 he1T).2.1 hJ1
            · exact (hTsub e.2 he2T).2.1 hJ2
        · ext x
          simp only [Finset.mem_inter, Finset.mem_union]
          constructor
          · intro h
            rcases h.1 with hxL | hxT
            · exact hxL
            · exact absurd h.2 (hTsub x hxT).2.1
          · intro hxL
            exact ⟨Or.inl hxL, hLJ hxL⟩)
      (fun S hS => by
        rw [Finset.mem_filter] at hS
        have hSL := hS.2
        change L ∪ (S \ J) = S
        rw [Finset.union_comm, ← hSL]
        exact Finset.sdiff_union_inter _ _)
      (fun T hT => by
        rw [Finset.mem_powerset] at hT
        have hTJ : ∀ x ∈ T, x ∉ J := by
          intro x hxT
          have hxU := hT hxT
          rw [Finset.mem_sdiff, Finset.mem_union] at hxU
          exact fun hxJ => hxU.2 (Or.inl hxJ)
        change (L ∪ T) \ J = T
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        constructor
        · intro h
          rcases h.1 with hxL | hxT
          · exact absurd (hLJ hxL) h.2
          · exact hxT
        · intro hxT
          exact ⟨Or.inr hxT, hTJ x hxT⟩)
      (fun S hS => by
        have hSJU := hFiberSub S hS
        rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset] at hS
        have hSeq : S = L ∪ (S \ J) := by
          rw [Finset.union_comm, ← hS.2]
          exact (Finset.sdiff_union_inter _ _).symm
        have hSdisj : Disjoint L (S \ J) := by
          rw [Finset.disjoint_left]
          intro x hxL hxSJ
          exact (Finset.mem_sdiff.mp hxSJ).2 (hLJ hxL)
        have hScard : S.card = L.card + (S \ J).card := by
          have h := Finset.card_union_of_disjoint hSdisj
          rw [← hSeq] at h
          exact h
        have hSdiff : (univ \ S).card = univ.card - S.card :=
          Finset.card_sdiff_of_subset hS.1.1
        have hleS := Finset.card_le_card hS.1.1
        have hleT := Finset.card_le_card hSJU
        have hUcard : (univ \ S).card = (J \ L).card +
            ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card +
            ((univ \ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).card -
              (S \ J).card) := by
          omega
        change t ^ S.card * (1 - t) ^ (univ \ S).card = _
        rw [hScard, hUcard])
  rw [hbij]
  have hterm : ∀ T ∈ (univ \ (J ∪
      (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).powerset,
      t ^ (L.card + T.card) * (1 - t) ^ ((J \ L).card +
        ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card +
        ((univ \ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).card -
          T.card))
      = (t ^ L.card * (1 - t) ^ ((J \ L).card +
        ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card)) *
        (t ^ T.card * (1 - t) ^
          ((univ \ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).card -
            T.card)) := by
    intro T _
    rw [pow_add, pow_add]
    ring
  trans (t ^ L.card * (1 - t) ^ ((J \ L).card +
      ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card)) *
    ∑ T ∈ (univ \ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).powerset,
      t ^ T.card * (1 - t) ^
        ((univ \ (J ∪ (univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E))).card -
          T.card)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  · rw [sum_powerset_pow_mul_pow_sub, mul_one]

/-- Grouping the independent-set sum by intersection with the vertex cover `J`. -/
private theorem sum_indep_eq_sum_vertex_cover {k : ℕ} (E : Finset (Fin k × Fin k))
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J) (t : ℝ) :
    ∑ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
        t ^ S.card * (1 - t) ^ (univ \ S).card =
      ∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬(e.1 ∈ L ∧ e.2 ∈ L)),
        t ^ L.card * (1 - t) ^
          ((J \ L).card +
            ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card) := by
  have hmaps : ∀ S ∈ univ.powerset.filter (fun S => ∀ e ∈ E, ¬(e.1 ∈ S ∧ e.2 ∈ S)),
      S ∩ J ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬(e.1 ∈ L ∧ e.2 ∈ L)) := by
    intro S hS
    rw [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    refine ⟨Finset.inter_subset_right, fun e he hcon => ?_⟩
    exact hS.2 e he ⟨(Finset.mem_inter.mp hcon.1).1, (Finset.mem_inter.mp hcon.2).1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun S => t ^ S.card * (1 - t) ^ (univ \ S).card)]
  refine Finset.sum_congr rfl fun L hL => ?_
  rw [Finset.mem_filter, Finset.mem_powerset] at hL
  exact fiber_sum_eq_vertex_cover_term E J L hJ hL.1 hL.2 t

-- The finite combinatorial argument also applies without the hypotheses on `k` and `E`.
set_option linter.unusedVariables false in
/-- **Vertex-cover Euler product for the coprimality density.** Let $k \ge 2$, let $E$ be a set of
pairs $(a, b)$ with $1 \le a < b \le k$, let $G$ be the graph on $\{1, \dots, k\}$ with edge set
$E$, and let $A_G$ be its coprimality density. Let $J \subseteq \{1, \dots, k\}$ be a vertex cover
of $G$, that is, every edge of $E$ has an endpoint in $J$. For $L \subseteq J$ let $N(L)$ be the
set of vertices adjacent to some vertex of $L$. Then
$$A_G = \prod_p \sum_{L} \left(\frac{1}{p}\right)^{|L|}
\left(1 - \frac{1}{p}\right)^{|J \setminus L| + |N(L) \setminus J|},$$
where the product runs over all primes $p$ and the sum over all independent sets $L \subseteq J$
of $G$, that is, subsets of $J$ such that no edge of $E$ has both endpoints in $L$.

Source: László Tóth, *On the Asymptotic Density of k-tuples of Positive
Integers with Pairwise Non-Coprime Components*, Journal of Integer Sequences 27
(2024), Article 24.8.5, Theorem 9 (`jis-2024-24.8.5-thm-9`). -/
public theorem coprimalityDensity_eq_vertex_cover_product {k : ℕ} (hk : 2 ≤ k)
    (E : Finset (Fin k × Fin k)) (hE : ∀ e ∈ E, e.1 < e.2)
    (J : Finset (Fin k)) (hJ : ∀ e ∈ E, e.1 ∈ J ∨ e.2 ∈ J) :
    coprimalityDensity E =
      ∏' p : Nat.Primes, ∑ L ∈ J.powerset.filter (fun L => ∀ e ∈ E, ¬ (e.1 ∈ L ∧ e.2 ∈ L)),
        (1 / ((p : ℕ) : ℝ)) ^ L.card * (1 - 1 / ((p : ℕ) : ℝ)) ^
          ((J \ L).card + ((univ.filter fun i => ∃ l ∈ L, (l, i) ∈ E ∨ (i, l) ∈ E) \ J).card) := by
  unfold coprimalityDensity
  apply tprod_congr
  intro p
  have hA := sum_edge_subset_eq_sum_indep E (1 / ((p : ℕ) : ℝ))
  have hB := sum_indep_eq_sum_vertex_cover E J hJ (1 / ((p : ℕ) : ℝ))
  have hterm : ∀ F ∈ E.powerset, (-1 : ℝ) ^ F.card / ((p : ℕ) : ℝ) ^
        (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card
      = (-1 : ℝ) ^ F.card * (1 / ((p : ℕ) : ℝ)) ^
        (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card := by
    intro F _
    rw [div_eq_mul_inv, div_pow, one_pow, one_div]
  trans ∑ F ∈ E.powerset, (-1 : ℝ) ^ F.card * (1 / ((p : ℕ) : ℝ)) ^
    (univ.filter fun i : Fin k => ∃ e ∈ F, e.1 = i ∨ e.2 = i).card
  · exact Finset.sum_congr rfl hterm
  · rw [hA, hB]

end

end MetaMathlibExt
