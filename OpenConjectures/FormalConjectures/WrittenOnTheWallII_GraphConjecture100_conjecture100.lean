/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean` (Formal Conjectures):
Copyright 2026 The Formal Conjectures Authors.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
-/

import Mathlib
















import FormalConjecturesUtil

set_option maxHeartbeats 1000000

























namespace WrittenOnTheWallII.GraphConjecture100

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]












@[category research open, AMS 5]
theorem conjecture100 (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ := by
  classical
  let m := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
  change (G.indepNum : ℝ) ≤
    (⌈((m : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ : ℤ)
  obtain ⟨S, hS⟩ := G.exists_isNIndepSet_indepNum
  let T := Finset.univ \ S
  have hScard : S.card = G.indepNum := hS.card_eq
  have hind_le (v : α) : indepNeighborsCard G v ≤ G.indepNum := by
    obtain ⟨U, hU⟩ :=
      (G.induce (G.neighborSet v)).exists_isNIndepSet_indepNum
    let V : Finset α := U.image Subtype.val
    have hV : G.IsIndepSet (V : Set α) := by
      intro x hx y hy hxy
      simp only [V, Finset.mem_coe, Finset.mem_image] at hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', heq⟩ := hy
      subst heq
      exact hU.isIndepSet hx' hy' (by
        intro e
        exact hxy (congrArg Subtype.val e))
    have hc : V.card = U.card :=
      Finset.card_image_of_injective _ Subtype.val_injective
    rw [indepNeighborsCard, ← hU.card_eq, ← hc]
    exact hV.card_le_indepNum
  have hm_le : m ≤ G.indepNum := by
    obtain ⟨v, -, hv⟩ := Finset.mem_image.mp
      (Finset.max'_mem _ (by simp : (Finset.univ.image (indepNeighborsCard G)).Nonempty))
    simpa [m, ← hv] using hind_le v
  have hinter (v : α) : (S.filter (G.Adj v)).card ≤ m := by
    let U : Finset (G.neighborSet v) :=
      S.preimage Subtype.val (Set.injOn_of_injective Subtype.val_injective)
    have hU : (G.induce (G.neighborSet v)).IsIndepSet
        (U : Set (G.neighborSet v)) := by
      intro x hx y hy hxy
      apply hS.isIndepSet
      · simpa [U] using hx
      · simpa [U] using hy
      · exact Subtype.coe_ne_coe.mpr hxy
    have hc : U.card = (S.filter (G.Adj v)).card := by
      rw [Finset.card_preimage]
      congr 1
      ext x
      simp [SimpleGraph.mem_neighborSet]
    rw [← hc]
    calc
      U.card ≤ indepNeighborsCard G v := hU.card_le_indepNum
      _ ≤ m := Finset.le_max' _ _ (Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
  have hcover : S.card ≤ T.card * m := by
    have hone : ∀ s ∈ S, 1 ≤ (T.filter (G.Adj s)).card := by
      intro s hs
      have hd : 0 < G.degree s := h.preconnected.degree_pos_of_nontrivial s
      rw [← G.card_neighborFinset_eq_degree, Finset.card_pos] at hd
      obtain ⟨v, hv⟩ := hd
      have hadj : G.Adj s v := (G.mem_neighborFinset s v).mp hv
      have hvS : v ∉ S := by
        intro hvS
        exact (hS.isIndepSet hs hvS (G.ne_of_adj hadj)) hadj
      apply Finset.card_pos.mpr
      exact ⟨v, by simp [T, hvS, hadj]⟩
    calc
      S.card = ∑ s ∈ S, 1 := by simp
      _ ≤ ∑ s ∈ S, (T.filter (G.Adj s)).card :=
        Finset.sum_le_sum fun s hs => hone s hs
      _ = ∑ v ∈ T, (S.filter (G.Adj v)).card := by
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro s hs
        simp only [G.adj_comm]
      _ ≤ ∑ v ∈ T, m := Finset.sum_le_sum fun v hv => hinter v
      _ = T.card * m := by simp
  have hkpos : 0 < S.card := by
    let x : α := Classical.choice (inferInstance : Nonempty α)
    have hsingle : G.IsIndepSet (({x} : Finset α) : Set α) := by simp
    have hone : ({x} : Finset α).card ≤ G.indepNum := hsingle.card_le_indepNum
    simpa [hScard] using hone
  have hmpos : 0 < m := by
    nlinarith
  have hdis : Disjoint S T := Finset.disjoint_sdiff
  have hdeg_sum :
      S.card * (S.card - 1) + T.card * (S.card - m)
        ≤ ∑ s ∈ S, Gᶜ.degree s := by
    have hpoint : ∀ s ∈ S,
        S.card - 1 + (T.filter (fun v => ¬ G.Adj s v)).card ≤ Gᶜ.degree s := by
      intro s hs
      rw [← Gᶜ.card_neighborFinset_eq_degree]
      let U := (S.erase s) ∪ (T.filter (fun v => ¬ G.Adj s v))
      have hsub : U ⊆ Gᶜ.neighborFinset s := by
        intro v hv
        simp only [U, Finset.mem_union, Finset.mem_erase, Finset.mem_filter] at hv
        rw [Gᶜ.mem_neighborFinset]
        simp only [compl_adj]
        rcases hv with hv | hv
        · exact ⟨hv.1.symm, hS.isIndepSet hs hv.2 hv.1.symm⟩
        · have hsv : s ≠ v := by
            intro e
            subst e
            exact Finset.disjoint_left.mp hdis hs hv.1
          exact ⟨hsv, hv.2⟩
      calc
        S.card - 1 + (T.filter (fun v => ¬ G.Adj s v)).card = U.card := by
          rw [Finset.card_union_of_disjoint]
          · simp [U, hs]
          · exact Finset.disjoint_of_subset_left (Finset.erase_subset _ _) <|
              Finset.disjoint_of_subset_right (Finset.filter_subset _ _) hdis
        _ ≤ (Gᶜ.neighborFinset s).card := Finset.card_le_card hsub
    have hnon : ∀ v ∈ T,
        S.card - m ≤ (S.filter (fun s => ¬ G.Adj v s)).card := by
      intro v hv
      have hp := Finset.filter_card_add_filter_neg_card_eq_card
        (s := S) (p := G.Adj v)
      have ha := hinter v
      omega
    calc
      S.card * (S.card - 1) + T.card * (S.card - m) =
          (∑ s ∈ S, (S.card - 1)) + ∑ v ∈ T, (S.card - m) := by
        simp [mul_comm]
      _ ≤ (∑ s ∈ S, (S.card - 1)) +
          ∑ v ∈ T, (S.filter (fun s => ¬ G.Adj v s)).card := by
        gcongr with v hv
        exact hnon v hv
      _ = ∑ s ∈ S,
          (S.card - 1 + (T.filter (fun v => ¬ G.Adj s v)).card) := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro v hv
        apply Finset.sum_congr rfl
        intro s hs
        simp only [G.adj_comm]
      _ ≤ ∑ s ∈ S, Gᶜ.degree s :=
        Finset.sum_le_sum fun s hs => hpoint s hs
  have houtside (v : α) (hv : v ∈ T) : S.card - m ≤ Gᶜ.degree v := by
    have hnon : S.card - m ≤ (S.filter (fun s => ¬ G.Adj v s)).card := by
      have hp := Finset.filter_card_add_filter_neg_card_eq_card
        (s := S) (p := G.Adj v)
      have ha := hinter v
      omega
    apply hnon.trans
    rw [← Gᶜ.card_neighborFinset_eq_degree]
    apply Finset.card_le_card
    intro s hs
    simp only [Finset.mem_filter] at hs
    rw [Gᶜ.mem_neighborFinset]
    simp only [compl_adj]
    exact ⟨by
      intro e
      subst e
      exact Finset.disjoint_left.mp hdis hs.1 hv, hs.2⟩
  have hnorm_nonneg : 0 ≤ degreeL2Norm Gᶜ := by
    simp [degreeL2Norm]
  have hnorm_sq : (degreeL2Norm Gᶜ) ^ 2 =
      ∑ v, ((Gᶜ.degree v : ℝ) ^ 2) := by
    rw [degreeL2Norm, Real.sq_sqrt]
    positivity
  have hquant :
      ((S.card * (S.card - 1) + T.card * (S.card - m) : ℕ) : ℝ) ^ 2 +
          (S.card : ℝ) * (T.card : ℝ) * ((S.card - m : ℕ) : ℝ) ^ 2
        ≤ (S.card : ℝ) * (degreeL2Norm Gᶜ) ^ 2 := by
    let dS : ℝ := ∑ s ∈ S, (Gᶜ.degree s : ℝ)
    let qS : ℝ := ∑ s ∈ S, (Gᶜ.degree s : ℝ) ^ 2
    let qT : ℝ := ∑ v ∈ T, (Gᶜ.degree v : ℝ) ^ 2
    let A : ℕ := S.card * (S.card - 1) + T.card * (S.card - m)
    have hA : (A : ℝ) ≤ dS := by
      dsimp [A, dS]
      exact_mod_cast hdeg_sum
    have hdS : 0 ≤ dS := by
      dsimp [dS]
      positivity
    have hcs : dS ^ 2 ≤ (S.card : ℝ) * qS := by
      simpa [dS, qS] using
        (sq_sum_le_card_mul_sum_sq
          (s := S) (f := fun s => (Gᶜ.degree s : ℝ)))
    have hAcs : (A : ℝ) ^ 2 ≤ (S.card : ℝ) * qS := by
      apply le_trans _ hcs
      nlinarith [sq_nonneg (dS - (A : ℝ))]
    have hTq : (T.card : ℝ) * ((S.card - m : ℕ) : ℝ) ^ 2 ≤ qT := by
      calc
        (T.card : ℝ) * ((S.card - m : ℕ) : ℝ) ^ 2 =
            ∑ v ∈ T, ((S.card - m : ℕ) : ℝ) ^ 2 := by simp
        _ ≤ ∑ v ∈ T, (Gᶜ.degree v : ℝ) ^ 2 := by
          apply Finset.sum_le_sum
          intro v hv
          have hh : ((S.card - m : ℕ) : ℝ) ≤ (Gᶜ.degree v : ℝ) := by
            exact_mod_cast houtside v hv
          have hn : 0 ≤ ((S.card - m : ℕ) : ℝ) := by positivity
          nlinarith [sq_nonneg ((Gᶜ.degree v : ℝ) - (S.card - m : ℕ))]
        _ = qT := rfl
    have hall : qS + qT = ∑ v, (Gᶜ.degree v : ℝ) ^ 2 := by
      have hs := Finset.sum_sdiff (f := fun v => (Gᶜ.degree v : ℝ) ^ 2)
        (Finset.subset_univ S)
      change qT + qS = _ at hs
      rw [add_comm]
      exact hs
    rw [hnorm_sq, ← hall]
    change (A : ℝ) ^ 2 + (S.card : ℝ) * (T.card : ℝ) *
      ((S.card - m : ℕ) : ℝ) ^ 2 ≤
        (S.card : ℝ) * (qS + qT)
    nlinarith
  have hmain :
      (G.indepNum : ℝ) - 1 <
        ((m : ℝ) + (1 / 2) * degreeL2Norm Gᶜ) / 2 := by
    rw [← hScard]
    have hmS : m ≤ S.card := by simpa [hScard] using hm_le
    have honeS : 1 ≤ S.card := by omega
    have hcoverR : (S.card : ℝ) ≤ (T.card : ℝ) * (m : ℝ) := by
      exact_mod_cast hcover
    push_cast [Nat.cast_sub hmS, Nat.cast_sub honeS] at hquant
    by_contra hcontra
    push_neg at hcontra
    by_cases hlarge : 16 ≤ S.card
    · have hmSR : (m : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hmS
      have hlargeR : (16 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hlarge
      have hdiff : 0 ≤ (S.card : ℝ) - (m : ℝ) := by linarith
      have hextra : 0 ≤ (T.card : ℝ) * ((S.card : ℝ) - (m : ℝ)) :=
        mul_nonneg (by positivity) hdiff
      have hbase : (S.card : ℝ) * ((S.card : ℝ) - 1) ≤
          ((S.card : ℝ) * ((S.card : ℝ) - 1) +
            (T.card : ℝ) * ((S.card : ℝ) - (m : ℝ))) := by
        linarith
      have hsnonneg : 0 ≤ (S.card : ℝ) * ((S.card : ℝ) - 1) := by
        have : (1 : ℝ) ≤ S.card := by exact_mod_cast honeS
        positivity
      have hsqbase :
          ((S.card : ℝ) * ((S.card : ℝ) - 1)) ^ 2 ≤
            ((S.card : ℝ) * ((S.card : ℝ) - 1) +
              (T.card : ℝ) * ((S.card : ℝ) - (m : ℝ))) ^ 2 := by
        nlinarith [sq_nonneg ((T.card : ℝ) * ((S.card : ℝ) - (m : ℝ)))]
      have hterm : 0 ≤ (S.card : ℝ) * (T.card : ℝ) *
          ((S.card : ℝ) - (m : ℝ)) ^ 2 := by positivity
      have hDsquare :
          (4 * ((S.card : ℝ) - 1)) ^ 2 ≤ (degreeL2Norm Gᶜ) ^ 2 := by
        nlinarith [sq_nonneg ((S.card : ℝ) - 1)]
      have hD : 4 * ((S.card : ℝ) - 1) ≤ degreeL2Norm Gᶜ := by
        nlinarith [sq_nonneg (degreeL2Norm Gᶜ - 4 * ((S.card : ℝ) - 1))]
      have hmR : 0 < (m : ℝ) := by exact_mod_cast hmpos
      linarith
    · have hsmall : S.card ≤ 15 := by omega
      have hqpoly : 0 ≤
          ((T.card : ℝ) * (m : ℝ) - (S.card : ℝ)) ^ 2 := sq_nonneg _
      have hDpoly : 0 ≤ (degreeL2Norm Gᶜ -
          (4 * ((S.card : ℝ) - 1) - 2 * (m : ℝ))) ^ 2 := sq_nonneg _
      generalize hq : (T.card : ℝ) = q at hquant hcoverR hqpoly
      generalize hD : degreeL2Norm Gᶜ = D at hquant hnorm_nonneg hDpoly hcontra
      interval_cases S.card <;> interval_cases m <;>
        norm_num at hquant hcoverR hmpos hkpos hmS hqpoly hDpoly hcontra ⊢ <;>
        nlinarith only [hquant, hcoverR, hnorm_nonneg, hqpoly, hDpoly, hcontra]
  have hzlt : (G.indepNum : ℤ) - 1 <
      ⌈((m : ℝ) + (1 / 2) * degreeL2Norm Gᶜ) / 2⌉ := by
    apply (Int.lt_ceil).2
    norm_num
    exact hmain
  have hz : (G.indepNum : ℤ) ≤
      ⌈((m : ℝ) + (1 / 2) * degreeL2Norm Gᶜ) / 2⌉ := by omega
  exact_mod_cast hz
end WrittenOnTheWallII.GraphConjecture100
