/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Ising.LebowitzPfisterReplicaOrbitExactTagSlotMove

open Finset

namespace StatMech.Ising

noncomputable section



noncomputable def lpReplicaEligibleInactivePairs
    {α β : Type*} [Fintype α] [DecidableEq α]
    (edge : α -> β) : Finset (Finset α) := by
  classical
  exact (Finset.univ.powersetCard 2).filter fun C =>
    Set.InjOn edge (↑(Finset.univ \ C) : Set α) ∧
      ∀ x ∈ C, ∀ y ∈ C, edge x = edge y




theorem lpReplicaEligibleInactivePairs_card_le_three
    {α β : Type*} [Fintype α] [DecidableEq α]
    (edge : α -> β) :
    (lpReplicaEligibleInactivePairs edge).card ≤ 3 := by
  classical
  let F := lpReplicaEligibleInactivePairs edge
  by_cases hF : F.Nonempty
  · obtain ⟨C0, hC0F⟩ := hF
    have hC0 := hC0F
    simp only [F, lpReplicaEligibleInactivePairs, Finset.mem_filter,
      Finset.mem_powersetCard, Finset.subset_univ, true_and] at hC0
    obtain ⟨a, b, hab, hC0eq⟩ := Finset.card_eq_two.mp hC0.1
    let A := Finset.univ.filter fun x => edge x = edge a
    have haC0 : a ∈ C0 := by simp [hC0eq]
    have hbC0 : b ∈ C0 := by simp [hC0eq]
    have habEdge : edge a = edge b := hC0.2.2 a haC0 b hbC0
    have hC0A : C0 ⊆ A := by
      intro x hx
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hC0.2.2 x hx a haC0
    have hdiffCard : (A \ C0).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro x hx y hy
      have hxA := (Finset.mem_sdiff.mp hx).1
      have hxC := (Finset.mem_sdiff.mp hx).2
      have hyA := (Finset.mem_sdiff.mp hy).1
      have hyC := (Finset.mem_sdiff.mp hy).2
      apply hC0.2.1
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxC⟩
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyC⟩
      · have hxEdge : edge x = edge a := by
          simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hxA
        have hyEdge : edge y = edge a := by
          simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hyA
        exact hxEdge.trans hyEdge.symm
    have hAcard : A.card ≤ 3 := by
      have hsplit := Finset.card_sdiff_add_card_eq_card hC0A
      rw [hC0.1] at hsplit
      omega
    have hFA : F ⊆ A.powersetCard 2 := by
      intro C hCF
      have hC := hCF
      simp only [F, lpReplicaEligibleInactivePairs, Finset.mem_filter,
        Finset.mem_powersetCard, Finset.subset_univ, true_and] at hC
      apply Finset.mem_powersetCard.mpr
      refine ⟨?_, hC.1⟩
      have hinter : (C ∩ C0).Nonempty := by
        by_contra hinter
        have hdisj : Disjoint C C0 := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          exact Finset.not_nonempty_iff_eq_empty.mp hinter
        have haNotC : a ∉ C := by
          intro ha
          exact (Finset.disjoint_left.mp hdisj) ha haC0
        have hbNotC : b ∉ C := by
          intro hb
          exact (Finset.disjoint_left.mp hdisj) hb hbC0
        exact hab (hC.2.1
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ a, haNotC⟩)
          (Finset.mem_sdiff.mpr ⟨Finset.mem_univ b, hbNotC⟩)
          habEdge)
      obtain ⟨x, hx⟩ := hinter
      have hx' := Finset.mem_inter.mp hx
      obtain ⟨hxC, hxC0⟩ := hx'
      intro y hyC
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      exact (hC.2.2 y hyC x hxC).trans (hC0.2.2 x hxC0 a haC0)
    calc
      F.card ≤ (A.powersetCard 2).card := Finset.card_le_card hFA
      _ ≤ 3 := by
        rw [Finset.card_powersetCard]
        have hAlower : 2 ≤ A.card := by
          calc
            2 = C0.card := hC0.1.symm
            _ ≤ A.card := Finset.card_le_card hC0A
        have hcases : A.card = 2 ∨ A.card = 3 := by omega
        rcases hcases with hA | hA <;> simp [hA]
  · have hFempty : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 3
    simp [hFempty]

end
end StatMech.Ising
