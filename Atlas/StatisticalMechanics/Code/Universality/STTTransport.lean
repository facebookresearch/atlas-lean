/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Universality.STT

open SimpleGraph

namespace StatMech

namespace Universality

variable {V : Type*}
















theorem bypass_vertex (G1 G2 : SimpleGraph V) (O : V)
    (hedge : ∀ a b, a ≠ O → b ≠ O → G1.Adj a b → G2.Reachable a b)
    (hcorner : ∀ s t, s ≠ O → t ≠ O → G1.Adj s O → G1.Adj O t → G2.Reachable s t)
    {u v : V} (hu : u ≠ O) (hv : v ≠ O) (h : G1.Reachable u v) : G2.Reachable u v := by
  obtain ⟨w⟩ := h
  induction n : w.length using Nat.strong_induction_on generalizing u v with
  | _ n IH =>
    subst n
    match w with
    | .nil => exact Reachable.refl _
    | .cons (v := b) hab w' =>
      by_cases hb : b = O
      · match w' with
        | .nil => exact absurd hb hv
        | .cons (v := c) hbc w'' =>
          have hc : c ≠ O := by intro hcO; subst hcO; exact (G1.ne_of_adj hbc) hb
          have hbO : G1.Adj u O := hb ▸ hab
          have hOc : G1.Adj O c := hb ▸ hbc
          exact (hcorner u c hu hc hbO hOc).trans
            (IH w''.length (by simp only [SimpleGraph.Walk.length_cons]; omega) hc hv w'' rfl)
      · exact (hedge u b hu hb hab).trans
          (IH w'.length (by simp only [SimpleGraph.Walk.length_cons]; omega) hb hv w' rfl)







theorem reach_collapse (G1 G2 : SimpleGraph V) (ρ : V → V)
    (hcell : ∀ a b, G1.Adj a b → G2.Reachable (ρ a) (ρ b))
    {u v : V} (hu : ρ u = u) (hv : ρ v = v) (h : G1.Reachable u v) : G2.Reachable u v := by
  obtain ⟨w⟩ := h
  have key : ∀ {x y : V}, (G1.Walk x y) → G2.Reachable (ρ x) (ρ y) := by
    intro x y w
    induction w with
    | nil => exact Reachable.refl _
    | @cons a b c hab w ih => exact (hcell a b hab).trans ih
  have := key w
  rwa [hu, hv] at this














def triCell (A B C : V) (ω : LocalConfig) : SimpleGraph V :=
  fromEdgeSet { e | (ω.1 ∧ e = s(B, C)) ∨ (ω.2.1 ∧ e = s(A, C)) ∨ (ω.2.2 ∧ e = s(A, B)) }




def starCell (A B C O : V) (ω : LocalConfig) : SimpleGraph V :=
  fromEdgeSet { e | (ω.1 ∧ e = s(O, A)) ∨ (ω.2.1 ∧ e = s(O, B)) ∨ (ω.2.2 ∧ e = s(O, C)) }



theorem triCell_adj_BC (A B C : V) (ω : LocalConfig) (h : ω.1 = true) (hBC : B ≠ C) :
    (triCell A B C ω).Adj B C := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inl ⟨h, rfl⟩, hBC⟩

theorem triCell_adj_AC (A B C : V) (ω : LocalConfig) (h : ω.2.1 = true) (hAC : A ≠ C) :
    (triCell A B C ω).Adj A C := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inl ⟨h, rfl⟩), hAC⟩

theorem triCell_adj_AB (A B C : V) (ω : LocalConfig) (h : ω.2.2 = true) (hAB : A ≠ B) :
    (triCell A B C ω).Adj A B := by
  unfold triCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inr ⟨h, rfl⟩), hAB⟩



theorem triCell_adj_imp (A B C : V) (ω : LocalConfig) {x y : V}
    (h : (triCell A B C ω).Adj x y) :
    (ω.1 ∧ s(x, y) = s(B, C)) ∨ (ω.2.1 ∧ s(x, y) = s(A, C)) ∨ (ω.2.2 ∧ s(x, y) = s(A, B)) := by
  unfold triCell at h
  rw [fromEdgeSet_adj] at h
  simpa using h.1



theorem starCell_adj_OA (A B C O : V) (ω : LocalConfig) (h : ω.1 = true) (hOA : O ≠ A) :
    (starCell A B C O ω).Adj O A := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inl ⟨h, rfl⟩, hOA⟩

theorem starCell_adj_OB (A B C O : V) (ω : LocalConfig) (h : ω.2.1 = true) (hOB : O ≠ B) :
    (starCell A B C O ω).Adj O B := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inl ⟨h, rfl⟩), hOB⟩

theorem starCell_adj_OC (A B C O : V) (ω : LocalConfig) (h : ω.2.2 = true) (hOC : O ≠ C) :
    (starCell A B C O ω).Adj O C := by
  unfold starCell; rw [fromEdgeSet_adj]; exact ⟨Or.inr (Or.inr ⟨h, rfl⟩), hOC⟩



theorem starCell_adj_imp (A B C O : V) (ω : LocalConfig) {x y : V}
    (h : (starCell A B C O ω).Adj x y) :
    (x = O ∧ ((y = A ∧ ω.1) ∨ (y = B ∧ ω.2.1) ∨ (y = C ∧ ω.2.2))) ∨
    (y = O ∧ ((x = A ∧ ω.1) ∨ (x = B ∧ ω.2.1) ∨ (x = C ∧ ω.2.2))) := by
  unfold starCell at h
  rw [fromEdgeSet_adj] at h
  obtain ⟨hmem, _⟩ := h
  simp only [Set.mem_setOf_eq] at hmem
  rcases hmem with ⟨hb, he⟩ | ⟨hb, he⟩ | ⟨hb, he⟩ <;>
    rw [Sym2.eq_iff] at he <;> rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all








variable (E : SimpleGraph V) {A B C : V}



theorem triCell_reach_BC (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triBC ω = true) :
    (E ⊔ triCell A B C ω).Reachable B C := by
  unfold triBC at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_BC A B C ω h hBC))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AB A B C ω h.2 hAB))).symm.trans
      (Adj.reachable (Or.inr (triCell_adj_AC A B C ω h.1 hAC)))



theorem triCell_reach_AC (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triAC ω = true) :
    (E ⊔ triCell A B C ω).Reachable A C := by
  unfold triAC at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_AC A B C ω h hAC))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AB A B C ω h.2 hAB))).trans
      (Adj.reachable (Or.inr (triCell_adj_BC A B C ω h.1 hBC)))



theorem triCell_reach_AB (A B C : V) (ω : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (h : triAB ω = true) :
    (E ⊔ triCell A B C ω).Reachable A B := by
  unfold triAB at h; rw [Bool.or_eq_true] at h
  rcases h with h | h
  · exact Adj.reachable (Or.inr (triCell_adj_AB A B C ω h hAB))
  · rw [Bool.and_eq_true] at h
    exact (Adj.reachable (Or.inr (triCell_adj_AC A B C ω h.2 hAC))).trans
      (Adj.reachable (Or.inr (triCell_adj_BC A B C ω h.1 hBC))).symm



theorem starCell_reach_AB (A B C O : V) (ω : LocalConfig)
    (hOA : O ≠ A) (hOB : O ≠ B) (h : starAB ω = true) :
    (E ⊔ starCell A B C O ω).Reachable A B := by
  unfold starAB at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OA A B C O ω h.1 hOA))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OB A B C O ω h.2 hOB)))



theorem starCell_reach_AC (A B C O : V) (ω : LocalConfig)
    (hOA : O ≠ A) (hOC : O ≠ C) (h : starAC ω = true) :
    (E ⊔ starCell A B C O ω).Reachable A C := by
  unfold starAC at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OA A B C O ω h.1 hOA))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OC A B C O ω h.2 hOC)))



theorem starCell_reach_BC (A B C O : V) (ω : LocalConfig)
    (hOB : O ≠ B) (hOC : O ≠ C) (h : starBC ω = true) :
    (E ⊔ starCell A B C O ω).Reachable B C := by
  unfold starBC at h; rw [Bool.and_eq_true] at h
  exact (Adj.reachable (Or.inr (starCell_adj_OB A B C O ω h.1 hOB))).symm.trans
    (Adj.reachable (Or.inr (starCell_adj_OC A B C O ω h.2 hOC)))











def MatchesPattern (ωt ωs : LocalConfig) : Prop :=
  triAB ωt = starAB ωs ∧ triAC ωt = starAC ωs ∧ triBC ωt = starBC ωs












theorem reach_tri_to_star (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) {u v : V}
    (h : (E ⊔ triCell A B C ωt).Reachable u v) :
    (E ⊔ starCell A B C O ωs).Reachable u v := by
  obtain ⟨hmAB, hmAC, hmBC⟩ := hm
  refine reach_collapse _ _ id ?_ rfl rfl h
  intro a b hab
  simp only [id]
  rcases hab with hE | hcell
  · exact Adj.reachable (Or.inl hE)
  · 
    rcases triCell_adj_imp A B C ωt hcell with ⟨hb, he⟩ | ⟨hb, he⟩ | ⟨hb, he⟩
    · 
      have hstar : starBC ωs = true := by
        rw [← hmBC]; unfold triBC; simp [hb]
      have r := starCell_reach_BC E A B C O ωs hOB hOC hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm
    · have hstar : starAC ωs = true := by
        rw [← hmAC]; unfold triAC; simp [hb]
      have r := starCell_reach_AC E A B C O ωs hOA hOC hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm
    · have hstar : starAB ωs = true := by
        rw [← hmAB]; unfold triAB; simp [hb]
      have r := starCell_reach_AB E A B C O ωs hOA hOB hstar
      rw [Sym2.eq_iff] at he
      rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact r
      · exact r.symm







theorem reach_star_to_tri (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs)
    (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O)
    (h : (E ⊔ starCell A B C O ωs).Reachable u v) :
    (E ⊔ triCell A B C ωt).Reachable u v := by
  obtain ⟨hmAB, hmAC, hmBC⟩ := hm
  
  have triAB' : starAB ωs = true → (E ⊔ triCell A B C ωt).Reachable A B := fun hs =>
    triCell_reach_AB E A B C ωt hAB hAC hBC (by rw [hmAB]; exact hs)
  have triAC' : starAC ωs = true → (E ⊔ triCell A B C ωt).Reachable A C := fun hs =>
    triCell_reach_AC E A B C ωt hAB hAC hBC (by rw [hmAC]; exact hs)
  have triBC' : starBC ωs = true → (E ⊔ triCell A B C ωt).Reachable B C := fun hs =>
    triCell_reach_BC E A B C ωt hAB hAC hBC (by rw [hmBC]; exact hs)
  refine bypass_vertex _ _ O ?_ ?_ hu hv h
  · 
    intro a b ha hb hab
    rcases hab with hE | hcell
    · exact Adj.reachable (Or.inl hE)
    · rcases starCell_adj_imp A B C O ωs hcell with ⟨hO, _⟩ | ⟨hO, _⟩
      · exact absurd hO ha
      · exact absurd hO hb
  · 
    intro s t hs ht hsO hOt
    
    have hspoke : ∀ {p : V}, (E ⊔ starCell A B C O ωs).Adj p O → p ≠ O →
        (p = A ∧ ωs.1 = true) ∨ (p = B ∧ ωs.2.1 = true) ∨ (p = C ∧ ωs.2.2 = true) := by
      intro p hpO hpne
      rcases hpO with hE | hcell
      · exact absurd hE (hEO p)
      · rcases starCell_adj_imp A B C O ωs hcell with ⟨hO, _⟩ | ⟨_, hcase⟩
        · exact absurd hO hpne
        · rcases hcase with ⟨rfl, hb⟩ | ⟨rfl, hb⟩ | ⟨rfl, hb⟩
          · exact Or.inl ⟨rfl, hb⟩
          · exact Or.inr (Or.inl ⟨rfl, hb⟩)
          · exact Or.inr (Or.inr ⟨rfl, hb⟩)
    have hsp_s := hspoke hsO hs
    have hsp_t := hspoke hOt.symm ht
    
    rcases hsp_s with ⟨rfl, hsb⟩ | ⟨rfl, hsb⟩ | ⟨rfl, hsb⟩ <;>
      rcases hsp_t with ⟨rfl, htb⟩ | ⟨rfl, htb⟩ | ⟨rfl, htb⟩
    
    · exact Reachable.refl _
    · exact triAB' (by unfold starAB; simp [hsb, htb])
    · exact triAC' (by unfold starAC; simp [hsb, htb])
    · exact (triAB' (by unfold starAB; simp [hsb, htb])).symm
    · exact Reachable.refl _
    · exact triBC' (by unfold starBC; simp [hsb, htb])
    · exact (triAC' (by unfold starAC; simp [hsb, htb])).symm
    · exact (triBC' (by unfold starBC; simp [hsb, htb])).symm
    · exact Reachable.refl _













theorem starTriangle_reach_iff (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O) :
    (E ⊔ triCell A B C ωt).Reachable u v ↔ (E ⊔ starCell A B C O ωs).Reachable u v :=
  ⟨reach_tri_to_star E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm,
   reach_star_to_tri E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv⟩













theorem starTriangle_crossing_transport (A B C O : V) (ωt ωs : LocalConfig)
    (hAB : A ≠ B) (hAC : A ≠ C) (hBC : B ≠ C) (hOA : O ≠ A) (hOB : O ≠ B) (hOC : O ≠ C)
    (hm : MatchesPattern ωt ωs) (hEO : ∀ x, ¬ E.Adj x O) {u v : V} (hu : u ≠ O) (hv : v ≠ O) :
    (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ triCell A B C ωt).Reachable p q) ↔
    (∃ p q : V, p = u ∧ q = v ∧ (E ⊔ starCell A B C O ωs).Reachable p q) := by
  constructor
  · rintro ⟨p, q, rfl, rfl, hpq⟩
    exact ⟨p, q, rfl, rfl,
      (starTriangle_reach_iff E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv).1 hpq⟩
  · rintro ⟨p, q, rfl, rfl, hpq⟩
    exact ⟨p, q, rfl, rfl,
      (starTriangle_reach_iff E A B C O ωt ωs hAB hAC hBC hOA hOB hOC hm hEO hu hv).2 hpq⟩

end Universality

end StatMech
