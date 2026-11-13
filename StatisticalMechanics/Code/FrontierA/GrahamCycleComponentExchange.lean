/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorBalancedCore










open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

private def exchangeCyclePair (A B : Finset I)
    (p : Finset I × Finset I) : Finset I × Finset I :=
  ((p.1 \ A) ∪ (p.2 ∩ B), (p.2 \ B) ∪ (p.1 ∩ A))

private theorem exchangeCyclePair_leftInverse
    {K L A B : Finset I} (hKL : Disjoint K L)
    (hAK : A ⊆ K) (hBL : B ⊆ L)
    {P Q : Finset I} (hPK : P ⊆ K) (hQL : Q ⊆ L) :
    exchangeCyclePair B A (exchangeCyclePair A B (P, Q)) = (P, Q) := by
  apply Prod.ext <;> ext i
  · have hPB : i ∈ P → i ∈ B → False := fun hiP hiB =>
      Finset.disjoint_left.mp hKL (hPK hiP) (hBL hiB)
    have hQA : i ∈ Q → i ∈ A → False := fun hiQ hiA =>
      Finset.disjoint_left.mp hKL (hAK hiA) (hQL hiQ)
    simp only [exchangeCyclePair, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter, Prod.fst, Prod.snd]
    by_cases hiA : i ∈ A <;> aesop
  · have hPB : i ∈ P → i ∈ B → False := fun hiP hiB =>
      Finset.disjoint_left.mp hKL (hPK hiP) (hBL hiB)
    have hQA : i ∈ Q → i ∈ A → False := fun hiQ hiA =>
      Finset.disjoint_left.mp hKL (hAK hiA) (hQL hiQ)
    simp only [exchangeCyclePair, Finset.mem_union, Finset.mem_sdiff,
      Finset.mem_inter, Prod.fst, Prod.snd]
    by_cases hiB : i ∈ B <;> aesop

private theorem sources_cycle_component_part
    {ends : I → Sym2 W} {P K : Finset I} (hPK : P ⊆ K)
    (hP : sources ends P = ∅) (u : W) :
    sources ends (P ∩ edgeComponent ends K u) = ∅ := by
  rw [sources_inter_edgeComponent hPK, hP]
  simp

private theorem sources_cycle_component_complement
    {ends : I → Sym2 W} {P K : Finset I} (hPK : P ⊆ K)
    (hP : sources ends P = ∅) (u : W) :
    sources ends (P \ edgeComponent ends K u) = ∅ := by
  classical
  have hpart := sources_cycle_component_part hPK hP u
  have heq : P \ edgeComponent ends K u =
      P \ (P ∩ edgeComponent ends K u) := by
    ext i
    simp
  rw [heq, sources_sdiff_of_subset Finset.inter_subset_left, hP, hpart]
  simp




noncomputable def cyclePairComponentExchangeEmbedding
    (ends : I → Sym2 W) (K L : Finset I) (u v : W)
    (hKL : Disjoint K L) :
    boundarySector ends K ∅ × boundarySector ends L ∅ ↪
      boundarySector ends
          ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅ ×
        boundarySector ends
          ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅ := by
  classical
  let A := edgeComponent ends K u
  let B := edgeComponent ends L v
  have hAK : A ⊆ K := by
    intro i hi
    change i ∈ edgeComponent ends K u at hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hBL : B ⊆ L := by
    intro i hi
    change i ∈ edgeComponent ends L v at hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  let f : boundarySector ends K ∅ × boundarySector ends L ∅ →
      boundarySector ends ((K \ A) ∪ B) ∅ ×
        boundarySector ends ((L \ B) ∪ A) ∅ := fun p => by
    let P := p.1.1
    let Q := p.2.1
    let P' := (P \ A) ∪ (Q ∩ B)
    let Q' := (Q \ B) ∪ (P ∩ A)
    have hPA : sources ends (P \ A) = ∅ := by
      simpa only [A, P] using
        sources_cycle_component_complement p.1.2.1 p.1.2.2 u
    have hQB : sources ends (Q ∩ B) = ∅ := by
      simpa only [B, Q] using sources_cycle_component_part p.2.2.1 p.2.2.2 v
    have hQB' : sources ends (Q \ B) = ∅ := by
      simpa only [B, Q] using
        sources_cycle_component_complement p.2.2.1 p.2.2.2 v
    have hPA' : sources ends (P ∩ A) = ∅ := by
      simpa only [A, P] using sources_cycle_component_part p.1.2.1 p.1.2.2 u
    have hd1 : Disjoint (P \ A) (Q ∩ B) := by
      exact hKL.mono (Finset.sdiff_subset.trans p.1.2.1)
        (Finset.inter_subset_left.trans p.2.2.1)
    have hd2 : Disjoint (Q \ B) (P ∩ A) := by
      exact hKL.symm.mono (Finset.sdiff_subset.trans p.2.2.1)
        (Finset.inter_subset_left.trans p.1.2.1)
    exact
      (⟨P',
        ⟨by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
              ⟨p.1.2.1 (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2,
          by rw [sources_union_of_disjoint hd1, hPA, hQB]; simp⟩⟩,
       ⟨Q',
        ⟨by
          intro i hi
          rcases Finset.mem_union.mp hi with hi | hi
          · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr
              ⟨p.2.2.1 (Finset.mem_sdiff.mp hi).1, (Finset.mem_sdiff.mp hi).2⟩)
          · exact Finset.mem_union_right _ (Finset.mem_inter.mp hi).2,
          by rw [sources_union_of_disjoint hd2, hQB', hPA']; simp⟩⟩)
  refine ⟨f, ?_⟩
  intro p q hpq
  have hval := congrArg (fun r => (r.1.1, r.2.1)) hpq
  change exchangeCyclePair A B (p.1.1, p.2.1) =
    exchangeCyclePair A B (q.1.1, q.2.1) at hval
  have hp := exchangeCyclePair_leftInverse hKL hAK hBL p.1.2.1 p.2.2.1
  have hq := exchangeCyclePair_leftInverse hKL hAK hBL q.1.2.1 q.2.2.1
  have hinv := congrArg (exchangeCyclePair B A) hval
  rw [hp, hq] at hinv
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.fst hinv
  · apply Subtype.ext
    exact congrArg Prod.snd hinv


theorem cyclePairComponentExchange_card_le
    (ends : I → Sym2 W) (K L : Finset I) (u v : W)
    (hKL : Disjoint K L) :
    Fintype.card (boundarySector ends K ∅ × boundarySector ends L ∅) ≤
      Fintype.card
        (boundarySector ends
            ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅ ×
          boundarySector ends
            ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅) := by
  exact Fintype.card_le_of_embedding
    (cyclePairComponentExchangeEmbedding ends K L u v hKL)




theorem cycleSpaceWeight_componentExchange_le
    (ends : I → Sym2 W) (K L : Finset I) (u v : W)
    (hKL : Disjoint K L) :
    Fintype.card (boundarySector ends K ∅) *
        Fintype.card (boundarySector ends L ∅) ≤
      Fintype.card
          (boundarySector ends
            ((K \ edgeComponent ends K u) ∪ edgeComponent ends L v) ∅) *
        Fintype.card
          (boundarySector ends
            ((L \ edgeComponent ends L v) ∪ edgeComponent ends K u) ∅) := by
  simpa only [Fintype.card_prod] using
    cyclePairComponentExchange_card_le ends K L u v hKL





theorem rowSupportWeight_le_componentExchange
    (ends : I → Sym2 W) (m K : Finset I) (k zero : W)
    (hKm : K ⊆ m) :
    rowSupportWeight ends m K ≤
      rowSupportWeight ends m
        (exchangeFirstRow ends K (m \ K) k zero) := by
  classical
  let L := m \ K
  let K' := exchangeFirstRow ends K L k zero
  let L' := exchangeSecondRow ends K L k zero
  have hKL : Disjoint K L := by
    rw [Finset.disjoint_left]
    intro i hiK hiL
    exact (Finset.mem_sdiff.mp hiL).2 hiK
  have hE0sub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hE1sub : edgeComponent ends L k ⊆ L := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hcompl : m \ K' = L' := by
    ext i
    have hE0 := @hE0sub i
    have hE1 := @hE1sub i
    have hKi := @hKm i
    simp only [K', L', exchangeFirstRow, exchangeSecondRow,
      Finset.mem_sdiff, Finset.mem_union]
    dsimp only [L] at hE1 ⊢
    by_cases hiK : i ∈ K <;> by_cases him : i ∈ m <;>
      by_cases hiE0 : i ∈ edgeComponent ends K zero <;>
        by_cases hiE1 : i ∈ edgeComponent ends (m \ K) k <;>
          simp [hiK, him, hiE0, hiE1] at hE0 hE1 hKi ⊢
  have hweight :=
    cycleSpaceWeight_componentExchange_le ends K L zero k hKL
  unfold rowSupportWeight
  dsimp only [K', L', L] at hcompl hweight ⊢
  rw [hcompl]
  exact hweight






theorem componentExchange_eq_of_eq_support_and_components
    (ends : I → Sym2 W) (m : Finset I) (k zero : W)
    {K₁ K₂ : Finset I}
    (hsupport :
      exchangeFirstRow ends K₁ (m \ K₁) k zero =
        exchangeFirstRow ends K₂ (m \ K₂) k zero)
    (hzero : edgeComponent ends K₁ zero = edgeComponent ends K₂ zero)
    (hk : edgeComponent ends (m \ K₁) k =
      edgeComponent ends (m \ K₂) k) :
    K₁ = K₂ := by
  classical
  have hA₁ : edgeComponent ends K₁ zero ⊆ K₁ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hA₂ : edgeComponent ends K₂ zero ⊆ K₂ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hB₁ : edgeComponent ends (m \ K₁) k ⊆ m \ K₁ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hB₂ : edgeComponent ends (m \ K₂) k ⊆ m \ K₂ := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hrecover₁ : K₁ =
      (exchangeFirstRow ends K₁ (m \ K₁) k zero \
          edgeComponent ends (m \ K₁) k) ∪
        edgeComponent ends K₁ zero := by
    ext i
    simp only [exchangeFirstRow, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · intro hiK
      by_cases hiA : i ∈ edgeComponent ends K₁ zero
      · exact Or.inr hiA
      · refine Or.inl ⟨Or.inl ⟨hiK, hiA⟩, ?_⟩
        intro hiB
        exact (Finset.mem_sdiff.mp (hB₁ hiB)).2 hiK
    · rintro (⟨hiR, hiB⟩ | hiA)
      · rcases hiR with hiK | hiB'
        · exact hiK.1
        · exact False.elim (hiB hiB')
      · exact hA₁ hiA
  have hrecover₂ : K₂ =
      (exchangeFirstRow ends K₂ (m \ K₂) k zero \
          edgeComponent ends (m \ K₂) k) ∪
        edgeComponent ends K₂ zero := by
    ext i
    simp only [exchangeFirstRow, Finset.mem_union,
      Finset.mem_sdiff]
    constructor
    · intro hiK
      by_cases hiA : i ∈ edgeComponent ends K₂ zero
      · exact Or.inr hiA
      · refine Or.inl ⟨Or.inl ⟨hiK, hiA⟩, ?_⟩
        intro hiB
        exact (Finset.mem_sdiff.mp (hB₂ hiB)).2 hiK
    · rintro (⟨hiR, hiB⟩ | hiA)
      · rcases hiR with hiK | hiB'
        · exact hiK.1
        · exact False.elim (hiB hiB')
      · exact hA₂ hiA
  rw [hrecover₁, hrecover₂]
  rw [hsupport, hzero, hk]

end StatMech.GrahamGHS.FourColor
