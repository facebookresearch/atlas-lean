/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Algebra.CharP.Defs
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Order.CompletePartialOrder

@[expose] public section

section
namespace MathlibExt.Combinatorics.Matroid.RadoWanted

/-! # Rado's matroidal marriage theorem

Finite Rado matroidal marriage iff Hall-Rado rank condition.
R. Rado, Quarterly J. Math. os-13 (1942), DOI 10.1093/qmath/os-13.1.83.
-/

private theorem contract_singleton_eRk_ge
    {E : Type*} [Finite E]
    (M' : Matroid E) (e : E) (he : M'.IsNonloop e)
    (Y : Set E) (k : ℕ) (hY : (k : ℕ∞) < M'.eRk Y) :
    (k : ℕ∞) ≤ (Matroid.contract M' {e}).eRk Y := by
  classical
  have he_indep : M'.Indep {e} := he.indep
  obtain ⟨B, hB, heB⟩ := he_indep.subset_isBasis'_of_subset (Set.subset_union_right : {e} ⊆ Y ∪ {e})
  have he_mem_B : e ∈ B := heB rfl
  have hB_indep_M'' : (Matroid.contract M' {e}).Indep (B \ {e}) :=
    hB.indep.diff_indep_contract_of_subset heB
  have hsub : B \ {e} ⊆ Y := by
    rintro x ⟨hxB, hxne⟩
    have hxYU := hB.subset hxB
    simp only [Set.mem_union, Set.mem_singleton_iff] at hxYU
    rcases hxYU with h | h
    · exact h
    · simp only [Set.mem_singleton_iff] at hxne
      exact absurd h hxne
  have hle : (B \ {e}).encard ≤ (Matroid.contract M' {e}).eRk Y :=
    hB_indep_M''.encard_le_eRk_of_subset hsub
  suffices hsuff : (k : ℕ∞) ≤ (B \ {e}).encard by exact hsuff.trans hle
  have hBfin : B.Finite := Set.toFinite B
  have hDfin : (B \ {e}).Finite := hBfin.subset Set.sdiff_subset
  obtain ⟨b, hb⟩ := hBfin.exists_encard_eq_coe
  obtain ⟨c, hc⟩ := hDfin.exists_encard_eq_coe
  have hBe : B.encard = M'.eRk (Y ∪ {e}) := hB.encard_eq_eRk
  have hmono : M'.eRk Y ≤ M'.eRk (Y ∪ {e}) := (Matroid.eRk_mono M') Set.subset_union_left
  have hlt : (k : ℕ∞) < B.encard := hY.trans_le (hBe ▸ hmono)
  have hadd : (B \ {e}).encard + ({e} : Set E).encard = B.encard :=
    Set.encard_sdiff_add_encard_of_subset (Set.singleton_subset_iff.mpr he_mem_B)
  rw [Set.encard_singleton, hb, hc] at hadd
  rw [hc]
  have hkb : k < b := by
    rw [hb] at hlt
    exact_mod_cast hlt
  have hcb : c + 1 = b := by exact_mod_cast hadd
  have hkc : k ≤ c := by omega
  exact_mod_cast hkc

private theorem contract_set_eRk_ge
    {E : Type*} [Finite E]
    (M' : Matroid E) (C : Set E) (hC : M'.Indep C)
    (Y : Set E) (k b : ℕ) (hCb : C.encard = (b : ℕ∞))
    (hY : ((k + b : ℕ) : ℕ∞) ≤ M'.eRk (Y ∪ C)) :
    (k : ℕ∞) ≤ (Matroid.contract M' C).eRk Y := by
  classical
  obtain ⟨B, hB, hCB⟩ := hC.subset_isBasis'_of_subset (Set.subset_union_right : C ⊆ Y ∪ C)
  have hB_indep_M1 : (Matroid.contract M' C).Indep (B \ C) :=
    hB.indep.diff_indep_contract_of_subset hCB
  have hsub : B \ C ⊆ Y := by
    rintro x ⟨hxB, hxne⟩
    have hxYU := hB.subset hxB
    simp only [Set.mem_union] at hxYU
    rcases hxYU with h | h
    · exact h
    · exact absurd h hxne
  have hle : (B \ C).encard ≤ (Matroid.contract M' C).eRk Y :=
    hB_indep_M1.encard_le_eRk_of_subset hsub
  suffices hsuff : (k : ℕ∞) ≤ (B \ C).encard by exact hsuff.trans hle
  have hBfin : B.Finite := Set.toFinite B
  have hDfin : (B \ C).Finite := hBfin.subset Set.sdiff_subset
  obtain ⟨m, hm⟩ := hBfin.exists_encard_eq_coe
  obtain ⟨c, hc⟩ := hDfin.exists_encard_eq_coe
  have hBe : B.encard = M'.eRk (Y ∪ C) := hB.encard_eq_eRk
  have hadd : (B \ C).encard + C.encard = B.encard :=
    Set.encard_sdiff_add_encard_of_subset hCB
  rw [hCb, hm, hc] at hadd
  rw [hc]
  have hlkb : k + b ≤ m := by
    rw [← hBe, hm] at hY
    exact_mod_cast hY
  have hcb : c + b = m := by exact_mod_cast hadd
  have hkc : k ≤ c := by omega
  exact_mod_cast hkc

private theorem rado_aux
    {E : Type*} [Finite E] (n : ℕ)
    {I' : Type*} [Fintype I'] (M' : Matroid E) (A' : I' → Set E)
    (hcard : Fintype.card I' ≤ n)
    (hcond : ∀ J : Finset I', (J.card : ℕ∞) ≤ M'.eRk (⋃ i ∈ J, A' i)) :
    ∃ f : I' → E, Function.Injective f ∧ (∀ i, f i ∈ A' i) ∧ M'.Indep (Set.range f) := by
  classical
  induction n using Nat.strongRecOn generalizing I' M' A' with
  | ind n ih =>
    classical
    by_cases hI0 : Fintype.card I' = 0
    · have hEmpty : IsEmpty I' := Fintype.card_eq_zero_iff.mp hI0
      refine ⟨isEmptyElim, isEmptyElim, isEmptyElim, ?_⟩
      have hrange : Set.range (isEmptyElim : I' → E) = ∅ := Set.range_eq_empty _
      rw [hrange]
      exact M'.empty_indep
    · have hpos : 0 < Fintype.card I' := Nat.pos_of_ne_zero hI0
      by_cases hStrict : ∀ s : Finset I', s.Nonempty → s ≠ Finset.univ →
          (s.card : ℕ∞) < M'.eRk (⋃ i ∈ s, A' i)
      · classical
        have hNe : Nonempty I' := Fintype.card_pos_iff.mp hpos
        let x0 := Classical.arbitrary I'
        have h1 : ((1 : ℕ) : ℕ∞) ≤ M'.eRk (A' x0) := by
          have h := hcond {x0}
          simpa using h
        obtain ⟨B0, hB0⟩ := M'.exists_isBasis' (A' x0)
        have hB0e : B0.encard = M'.eRk (A' x0) := hB0.encard_eq_eRk
        have hB0ne : B0.Nonempty := by
          by_contra hcon
          rw [Set.not_nonempty_iff_eq_empty] at hcon
          subst hcon
          rw [Set.encard_empty] at hB0e
          rw [← hB0e] at h1
          simp at h1
        obtain ⟨e, heB0⟩ := hB0ne
        have he_mem : e ∈ A' x0 := hB0.subset heB0
        have he_loop : M'.IsNonloop e := by
          rw [← Matroid.indep_singleton]
          exact hB0.indep.subset (Set.singleton_subset_iff.mpr heB0)
        let I'' := { x' : I' // x' ≠ x0 }
        let M'' := Matroid.contract M' {e}
        let A'' : I'' → Set E := fun x'' => A' x''.1
        have hcard_eq : Fintype.card I'' = Fintype.card I' - 1 := Set.card_ne_eq x0
        have hcard'' : Fintype.card I'' < n := by omega
        have hcond'' : ∀ J : Finset I'', (J.card : ℕ∞) ≤ M''.eRk (⋃ i ∈ J, A'' i) := by
          intro J
          by_cases hJe : J = ∅
          · subst hJe
            simp
          · have hJne : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr hJe
            let JJ : Finset I' := J.image (fun x'' => x''.1)
            have hJJcard : JJ.card = J.card :=
              Finset.card_image_of_injective J Subtype.val_injective
            have hx0JJ : x0 ∉ JJ := by
              rintro hx
              obtain ⟨x'', _, hfx⟩ := Finset.mem_image.mp hx
              exact x''.2 hfx
            have hJJne : JJ ≠ Finset.univ := by
              intro huniv
              rw [huniv] at hx0JJ
              exact hx0JJ (Finset.mem_univ x0)
            obtain ⟨x0'', hx0''⟩ := hJne
            have hJJnonempty : JJ.Nonempty := ⟨_, Finset.mem_image.mpr ⟨x0'', hx0'', rfl⟩⟩
            have hlt := hStrict JJ hJJnonempty hJJne
            have hunion : (⋃ i ∈ J, A'' i) = (⋃ j ∈ JJ, A' j) := by
              ext y
              simp only [Set.mem_iUnion]
              constructor
              · rintro ⟨x'', hx'', hy⟩
                exact ⟨x''.1, Finset.mem_image.mpr ⟨x'', hx'', rfl⟩, hy⟩
              · rintro ⟨j, hj, hy⟩
                obtain ⟨x'', hx'', rfl⟩ := Finset.mem_image.mp hj
                exact ⟨x'', hx'', hy⟩
            have hle := contract_singleton_eRk_ge M' e he_loop (⋃ j ∈ JJ, A' j) JJ.card hlt
            rw [← hunion] at hle
            rwa [hJJcard] at hle
        obtain ⟨f'', hf''_inj, hf''_mem, hf''_indep⟩ := ih _ hcard'' M'' A'' le_rfl hcond''
        refine ⟨fun z => if h : z = x0 then e else f'' ⟨z, h⟩, ?_, ?_, ?_⟩
        · rintro z₁ z₂ h12
          have key : ∀ {x : I''}, e ≠ f'' x := by
            intro x hcon
            have hmem : f'' x ∈ Set.range f'' := Set.mem_range_self x
            have hsub : Set.range f'' ⊆ M''.E := hf''_indep.subset_ground
            have heE : f'' x ∈ M''.E := hsub hmem
            rw [← hcon] at heE
            have heE' : e ∈ M'.E \ {e} := heE
            simp at heE'
          by_cases h₁ : z₁ = x0 <;> by_cases h₂ : z₂ = x0 <;>
            simp only [h₁, ↓reduceDIte, h₂, ne_eq, key, key.symm, hf''_inj.eq_iff] at h12 ⊢
          · exact congrArg Subtype.val h12
        · intro z
          simp only
          split_ifs with hz
          · rwa [hz]
          · exact hf''_mem ⟨z, hz⟩
        · have hrange : Set.range (fun z => if h : z = x0 then e else f'' ⟨z, h⟩)
              = insert e (Set.range f'') := by
            ext y
            constructor
            · rintro ⟨z, rfl⟩
              by_cases hz : z = x0
              · change (if h : z = x0 then e else f'' ⟨z, h⟩) ∈ insert e (Set.range f'')
                rw [dite_eq_left hz]
                simp
              · change (if h : z = x0 then e else f'' ⟨z, h⟩) ∈ insert e (Set.range f'')
                rw [dite_eq_right hz]
                exact Set.mem_insert_of_mem e (Set.mem_range_self _)
            · intro hy
              rw [Set.mem_insert_iff] at hy
              rcases hy with rfl | ⟨x'', rfl⟩
              · exact ⟨x0, by simp⟩
              · refine ⟨x''.1, ?_⟩
                change (if h : x''.1 = x0 then e else f'' ⟨x''.1, h⟩) = f'' x''
                rw [dite_eq_right x''.2]
          rw [hrange]
          exact (he_loop.contractElem_indep_iff.mp hf''_indep).2
      · push Not at hStrict
        obtain ⟨s, hs_ne, hs_univ, hs_ge⟩ := hStrict
        have hs_le := hcond s
        have hs_eq : (s.card : ℕ∞) = M'.eRk (⋃ i ∈ s, A' i) := le_antisymm hs_le hs_ge
        have hs_pos : 0 < s.card := Finset.card_pos.mpr hs_ne
        have hcard0 : Fintype.card ↥s < n := by
          rw [Fintype.card_coe]
          have hlt : s.card < Fintype.card I' := (Finset.card_lt_iff_ne_univ _).mpr hs_univ
          omega
        have hcond0 : ∀ T : Finset ↥s, (T.card : ℕ∞) ≤ M'.eRk (⋃ i ∈ T, A' i.1) := by
          intro T
          let JJ : Finset I' := T.image (fun x => x.1)
          have hJJcard : JJ.card = T.card := Finset.card_image_of_injective T Subtype.val_injective
          have hunion : (⋃ i ∈ T, A' i.1) = (⋃ j ∈ JJ, A' j) := by
            ext y
            simp only [Set.mem_iUnion]
            constructor
            · rintro ⟨x, hx, hy⟩
              exact ⟨x.1, Finset.mem_image.mpr ⟨x, hx, rfl⟩, hy⟩
            · rintro ⟨j, hj, hy⟩
              obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
              exact ⟨x, hx, hy⟩
          have hle := hcond JJ
          rw [← hunion] at hle
          rwa [hJJcard] at hle
        obtain ⟨f0, hf0_inj, hf0_mem, hf0_indep⟩ := ih _ hcard0 M' (fun x : ↥s => A' x.1) le_rfl
            hcond0
        have hB0card : (Set.range f0).encard = (s.card : ℕ∞) := by
          classical
          let F : Finset E := Finset.univ.image f0
          have hFcard : F.card = s.card := by
            rw [Finset.card_image_of_injective _ hf0_inj, Finset.card_univ, Fintype.card_coe]
          have hFcoe : (F : Set E) = Set.range f0 := by
            change ((Finset.univ.image f0 : Finset E) : Set E) = Set.range f0
            rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
          rw [← hFcoe, Set.encard_coe_eq_coe_finsetCard, hFcard]
        have hB0sub : Set.range f0 ⊆ (⋃ i ∈ s, A' i) := by
          rintro y ⟨x, rfl⟩
          simp only [Set.mem_iUnion]
          exact ⟨x.1, x.2, hf0_mem x⟩
        have hBasis : M'.IsBasis' (Set.range f0) (⋃ i ∈ s, A' i) := by
          apply hf0_indep.isBasis'_of_eRk_ge (Set.toFinite _) hB0sub
          rw [hf0_indep.eRk_eq_encard, ← hs_eq, hB0card]
        let C := { x : I' // x ∉ s }
        let M1 := Matroid.contract M' (Set.range f0)
        let A1 : C → Set E := fun x => A' x.1
        have hcardC : Fintype.card C < n := by
          have eC : Fintype.card C = Fintype.card I' - s.card := by
            have h1 : Fintype.card C = Fintype.card { x : I' // x ∉ s } := rfl
            rw [h1, Fintype.card_subtype_compl (· ∈ s)]
            congr 1
            exact Fintype.card_coe s
          omega
        have hcondC : ∀ T : Finset C, (T.card : ℕ∞) ≤ M1.eRk (⋃ i ∈ T, A1 i) := by
          intro T
          let K : Finset I' := T.image (fun x => x.1)
          have hKcard : K.card = T.card := Finset.card_image_of_injective T Subtype.val_injective
          have hKdisj : Disjoint K s := by
            rw [Finset.disjoint_left]
            rintro j hj js
            obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hj
            exact x.2 js
          have hunion2 : (⋃ i ∈ T, A1 i) ∪ (⋃ j ∈ s, A' j) = (⋃ j ∈ K ∪ s, A' j) := by
            ext y
            simp only [Set.mem_union, Set.mem_iUnion]
            constructor
            · rintro (⟨x, hx, hy⟩ | ⟨j, hj, hy⟩)
              · exact ⟨x.1, Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨x, hx, rfl⟩)), hy⟩
              · exact ⟨j, Finset.mem_union.mpr (Or.inr hj), hy⟩
            · rintro ⟨j, hj, hy⟩
              rw [Finset.mem_union] at hj
              rcases hj with hjK | hjs
              · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hjK
                exact Or.inl ⟨x, hx, hy⟩
              · exact Or.inr ⟨j, hjs, hy⟩
          have hcardKs : (K ∪ s).card = T.card + s.card := by
            rw [Finset.card_union_of_disjoint hKdisj, hKcard]
          have hY : ((T.card + s.card : ℕ) : ℕ∞) ≤ M'.eRk ((⋃ i ∈ T, A1 i) ∪ Set.range f0) := by
            have hstep : M'.eRk ((⋃ i ∈ T, A1 i) ∪ Set.range f0) = M'.eRk (⋃ j ∈ K ∪ s, A' j) := by
              rw [Set.union_comm, hBasis.eRk_eq_eRk_union, Set.union_comm, hunion2]
            rw [hstep]
            have hle := hcond (K ∪ s)
            rw [hcardKs] at hle
            exact hle
          have hleC := contract_set_eRk_ge M' (Set.range f0) hf0_indep (⋃ i ∈ T, A1 i) T.card s.card
              hB0card hY
          exact hleC
        obtain ⟨f1, hf1_inj, hf1_mem, hf1_indep⟩ := ih _ hcardC M1 A1 le_rfl hcondC
        have hdisj : Disjoint (Set.range f1) (Set.range f0) := by
          rw [Set.disjoint_left]
          rintro y hy hyB
          have hsub : Set.range f1 ⊆ M1.E := hf1_indep.subset_ground
          have hyE := hsub hy
          have hyE' : y ∈ M'.E \ Set.range f0 := hyE
          exact ((Set.mem_sdiff _).mp hyE').2 hyB
        have key0 : ∀ {x : C}, f1 x ∉ Set.range f0 :=
          fun {x} => Set.disjoint_left.mp hdisj (Set.mem_range_self x)
        have hcross : ∀ {x : I'} {hx : x ∈ s} {x' : I'} {hx' : x' ∉ s},
            f0 ⟨x, hx⟩ ≠ f1 ⟨x', hx'⟩ := by
          intro x hx x' hx' hcon
          have hmem : f0 ⟨x, hx⟩ ∈ Set.range f0 := Set.mem_range_self _
          rw [hcon] at hmem
          exact key0 hmem
        refine ⟨fun x => if h : x ∈ s then f0 ⟨x, h⟩ else f1 ⟨x, h⟩, ?_, ?_, ?_⟩
        · exact hf0_inj.dite _ hf1_inj hcross
        · intro z
          simp only
          split_ifs with hz
          · exact hf0_mem ⟨z, hz⟩
          · exact hf1_mem ⟨z, hz⟩
        · have hrange : Set.range (fun x => if h : x ∈ s then f0 ⟨x, h⟩ else f1 ⟨x, h⟩)
              = Set.range f0 ∪ Set.range f1 := by
            ext y
            constructor
            · rintro ⟨z, rfl⟩
              by_cases hz : z ∈ s
              · change (if h : z ∈ s then f0 ⟨z, h⟩ else f1 ⟨z, h⟩) ∈ _ ∪ _
                rw [dite_eq_left hz]
                simp
              · change (if h : z ∈ s then f0 ⟨z, h⟩ else f1 ⟨z, h⟩) ∈ _ ∪ _
                rw [dite_eq_right hz]
                simp
            · intro hy
              rw [Set.mem_union] at hy
              rcases hy with ⟨x0, rfl⟩ | ⟨x1, rfl⟩
              · refine ⟨x0.1, ?_⟩
                change (if h : (x0 : I') ∈ s then f0 ⟨x0.1, h⟩ else f1 ⟨x0.1, h⟩) = f0 x0
                rw [dite_eq_left x0.2]
              · refine ⟨x1.1, ?_⟩
                change (if h : (x1 : I') ∈ s then f0 ⟨x1.1, h⟩ else f1 ⟨x1.1, h⟩) = f1 x1
                have hx1 : (x1 : I') ∉ s := x1.2
                rw [dite_eq_right hx1]
          rw [hrange]
          have hindep := (hf0_indep.contract_indep_iff.mp hf1_indep).2
          rwa [Set.union_comm] at hindep

/--
**Rado's theorem on independent transversals, arbitrary ground set.** Let $I$ and $E$ be finite
sets, let $M$ be a matroid with ground set $E(M) \subseteq E$, and let $(A_i)_{i \in I}$ be a
family of subsets of $E$. Then there is an injective map $f : I \to E$ such that $f(i) \in A_i$
for every $i \in I$ and the image $f(I)$ is independent in $M$, if and only if
$|J| \le r_M\bigl(\bigcup_{i \in J} A_i\bigr)$ for every $J \subseteq I$, where $r_M(X)$ denotes
the rank in $M$ of $X \cap E(M)$.
-/
theorem rado_matroidal_marriage' {I E : Type*} [Finite I] [Finite E] {M : Matroid E}
    (A : I → Set E) :
    (∃ f : I → E, Function.Injective f ∧ (∀ i, f i ∈ A i) ∧
      M.Indep (Set.range f)) ↔
    ∀ J : Finset I, (J.card : ℕ∞) ≤ M.eRk (⋃ i ∈ J, A i) := by
  classical
  have := Fintype.ofFinite I
  constructor
  · rintro ⟨f, hf_inj, hf_mem, hf_indep⟩ J
    have h_img_sub : (f '' (↑J : Set I)) ⊆ (⋃ i ∈ (↑J : Set I), A i) := by
      rintro y ⟨j, hj, rfl⟩
      exact Set.mem_biUnion hj (hf_mem j)
    have h_indep_img : M.Indep (f '' (↑J : Set I)) :=
      hf_indep.subset (Set.image_subset_range f _)
    calc (J.card : ℕ∞) = (f '' (↑J : Set I)).encard := by
          rw [hf_inj.encard_image, Set.encard_coe_eq_coe_finsetCard]
      _ = M.eRk (f '' (↑J : Set I)) := by rw [h_indep_img.eRk_eq_encard]
      _ ≤ M.eRk (⋃ i ∈ (↑J : Set I), A i) := (Matroid.eRk_mono M) h_img_sub
  · intro hHall
    exact rado_aux (Fintype.card I) M A le_rfl hHall

set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
set_option linter.unusedVariables false in
/--
**Rado's theorem on independent transversals.** Let $I$ and $E$ be finite sets, let $M$ be a
matroid whose ground set is all of $E$, and let $(A_i)_{i \in I}$ be a family of subsets of $E$.
Then there is an injective map $f : I \to E$ such that $f(i) \in A_i$ for every $i \in I$ and
the image $f(I)$ is independent in $M$, if and only if
$|J| \le r_M\bigl(\bigcup_{i \in J} A_i\bigr)$ for every $J \subseteq I$, where $r_M$ is the rank
function of $M$.

The hypothesis that the ground set of $M$ is all of $E$ is not needed.

Proves `Wanted` entry `rado_matroidal_marriage`.

Source: R. Rado, Quart. J. Math. os-13 (1942), DOI 10.1093/qmath/os-13.1.83.
-/
theorem rado_matroidal_marriage
    {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
    {M : Matroid E} (hM : M.E = Set.univ) (A : I → Set E) :
    (∃ f : I → E, Function.Injective f ∧ (∀ i, f i ∈ A i) ∧
      M.Indep (Set.range f)) ↔
    ∀ J : Finset I, (J.card : ℕ∞) ≤ M.eRk (⋃ i ∈ J, A i) :=
  rado_matroidal_marriage' A

end MathlibExt.Combinatorics.Matroid.RadoWanted
