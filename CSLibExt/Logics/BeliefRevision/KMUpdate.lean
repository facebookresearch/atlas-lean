/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.BeliefRevision.KMRevision
public import Mathlib.Data.Fin.VecNotation

/-!
# Katsuno–Mendelzon update

The Katsuno–Mendelzon update postulates (U1)–(U8) on finite model sets and the representation
theorem (Theorem 3.1): an operator satisfies (U1)–(U8) iff it is induced by a faithful
assignment of partial preorders, one per interpretation, and iff it is induced by such an
assignment of partial orders. Winslett's possible models approach (PMA) is the instance given
by inclusion of difference sets; Example 3.1 shows PMA violates the revision postulate (R2).

Formulas are represented by their model sets (`Interp` and `minSet` are imported from
`KMRevision`), so (U4) is congruence in the model sets and empty model sets are allowed.

## References

* H. Katsuno and A. O. Mendelzon, *On the Difference between Updating a Knowledge Base and
  Revising It*. A preliminary version appeared in KR 1991. Locators follow the 21-page
  extended version: complete formulas §2 (p. 4); PMA §3.1 (p. 6); Example 3.1 (p. 7);
  (U1)–(U8) §3.2 (p. 7); Theorem 3.1 in the Appendix (p. 16), labelled Theorem 3.4 in the
  main text (p. 9); the identity-or-strict-part conversion in the proof sketch (p. 10).
* M. Winslett, *Reasoning about Action Using a Possible Models Approach*, AAAI 1988.
-/

@[expose] public section

namespace Cslib.BeliefRevision

/-! ## Update definitions -/

/-- A model set `A` is complete (KM §2) if for every sentence `C` it implies `C` or implies
`¬C`, that is `A ⊆ C` or `A ⊆ Cᶜ`. The empty (inconsistent) model set is complete; see
`isComplete_iff_card_le_one`. -/
def IsComplete {σ : Type*} [Fintype σ] [DecidableEq σ] (A : Finset (Interp σ)) : Prop :=
  ∀ C : Finset (Interp σ), A ⊆ C ∨ A ⊆ Cᶜ

/-- The Katsuno–Mendelzon update postulates (U1)–(U8) for an operator on model sets, after
Katsuno & Mendelzon, *On the Difference between Updating a Knowledge Base and Revising It*,
§3.2. For model sets `A`, `A₁`, `A₂` (old knowledge bases) and `B`, `B₁`, `B₂`, `C`
(sentences): (U1) the update implies the new sentence; (U2) if `A ⊆ B` the update is `A`;
(U3) nonempty `A` and `B` give a nonempty update; (U4) syntax irrelevance, here congruence in
the model sets; (U5) `upd A B ∩ C ⊆ upd A (B ∩ C)`; (U6) if `upd A B₁ ⊆ B₂` and
`upd A B₂ ⊆ B₁` then `upd A B₁ = upd A B₂`; (U7) if `A` is complete then
`upd A B₁ ∩ upd A B₂ ⊆ upd A (B₁ ∪ B₂)`; (U8) `upd (A₁ ∪ A₂) B = upd A₁ B ∪ upd A₂ B`. -/
structure SatisfiesKMUpdate {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ)) : Prop where
  u1 : ∀ A B, upd A B ⊆ B
  u2 : ∀ A B, A ⊆ B → upd A B = A
  u3 : ∀ A B, A.Nonempty → B.Nonempty → (upd A B).Nonempty
  u4 : ∀ A A' B B', A = A' → B = B' → upd A B = upd A' B'
  u5 : ∀ A B C, upd A B ∩ C ⊆ upd A (B ∩ C)
  u6 : ∀ A B₁ B₂, upd A B₁ ⊆ B₂ → upd A B₂ ⊆ B₁ → upd A B₁ = upd A B₂
  u7 : ∀ A B₁ B₂, IsComplete A → upd A B₁ ∩ upd A B₂ ⊆ upd A (B₁ ∪ B₂)
  u8 : ∀ A₁ A₂ B, upd (A₁ ∪ A₂) B = upd A₁ B ∪ upd A₂ B

/-- A faithful update assignment (KM §3.2): to each interpretation `I`, a partial preorder
`ord I` on interpretations (reflexive and transitive, not necessarily total), where
`ord I J K` reads `J ≤_I K`, such that `I` is strictly below every other interpretation:
`ord I I J ∧ ¬ ord I J I` whenever `I ≠ J`. Unlike the revision `FaithfulAssignment`, the order
is indexed by an interpretation rather than a model set, and need not be total. -/
structure FaithfulUpdateAssignment (σ : Type*) [Fintype σ] [DecidableEq σ] where
  ord : Interp σ → Interp σ → Interp σ → Prop
  refl : ∀ I J, ord I J J
  trans : ∀ I J K L, ord I J K → ord I K L → ord I J L
  faithful : ∀ I J, I ≠ J → ord I I J ∧ ¬ ord I J I

/-- The identity-or-strict-part reflexification of a relation `R` (KM, proof of Theorem 3.1,
2 ⇒ 3): `J` precedes `K` iff `J = K` or `R J K ∧ ¬ R K J`. It has the same strict part as `R`,
hence the same minimal elements, and it is antisymmetric. It breaks no ties: distinct
`R`-equivalent elements become incomparable. -/
def idOrStrict {α : Type*} (R : α → α → Prop) (J K : α) : Prop :=
  J = K ∨ (R J K ∧ ¬ R K J)

/-- Winslett's `Diff(I, J)` (KM §3.1): the atoms on which `I` and `J` differ. -/
def pmaDiff {σ : Type*} [Fintype σ] [DecidableEq σ] (I J : Interp σ) : Finset σ :=
  Finset.univ.filter fun a => I a ≠ J a

/-- Winslett's order relative to `I` (KM §3.1): `pmaLe I J₁ J₂`, written `J₁ ≤_{I,pma} J₂`,
holds iff `Diff(I, J₁) ⊆ Diff(I, J₂)`. Closeness is inclusion of the sets of changed atoms, not
comparison of their sizes. -/
def pmaLe {σ : Type*} [Fintype σ] [DecidableEq σ] (I J₁ J₂ : Interp σ) : Prop :=
  pmaDiff I J₁ ⊆ pmaDiff I J₂

/-- The PMA orders form a faithful update assignment: each `pmaLe I` is reflexive and
transitive, and `I` is its strict minimum because `Diff(I, I)` is empty. -/
def pmaAssignment (σ : Type*) [Fintype σ] [DecidableEq σ] : FaithfulUpdateAssignment σ where
  ord := pmaLe
  refl := by
    intro I J
    exact Finset.Subset.refl _
  trans := by
    intro I J K L h₁ h₂
    exact Finset.Subset.trans h₁ h₂
  faithful := by
    intro I J hIJ
    unfold pmaLe
    refine ⟨?_, ?_⟩
    · intro a ha
      simp [pmaDiff] at ha
    · intro h
      apply hIJ
      funext a
      by_contra hne
      have ha : a ∈ pmaDiff I J := Finset.mem_filter.mpr ⟨Finset.mem_univ a, hne⟩
      have hmem := h ha
      simp [pmaDiff] at hmem

/-- Winslett's possible models approach (KM §3.1): each model `I` of the old knowledge base
selects the `≤_{I,pma}`-minimal models of the new sentence (KM's `Incorporate(Mod(μ), I)`), and
the update is the union of these selections. -/
noncomputable def pmaUpdate {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A B : Finset (Interp σ)) : Finset (Interp σ) :=
  A.biUnion fun I => minSet (pmaLe I) B

/-! ## The representation theorem and its instances -/

/-- A model set is complete iff it has at most one model; the empty (inconsistent) model set
is complete. -/
theorem isComplete_iff_card_le_one {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Finset (Interp σ)) : IsComplete A ↔ A.card ≤ 1 := by
  classical
  constructor
  · intro h
    by_contra hlt
    have h1lt : 1 < A.card := not_le.mp hlt
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp h1lt
    have hC := h {x}
    rcases hC with hsub | hsub
    · have hyx : y ∈ ({x} : Finset (Interp σ)) := hsub hy
      rw [Finset.mem_singleton] at hyx
      exact hxy hyx.symm
    · have hxc : x ∈ ({x} : Finset (Interp σ))ᶜ := hsub hx
      rw [Finset.mem_compl, Finset.mem_singleton] at hxc
      exact hxc rfl
  · intro hcard C
    by_cases h0 : A.card = 0
    · have hA : A = ∅ := Finset.card_eq_zero.mp h0
      left
      rw [hA]
      exact Finset.empty_subset C
    · have h1 : A.card = 1 := by omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
      by_cases hxC : x ∈ C
      · left
        rw [hx]
        exact Finset.singleton_subset_iff.mpr hxC
      · right
        rw [hx]
        exact Finset.singleton_subset_iff.mpr (Finset.mem_compl.mpr hxC)

/-- `idOrStrict R` is reflexive. -/
theorem idOrStrict_refl {α : Type*} (R : α → α → Prop) (J : α) : idOrStrict R J J := by
  exact Or.inl rfl

/-- `idOrStrict R` is transitive when `R` is. -/
theorem idOrStrict_trans {α : Type*} {R : α → α → Prop}
    (hR : ∀ J K L, R J K → R K L → R J L) (J K L : α) :
    idOrStrict R J K → idOrStrict R K L → idOrStrict R J L := by
  intro h1 h2
  unfold idOrStrict at h1 h2 ⊢
  rcases h1 with rfl | ⟨hJK, hnKJ⟩
  · exact h2
  · rcases h2 with rfl | ⟨hKL, hnLK⟩
    · exact Or.inr ⟨hJK, hnKJ⟩
    · refine Or.inr ⟨hR _ _ _ hJK hKL, ?_⟩
      intro hLJ
      exact hnLK (hR _ _ _ hLJ hJK)

/-- `idOrStrict R` is antisymmetric, for every relation `R`. -/
theorem idOrStrict_antisymm {α : Type*} (R : α → α → Prop) (J K : α) :
    idOrStrict R J K → idOrStrict R K J → J = K := by
  intro h1 h2
  unfold idOrStrict at h1 h2
  rcases h1 with rfl | ⟨hJK, hnKJ⟩
  · rfl
  · rcases h2 with hKJ | ⟨hKJ, hnJK⟩
    · exact hKJ.symm
    · exact (hnKJ hKJ).elim

/-- `idOrStrict R` has the same strict part as `R` (KM p. 10: `J <_I J'` iff `J <'_I J'`).
In particular it keeps faithfulness. -/
theorem idOrStrict_strict_iff {α : Type*} (R : α → α → Prop) (J K : α) :
    (idOrStrict R J K ∧ ¬ idOrStrict R K J) ↔ (R J K ∧ ¬ R K J) := by
  unfold idOrStrict
  constructor
  · rintro ⟨h1, hn2⟩
    rcases h1 with rfl | ⟨hJK, hnKJ⟩
    · exact (hn2 (Or.inl rfl)).elim
    · exact ⟨hJK, hnKJ⟩
  · rintro ⟨hJK, hnKJ⟩
    refine ⟨Or.inr ⟨hJK, hnKJ⟩, ?_⟩
    rintro (rfl | ⟨hKJ, -⟩)
    · exact hnKJ hJK
    · exact hnKJ hKJ

/-- The identity-or-strict-part conversion keeps every Min set. -/
theorem minSet_idOrStrict {σ : Type*} [Fintype σ] [DecidableEq σ]
    (le : Interp σ → Interp σ → Prop) (B : Finset (Interp σ)) :
    minSet (idOrStrict le) B = minSet le B := by
  apply Finset.ext
  intro I
  simp only [mem_minSet, idOrStrict_strict_iff]

private theorem biUnion_minSet_subset {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : FaithfulUpdateAssignment σ) (A B : Finset (Interp σ)) :
    A.biUnion (fun I => minSet (G.ord I) B) ⊆ B := by
  classical
  intro J hJ
  obtain ⟨I, _, hIJ⟩ := Finset.mem_biUnion.mp hJ
  exact minSet_subset _ _ hIJ

private theorem mem_minSet_of_faithful_mem {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : FaithfulUpdateAssignment σ) (I : Interp σ) (B : Finset (Interp σ))
    (hIB : I ∈ B) :
    I ∈ minSet (G.ord I) B := by
  classical
  rw [mem_minSet]
  refine ⟨hIB, ?_⟩
  intro J hJB hlt
  obtain ⟨_, hnle⟩ := hlt
  apply hnle
  by_cases hJI : J = I
  · rw [hJI]
    exact G.refl I I
  · have hne : I ≠ J := fun h => hJI h.symm
    exact (G.faithful I J hne).1

private theorem minSet_eq_singleton_of_faithful_mem {σ : Type*} [Fintype σ]
    [DecidableEq σ] (G : FaithfulUpdateAssignment σ) (I : Interp σ)
    (B : Finset (Interp σ)) (hIB : I ∈ B) :
    minSet (G.ord I) B = {I} := by
  classical
  apply Finset.ext
  intro K
  rw [Finset.mem_singleton]
  constructor
  · intro hK
    rw [mem_minSet] at hK
    obtain ⟨_, hmin⟩ := hK
    by_contra hKI
    have hne : I ≠ K := fun h => hKI h.symm
    have hfaith := G.faithful I K hne
    exact hmin I hIB hfaith
  · intro hKI
    rw [hKI]
    exact mem_minSet_of_faithful_mem G I B hIB

private theorem biUnion_minSet_eq_self_of_subset {σ : Type*} [Fintype σ]
    [DecidableEq σ] (G : FaithfulUpdateAssignment σ) (A B : Finset (Interp σ))
    (hAB : A ⊆ B) :
    A.biUnion (fun I => minSet (G.ord I) B) = A := by
  classical
  apply Finset.ext
  intro J
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨I, hIA, hIJ⟩
    have hIB : I ∈ B := hAB hIA
    have heq := minSet_eq_singleton_of_faithful_mem G I B hIB
    rw [heq, Finset.mem_singleton] at hIJ
    exact hIJ.symm ▸ hIA
  · intro hJA
    refine ⟨J, hJA, ?_⟩
    exact mem_minSet_of_faithful_mem G J B (hAB hJA)

private theorem mem_minSet_inter_of_mem_minSet {σ : Type*} [Fintype σ]
    [DecidableEq σ] (le : Interp σ → Interp σ → Prop) (B C : Finset (Interp σ))
    (J : Interp σ) (hJB : J ∈ minSet le B) (hJC : J ∈ C) :
    J ∈ minSet le (B ∩ C) := by
  classical
  rw [mem_minSet] at hJB ⊢
  obtain ⟨hB, hmin⟩ := hJB
  refine ⟨Finset.mem_inter.mpr ⟨hB, hJC⟩, ?_⟩
  intro K hKC hlt
  have hKB : K ∈ B := (Finset.mem_inter.mp hKC).1
  exact hmin K hKB hlt

private theorem biUnion_minSet_inter_subset {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : FaithfulUpdateAssignment σ) (A B C : Finset (Interp σ)) :
    A.biUnion (fun I => minSet (G.ord I) B) ∩ C ⊆
      A.biUnion (fun I => minSet (G.ord I) (B ∩ C)) := by
  classical
  intro J hJ
  rw [Finset.mem_inter] at hJ
  obtain ⟨hJB, hJC⟩ := hJ
  obtain ⟨I, hIA, hIJ⟩ := Finset.mem_biUnion.mp hJB
  rw [Finset.mem_biUnion]
  refine ⟨I, hIA, ?_⟩
  exact mem_minSet_inter_of_mem_minSet _ _ _ _ hIJ hJC

private theorem mem_minSet_union_of_mem_both {σ : Type*} [Fintype σ]
    [DecidableEq σ] (le : Interp σ → Interp σ → Prop) (B₁ B₂ : Finset (Interp σ))
    (J : Interp σ) (h1 : J ∈ minSet le B₁) (h2 : J ∈ minSet le B₂) :
    J ∈ minSet le (B₁ ∪ B₂) := by
  classical
  rw [mem_minSet] at h1 h2 ⊢
  obtain ⟨hB1, hmin1⟩ := h1
  obtain ⟨_, hmin2⟩ := h2
  refine ⟨Finset.mem_union.mpr (Or.inl hB1), ?_⟩
  intro K hKU hlt
  have hKB : K ∈ B₁ ∨ K ∈ B₂ := Finset.mem_union.mp hKU
  cases hKB with
  | inl hK1 => exact hmin1 K hK1 hlt
  | inr hK2 => exact hmin2 K hK2 hlt

private theorem biUnion_minSet_singleton_inter {σ : Type*} [Fintype σ]
    [DecidableEq σ] (G : FaithfulUpdateAssignment σ) (I : Interp σ)
    (B₁ B₂ : Finset (Interp σ)) :
    ({I} : Finset (Interp σ)).biUnion (fun J => minSet (G.ord J) B₁) ∩
        ({I} : Finset (Interp σ)).biUnion (fun J => minSet (G.ord J) B₂) ⊆
      ({I} : Finset (Interp σ)).biUnion (fun J => minSet (G.ord J) (B₁ ∪ B₂)) := by
  classical
  intro J hJ
  rw [Finset.mem_inter] at hJ
  obtain ⟨h1, h2⟩ := hJ
  obtain ⟨K1, hK1, hJK1⟩ := Finset.mem_biUnion.mp h1
  obtain ⟨K2, hK2, hJK2⟩ := Finset.mem_biUnion.mp h2
  rw [Finset.mem_singleton] at hK1 hK2
  rw [hK1] at hJK1
  rw [hK2] at hJK2
  rw [Finset.mem_biUnion]
  refine ⟨I, Finset.mem_singleton_self I, ?_⟩
  exact mem_minSet_union_of_mem_both _ _ _ _ hJK1 hJK2

private theorem biUnion_union_index {σ : Type*} [Fintype σ] [DecidableEq σ]
    (f : Interp σ → Finset (Interp σ)) (A₁ A₂ : Finset (Interp σ)) :
    (A₁ ∪ A₂).biUnion f = A₁.biUnion f ∪ A₂.biUnion f := by
  classical
  apply Finset.ext
  intro J
  rw [Finset.mem_biUnion, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_biUnion]
  constructor
  · rintro ⟨I, hIA, hIJ⟩
    have h : I ∈ A₁ ∨ I ∈ A₂ := Finset.mem_union.mp hIA
    cases h with
    | inl h1 => exact Or.inl ⟨I, h1, hIJ⟩
    | inr h2 => exact Or.inr ⟨I, h2, hIJ⟩
  · rintro (⟨I, hIA1, hIJ⟩ | ⟨I, hIA2, hIJ⟩)
    · exact ⟨I, Finset.mem_union.mpr (Or.inl hIA1), hIJ⟩
    · exact ⟨I, Finset.mem_union.mpr (Or.inr hIA2), hIJ⟩

private theorem minSet_nonempty_of_nonempty_aux {σ : Type*} [Fintype σ]
    [DecidableEq σ] (le : Interp σ → Interp σ → Prop)
    (htrans : ∀ J K L, le J K → le K L → le J L) (B : Finset (Interp σ))
    (hne : B.Nonempty) : (minSet le B).Nonempty := by
  classical
  revert hne
  induction B using Finset.induction with
  | empty =>
    intro hne
    obtain ⟨x, hx⟩ := hne
    exact (Finset.notMem_empty x hx).elim
  | insert a s _ IH =>
    intro hne
    by_cases hs : s.Nonempty
    · obtain ⟨b, hb⟩ := IH hs
      rw [mem_minSet] at hb
      obtain ⟨hbs, hmin⟩ := hb
      by_cases hab : le a b ∧ ¬ le b a
      · refine ⟨a, ?_⟩
        rw [mem_minSet]
        refine ⟨Finset.mem_insert_self a s, ?_⟩
        intro K hK hlt
        have hKa : K = a ∨ K ∈ s := Finset.mem_insert.mp hK
        cases hKa with
        | inl heq =>
          rw [heq] at hlt
          obtain ⟨h1, h2⟩ := hlt
          exact h2 h1
        | inr hKs =>
          obtain ⟨hltKA, _⟩ := hlt
          obtain ⟨hleAB, hnleBA⟩ := hab
          have hleKB : le K b := htrans _ _ _ hltKA hleAB
          have hnleBK : ¬ le b K := by
            intro hBK
            have hBA : le b a := htrans _ _ _ hBK hltKA
            exact hnleBA hBA
          exact hmin K hKs ⟨hleKB, hnleBK⟩
      · refine ⟨b, ?_⟩
        rw [mem_minSet]
        refine ⟨Finset.mem_insert_of_mem hbs, ?_⟩
        intro K hK hlt
        have hKa : K = a ∨ K ∈ s := Finset.mem_insert.mp hK
        cases hKa with
        | inl heq =>
          rw [heq] at hlt
          exact hab hlt
        | inr hKs =>
          exact hmin K hKs hlt
    · refine ⟨a, ?_⟩
      rw [mem_minSet]
      refine ⟨Finset.mem_insert_self a s, ?_⟩
      intro K hK hlt
      have hKa : K = a ∨ K ∈ s := Finset.mem_insert.mp hK
      cases hKa with
      | inl heq =>
        rw [heq] at hlt
        obtain ⟨h1, h2⟩ := hlt
        exact h2 h1
      | inr hKs =>
        exact (hs ⟨K, hKs⟩).elim

private theorem biUnion_minSet_nonempty {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : FaithfulUpdateAssignment σ) (A B : Finset (Interp σ))
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (A.biUnion fun I => minSet (G.ord I) B).Nonempty := by
  classical
  obtain ⟨I, hIA⟩ := hA
  obtain ⟨J, hJB⟩ := minSet_nonempty_of_nonempty_aux (G.ord I)
    (G.trans I) B hB
  refine ⟨J, ?_⟩
  rw [Finset.mem_biUnion]
  exact ⟨I, hIA, hJB⟩

private theorem biUnion_minSet_u7_of_complete {σ : Type*} [Fintype σ]
    [DecidableEq σ] (G : FaithfulUpdateAssignment σ) (A B₁ B₂ : Finset (Interp σ))
    (hA : IsComplete A) :
    A.biUnion (fun I => minSet (G.ord I) B₁) ∩
        A.biUnion (fun I => minSet (G.ord I) B₂) ⊆
      A.biUnion (fun I => minSet (G.ord I) (B₁ ∪ B₂)) := by
  classical
  have hcard : A.card ≤ 1 := (isComplete_iff_card_le_one A).mp hA
  by_cases h0 : A.card = 0
  · have hA0 : A = ∅ := Finset.card_eq_zero.mp h0
    subst hA0
    intro J hJ
    rw [Finset.mem_inter] at hJ
    obtain ⟨h1, _⟩ := hJ
    obtain ⟨I, hIA, _⟩ := Finset.mem_biUnion.mp h1
    exact (Finset.notMem_empty I hIA).elim
  · have h1 : A.card = 1 := by omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp h1
    subst hx
    exact biUnion_minSet_singleton_inter G x B₁ B₂

private theorem exists_min_le_of_mem {σ : Type*} [Fintype σ] [DecidableEq σ]
    (le : Interp σ → Interp σ → Prop) (hrefl : ∀ J, le J J)
    (htrans : ∀ J K L, le J K → le K L → le J L) (B : Finset (Interp σ))
    (J : Interp σ) (hJB : J ∈ B) :
    ∃ K, K ∈ minSet le B ∧ le K J := by
  classical
  let B' := B.filter fun X => le X J
  have hJB' : J ∈ B' := Finset.mem_filter.mpr ⟨hJB, hrefl J⟩
  have hne' : B'.Nonempty := ⟨J, hJB'⟩
  obtain ⟨L, hLB'⟩ := minSet_nonempty_of_nonempty_aux le htrans B' hne'
  rw [mem_minSet] at hLB'
  obtain ⟨hLB'mem, hmin'⟩ := hLB'
  have hLB : L ∈ B := (Finset.mem_filter.mp hLB'mem).1
  have hLJ : le L J := (Finset.mem_filter.mp hLB'mem).2
  refine ⟨L, ?_, hLJ⟩
  rw [mem_minSet]
  refine ⟨hLB, ?_⟩
  intro K hKB hlt
  have hltKL : le K L := hlt.1
  have hKJ : le K J := htrans _ _ _ hltKL hLJ
  have hKB' : K ∈ B' := Finset.mem_filter.mpr ⟨hKB, hKJ⟩
  exact hmin' K hKB' hlt

private theorem minSet_eq_of_subset_both {σ : Type*} [Fintype σ] [DecidableEq σ]
    (le : Interp σ → Interp σ → Prop) (hrefl : ∀ J, le J J)
    (htrans : ∀ J K L, le J K → le K L → le J L)
    (B₁ B₂ : Finset (Interp σ)) (h1 : minSet le B₁ ⊆ B₂)
    (h2 : minSet le B₂ ⊆ B₁) : minSet le B₁ = minSet le B₂ := by
  classical
  apply Finset.ext
  intro J
  constructor
  · intro hJ1
    rw [mem_minSet] at hJ1 ⊢
    obtain ⟨hJB1, hmin1⟩ := hJ1
    have hJB2 : J ∈ B₂ := h1 ((mem_minSet le B₁ J).mpr ⟨hJB1, hmin1⟩)
    refine ⟨hJB2, ?_⟩
    intro K hKB2 hltKJ
    obtain ⟨hltK, hnltJ⟩ := hltKJ
    obtain ⟨L, hLM2, hLK⟩ :=
      exists_min_le_of_mem le hrefl htrans B₂ K hKB2
    have hLB1 : L ∈ B₁ := h2 hLM2
    rw [mem_minSet] at hLM2
    obtain ⟨_, _⟩ := hLM2
    have hLJ : le L J := htrans _ _ _ hLK hltK
    have hnJL : ¬ le J L := by
      intro hJL
      have hJK : le J K := htrans _ _ _ hJL hLK
      exact hnltJ hJK
    exact hmin1 L hLB1 ⟨hLJ, hnJL⟩
  · intro hJ2
    rw [mem_minSet] at hJ2 ⊢
    obtain ⟨hJB2, hmin2⟩ := hJ2
    have hJB1 : J ∈ B₁ := h2 ((mem_minSet le B₂ J).mpr ⟨hJB2, hmin2⟩)
    refine ⟨hJB1, ?_⟩
    intro K hKB1 hltKJ
    obtain ⟨hltK, hnltJ⟩ := hltKJ
    obtain ⟨L, hLM1, hLK⟩ :=
      exists_min_le_of_mem le hrefl htrans B₁ K hKB1
    have hLB2 : L ∈ B₂ := h1 hLM1
    have hLJ : le L J := htrans _ _ _ hLK hltK
    have hnJL : ¬ le J L := by
      intro hJL
      have hJK : le J K := htrans _ _ _ hJL hLK
      exact hnltJ hJK
    exact hmin2 L hLB2 ⟨hLJ, hnJL⟩

private theorem biUnion_minSet_u6 {σ : Type*} [Fintype σ] [DecidableEq σ]
    (G : FaithfulUpdateAssignment σ) (A B₁ B₂ : Finset (Interp σ))
    (h1 : A.biUnion (fun I => minSet (G.ord I) B₁) ⊆ B₂)
    (h2 : A.biUnion (fun I => minSet (G.ord I) B₂) ⊆ B₁) :
    A.biUnion (fun I => minSet (G.ord I) B₁) =
      A.biUnion (fun I => minSet (G.ord I) B₂) := by
  classical
  apply Finset.ext
  intro J
  rw [Finset.mem_biUnion, Finset.mem_biUnion]
  constructor
  · rintro ⟨I, hIA, hIJ1⟩
    have hsub1 : minSet (G.ord I) B₁ ⊆ B₂ := by
      intro K hK
      exact h1 (Finset.mem_biUnion.mpr ⟨I, hIA, hK⟩)
    have hsub2 : minSet (G.ord I) B₂ ⊆ B₁ := by
      intro K hK
      exact h2 (Finset.mem_biUnion.mpr ⟨I, hIA, hK⟩)
    have heq := minSet_eq_of_subset_both (G.ord I) (G.refl I) (G.trans I)
      B₁ B₂ hsub1 hsub2
    rw [heq] at hIJ1
    exact ⟨I, hIA, hIJ1⟩
  · rintro ⟨I, hIA, hIJ2⟩
    have hsub1 : minSet (G.ord I) B₁ ⊆ B₂ := by
      intro K hK
      exact h1 (Finset.mem_biUnion.mpr ⟨I, hIA, hK⟩)
    have hsub2 : minSet (G.ord I) B₂ ⊆ B₁ := by
      intro K hK
      exact h2 (Finset.mem_biUnion.mpr ⟨I, hIA, hK⟩)
    have heq := minSet_eq_of_subset_both (G.ord I) (G.refl I) (G.trans I)
      B₁ B₂ hsub1 hsub2
    rw [←heq] at hIJ2
    exact ⟨I, hIA, hIJ2⟩

private def fwdOrd {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (I J K : Interp σ) : Prop :=
  J ∈ upd {I} {J, K}

private theorem fwdOrd_refl {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (h : SatisfiesKMUpdate upd) (I J : Interp σ) : fwdOrd upd I J J := by
  classical
  unfold fwdOrd
  have hJJ : ({J, J} : Finset (Interp σ)) = {J} :=
    Finset.insert_eq_of_mem (Finset.mem_singleton_self J)
  rw [hJJ]
  have hne : (upd {I} {J}).Nonempty :=
    h.u3 {I} {J} ⟨I, Finset.mem_singleton_self I⟩
      ⟨J, Finset.mem_singleton_self J⟩
  have hsub : upd {I} {J} ⊆ {J} := h.u1 {I} {J}
  obtain ⟨X, hX⟩ := hne
  have hXJ : X = J := Finset.mem_singleton.mp (hsub hX)
  exact hXJ ▸ hX

private theorem fwdOrd_faithful {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (h : SatisfiesKMUpdate upd) (I J : Interp σ) (hne : I ≠ J) :
    fwdOrd upd I I J ∧ ¬ fwdOrd upd I J I := by
  classical
  unfold fwdOrd
  have hsub1 : ({I} : Finset (Interp σ)) ⊆ {I, J} :=
    Finset.singleton_subset_iff.mpr (Finset.mem_insert_self I {J})
  have heq1 : upd {I} {I, J} = {I} := h.u2 {I} {I, J} hsub1
  have hsub2 : ({I} : Finset (Interp σ)) ⊆ {J, I} :=
    Finset.singleton_subset_iff.mpr
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self I))
  have heq2 : upd {I} {J, I} = {I} := h.u2 {I} {J, I} hsub2
  constructor
  · rw [heq1]
    exact Finset.mem_singleton_self I
  · rw [heq2]
    intro hJI
    have heqJI : J = I := Finset.mem_singleton.mp hJI
    exact hne heqJI.symm

private theorem pair_comm {σ : Type*} [Fintype σ] [DecidableEq σ]
    (X Y : Interp σ) : ({Y, X} : Finset (Interp σ)) = {X, Y} := by
  classical
  ext Z
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

private def fwdStrict {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (I J K : Interp σ) : Prop :=
  J ∈ upd {I} {J, K} ∧ K ∉ upd {I} {J, K}

private theorem fwdStrict_iff {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (I J K : Interp σ) :
    fwdStrict upd I J K ↔ fwdOrd upd I J K ∧ ¬ fwdOrd upd I K J := by
  classical
  unfold fwdStrict fwdOrd
  rw [pair_comm (σ := σ) J K]

private theorem upd_singleton_singleton {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (h : SatisfiesKMUpdate upd) (I J : Interp σ) : upd {I} {J} = {J} := by
  classical
  apply Finset.ext
  intro X
  constructor
  · intro hX
    exact h.u1 {I} {J} hX
  · intro hX
    obtain ⟨Y, hY⟩ := h.u3 {I} {J} ⟨I, Finset.mem_singleton_self I⟩
      ⟨J, Finset.mem_singleton_self J⟩
    have hYJ : Y = J := Finset.mem_singleton.mp (h.u1 {I} {J} hY)
    have hXJ : X = J := Finset.mem_singleton.mp hX
    rw [hXJ]
    exact hYJ ▸ hY

private theorem complete_singleton {σ : Type*} [Fintype σ] [DecidableEq σ]
    (I : Interp σ) : IsComplete ({I} : Finset (Interp σ)) := by
  classical
  rw [isComplete_iff_card_le_one]
  simp

private theorem eq_singleton_of_subset_singleton {α : Type*} [DecidableEq α]
    (s : Finset α) (b : α) (hne : s.Nonempty) (hsub : s ⊆ {b}) : s = {b} := by
  classical
  apply Finset.ext
  intro X
  constructor
  · intro hX
    exact hsub hX
  · intro hX
    obtain ⟨Y, hY⟩ := hne
    have hYb : Y = b := Finset.mem_singleton.mp (hsub hY)
    have hXb : X = b := Finset.mem_singleton.mp hX
    rw [hXb]
    exact hYb ▸ hY

private theorem mem_of_nonempty_subset_pair_not_mem {α : Type*} [DecidableEq α]
    (s : Finset α) (a b : α) (hne : s.Nonempty) (hsub : s ⊆ {a, b})
    (hna : a ∉ s) : b ∈ s := by
  classical
  obtain ⟨Y, hY⟩ := hne
  have hYab : Y = a ∨ Y = b := by
    have hmem := hsub hY
    simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hYab with rfl | rfl
  · exact (hna hY).elim
  · exact hY

private theorem triple_inter_JL {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J K L : Interp σ) :
    (({J, K, L} : Finset (Interp σ)) ∩ {J, L}) = {J, L} := by
  ext X
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem triple_inter_JK {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J K L : Interp σ) :
    (({J, K, L} : Finset (Interp σ)) ∩ {J, K}) = {J, K} := by
  ext X
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem triple_inter_KL {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J K L : Interp σ) :
    (({J, K, L} : Finset (Interp σ)) ∩ {K, L}) = {K, L} := by
  ext X
  simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem pair_union_triple {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J K L : Interp σ) :
    (({J, K} : Finset (Interp σ)) ∪ {J, L}) = {J, K, L} := by
  ext X
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

private theorem fwdStrict_trans {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (h : SatisfiesKMUpdate upd) (I J K L : Interp σ)
    (hJK : fwdStrict upd I J K) (hKL : fwdStrict upd I K L) :
    fwdStrict upd I J L := by
  classical
  unfold fwdStrict at hJK hKL ⊢
  obtain ⟨hJ1, hnK1⟩ := hJK
  obtain ⟨hK2, hnL2⟩ := hKL
  by_cases hJKeq : J = K
  · rw [hJKeq] at hJ1 hnK1
    exact (hnK1 hJ1).elim
  by_cases hKLeq : K = L
  · rw [hKLeq] at hK2 hnL2
    exact (hnL2 hK2).elim
  by_cases hJLeq : J = L
  · rw [← hJLeq] at hK2
    rw [pair_comm (σ := σ) J K] at hK2
    exact (hnK1 hK2).elim
  by_cases hIJ : I = J
  · rw [hIJ] at ⊢ hJ1 hnK1 hK2 hnL2
    have heq : upd {J} {J, L} = {J} :=
      h.u2 {J} {J, L}
        (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self J {L}))
    rw [heq]
    refine ⟨Finset.mem_singleton_self J, ?_⟩
    have hLne : L ≠ J := by
      intro hLJ
      rw [hLJ] at hnL2
      have heq2 : upd {J} {K, J} = {J} :=
        h.u2 {J} {K, J}
          (Finset.singleton_subset_iff.mpr
            (Finset.mem_insert_of_mem (Finset.mem_singleton_self J)))
      rw [heq2] at hnL2
      exact hnL2 (Finset.mem_singleton_self J)
    rw [Finset.mem_singleton]
    exact hLne
  by_cases hIK : I = K
  · rw [hIK] at hnK1
    have heq : upd {K} {J, K} = {K} :=
      h.u2 {K} {J, K}
        (Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self K)))
    rw [heq] at hnK1
    exact (hnK1 (Finset.mem_singleton_self K)).elim
  by_cases hIL : I = L
  · rw [hIL] at hnL2
    have heq : upd {L} {K, L} = {L} :=
      h.u2 {L} {K, L}
        (Finset.singleton_subset_iff.mpr
          (Finset.mem_insert_of_mem (Finset.mem_singleton_self L)))
    rw [heq] at hnL2
    exact (hnL2 (Finset.mem_singleton_self L)).elim
  have hJ3 : J ∈ upd {I} {J, L} := by
    by_contra hnJ3
    have hS3sub : upd {I} {J, L} ⊆ {L} := by
      intro X hX
      have hXm := h.u1 {I} {J, L} hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hXm
      rcases hXm with hXJ | hXL
      · rw [hXJ] at hX
        exact (hnJ3 hX).elim
      · rw [hXL]
        exact Finset.mem_singleton_self L
    have hS3ne : (upd {I} {J, L}).Nonempty :=
      h.u3 {I} {J, L} ⟨I, Finset.mem_singleton_self I⟩
        ⟨J, Finset.mem_insert_self J {L}⟩
    have hS3eq : upd {I} {J, L} = {L} :=
      eq_singleton_of_subset_singleton _ _ hS3ne hS3sub
    have hLT : L ∈ upd {I} {J, K, L} := by
      by_contra hnLT
      have hTsub : upd {I} {J, K, L} ⊆ {J, K} := by
        intro X hX
        have hXm := h.u1 {I} {J, K, L} hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hXm
        rcases hXm with hXJ | hXK | hXL
        · rw [hXJ]
          exact Finset.mem_insert_self J {K}
        · rw [hXK]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self K)
        · rw [hXL] at hX
          exact (hnLT hX).elim
      have hJKsubTriple : ({J, K} : Finset (Interp σ)) ⊆ {J, K, L} := by
        intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX ⊢
        tauto
      have hS1sub : upd {I} {J, K} ⊆ {J, K, L} := fun X hX =>
        hJKsubTriple (h.u1 {I} {J, K} hX)
      have hST : upd {I} {J, K} = upd {I} {J, K, L} :=
        h.u6 {I} {J, K} {J, K, L} hS1sub hTsub
      have hJT : J ∈ upd {I} {J, K, L} := by
        rw [← hST]
        exact hJ1
      have hinter : (({J, K, L} : Finset (Interp σ)) ∩ {J, L}) = {J, L} :=
        triple_inter_JL J K L
      have hJmem := h.u5 {I} {J, K, L} {J, L}
        (Finset.mem_inter.mpr ⟨hJT, Finset.mem_insert_self J {L}⟩)
      rw [hinter, hS3eq] at hJmem
      have hJL : J = L := Finset.mem_singleton.mp hJmem
      exact hJLeq hJL
    have hinter2 : (({J, K, L} : Finset (Interp σ)) ∩ {K, L}) = {K, L} :=
      triple_inter_KL J K L
    have hLmem2 := h.u5 {I} {J, K, L} {K, L}
      (Finset.mem_inter.mpr ⟨hLT,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self L)⟩)
    rw [hinter2] at hLmem2
    exact hnL2 hLmem2
  have hnL3 : L ∉ upd {I} {J, L} := by
    intro hL3
    have hunion : (({J, K} : Finset (Interp σ)) ∪ {J, L}) = {J, K, L} :=
      pair_union_triple J K L
    have hJT : J ∈ upd {I} {J, K, L} := by
      have hsub := h.u7 {I} {J, K} {J, L} (complete_singleton I)
      rw [hunion] at hsub
      exact hsub (Finset.mem_inter.mpr ⟨hJ1, hJ3⟩)
    have hnKT : K ∉ upd {I} {J, K, L} := by
      intro hKT
      have hinter : (({J, K, L} : Finset (Interp σ)) ∩ {J, K}) = {J, K} :=
        triple_inter_JK J K L
      have hKmem := h.u5 {I} {J, K, L} {J, K}
        (Finset.mem_inter.mpr ⟨hKT,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self K)⟩)
      rw [hinter] at hKmem
      exact hnK1 hKmem
    have hnLT : L ∉ upd {I} {J, K, L} := by
      intro hLT
      have hinter : (({J, K, L} : Finset (Interp σ)) ∩ {K, L}) = {K, L} :=
        triple_inter_KL J K L
      have hLmem := h.u5 {I} {J, K, L} {K, L}
        (Finset.mem_inter.mpr ⟨hLT,
          Finset.mem_insert_of_mem (Finset.mem_singleton_self L)⟩)
      rw [hinter] at hLmem
      exact hnL2 hLmem
    have hTeq : upd {I} {J, K, L} = {J} := by
      apply Finset.ext
      intro X
      constructor
      · intro hX
        have hXm := h.u1 {I} {J, K, L} hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hXm
        rcases hXm with hXJ | hXK | hXL
        · rw [hXJ]
          exact Finset.mem_singleton_self J
        · rw [hXK] at hX
          exact (hnKT hX).elim
        · rw [hXL] at hX
          exact (hnLT hX).elim
      · intro hX
        have hXJ : X = J := Finset.mem_singleton.mp hX
        rw [hXJ]
        exact hJT
    have hS3subT : upd {I} {J, L} ⊆ {J, K, L} := by
      intro X hX
      have hXm := h.u1 {I} {J, L} hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hXm ⊢
      tauto
    have hTsubS : upd {I} {J, K, L} ⊆ {J, L} := by
      rw [hTeq]
      intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX ⊢
      tauto
    have hSTeq : upd {I} {J, L} = upd {I} {J, K, L} :=
      h.u6 {I} {J, L} {J, K, L} hS3subT hTsubS
    rw [hSTeq, hTeq] at hL3
    have hLJ : L = J := Finset.mem_singleton.mp hL3
    exact hJLeq hLJ.symm
  exact ⟨hJ3, hnL3⟩

private theorem idOrStrict_fwdOrd_trans {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (h : SatisfiesKMUpdate upd) (I J K L : Interp σ) :
    idOrStrict (fwdOrd upd I) J K → idOrStrict (fwdOrd upd I) K L →
      idOrStrict (fwdOrd upd I) J L := by
  classical
  intro h1 h2
  unfold idOrStrict at h1 h2 ⊢
  rcases h1 with rfl | ⟨hJK, hnKJ⟩
  · exact h2
  · rcases h2 with rfl | ⟨hKL, hnLK⟩
    · exact Or.inr ⟨hJK, hnKJ⟩
    · have hJK' := (fwdStrict_iff upd I J K).mpr ⟨hJK, hnKJ⟩
      have hKL' := (fwdStrict_iff upd I K L).mpr ⟨hKL, hnLK⟩
      have hJL' := fwdStrict_trans upd h I J K L hJK' hKL'
      have hJL := (fwdStrict_iff upd I J L).mp hJL'
      exact Or.inr hJL

private theorem upd_singleton_eq_minSet {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (h : SatisfiesKMUpdate upd) (I : Interp σ) (B : Finset (Interp σ)) :
    upd {I} B = minSet (idOrStrict (fwdOrd upd I)) B := by
  classical
  apply Finset.ext
  intro J
  rw [mem_minSet]
  constructor
  · intro hJB
    have hJBmem : J ∈ B := h.u1 {I} B hJB
    refine ⟨hJBmem, ?_⟩
    intro X hXB hstrict
    have hstrict' := (idOrStrict_strict_iff (fwdOrd upd I) X J).mp hstrict
    have hfw := (fwdStrict_iff upd I X J).mpr hstrict'
    unfold fwdStrict at hfw
    obtain ⟨hXmem, hnJmem⟩ := hfw
    have hXJsub : ({X, J} : Finset (Interp σ)) ⊆ B :=
      Finset.insert_subset_iff.mpr
        ⟨hXB, Finset.singleton_subset_iff.mpr hJBmem⟩
    have hinter : B ∩ {X, J} = {X, J} := by
      ext Y
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hY
        exact hY.2
      · intro hY
        have hYmem : Y ∈ ({X, J} : Finset (Interp σ)) := by
          simpa [Finset.mem_insert, Finset.mem_singleton] using hY
        exact ⟨hXJsub hYmem, hY⟩
    have hJmem := h.u5 {I} B {X, J}
      (Finset.mem_inter.mpr ⟨hJB,
        Finset.mem_insert_of_mem (Finset.mem_singleton_self J)⟩)
    rw [hinter] at hJmem
    exact hnJmem hJmem
  · rintro ⟨hJB, hmin⟩
    by_contra hnJ
    have hall : ∀ X ∈ B, X ≠ J → J ∈ upd {I} {X, J} := by
      intro X hXB hXJ
      by_contra hnJX
      have hXne : (upd {I} {X, J}).Nonempty :=
        h.u3 {I} {X, J} ⟨I, Finset.mem_singleton_self I⟩
          ⟨X, Finset.mem_insert_self X {J}⟩
      have hXsub : upd {I} {X, J} ⊆ {X, J} := h.u1 {I} {X, J}
      have hXsub' : upd {I} {X, J} ⊆ {J, X} := by
        rwa [pair_comm (σ := σ) X J]
      have hXmem : X ∈ upd {I} {X, J} :=
        mem_of_nonempty_subset_pair_not_mem _ _ _ hXne hXsub' hnJX
      have hstrict : idOrStrict (fwdOrd upd I) X J ∧
          ¬ idOrStrict (fwdOrd upd I) J X :=
        (idOrStrict_strict_iff _ _ _).mpr
          ((fwdStrict_iff upd I X J).mp ⟨hXmem, hnJX⟩)
      exact hmin X hXB hstrict
    have key : ∀ S : Finset (Interp σ), S ⊆ B \ {J} →
        J ∈ upd {I} (S ∪ {J}) := by
      intro S
      induction S using Finset.induction with
      | empty =>
        intro _
        have heq : upd {I} ((∅ : Finset (Interp σ)) ∪ {J}) = {J} := by
          rw [Finset.empty_union]
          exact upd_singleton_singleton upd h I J
        rw [heq]
        exact Finset.mem_singleton_self J
      | insert X S' _ IH =>
        intro hsub
        have hXmem : X ∈ B ∧ X ≠ J := by
          have hXins : X ∈ insert X S' := Finset.mem_insert_self X S'
          have hXsd := hsub hXins
          rw [Finset.mem_sdiff, Finset.mem_singleton] at hXsd
          exact hXsd
        have hS'sub : S' ⊆ B \ {J} := by
          intro Y hY
          exact hsub (Finset.mem_insert_of_mem hY)
        have h1 : J ∈ upd {I} (S' ∪ {J}) := IH hS'sub
        have h2 : J ∈ upd {I} {X, J} := hall X hXmem.1 hXmem.2
        have hsub7 := h.u7 {I} (S' ∪ {J}) {X, J} (complete_singleton I)
        have hunion : (S' ∪ {J}) ∪ {X, J} = insert X S' ∪ {J} := by
          ext Y
          simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro ((hS | hYJ) | (hYX | hYJ2))
            · exact Or.inl (Or.inr hS)
            · exact Or.inr hYJ
            · exact Or.inl (Or.inl hYX)
            · exact Or.inr hYJ2
          · rintro ((hYX | hS) | hYJ)
            · exact Or.inr (Or.inl hYX)
            · exact Or.inl (Or.inl hS)
            · exact Or.inl (Or.inr hYJ)
        rw [hunion] at hsub7
        exact hsub7 (Finset.mem_inter.mpr ⟨h1, h2⟩)
    have hJmemB := key (B \ {J}) (Finset.Subset.refl _)
    have hunionB : (B \ {J}) ∪ {J} = B :=
      Finset.sdiff_union_of_subset (Finset.singleton_subset_iff.mpr hJB)
    rw [hunionB] at hJmemB
    exact hnJ hJmemB

private theorem upd_eq_biUnion_singleton {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (h : SatisfiesKMUpdate upd) (A B : Finset (Interp σ)) :
    upd A B = A.biUnion fun I => upd {I} B := by
  classical
  induction A using Finset.induction with
  | empty =>
    have h0 : upd ∅ B = ∅ := h.u2 ∅ B (Finset.empty_subset B)
    rw [h0, Finset.biUnion_empty]
  | insert X S' _ IH =>
    have hins : insert X S' = {X} ∪ S' := by
      ext Y
      simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
    conv_lhs => rw [hins]
    rw [h.u8 {X} S' B, IH, Finset.biUnion_insert]

/-- **Katsuno–Mendelzon update representation theorem**, Theorem 3.1, conditions 1 ⇔ 2: an
update operator on model sets satisfies (U1)–(U8) if and only if there is a faithful
assignment of partial preorders such that `upd A B` is the union, over the models `I` of `A`,
of the `G.ord I`-minimal models of `B`, for every `A` and `B`. -/
theorem km_update_representation {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ)) :
    SatisfiesKMUpdate upd ↔
      ∃ G : FaithfulUpdateAssignment σ,
        ∀ A B, upd A B = A.biUnion fun I => minSet (G.ord I) B := by
  classical
  constructor
  · intro hUpd
    refine ⟨⟨fun I => idOrStrict (fwdOrd upd I), ?_, ?_, ?_⟩, ?_⟩
    · intro I J
      exact idOrStrict_refl _ J
    · intro I J K L h1 h2
      exact idOrStrict_fwdOrd_trans upd hUpd I J K L h1 h2
    · intro I J hne
      exact (idOrStrict_strict_iff _ _ _).mpr (fwdOrd_faithful upd hUpd I J hne)
    · intro A B
      rw [upd_eq_biUnion_singleton upd hUpd A B]
      apply Finset.biUnion_congr rfl
      intro I _
      exact upd_singleton_eq_minSet upd hUpd I B
  · rintro ⟨G, hG⟩
    refine ⟨?u1, ?u2, ?u3, ?u4, ?u5, ?u6, ?u7, ?u8⟩
    · intro A B
      rw [hG]
      exact biUnion_minSet_subset G A B
    · intro A B hAB
      rw [hG]
      exact biUnion_minSet_eq_self_of_subset G A B hAB
    · intro A B hA hB
      rw [hG]
      exact biUnion_minSet_nonempty G A B hA hB
    · intro A A' B B' hA hB
      rw [hA, hB]
    · intro A B C
      rw [hG A B, hG A (B ∩ C)]
      exact biUnion_minSet_inter_subset G A B C
    · intro A B₁ B₂ hsub1 hsub2
      rw [hG A B₁] at hsub1
      rw [hG A B₂] at hsub2
      rw [hG A B₁, hG A B₂]
      exact biUnion_minSet_u6 G A B₁ B₂ hsub1 hsub2
    · intro A B₁ B₂ hA
      simp only [hG] at ⊢
      exact biUnion_minSet_u7_of_complete G A B₁ B₂ hA
    · intro A₁ A₂ B
      simp only [hG]
      exact biUnion_union_index _ A₁ A₂

/-- Theorem 3.1, conditions 1 ⇔ 3: the same representation with every `G.ord I` a partial
order, that is, antisymmetric as well. -/
theorem km_update_representation_partialOrder {σ : Type*} [Fintype σ] [DecidableEq σ]
    (upd : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ)) :
    SatisfiesKMUpdate upd ↔
      ∃ G : FaithfulUpdateAssignment σ, (∀ I J K, G.ord I J K → G.ord I K J → J = K) ∧
        ∀ A B, upd A B = A.biUnion fun I => minSet (G.ord I) B := by
  classical
  constructor
  · intro hUpd
    obtain ⟨G, hG⟩ := (km_update_representation upd).mp hUpd
    refine ⟨⟨fun I => idOrStrict (G.ord I), ?_, ?_, ?_⟩, ?_, ?_⟩
    · intro I J
      exact idOrStrict_refl _ J
    · intro I
      exact idOrStrict_trans (G.trans I)
    · intro I J hne
      exact (idOrStrict_strict_iff _ _ _).mpr (G.faithful I J hne)
    · intro I J K h1 h2
      exact idOrStrict_antisymm _ _ _ h1 h2
    · intro A B
      rw [hG]
      apply Finset.biUnion_congr rfl
      intro I _
      exact (minSet_idOrStrict _ _).symm
  · rintro ⟨G, _, hG⟩
    refine ⟨?u1, ?u2, ?u3, ?u4, ?u5, ?u6, ?u7, ?u8⟩
    · intro A B
      rw [hG]
      exact biUnion_minSet_subset G A B
    · intro A B hAB
      rw [hG]
      exact biUnion_minSet_eq_self_of_subset G A B hAB
    · intro A B hA hB
      rw [hG]
      exact biUnion_minSet_nonempty G A B hA hB
    · intro A A' B B' hA hB
      rw [hA, hB]
    · intro A B C
      rw [hG A B, hG A (B ∩ C)]
      exact biUnion_minSet_inter_subset G A B C
    · intro A B₁ B₂ hsub1 hsub2
      rw [hG A B₁] at hsub1
      rw [hG A B₂] at hsub2
      rw [hG A B₁, hG A B₂]
      exact biUnion_minSet_u6 G A B₁ B₂ hsub1 hsub2
    · intro A B₁ B₂ hA
      simp only [hG] at ⊢
      exact biUnion_minSet_u7_of_complete G A B₁ B₂ hA
    · intro A₁ A₂ B
      simp only [hG]
      exact biUnion_union_index _ A₁ A₂

/-- The PMA order relative to `I` is antisymmetric: an interpretation is determined by `I` and
its `Diff` from `I`. With `pmaAssignment`, PMA is a faithful partial-order assignment. -/
theorem pmaLe_antisymm {σ : Type*} [Fintype σ] [DecidableEq σ] {I J K : Interp σ}
    (h₁ : pmaLe I J K) (h₂ : pmaLe I K J) : J = K := by
  have heq : pmaDiff I J = pmaDiff I K := Finset.Subset.antisymm h₁ h₂
  funext a
  have hmem : (I a ≠ J a) ↔ (I a ≠ K a) := by
    have h := Finset.ext_iff.mp heq a
    simpa [pmaDiff] using h
  cases hI : I a <;> cases hJ : J a <;> cases hK : K a <;> simp_all

/-- Winslett's PMA satisfies (U1)–(U8): it is the instance of Theorem 3.1 given by
`pmaAssignment`. KM derive this from the theorem; it is not a separately numbered result. -/
theorem pma_satisfiesKMUpdate {σ : Type*} [Fintype σ] [DecidableEq σ] :
    SatisfiesKMUpdate (σ := σ) pmaUpdate := by
  apply (km_update_representation_partialOrder pmaUpdate).mpr
  exact ⟨pmaAssignment σ, fun I J K h₁ h₂ => pmaLe_antisymm h₁ h₂, fun A B => rfl⟩

/-- KM Example 3.1, with atom `0` for `b` and atom `1` for `m`, writing `10` for
`![true, false]`: updating `A = {10, 01}`, the models of `(b ∧ ¬m) ∨ (¬b ∧ m)`, by
`B = {10, 11}`, the models of `b`, gives `B`. -/
theorem pma_example_3_1 :
    pmaUpdate ({![true, false], ![false, true]} : Finset (Interp (Fin 2)))
        {![true, false], ![true, true]} = {![true, false], ![true, true]} := by
  have le10 : pmaLe ![true, false] ![true, false] ![true, true] := by
    unfold pmaLe; decide
  have nle10 : ¬ pmaLe ![true, false] ![true, true] ![true, false] := by
    unfold pmaLe; decide
  have le01 : pmaLe ![false, true] ![true, true] ![true, false] := by
    unfold pmaLe; decide
  have nle01 : ¬ pmaLe ![false, true] ![true, false] ![true, true] := by
    unfold pmaLe; decide
  have m1 : minSet (pmaLe ![true, false])
      {![true, false], ![true, true]} = {![true, false]} := by
    ext X
    simp only [mem_minSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hX | hX, hall⟩
      · exact hX
      · subst hX
        have hcon := hall ![true, false] (by simp)
        exact (hcon ⟨le10, nle10⟩).elim
    · rintro rfl
      constructor
      · simp
      · intro J hJ
        rcases hJ with rfl | rfl
        · exact fun hcon => hcon.2 hcon.1
        · exact fun hcon => nle10 hcon.1
  have m2 : minSet (pmaLe ![false, true])
      {![true, false], ![true, true]} = {![true, true]} := by
    ext X
    simp only [mem_minSet, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hX | hX, hall⟩
      · subst hX
        have hcon := hall ![true, true] (by simp)
        exact (hcon ⟨le01, nle01⟩).elim
      · exact hX
    · rintro rfl
      constructor
      · simp
      · intro J hJ
        rcases hJ with rfl | rfl
        · exact fun hcon => nle01 hcon.1
        · exact fun hcon => hcon.2 hcon.1
  unfold pmaUpdate
  simp only [Finset.biUnion_insert, Finset.singleton_biUnion, m1, m2]
  decide

/-- In Example 3.1, `A ∩ B = {10}` is nonempty, so (R2) would require the result `{10}`. -/
theorem km_example_3_1_inter :
    ({![true, false], ![false, true]} ∩ {![true, false], ![true, true]} :
        Finset (Interp (Fin 2))) = {![true, false]} := by
  decide

/-- PMA violates the revision postulate (R2), the field `SatisfiesKM.r2`, on two atoms, as
Example 3.1 witnesses. This is an existential statement about one signature and one operator. -/
theorem pma_violates_r2 :
    ∃ A B : Finset (Interp (Fin 2)), (A ∩ B).Nonempty ∧ pmaUpdate A B ≠ A ∩ B := by
  refine ⟨{![true, false], ![false, true]}, {![true, false], ![true, true]},
    ⟨![true, false], by decide⟩, ?_⟩
  rw [pma_example_3_1, km_example_3_1_inter]
  decide


end Cslib.BeliefRevision
