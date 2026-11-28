/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Image
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.Tauto

/-!
# Katsuno–Mendelzon belief revision: postulates and representation

Revision operators on finite model sets of a finite propositional signature:
the postulates (R1)–(R6) (`SatisfiesKM`), faithful assignments of total
preorders, the representation theorem (`km_representation`: (R1)–(R6) hold
exactly for the operators that select minimal models of a faithful
assignment), and Dalal's Hamming-distance revision (`dalalRev`,
`dalal_satisfiesKM`) as the standard concrete instance.

## References

* H. Katsuno and A. O. Mendelzon, *On the Difference between Updating a
  Knowledge Base and Revising It*, KR 1991, §2.
* M. Dalal, *Investigations into a Theory of Knowledge Base Revision:
  Preliminary Report*, AAAI 1988.
-/

@[expose] public section

namespace Cslib.BeliefRevision

/-- Interpretations of a propositional signature `σ`, which may be any type: assignments of
truth values to the atoms. Finiteness of `σ` and decidable equality are assumptions of the
model-set revision development that uses it (`minSet`, `dalalRev`), not of `Interp`.
Throughout, a propositional formula is represented
semantically by its model set, a `Finset` of interpretations; this is the
semantic representation in which Katsuno–Mendelzon's syntax-irrelevance
postulate (R4) is a congruence property of equality of model sets. -/
abbrev Interp (σ : Type*) : Type _ := σ → Bool

/-- The Katsuno–Mendelzon revision postulates (R1)–(R6) for an operator on
model sets, after Katsuno & Mendelzon, *On the Difference between Updating a
Knowledge Base and Revising It* (KR 1991), §2.1. For model sets `A` (the old
knowledge base), `B` (the new sentence) and `C` (a further sentence):
(R1) the revision implies the new sentence; (R2) if `A ∩ B` is nonempty the
revision is `A ∩ B`; (R3) a satisfiable new sentence has a satisfiable
revision; (R4) syntax irrelevance, here congruence in the model sets;
(R5) `(rev A B) ∩ C ⊆ rev A (B ∩ C)`; (R6) the reverse inclusion when the
left side is nonempty. -/
structure SatisfiesKM {σ : Type*} [Fintype σ] [DecidableEq σ]
    (rev : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ)) : Prop where
  r1 : ∀ A B, rev A B ⊆ B
  r2 : ∀ A B, (A ∩ B).Nonempty → rev A B = A ∩ B
  r3 : ∀ A B, B.Nonempty → (rev A B).Nonempty
  r4 : ∀ A A' B B', A = A' → B = B' → rev A B = rev A' B'
  r5 : ∀ A B C, rev A B ∩ C ⊆ rev A (B ∩ C)
  r6 : ∀ A B C, (rev A B ∩ C).Nonempty → rev A (B ∩ C) ⊆ rev A B ∩ C

/-- A faithful assignment (KM §2.2): to each model set `A`, a total preorder
`ord A` on interpretations such that models of `A` are never strictly below
other models of `A`, and every model of `A` is strictly below every
non-model. The third KM clause, dependence only on the model set, is built
into the semantic representation. Here `I` is strictly below `J` for `ord A`
when `ord A I J ∧ ¬ ord A J I`. -/
structure FaithfulAssignment (σ : Type*) [Fintype σ] [DecidableEq σ] where
  ord : Finset (Interp σ) → Interp σ → Interp σ → Prop
  refl : ∀ A I, ord A I I
  trans : ∀ A I J K, ord A I J → ord A J K → ord A I K
  total : ∀ A I J, ord A I J ∨ ord A J I
  faithful_models : ∀ A, ∀ I ∈ A, ∀ J ∈ A, ¬ (ord A I J ∧ ¬ ord A J I)
  faithful_strict : ∀ A, ∀ I ∈ A, ∀ J ∉ A, ord A I J ∧ ¬ ord A J I

open Classical in
/-- The `le`-minimal elements of a finite set of interpretations: `I ∈ B`
with no `J ∈ B` strictly below `I`. -/
noncomputable def minSet {σ : Type*} [Fintype σ] [DecidableEq σ]
    (le : Interp σ → Interp σ → Prop) (B : Finset (Interp σ)) : Finset (Interp σ) :=
  B.filter (fun I => ∀ J ∈ B, ¬ (le J I ∧ ¬ le I J))

theorem mem_minSet {σ : Type*} [Fintype σ] [DecidableEq σ]
    (le : Interp σ → Interp σ → Prop) (B : Finset (Interp σ)) (I : Interp σ) :
    I ∈ minSet le B ↔ I ∈ B ∧ ∀ J ∈ B, ¬ (le J I ∧ ¬ le I J) := by
  classical
  unfold minSet
  exact Finset.mem_filter

theorem minSet_subset {σ : Type*} [Fintype σ] [DecidableEq σ]
    (le : Interp σ → Interp σ → Prop) (B : Finset (Interp σ)) :
    minSet le B ⊆ B := by
  classical
  unfold minSet
  exact Finset.filter_subset _ _

private theorem exists_min_of_nonempty {σ : Type*}
    (le : Interp σ → Interp σ → Prop)
    (hTrans : ∀ I J K, le I J → le J K → le I K)
    (hTotal : ∀ I J, le I J ∨ le J I)
    (B : Finset (Interp σ)) (hB : B.Nonempty) :
    ∃ M ∈ B, ∀ J ∈ B, ¬ (le J M ∧ ¬ le M J) := by
  classical
  revert hB
  induction B using Finset.induction with
  | empty => intro hB; exact absurd hB Finset.not_nonempty_empty
  | insert a s ha ih =>
    intro hB
    by_cases hs : s.Nonempty
    · obtain ⟨m, hmMem, hmMin⟩ := ih hs
      by_cases hma : le m a
      · refine ⟨m, Finset.mem_insert_of_mem hmMem, ?_⟩
        intro J hJ hStrict
        obtain rfl | hJs := Finset.mem_insert.mp hJ
        · exact hStrict.2 hma
        · exact hmMin J hJs hStrict
      · have ham : le a m := (hTotal m a).resolve_left hma
        refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro J hJ hStrict
        obtain rfl | hJs := Finset.mem_insert.mp hJ
        · exact hStrict.2 hStrict.1
        · have hJm : le J m := hTrans J a m hStrict.1 ham
          have hn : ¬ le m J := fun hmJ => hma (hTrans m J a hmJ hStrict.1)
          exact hmMin J hJs ⟨hJm, hn⟩
    · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
      intro J hJ hStrict
      obtain rfl | hJs := Finset.mem_insert.mp hJ
      · exact hStrict.2 hStrict.1
      · exact hs ⟨J, hJs⟩

theorem minSet_nonempty_of_nonempty {σ : Type*} [Fintype σ] [DecidableEq σ]
    (F : FaithfulAssignment σ) (A B : Finset (Interp σ)) (hB : B.Nonempty) :
    (minSet (F.ord A) B).Nonempty := by
  obtain ⟨M, hMB, hMMin⟩ :=
    exists_min_of_nonempty (F.ord A) (F.trans A) (F.total A) B hB
  exact ⟨M, (mem_minSet _ _ _).mpr ⟨hMB, hMMin⟩⟩

theorem minSet_eq_inter_of_nonempty {σ : Type*} [Fintype σ] [DecidableEq σ]
    (F : FaithfulAssignment σ) (A B : Finset (Interp σ))
    (h : (A ∩ B).Nonempty) : minSet (F.ord A) B = A ∩ B := by
  apply Finset.ext
  intro I
  rw [mem_minSet, Finset.mem_inter]
  constructor
  · intro hI
    obtain ⟨hIB, hMin⟩ := hI
    have hIA : I ∈ A := by
      by_contra hIA
      obtain ⟨K, hK⟩ := h
      rw [Finset.mem_inter] at hK
      obtain ⟨hKA, hKB⟩ := hK
      obtain ⟨hKI, hnIK⟩ := F.faithful_strict A K hKA I hIA
      exact hMin K hKB ⟨hKI, hnIK⟩
    exact ⟨hIA, hIB⟩
  · intro hI
    obtain ⟨hIA, hIB⟩ := hI
    refine ⟨hIB, ?_⟩
    intro J hJB hStrict
    obtain ⟨hJI, hnIJ⟩ := hStrict
    by_cases hJA : J ∈ A
    · exact F.faithful_models A J hJA I hIA ⟨hJI, hnIJ⟩
    · obtain ⟨hIJ, hnJI⟩ := F.faithful_strict A I hIA J hJA
      exact hnJI hJI

theorem minSet_inter_subset {σ : Type*} [Fintype σ] [DecidableEq σ]
    (F : FaithfulAssignment σ) (A B C : Finset (Interp σ)) :
    minSet (F.ord A) B ∩ C ⊆ minSet (F.ord A) (B ∩ C) := by
  intro I hI
  rw [Finset.mem_inter] at hI
  obtain ⟨hIMin, hIC⟩ := hI
  rw [mem_minSet] at hIMin
  obtain ⟨hIB, hMin⟩ := hIMin
  rw [mem_minSet]
  constructor
  · exact Finset.mem_inter.mpr ⟨hIB, hIC⟩
  · intro K hK hStrict
    rw [Finset.mem_inter] at hK
    exact hMin K hK.1 hStrict

theorem minSet_subset_inter_of_nonempty {σ : Type*} [Fintype σ] [DecidableEq σ]
    (F : FaithfulAssignment σ) (A B C : Finset (Interp σ))
    (hW : (minSet (F.ord A) B ∩ C).Nonempty) :
    minSet (F.ord A) (B ∩ C) ⊆ minSet (F.ord A) B ∩ C := by
  obtain ⟨W, hWmem⟩ := hW
  rw [Finset.mem_inter] at hWmem
  obtain ⟨hWMin, hWC⟩ := hWmem
  rw [mem_minSet] at hWMin
  obtain ⟨hWB, hWmin⟩ := hWMin
  intro I hI
  rw [mem_minSet] at hI
  obtain ⟨hIBC, hImin⟩ := hI
  rw [Finset.mem_inter] at hIBC
  obtain ⟨hIB, hIC⟩ := hIBC
  rw [Finset.mem_inter]
  constructor
  · rw [mem_minSet]
    constructor
    · exact hIB
    · intro J hJB hStrict
      obtain ⟨hJI, hnIJ⟩ := hStrict
      by_cases hIW : F.ord A I W
      · have hJW : F.ord A J W := F.trans A J I W hJI hIW
        have hnWJ : ¬ F.ord A W J :=
          fun hWJ => hnIJ (F.trans A I W J hIW hWJ)
        exact hWmin J hJB ⟨hJW, hnWJ⟩
      · have hWI : F.ord A W I := (F.total A I W).resolve_left hIW
        have hWBC : W ∈ B ∩ C := Finset.mem_inter.mpr ⟨hWB, hWC⟩
        exact hImin W hWBC ⟨hWI, hIW⟩
  · exact hIC

theorem minSet_satisfiesKM {σ : Type*} [Fintype σ] [DecidableEq σ]
    (F : FaithfulAssignment σ) :
    SatisfiesKM (fun A B => minSet (F.ord A) B) where
  r1 := fun A B => minSet_subset _ _
  r2 := fun A B h => minSet_eq_inter_of_nonempty F A B h
  r3 := fun A B hB => minSet_nonempty_of_nonempty F A B hB
  r4 := by
    intro A A' B B' hA hB
    subst hA
    subst hB
    rfl
  r5 := fun A B C => minSet_inter_subset F A B C
  r6 := fun A B C h => minSet_subset_inter_of_nonempty F A B C h

private theorem km_rev_singleton_mem {σ : Type*} [Fintype σ] [DecidableEq σ]
    (rev : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (hKM : SatisfiesKM rev) (A : Finset (Interp σ)) (I : Interp σ) :
    I ∈ rev A {I} := by
  have hNon := hKM.r3 A {I} (Finset.singleton_nonempty I)
  obtain ⟨X, hX⟩ := hNon
  have hSub := hKM.r1 A {I} hX
  rw [Finset.mem_singleton] at hSub
  rw [hSub] at hX
  exact hX

private theorem km_canonical_trans {σ : Type*} [Fintype σ] [DecidableEq σ]
    (rev : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (hKM : SatisfiesKM rev) (A : Finset (Interp σ))
    (I J K : Interp σ) (hIJ : I ∈ rev A {I, J}) (hJK : J ∈ rev A {J, K}) :
    I ∈ rev A {I, K} := by
  have hSubIJ : ({I, J} : Finset (Interp σ)) ⊆ ({I, J, K} : Finset (Interp σ)) := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX ⊢
    tauto
  have hSubJK : ({J, K} : Finset (Interp σ)) ⊆ ({I, J, K} : Finset (Interp σ)) := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX ⊢
    tauto
  have hSubIK : ({I, K} : Finset (Interp σ)) ⊆ ({I, J, K} : Finset (Interp σ)) := by
    intro X hX
    simp only [Finset.mem_insert, Finset.mem_singleton] at hX ⊢
    tauto
  have hInterIJ : ({I, J, K} : Finset (Interp σ)) ∩ {I, J} =
      ({I, J} : Finset (Interp σ)) :=
    Finset.inter_eq_right.mpr hSubIJ
  have hInterJK : ({I, J, K} : Finset (Interp σ)) ∩ {J, K} =
      ({J, K} : Finset (Interp σ)) :=
    Finset.inter_eq_right.mpr hSubJK
  have hInterIK : ({I, J, K} : Finset (Interp σ)) ∩ {I, K} =
      ({I, K} : Finset (Interp σ)) :=
    Finset.inter_eq_right.mpr hSubIK
  have hJtoI : J ∈ rev A {I, J, K} → I ∈ rev A {I, J, K} := by
    intro hJS
    have hJC : J ∈ ({I, J} : Finset (Interp σ)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self J)
    have hNon : (rev A {I, J, K} ∩ ({I, J} : Finset (Interp σ))).Nonempty :=
      ⟨J, Finset.mem_inter.mpr ⟨hJS, hJC⟩⟩
    have hR6 := hKM.r6 A {I, J, K} {I, J} hNon
    rw [hInterIJ] at hR6
    have hIin := hR6 hIJ
    exact (Finset.mem_inter.mp hIin).1
  have hKtoJ : K ∈ rev A {I, J, K} → J ∈ rev A {I, J, K} := by
    intro hKS
    have hKC : K ∈ ({J, K} : Finset (Interp σ)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self K)
    have hNon : (rev A {I, J, K} ∩ ({J, K} : Finset (Interp σ))).Nonempty :=
      ⟨K, Finset.mem_inter.mpr ⟨hKS, hKC⟩⟩
    have hR6 := hKM.r6 A {I, J, K} {J, K} hNon
    rw [hInterJK] at hR6
    have hJin := hR6 hJK
    exact (Finset.mem_inter.mp hJin).1
  have hSNon : ({I, J, K} : Finset (Interp σ)).Nonempty :=
    ⟨I, Finset.mem_insert_self I _⟩
  obtain ⟨X, hX⟩ := hKM.r3 A {I, J, K} hSNon
  have hXmem : X ∈ ({I, J, K} : Finset (Interp σ)) := hKM.r1 A {I, J, K} hX
  simp only [Finset.mem_insert, Finset.mem_singleton] at hXmem
  have hIS : I ∈ rev A {I, J, K} := by
    rcases hXmem with rfl | rfl | rfl
    · exact hX
    · exact hJtoI hX
    · exact hJtoI (hKtoJ hX)
  have hIC : I ∈ ({I, K} : Finset (Interp σ)) :=
    Finset.mem_insert_self I {K}
  have hIinInter : I ∈ rev A {I, J, K} ∩ ({I, K} : Finset (Interp σ)) :=
    Finset.mem_inter.mpr ⟨hIS, hIC⟩
  have hR5 := hKM.r5 A {I, J, K} {I, K}
  rw [hInterIK] at hR5
  exact hR5 hIinInter

private theorem km_canonical_rep {σ : Type*} [Fintype σ] [DecidableEq σ]
    (rev : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ))
    (hKM : SatisfiesKM rev) (A B : Finset (Interp σ)) :
    rev A B = minSet (fun I J => I ∈ rev A {I, J}) B := by
  apply Finset.ext
  intro I
  rw [mem_minSet]
  constructor
  · intro hIRev
    have hIB : I ∈ B := hKM.r1 A B hIRev
    constructor
    · exact hIB
    · intro J hJB hStrict
      obtain ⟨hJI, hnIJ⟩ := hStrict
      have hSub : ({I, J} : Finset (Interp σ)) ⊆ B := by
        intro X hX
        simp only [Finset.mem_insert, Finset.mem_singleton] at hX
        obtain rfl | rfl := hX
        · exact hIB
        · exact hJB
      have hInter : B ∩ ({I, J} : Finset (Interp σ)) = {I, J} :=
        Finset.inter_eq_right.mpr hSub
      have hIC : I ∈ ({I, J} : Finset (Interp σ)) :=
        Finset.mem_insert_self I {J}
      have hIinInter : I ∈ rev A B ∩ ({I, J} : Finset (Interp σ)) :=
        Finset.mem_inter.mpr ⟨hIRev, hIC⟩
      have hR5 := hKM.r5 A B {I, J}
      rw [hInter] at hR5
      exact hnIJ (hR5 hIinInter)
  · intro hMin
    obtain ⟨hIB, hMin⟩ := hMin
    by_contra hNI
    have hBNon : B.Nonempty := ⟨I, hIB⟩
    obtain ⟨J, hJRev⟩ := hKM.r3 A B hBNon
    have hJB : J ∈ B := hKM.r1 A B hJRev
    have hSub : ({I, J} : Finset (Interp σ)) ⊆ B := by
      intro X hX
      simp only [Finset.mem_insert, Finset.mem_singleton] at hX
      obtain rfl | rfl := hX
      · exact hIB
      · exact hJB
    have hInter : B ∩ ({I, J} : Finset (Interp σ)) = {I, J} :=
      Finset.inter_eq_right.mpr hSub
    have hJC : J ∈ ({I, J} : Finset (Interp σ)) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self J)
    have hNon : (rev A B ∩ ({I, J} : Finset (Interp σ))).Nonempty :=
      ⟨J, Finset.mem_inter.mpr ⟨hJRev, hJC⟩⟩
    have hR5 := hKM.r5 A B {I, J}
    have hR6 := hKM.r6 A B {I, J} hNon
    rw [hInter] at hR5 hR6
    have hJinIJ : J ∈ rev A ({I, J} : Finset (Interp σ)) :=
      hR5 (Finset.mem_inter.mpr ⟨hJRev, hJC⟩)
    have hInot : I ∉ rev A ({I, J} : Finset (Interp σ)) := by
      intro hImem
      have hIin := hR6 hImem
      exact hNI (Finset.mem_inter.mp hIin).1
    have hEq := Finset.pair_comm I J
    rw [hEq] at hJinIJ
    exact hMin J hJB ⟨hJinIJ, hInot⟩

/-- **Katsuno–Mendelzon representation theorem** (Theorem 2.1): a revision
operator on model sets satisfies (R1)–(R6) if and only if there is a faithful
assignment such that revising by `B` selects the `ord A`-minimal models of
`B`, for every `A` and `B`. -/
theorem km_representation {σ : Type*} [Fintype σ] [DecidableEq σ]
    (rev : Finset (Interp σ) → Finset (Interp σ) → Finset (Interp σ)) :
    SatisfiesKM rev ↔
      ∃ F : FaithfulAssignment σ, ∀ A B, rev A B = minSet (F.ord A) B := by
  constructor
  · intro hKM
    refine ⟨⟨fun A I J => I ∈ rev A {I, J}, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro A I
      have hEq : ({I, I} : Finset (Interp σ)) = {I} := by
        apply Finset.ext
        intro X
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      rw [hEq]
      exact km_rev_singleton_mem rev hKM A I
    · intro A I J K hIJ hJK
      exact km_canonical_trans rev hKM A I J K hIJ hJK
    · intro A I J
      have hNon : ({I, J} : Finset (Interp σ)).Nonempty :=
        ⟨I, Finset.mem_insert_self I {J}⟩
      obtain ⟨X, hX⟩ := hKM.r3 A {I, J} hNon
      have hXmem := hKM.r1 A {I, J} hX
      rw [Finset.mem_insert, Finset.mem_singleton] at hXmem
      obtain hXI | hXJ := hXmem
      · rw [hXI] at hX
        exact Or.inl hX
      · rw [hXJ] at hX
        have hEq := Finset.pair_comm I J
        rw [hEq] at hX
        exact Or.inr hX
    · intro A I hIA J hJA hStrict
      have hNon : (A ∩ ({I, J} : Finset (Interp σ))).Nonempty := by
        refine ⟨I, Finset.mem_inter.mpr ⟨hIA, ?_⟩⟩
        exact Finset.mem_insert_self I {J}
      have hR2 := hKM.r2 A {I, J} hNon
      have hJmem : J ∈ rev A {I, J} := by
        rw [hR2]
        rw [Finset.mem_inter]
        constructor
        · exact hJA
        · rw [Finset.mem_insert, Finset.mem_singleton]
          exact Or.inr rfl
      have hEq := Finset.pair_comm I J
      rw [hEq] at hJmem
      exact hStrict.2 hJmem
    · intro A I hIA J hJA
      have hNon : (A ∩ ({I, J} : Finset (Interp σ))).Nonempty := by
        refine ⟨I, Finset.mem_inter.mpr ⟨hIA, ?_⟩⟩
        exact Finset.mem_insert_self I {J}
      have hR2 := hKM.r2 A {I, J} hNon
      constructor
      · rw [hR2]
        rw [Finset.mem_inter]
        constructor
        · exact hIA
        · exact Finset.mem_insert_self I {J}
      · intro hJmem
        have hEq := Finset.pair_comm I J
        rw [← hEq] at hJmem
        rw [hR2] at hJmem
        rw [Finset.mem_inter] at hJmem
        exact hJA hJmem.1
    · intro A B
      exact km_canonical_rep rev hKM A B
  · intro hEx
    obtain ⟨F, hF⟩ := hEx
    have hMin := minSet_satisfiesKM F
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro A B
      rw [hF A B]
      exact hMin.r1 A B
    · intro A B h
      rw [hF A B]
      exact hMin.r2 A B h
    · intro A B h
      rw [hF A B]
      exact hMin.r3 A B h
    · intro A A' B B' hA hB
      rw [hF A B, hF A' B', hA, hB]
    · intro A B C
      rw [hF A B, hF A (B ∩ C)]
      exact hMin.r5 A B C
    · intro A B C h
      rw [hF A B] at h
      rw [hF A (B ∩ C), hF A B]
      exact hMin.r6 A B C h

/-- Hamming distance between two interpretations: the number of atoms on
which they differ. -/
def dalalDist {σ : Type*} [Fintype σ] [DecidableEq σ] (I J : Interp σ) : ℕ :=
  (Finset.univ.filter fun a => I a ≠ J a).card

/-- The Dalal key of an interpretation `J` relative to a model set `A`: its
least Hamming distance to a model in `A`. Dalal's original construction
(AAAI 1988) assumes a consistent knowledge base, so the empty case needs a
convention: here the key of every interpretation is `0` when `A` is empty
(so every interpretation is then Dalal-equivalent). This totalization is
an explicit extension of Dalal's definition, chosen so that `dalalRev`
satisfies the KM postulates also for the empty base. -/
noncomputable def dalalKey {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Finset (Interp σ)) (J : Interp σ) : ℕ :=
  if h : A.Nonempty then (A.image (fun I => dalalDist I J)).min' (h.image _) else 0

/-- The Dalal preorder: `I` precedes `J` when `I` is at least as close to
`A` as `J` is, in Hamming distance. -/
def dalalLe {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Finset (Interp σ)) (I J : Interp σ) : Prop :=
  dalalKey A I ≤ dalalKey A J

theorem dalalDist_self {σ : Type*} [Fintype σ] [DecidableEq σ] (I : Interp σ) :
    dalalDist I I = 0 := by
  unfold dalalDist
  have h : ∀ a ∈ Finset.univ, ¬ (I a ≠ I a) := fun a _ hne => hne rfl
  rw [Finset.filter_false_of_mem h, Finset.card_empty]

theorem dalalDist_eq_of_eq_zero {σ : Type*} [Fintype σ] [DecidableEq σ]
    {I J : Interp σ} (h : dalalDist I J = 0) : I = J := by
  unfold dalalDist at h
  have hEmpty : Finset.univ.filter (fun a => I a ≠ J a) = ∅ :=
    Finset.card_eq_zero.mp h
  have hEq : ∀ a, I a = J a := by
    intro a
    by_contra hNe
    have hMem : a ∈ Finset.univ.filter (fun a => I a ≠ J a) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hNe⟩
    rw [hEmpty] at hMem
    exact Finset.notMem_empty a hMem
  exact funext hEq

theorem dalalKey_eq_zero_of_mem {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Finset (Interp σ)) (I : Interp σ) (hI : I ∈ A) : dalalKey A I = 0 := by
  unfold dalalKey
  split
  · next h =>
    have h0mem : 0 ∈ A.image (fun K => dalalDist K I) :=
      Finset.mem_image.mpr ⟨I, hI, dalalDist_self I⟩
    have hLe : (A.image (fun K => dalalDist K I)).min' (h.image _) ≤ 0 :=
      Finset.min'_le _ _ h0mem
    exact Nat.le_antisymm hLe (Nat.zero_le _)
  · rfl

theorem dalalKey_pos_of_notMem {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A : Finset (Interp σ)) (J : Interp σ) (hA : A.Nonempty) (hJ : J ∉ A) :
    0 < dalalKey A J := by
  unfold dalalKey
  split
  · next h =>
    apply Nat.pos_of_ne_zero
    intro hEq
    have hMem : (A.image (fun K => dalalDist K J)).min' (h.image _) ∈
        A.image (fun K => dalalDist K J) :=
      Finset.min'_mem _ _
    rw [hEq] at hMem
    obtain ⟨K, hKmem, hKeq⟩ := Finset.mem_image.mp hMem
    have hKJ : K = J := dalalDist_eq_of_eq_zero hKeq
    rw [hKJ] at hKmem
    exact hJ hKmem
  · next h =>
    exact absurd hA h

/-- The Dalal assignment is faithful. -/
noncomputable def dalalAssignment (σ : Type*) [Fintype σ] [DecidableEq σ] :
    FaithfulAssignment σ where
  ord := dalalLe
  refl := by
    intro A I
    exact Nat.le_refl _
  trans := by
    intro A I J K h1 h2
    exact Nat.le_trans h1 h2
  total := by
    intro A I J
    exact Nat.le_total _ _
  faithful_models := by
    intro A I hI J hJ hStrict
    have hI0 : dalalKey A I = 0 := dalalKey_eq_zero_of_mem A I hI
    have hJ0 : dalalKey A J = 0 := dalalKey_eq_zero_of_mem A J hJ
    have hJI : dalalLe A J I := by
      unfold dalalLe
      rw [hJ0, hI0]
    exact hStrict.2 hJI
  faithful_strict := by
    intro A I hI J hJ
    have hA : A.Nonempty := ⟨I, hI⟩
    have hI0 : dalalKey A I = 0 := dalalKey_eq_zero_of_mem A I hI
    have hJpos : 0 < dalalKey A J := dalalKey_pos_of_notMem A J hA hJ
    unfold dalalLe
    rw [hI0]
    constructor
    · exact Nat.zero_le _
    · intro hle
      omega

/-- Dalal's revision operator: revise by selecting the models of the new
sentence closest (in Hamming distance) to the old model set `A`, when `A` is nonempty.
For an empty old model set every key `dalalKey ∅ J` is `0`, so `dalalRev ∅ B = B`. -/
noncomputable def dalalRev {σ : Type*} [Fintype σ] [DecidableEq σ]
    (A B : Finset (Interp σ)) : Finset (Interp σ) :=
  minSet (dalalLe A) B

/-- Dalal revision satisfies the KM postulates (nonvacuity of the
representation theorem's right-to-left direction, with an explicitly
constructed operator). -/
theorem dalal_satisfiesKM {σ : Type*} [Fintype σ] [DecidableEq σ] :
    SatisfiesKM (σ := σ) dalalRev := by
  exact minSet_satisfiesKM (dalalAssignment σ)

end Cslib.BeliefRevision
