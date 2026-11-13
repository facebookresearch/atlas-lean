/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Kneser–Lovász theorem

For `0 < k` and `2 * k ≤ n`, the Kneser graph on the `k`-subsets of an
`n`-element set has chromatic number `n - 2 * k + 2`.
-/

namespace MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted

open Finset

abbrev KneserVertex (n k : ℕ) := { s : Finset (Fin n) // s.card = k }

def kneserGraph (n k : ℕ) : SimpleGraph (KneserVertex n k) where
  Adj x y := Disjoint x.val y.val ∧ x ≠ y
  symm.symm := by
    intro a b ⟨hdisj, hne⟩
    exact ⟨hdisj.symm, hne.symm⟩
  loopless.irrefl := by
    intro a ⟨_, hne⟩
    exact hne rfl

instance (n k : ℕ) : DecidableRel (kneserGraph n k).Adj := by
  unfold kneserGraph
  infer_instance

/-- **Adjacency in the Kneser graph.** For natural numbers $n$ and $k$ and $k$-element subsets
$x$ and $y$ of $\{0, 1, \dots, n-1\}$, the vertices $x$ and $y$ of the Kneser graph $K(n, k)$
are adjacent if and only if $x$ and $y$ are disjoint and $x \ne y$. -/
public theorem kneserGraph_adj_iff (n k : ℕ) (x y : KneserVertex n k) :
    (kneserGraph n k).Adj x y ↔ Disjoint x.val y.val ∧ x ≠ y :=
  Iff.rfl

private def knNegLabel {n : ℕ} (l : Bool × Fin n) : Bool × Fin n := (!l.1, l.2)

private theorem knNegLabel_invol {n : ℕ} : Function.Involutive (@knNegLabel n) := by
  classical
  intro l
  obtain ⟨b, i⟩ := l
  cases b <;> rfl

private theorem knNegLabel_inj {n : ℕ} : Function.Injective (@knNegLabel n) :=
  knNegLabel_invol.injective

private theorem knNegLabel_invol_apply {n : ℕ} (l : Bool × Fin n) :
    knNegLabel (knNegLabel l) = l :=
  knNegLabel_invol l

private def knNegLabelEmb {n : ℕ} : (Bool × Fin n) ↪ (Bool × Fin n) :=
  ⟨knNegLabel, knNegLabel_inj⟩

private def knNegCell {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Bool × Fin n) :=
  x.map knNegLabelEmb

private theorem knNegCell_empty {n : ℕ} :
    knNegCell (∅ : Finset (Bool × Fin n)) = ∅ := by
  classical
  simp [knNegCell]

private theorem knNegCell_card {n : ℕ} (x : Finset (Bool × Fin n)) :
    (knNegCell x).card = x.card := by
  classical
  simp [knNegCell]

private theorem knMem_negCell {n : ℕ} {x : Finset (Bool × Fin n)} {l : Bool × Fin n} :
    l ∈ knNegCell x ↔ ∃ m ∈ x, knNegLabel m = l := by
  classical
  rw [knNegCell]
  exact Finset.mem_map

private theorem knNegLabel_mem_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
    {m : Bool × Fin n} (hm : m ∈ x) : knNegLabel m ∈ knNegCell x := by
  classical
  rw [knMem_negCell]
  exact ⟨m, hm, rfl⟩

private theorem knNegCell_invol {n : ℕ} (x : Finset (Bool × Fin n)) :
    knNegCell (knNegCell x) = x := by
  classical
  ext l
  simp only [knMem_negCell]
  constructor
  · rintro ⟨m, hm, hml⟩
    obtain ⟨m', hm', hm'm⟩ := hm
    have hme : m' = l := by
      have h1 : knNegLabel (knNegLabel m') = knNegLabel m :=
        congrArg knNegLabel hm'm
      rwa [knNegLabel_invol_apply, hml] at h1
    rw [← hme]
    exact hm'
  · intro hl
    exact ⟨knNegLabel l, ⟨l, hl, rfl⟩, knNegLabel_invol_apply l⟩

private def knConsistent {n : ℕ} (x : Finset (Bool × Fin n)) : Prop :=
  ∀ l ∈ x, knNegLabel l ∉ x

private def knIsChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  ∀ a ∈ σ, ∀ b ∈ σ, a ⊆ b ∨ b ⊆ a

private def knChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  σ.Nonempty ∧ (∀ x ∈ σ, knConsistent x) ∧ knIsChain σ

private def knTop {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
    Finset (Bool × Fin n) :=
  σ.sup id

private def knImg {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Bool × Fin n) :=
  σ.image L

private def knHappy {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knChain σ ∧ knTop σ ⊆ knImg σ L

private def knTight {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knHappy σ L ∧ σ.card = (knTop σ).card

private def knLoose {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  knHappy σ L ∧ σ.card = (knTop σ).card + 1

private def knAntipodal {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  ∀ x, knConsistent x → x.Nonempty → L (knNegCell x) = knNegLabel (L x)

private def knNoCompl {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) : Prop :=
  ∀ x y, knConsistent x → knConsistent y → x ⊆ y → L y ≠ knNegLabel (L x)

private theorem knMem_subset_top {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    {x : Finset (Bool × Fin n)} (hx : x ∈ σ) : x ⊆ knTop σ := by
  classical
  have h := Finset.le_sup (s := σ) (f := id) hx
  simpa [knTop] using h

private theorem knTop_sup_le {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    {m : Finset (Bool × Fin n)} (h : ∀ x ∈ σ, x ⊆ m) : knTop σ ⊆ m := by
  classical
  have h2 : σ.sup id ≤ m := by
    rw [Finset.sup_le_iff]
    intro b hb
    simpa using h b hb
  simpa [knTop] using h2

private theorem knChain_top_mem {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (h : knChain σ) : knTop σ ∈ σ := by
  classical
  obtain ⟨hne, _, hchain⟩ := h
  obtain ⟨m, hmσ, hmax⟩ := Finset.exists_max_image σ Finset.card hne
  have hsub : ∀ x ∈ σ, x ⊆ m := by
    intro x hx
    rcases hchain x hx m hmσ with hsub | hsub
    · exact hsub
    · have hle : x.card ≤ m.card := hmax x hx
      have hme : m = x := Finset.eq_of_subset_of_card_le hsub hle
      subst hme
      exact Subset.rfl
  have htop : knTop σ = m := by
    apply le_antisymm
    · exact knTop_sup_le σ hsub
    · exact knMem_subset_top σ hmσ
  rw [htop]
  exact hmσ

private theorem knChain_eq_of_mem_card_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (hchain : knIsChain σ) {a b : Finset (Bool × Fin n)}
    (ha : a ∈ σ) (hb : b ∈ σ) (hcard : a.card = b.card) : a = b := by
  classical
  rcases hchain a ha b hb with h | h
  · exact Finset.eq_of_subset_of_card_le h (by omega)
  · exact (Finset.eq_of_subset_of_card_le h (by omega)).symm

private theorem knChain_card_le {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (h : knChain σ) : σ.card ≤ (knTop σ).card + 1 := by
  classical
  obtain ⟨_, _, hchain⟩ := h
  have hmaps : Set.MapsTo Finset.card (↑σ : Set (Finset (Bool × Fin n)))
      (↑(Finset.range ((knTop σ).card + 1)) : Set ℕ) := by
    intro x hx
    have hxσ : x ∈ σ := Finset.mem_coe.mp hx
    have hsub : x ⊆ knTop σ := knMem_subset_top σ hxσ
    have hcc := Finset.card_le_card hsub
    rw [Finset.mem_coe, Finset.mem_range]
    omega
  have hinj : Set.InjOn Finset.card (↑σ : Set (Finset (Bool × Fin n))) := by
    intro a ha b hb hab
    have ha' : a ∈ σ := Finset.mem_coe.mp ha
    have hb' : b ∈ σ := Finset.mem_coe.mp hb
    exact knChain_eq_of_mem_card_eq σ hchain ha' hb' hab
  have hle := Finset.card_le_card_of_injOn Finset.card hmaps hinj
  rwa [Finset.card_range] at hle

private theorem knChain_insert {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    {v : Finset (Bool × Fin n)} (hchain : knChain σ) (hcons : knConsistent v)
    (hcomp : ∀ x ∈ σ, x ⊆ v ∨ v ⊆ x) : knChain (insert v σ) := by
  classical
  obtain ⟨_, hconsσ, hch⟩ := hchain
  refine ⟨Finset.insert_nonempty v σ, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hcons
    · exact hconsσ x hx
  · intro a ha b hb
    rw [Finset.mem_insert] at ha hb
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact Or.inl Subset.rfl
    · exact (hcomp b hb).symm
    · exact hcomp a ha
    · exact hch a ha b hb

private theorem knTop_insert {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (v : Finset (Bool × Fin n)) : knTop (insert v σ) = v ∪ knTop σ := by
  classical
  have h : (insert v σ).sup id = id v ⊔ σ.sup id := Finset.sup_insert
  have h2 : id v ⊔ σ.sup id = v ∪ knTop σ := by
    simp [knTop, Finset.sup_eq_union]
  unfold knTop
  rw [h]
  exact h2

private theorem knTop_insert_of_subset {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (v : Finset (Bool × Fin n)) (h : v ⊆ knTop σ) :
    knTop (insert v σ) = knTop σ := by
  classical
  rw [knTop_insert]
  exact Finset.union_eq_right.mpr h

private theorem knTop_insert_of_supset {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (v : Finset (Bool × Fin n)) (h : knTop σ ⊆ v) :
    knTop (insert v σ) = v := by
  classical
  rw [knTop_insert]
  exact Finset.union_eq_left.mpr h

private theorem knImageCard_subset {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
    σ.image Finset.card ⊆ Finset.range ((knTop σ).card + 1) := by
  classical
  intro j hj
  rw [Finset.mem_image] at hj
  obtain ⟨x, hx, rfl⟩ := hj
  rw [Finset.mem_range]
  have hle := Finset.card_le_card (knMem_subset_top σ hx)
  omega

private theorem knImageCard_card {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (h : knChain σ) : (σ.image Finset.card).card = σ.card := by
  classical
  apply Finset.card_image_of_injOn
  intro a ha b hb hab
  have ha' : a ∈ σ := Finset.mem_coe.mp ha
  have hb' : b ∈ σ := Finset.mem_coe.mp hb
  exact knChain_eq_of_mem_card_eq σ h.2.2 ha' hb' hab

private theorem knHappy_card_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knHappy σ L) :
    σ.card = (knTop σ).card ∨ σ.card = (knTop σ).card + 1 := by
  classical
  obtain ⟨hchain, hsub⟩ := h
  have h1 : (knTop σ).card ≤ (knImg σ L).card := Finset.card_le_card hsub
  have h2 : (knImg σ L).card ≤ σ.card := by
    unfold knImg
    exact Finset.card_image_le
  have h3 : σ.card ≤ (knTop σ).card + 1 := knChain_card_le σ hchain
  omega

private theorem knTight_image {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
    knImg σ L = knTop σ := by
  classical
  obtain ⟨⟨_, hsub⟩, hcard⟩ := h
  have h2 : (knImg σ L).card ≤ (knTop σ).card := by
    calc (knImg σ L).card ≤ σ.card := by
            unfold knImg
            exact Finset.card_image_le
      _ = (knTop σ).card := hcard
  have heq := Finset.eq_of_subset_of_card_le hsub h2
  exact heq.symm

private theorem knTight_injOn {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
    Set.InjOn L (↑σ : Set (Finset (Bool × Fin n))) := by
  classical
  have htop : knImg σ L = knTop σ := knTight_image σ L h
  obtain ⟨_, hcard⟩ := h
  have h2 : (σ.image L).card = σ.card := by
    have hcc := congrArg Finset.card htop
    simp only [knImg] at hcc
    omega
  exact Finset.injOn_of_card_image_eq h2

private theorem knTight_top_card_pos {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
    1 ≤ (knTop σ).card := by
  classical
  obtain ⟨⟨⟨hne, _, _⟩, _⟩, hcard⟩ := h
  obtain ⟨x, hx⟩ := hne
  have h1 : 1 ≤ σ.card := Finset.one_le_card.mpr ⟨x, hx⟩
  omega

private theorem knLoose_imageCard {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L) :
    σ.image Finset.card = Finset.range ((knTop σ).card + 1) := by
  classical
  obtain ⟨⟨hchain, _⟩, hcard⟩ := h
  have hsub := knImageCard_subset σ
  have hcc := knImageCard_card σ hchain
  have hreq : (σ.image Finset.card).card = (Finset.range ((knTop σ).card + 1)).card := by
    rw [hcc, hcard, Finset.card_range]
  exact Finset.eq_of_subset_of_card_le hsub (by omega)

private theorem knLoose_has_level {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L) {j : ℕ}
    (hj : j ≤ (knTop σ).card) : ∃ x ∈ σ, x.card = j := by
  classical
  have hmem : j ∈ σ.image Finset.card := by
    rw [knLoose_imageCard σ L h, Finset.mem_range]
    omega
  obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hmem
  exact ⟨x, hx, hxj⟩

private theorem knLoose_empty_mem {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L) : ∅ ∈ σ := by
  classical
  obtain ⟨x, hx, hxj⟩ := knLoose_has_level σ L h (Nat.zero_le _)
  have hx0 : x = ∅ := Finset.card_eq_zero.mp hxj
  rwa [hx0] at hx

private theorem knTight_missing {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
    ∃ j, j ≤ (knTop σ).card ∧
      σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j := by
  classical
  obtain ⟨⟨hchain, _⟩, hcard⟩ := h
  have hsub : σ.image Finset.card ⊆ Finset.range ((knTop σ).card + 1) :=
    knImageCard_subset σ
  have hcc : (σ.image Finset.card).card = (knTop σ).card := by
    have hcc2 := knImageCard_card σ hchain
    omega
  have hsdiff : ((Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card).card = 1 := by
    have hunion := Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint ((Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card)
        (σ.image Finset.card) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx1).2 hx2
    have hcu := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_range] at hcu
    omega
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hsdiff
  have hjmem : j ∈ Finset.range ((knTop σ).card + 1) := by
    have hmem : j ∈ ({j} : Finset ℕ) := Finset.mem_singleton_self j
    rw [← hj] at hmem
    exact (Finset.mem_sdiff.mp hmem).1
  have hjeq : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j := by
    ext x
    rw [Finset.mem_erase]
    constructor
    · intro hx
      refine ⟨?_, hsub hx⟩
      intro hxj
      have hmem : j ∈ (Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card := by
        rw [hj]
        exact Finset.mem_singleton_self j
      have hxj' : j ∈ σ.image Finset.card := by
        rw [← hxj]
        exact hx
      exact (Finset.mem_sdiff.mp hmem).2 hxj'
    · intro hx
      obtain ⟨hne, hxr⟩ := hx
      by_contra hxnot
      have hmem : x ∈ (Finset.range ((knTop σ).card + 1)) \ σ.image Finset.card :=
        Finset.mem_sdiff.mpr ⟨hxr, hxnot⟩
      rw [hj] at hmem
      exact hne (Finset.mem_singleton.mp hmem)
  rw [Finset.mem_range] at hjmem
  exact ⟨j, by omega, hjeq⟩

private theorem knTight_no_level {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (_h : knTight σ L) {j : ℕ}
    (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
    {x : Finset (Bool × Fin n)} (hx : x ∈ σ) : x.card ≠ j := by
  classical
  intro hcx
  have hmem : x.card ∈ (Finset.range ((knTop σ).card + 1)).erase j := by
    rw [← hj]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  exact (Finset.mem_erase.mp hmem).1 hcx

private theorem knTight_has_level {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (_h : knTight σ L) {j : ℕ}
    (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
    {m : ℕ} (hm : m ≤ (knTop σ).card) (hmj : m ≠ j) : ∃ x ∈ σ, x.card = m := by
  classical
  have hmem : m ∈ σ.image Finset.card := by
    rw [hj, Finset.mem_erase, Finset.mem_range]
    exact ⟨hmj, by omega⟩
  obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hmem
  exact ⟨x, hx, hxj⟩

private theorem knTight_empty_iff {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
    (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j) :
    (∅ ∈ σ) ↔ j ≠ 0 := by
  classical
  constructor
  · intro hmem heq
    subst heq
    exact knTight_no_level σ L h hj hmem Finset.card_empty
  · intro hne
    obtain ⟨x, hx, hxj⟩ := knTight_has_level σ L h hj (Nat.zero_le _) (Ne.symm hne)
    have hx0 : x = ∅ := Finset.card_eq_zero.mp hxj
    rwa [hx0] at hx

private theorem knSdiff_card_two {α : Type*} [DecidableEq α] {a b : Finset α}
    (hab : a ⊆ b) (hcard : b.card = a.card + 2) : (b \ a).card = 2 := by
  classical
  have hunion := Finset.sdiff_union_of_subset hab
  have hdisj : Disjoint (b \ a) a := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_sdiff.mp hx1).2 hx2
  have hcu := Finset.card_union_of_disjoint hdisj
  rw [hunion] at hcu
  omega

private theorem knInsert_injOn {α : Type*} [DecidableEq α] {a b : Finset α} :
    Set.InjOn (fun x => insert x a) (↑(b \ a) : Set α) := by
  classical
  intro x hx y hy hxy
  have hxna : x ∉ a := (Finset.mem_sdiff.mp (Finset.mem_coe.mp hx)).2
  have hxy' : insert x a = insert y a := hxy
  have hxmem : x ∈ insert y a := by
    rw [← hxy']
    exact Finset.mem_insert_self x a
  rcases Finset.mem_insert.mp hxmem with heq | hcon
  · exact heq
  · exact absurd hcon hxna

private theorem knBetween_mem {α : Type*} [DecidableEq α] {a b : Finset α}
    (hab : a ⊆ b) {v : Finset α} :
    v ∈ (b \ a).image (fun x => insert x a) ↔
      a ⊆ v ∧ v ⊆ b ∧ v.card = a.card + 1 := by
  classical
  constructor
  · intro hv
    obtain ⟨x, hx, hxeq⟩ := Finset.mem_image.mp hv
    have hxmem := Finset.mem_sdiff.mp hx
    have hxa : x ∉ a := hxmem.2
    have hxb : x ∈ b := hxmem.1
    refine ⟨?_, ?_, ?_⟩
    · rw [← hxeq]
      exact Finset.subset_insert x a
    · rw [← hxeq]
      exact Finset.insert_subset hxb hab
    · rw [← hxeq]
      exact Finset.card_insert_of_notMem hxa
  · intro hv
    obtain ⟨hav1, hbv, hvcard⟩ := hv
    have hva1 : (v \ a).card = 1 := by
      have hunion := Finset.sdiff_union_of_subset hav1
      have hdisj : Disjoint (v \ a) a := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        exact (Finset.mem_sdiff.mp hx1).2 hx2
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hunion] at hcu
      omega
    obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hva1
    have hxmem : x ∈ v ∧ x ∉ a := by
      have hself : x ∈ ({x} : Finset α) := Finset.mem_singleton_self x
      rw [← hx] at hself
      exact ⟨(Finset.mem_sdiff.mp hself).1, (Finset.mem_sdiff.mp hself).2⟩
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_sdiff.mpr ⟨hbv hxmem.1, hxmem.2⟩, ?_⟩
    show insert x a = v
    apply le_antisymm
    · exact Finset.insert_subset hxmem.1 hav1
    · intro y hy
      show y ∈ insert x a
      rw [Finset.mem_insert]
      by_cases hya : y ∈ a
      · exact Or.inr hya
      · left
        have hmem : y ∈ v \ a := Finset.mem_sdiff.mpr ⟨hy, hya⟩
        rw [hx] at hmem
        exact Finset.mem_singleton.mp hmem

private theorem knBetween_card {α : Type*} [DecidableEq α] {a b : Finset α}
    (hab : a ⊆ b) (hcard : b.card = a.card + 2) :
    ((b \ a).image (fun x => insert x a)).card = 2 := by
  classical
  rw [Finset.card_image_of_injOn knInsert_injOn]
  exact knSdiff_card_two hab hcard

open Classical in
private noncomputable def knOut {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Finset (Bool × Fin n)) :=
  Finset.univ.filter (fun v => v ∉ σ ∧ knChain (insert v σ) ∧ knTop (insert v σ) ⊆ knImg σ L)

open Classical in
private noncomputable def knIn {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) : Finset (Finset (Bool × Fin n)) :=
  σ.filter (fun w => knHappy (σ.erase w) L ∧ knTop σ ⊆ knImg (σ.erase w) L)

private theorem knMem_out {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
    {L : Finset (Bool × Fin n) → Bool × Fin n} {v : Finset (Bool × Fin n)} :
    v ∈ knOut σ L ↔
      v ∉ σ ∧ knChain (insert v σ) ∧ knTop (insert v σ) ⊆ knImg σ L := by
  classical
  unfold knOut
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem knMem_in {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
    {L : Finset (Bool × Fin n) → Bool × Fin n} {w : Finset (Bool × Fin n)} :
    w ∈ knIn σ L ↔
      w ∈ σ ∧ knHappy (σ.erase w) L ∧ knTop σ ⊆ knImg (σ.erase w) L := by
  classical
  unfold knIn
  rw [Finset.mem_filter]

private def knGAdj {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ τ : Finset (Finset (Bool × Fin n))) : Prop :=
  knHappy σ L ∧ knHappy τ L ∧
    ((∃ v, v ∉ σ ∧ τ = insert v σ ∧ knTop τ ⊆ knImg σ L) ∨
     (∃ w, w ∉ τ ∧ σ = insert w τ ∧ knTop σ ⊆ knImg τ L))

private theorem knGAdj_symm {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ τ : Finset (Finset (Bool × Fin n))) (h : knGAdj L σ τ) : knGAdj L τ σ := by
  classical
  obtain ⟨hs, ht, hdoor⟩ := h
  exact ⟨ht, hs, hdoor.elim Or.inr Or.inl⟩

private theorem knGAdj_irrefl {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n)
    (σ : Finset (Finset (Bool × Fin n))) (h : knGAdj L σ σ) : False := by
  classical
  obtain ⟨_, _, hdoor⟩ := h
  rcases hdoor with ⟨v, hv, heq, _⟩ | ⟨w, hw, heq, _⟩
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hv] at hcc
    omega
  · have hcc := congrArg Finset.card heq
    rw [Finset.card_insert_of_notMem hw] at hcc
    omega

private def knG {n : ℕ} (L : Finset (Bool × Fin n) → Bool × Fin n) :
    SimpleGraph (Finset (Finset (Bool × Fin n))) where
  Adj := knGAdj L
  symm := ⟨fun σ τ h => knGAdj_symm L σ τ h⟩
  loopless := ⟨fun σ h => knGAdj_irrefl L σ h⟩

private noncomputable instance knGDec {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    DecidableRel (knG L).Adj :=
  Classical.decRel _

private theorem knOut_neighbor {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
    {L : Finset (Bool × Fin n) → Bool × Fin n} (hσ : knHappy σ L)
    {v : Finset (Bool × Fin n)} (hv : v ∈ knOut σ L) :
    (knG L).Adj σ (insert v σ) := by
  classical
  rw [knMem_out] at hv
  obtain ⟨hvn, hchain, htop⟩ := hv
  refine ⟨hσ, ⟨hchain, ?_⟩, Or.inl ⟨v, hvn, rfl, htop⟩⟩
  exact htop.trans (Finset.image_subset_image (Finset.subset_insert v σ))

private theorem knIn_neighbor {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
    {L : Finset (Bool × Fin n) → Bool × Fin n} (hσ : knHappy σ L)
    {w : Finset (Bool × Fin n)} (hw : w ∈ knIn σ L) :
    (knG L).Adj σ (σ.erase w) := by
  classical
  rw [knMem_in] at hw
  obtain ⟨hwm, hhappy, htop⟩ := hw
  refine ⟨hσ, hhappy, Or.inr ⟨w, Finset.notMem_erase w σ, ?_, htop⟩⟩
  exact (Finset.insert_erase hwm).symm

private theorem knNeighbor_out_or_in {n : ℕ} {σ τ : Finset (Finset (Bool × Fin n))}
    {L : Finset (Bool × Fin n) → Bool × Fin n} (h : (knG L).Adj σ τ) :
    (∃ v ∈ knOut σ L, insert v σ = τ) ∨ (∃ w ∈ knIn σ L, σ.erase w = τ) := by
  classical
  obtain ⟨_, hτ, hdoor⟩ := h
  rcases hdoor with ⟨v, hvn, heq, htop⟩ | ⟨w, hwn, heq, htop⟩
  · left
    have hchain : knChain (insert v σ) := by
      rw [← heq]
      exact hτ.1
    have htop' : knTop (insert v σ) ⊆ knImg σ L := by
      rw [← heq]
      exact htop
    have hmem : v ∈ knOut σ L := by
      rw [knMem_out]
      exact ⟨hvn, hchain, htop'⟩
    exact ⟨v, hmem, heq.symm⟩
  · right
    have hwm : w ∈ σ := by
      rw [heq]
      exact Finset.mem_insert_self w τ
    have herase : σ.erase w = τ := by
      rw [heq]
      exact Finset.erase_insert hwn
    have hhappy : knHappy (σ.erase w) L := by
      rw [herase]
      exact hτ
    have htop' : knTop σ ⊆ knImg (σ.erase w) L := by
      rw [herase]
      exact htop
    have hmem : w ∈ knIn σ L := by
      rw [knMem_in]
      exact ⟨hwm, hhappy, htop'⟩
    exact ⟨w, hmem, herase⟩

private theorem knNeighborFinset_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hσ : knHappy σ L) :
    (knG L).neighborFinset σ =
      (knOut σ L).image (fun v => insert v σ) ∪
        (knIn σ L).image (fun w => σ.erase w) := by
  classical
  ext τ
  rw [SimpleGraph.mem_neighborFinset, Finset.mem_union]
  constructor
  · intro hadj
    rcases knNeighbor_out_or_in hadj with ⟨v, hv, heqv⟩ | ⟨w, hw, heqw⟩
    · left
      exact Finset.mem_image.mpr ⟨v, hv, heqv⟩
    · right
      exact Finset.mem_image.mpr ⟨w, hw, heqw⟩
  · intro hmem
    rcases hmem with hmem | hmem
    · obtain ⟨v, hv, heqv⟩ := Finset.mem_image.mp hmem
      rw [← heqv]
      exact knOut_neighbor hσ hv
    · obtain ⟨w, hw, heqw⟩ := Finset.mem_image.mp hmem
      rw [← heqw]
      exact knIn_neighbor hσ hw

private theorem knOutIn_disjoint {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    Disjoint ((knOut σ L).image (fun v => insert v σ))
      ((knIn σ L).image (fun w => σ.erase w)) := by
  classical
  rw [Finset.disjoint_left]
  intro τ h1 h2
  obtain ⟨v, hv, heqv⟩ := Finset.mem_image.mp h1
  obtain ⟨w, hw, heqw⟩ := Finset.mem_image.mp h2
  rw [knMem_out] at hv
  rw [knMem_in] at hw
  have h1c : τ.card = σ.card + 1 := by
    rw [← heqv]
    exact Finset.card_insert_of_notMem hv.1
  have h2c : (σ.erase w).card = σ.card - 1 := Finset.card_erase_of_mem hw.1
  have heqw' : σ.erase w = τ := heqw
  rw [heqw'] at h2c
  omega

private theorem knInsert_injOn_out {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
    Set.InjOn (fun v => insert v σ) {v | v ∉ σ} := by
  classical
  intro u hu v hv huv
  have hu' : u ∉ σ := hu
  have hv' : v ∉ σ := hv
  have huv' : insert u σ = insert v σ := huv
  have hmem : u ∈ insert v σ := by
    rw [← huv']
    exact Finset.mem_insert_self u σ
  rcases Finset.mem_insert.mp hmem with heq | hcon
  · exact heq
  · exact absurd hcon hu'

private theorem knOut_image_card {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    ((knOut σ L).image (fun v => insert v σ)).card = (knOut σ L).card := by
  classical
  apply Finset.card_image_of_injOn
  refine Set.InjOn.mono ?_ (knInsert_injOn_out σ)
  intro x hx
  change x ∉ σ
  have hxo : x ∈ knOut σ L := Finset.mem_coe.mp hx
  exact (knMem_out.mp hxo).1

private theorem knErase_injOn_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
    Set.InjOn (fun w => σ.erase w) (↑σ : Set (Finset (Bool × Fin n))) := by
  classical
  intro a ha b hb hab
  have ha' : a ∈ σ := Finset.mem_coe.mp ha
  have hb' : b ∈ σ := Finset.mem_coe.mp hb
  by_contra hne0
  have hmem : a ∈ σ.erase b := Finset.mem_erase.mpr ⟨hne0, ha'⟩
  have hab' : σ.erase a = σ.erase b := hab
  rw [← hab'] at hmem
  exact Finset.notMem_erase a σ hmem

private theorem knIn_image_card {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    ((knIn σ L).image (fun w => σ.erase w)).card = (knIn σ L).card := by
  classical
  apply Finset.card_image_of_injOn
  refine Set.InjOn.mono ?_ (knErase_injOn_in σ)
  intro x hx
  have hxo : x ∈ knIn σ L := Finset.mem_coe.mp hx
  exact Finset.mem_coe.mpr (knMem_in.mp hxo).1

private theorem knDegree_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hσ : knHappy σ L) :
    (knG L).degree σ = (knOut σ L).card + (knIn σ L).card := by
  classical
  have hne := knNeighborFinset_eq σ L hσ
  have hdisj := knOutIn_disjoint σ L
  have hcard := Finset.card_union_of_disjoint hdisj
  have ho := knOut_image_card σ L
  have hi := knIn_image_card σ L
  unfold SimpleGraph.degree
  rw [hne, hcard, ho, hi]

private theorem knDegree_nothappy {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hσ : ¬ knHappy σ L) :
    (knG L).degree σ = 0 := by
  classical
  have hempty : (knG L).neighborFinset σ = ∅ := by
    ext τ
    simp only [SimpleGraph.mem_neighborFinset, Finset.notMem_empty, iff_false]
    intro hadj
    obtain ⟨hs, _, _⟩ := hadj
    exact hσ hs
  unfold SimpleGraph.degree
  rw [hempty, Finset.card_empty]

private theorem knTight_no_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
    knIn σ L = ∅ := by
  classical
  ext w
  simp only [knMem_in, Finset.notMem_empty, iff_false]
  intro hw
  obtain ⟨hwm, _, htopsub⟩ := hw
  obtain ⟨hhappy, hcard⟩ := h
  obtain ⟨x, hx⟩ := hhappy.1.1
  have hpos : 1 ≤ σ.card := Finset.one_le_card.mpr ⟨x, hx⟩
  have h1 : (knTop σ).card ≤ (knImg (σ.erase w) L).card :=
    Finset.card_le_card htopsub
  have h2 : (knImg (σ.erase w) L).card ≤ (σ.erase w).card := by
    unfold knImg
    exact Finset.card_image_le
  have h3 : (σ.erase w).card = σ.card - 1 := Finset.card_erase_of_mem hwm
  omega

private theorem knTight_out_card_eq {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
    (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
    {v : Finset (Bool × Fin n)} (hv : v ∈ knOut σ L) : v.card = j := by
  classical
  have himg : knImg σ L = knTop σ := knTight_image σ L h
  rw [knMem_out] at hv
  obtain ⟨hvn, hchainI, htopI⟩ := hv
  have hsub : v ⊆ knTop σ := by
    have hunion : v ∪ knTop σ ⊆ knTop σ := by
      rw [← knTop_insert]
      rw [himg] at htopI
      exact htopI
    exact Finset.subset_union_left.trans hunion
  have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
  by_contra hne
  obtain ⟨x, hx, hxc⟩ := knTight_has_level σ L h hj hle hne
  obtain ⟨_, _, hisch⟩ := hchainI
  have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
  have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
  have heq : x = v := knChain_eq_of_mem_card_eq _ hisch hxv hvv hxc
  rw [heq] at hx
  exact hvn hx

private theorem knTight_out_mem {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L)
    {v : Finset (Bool × Fin n)} (hsub : v ⊆ knTop σ)
    (hcomp : ∀ x ∈ σ, x ⊆ v ∨ v ⊆ x) (hvn : v ∉ σ) : v ∈ knOut σ L := by
  classical
  obtain ⟨hhappy, _⟩ := h
  obtain ⟨hchain, hsub2⟩ := hhappy
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  have hconsσ : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hconTop : knConsistent (knTop σ) := hconsσ _ htopmem
  have hconv : knConsistent v := by
    intro l hl hnl
    exact hconTop l (hsub hl) (hsub hnl)
  have hchainI := knChain_insert σ hchain hconv hcomp
  rw [knMem_out]
  refine ⟨hvn, hchainI, ?_⟩
  rw [knTop_insert_of_subset σ v hsub]
  exact hsub2

private theorem knTight_out_zero {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
    (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
    (hj0 : j = 0) : knOut σ L = {∅} := by
  classical
  ext v
  rw [Finset.mem_singleton]
  constructor
  · intro hv
    have hcv := knTight_out_card_eq σ L h hj hv
    rw [hj0] at hcv
    exact Finset.card_eq_zero.mp hcv
  · intro hv
    rw [hv]
    refine knTight_out_mem σ L h (Finset.empty_subset _) ?_ ?_
    · intro x _
      exact Or.inr (Finset.empty_subset x)
    · intro hcon
      have hne := knTight_no_level σ L h hj hcon
      rw [hj0] at hne
      exact hne Finset.card_empty

private theorem knTight_out_two {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) {j : ℕ}
    (hj : σ.image Finset.card = (Finset.range ((knTop σ).card + 1)).erase j)
    (hjle : j ≤ (knTop σ).card) (hjge : 1 ≤ j) : (knOut σ L).card = 2 := by
  classical
  have hchain : knChain σ := h.1.1
  have hcard : σ.card = (knTop σ).card := h.2
  have hisch : knIsChain σ := hchain.2.2
  have htop_hit : (knTop σ).card ∈ σ.image Finset.card :=
    Finset.mem_image.mpr ⟨knTop σ, knChain_top_mem σ hchain, rfl⟩
  rw [hj] at htop_hit
  have hkj : (knTop σ).card ≠ j := (Finset.mem_erase.mp htop_hit).1
  have hjlt : j + 1 ≤ (knTop σ).card := by omega
  obtain ⟨a, ha_mem, ha_card⟩ :=
    knTight_has_level (m := j - 1) σ L h hj (by omega) (by omega)
  obtain ⟨b, hb_mem, hb_card⟩ :=
    knTight_has_level (m := j + 1) σ L h hj hjlt (by omega)
  have hab : a ⊆ b := by
    rcases hisch a ha_mem b hb_mem with hsub | hsub
    · exact hsub
    · exfalso
      have hle := Finset.card_le_card hsub
      omega
  have hOut_eq : knOut σ L = (b \ a).image (fun x => insert x a) := by
    ext v
    rw [knBetween_mem hab]
    constructor
    · intro hv
      have hvj := knTight_out_card_eq σ L h hj hv
      rw [knMem_out] at hv
      obtain ⟨_, hchainI, _⟩ := hv
      obtain ⟨_, _, hischI⟩ := hchainI
      have hav : a ⊆ v := by
        rcases hischI a (Finset.mem_insert_of_mem ha_mem) v
            (Finset.mem_insert_self v σ) with hsub | hsub
        · exact hsub
        · exfalso
          have hle := Finset.card_le_card hsub
          omega
      have hvb : v ⊆ b := by
        rcases hischI v (Finset.mem_insert_self v σ) b
            (Finset.mem_insert_of_mem hb_mem) with hsub | hsub
        · exact hsub
        · exfalso
          have hle := Finset.card_le_card hsub
          omega
      refine ⟨hav, hvb, ?_⟩
      omega
    · intro hv
      obtain ⟨hav, hvb, hvc⟩ := hv
      have hvj : v.card = j := by omega
      have hsub_top : v ⊆ knTop σ :=
        hvb.trans (knMem_subset_top σ hb_mem)
      have hcomp : ∀ x ∈ σ, x ⊆ v ∨ v ⊆ x := by
        intro x hx
        have hxj : x.card ≠ j := knTight_no_level σ L h hj hx
        have hxa := hisch x hx a ha_mem
        have hxb := hisch x hx b hb_mem
        by_cases hlt : x.card < v.card
        · left
          rcases hxa with hsub | hsub
          · exact hsub.trans hav
          · have hle1 := Finset.card_le_card hsub
            have heq : x.card = a.card := by omega
            have hxeq : x = a :=
              knChain_eq_of_mem_card_eq σ hisch hx ha_mem heq
            rw [hxeq]
            exact hav
        · right
          have hlt' : v.card < x.card := by omega
          rcases hxb with hsub | hsub
          · have hle2 := Finset.card_le_card hsub
            have heq : x.card = b.card := by omega
            have hxeq : x = b :=
              knChain_eq_of_mem_card_eq σ hisch hx hb_mem heq
            rw [hxeq]
            exact hvb
          · exact hvb.trans hsub
      have hvn : v ∉ σ := by
        intro hcon
        exact knTight_no_level σ L h hj hcon hvj
      exact knTight_out_mem σ L h hsub_top hcomp hvn
  rw [hOut_eq]
  exact knBetween_card hab (by omega)

private theorem knTight_degree {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
    ((knG L).degree σ = 1 ∧ ∅ ∉ σ) ∨ ((knG L).degree σ = 2 ∧ ∅ ∈ σ) := by
  classical
  obtain ⟨hhappy, hcard⟩ := h
  obtain ⟨j, hjle, hjeq⟩ := knTight_missing σ L ⟨hhappy, hcard⟩
  have hin : (knIn σ L).card = 0 := by
    rw [knTight_no_in σ L ⟨hhappy, hcard⟩, Finset.card_empty]
  have hdeg : (knG L).degree σ = (knOut σ L).card := by
    rw [knDegree_eq σ L hhappy, hin, add_zero]
  by_cases hj0 : j = 0
  · left
    have hout : knOut σ L = {∅} :=
      knTight_out_zero σ L ⟨hhappy, hcard⟩ hjeq hj0
    have hempty : ∅ ∉ σ := by
      have hiff := knTight_empty_iff σ L ⟨hhappy, hcard⟩ hjeq
      intro hcon
      have hne := hiff.mp hcon
      rw [hj0] at hne
      exact hne rfl
    rw [hdeg, hout, Finset.card_singleton]
    exact ⟨rfl, hempty⟩
  · right
    have hjge : 1 ≤ j := by omega
    have hout : (knOut σ L).card = 2 :=
      knTight_out_two σ L ⟨hhappy, hcard⟩ hjeq hjle hjge
    have hempty : ∅ ∈ σ := by
      have hiff := knTight_empty_iff σ L ⟨hhappy, hcard⟩ hjeq
      apply hiff.mpr
      omega
    rw [hdeg, hout]
    exact ⟨rfl, hempty⟩

private theorem knSum_two {α : Type*} (s : Finset α) (g : α → ℕ)
    (hge : ∀ y ∈ s, 1 ≤ g y) (hsum : ∑ y ∈ s, g y = s.card + 1) :
    ∃ l0 ∈ s, g l0 = 2 ∧ ∀ l ∈ s, l ≠ l0 → g l = 1 := by
  classical
  have hex : ∃ l0 ∈ s, 2 ≤ g l0 := by
    by_contra hcon
    have hall : ∀ l ∈ s, g l = 1 := by
      intro l hl
      have h1 := hge l hl
      have h2 : ¬ 2 ≤ g l := fun hle => hcon ⟨l, hl, hle⟩
      omega
    have hsum1 : ∑ y ∈ s, g y = s.card := by
      calc ∑ y ∈ s, g y = ∑ y ∈ s, 1 :=
            Finset.sum_congr rfl (fun l hl => hall l hl)
        _ = s.card := by simp
    omega
  obtain ⟨l0, hl0, hg0⟩ := hex
  have huniq : ∀ l1 ∈ s, ∀ l2 ∈ s, 2 ≤ g l1 → 2 ≤ g l2 → l1 = l2 := by
    intro l1 hl1 l2 hl2 hg1 hg2
    by_contra hne
    have hsub : ({l1, l2} : Finset α) ⊆ s := by
      intro x hx
      rw [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hl1
      · exact hl2
    have hpair_ne : l1 ≠ l2 := hne
    have h2 : ({l1, l2} : Finset α).card = 2 := Finset.card_pair hpair_ne
    have hunion : ({l1, l2} ∪ s \ {l1, l2}) = s := by
      rw [Finset.union_comm]
      exact Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint ({l1, l2} : Finset α) (s \ {l1, l2}) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx2).2 hx1
    have hsum_split : ∑ y ∈ ({l1, l2} ∪ s \ {l1, l2}), g y =
        (∑ x ∈ ({l1, l2} : Finset α), g x) + ∑ x ∈ s \ {l1, l2}, g x :=
      Finset.sum_union hdisj
    rw [hunion] at hsum_split
    have hpair_sum : ∑ x ∈ ({l1, l2} : Finset α), g x = g l1 + g l2 :=
      Finset.sum_pair hpair_ne
    have hrest_ge : (s \ {l1, l2}).card ≤ ∑ x ∈ s \ {l1, l2}, g x := by
      have hle := Finset.sum_le_sum (s := s \ {l1, l2}) (f := fun _ => 1) (g := g)
        (fun i hi => hge i (Finset.mem_sdiff.mp hi).1)
      rwa [Finset.sum_const, nsmul_eq_mul, mul_one] at hle
    have hrest_card : (s \ {l1, l2}).card = s.card - 2 := by
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hunion, h2] at hcu
      omega
    omega
  have hg02 : g l0 = 2 := by
    by_contra hne
    have h3 : 3 ≤ g l0 := by omega
    have herase_card : (s.erase l0).card = s.card - 1 :=
      Finset.card_erase_of_mem hl0
    have hsplit : ∑ y ∈ s, g y = g l0 + ∑ y ∈ s.erase l0, g y :=
      (Finset.add_sum_erase s g hl0).symm
    have hrest : (s.erase l0).card ≤ ∑ y ∈ s.erase l0, g y := by
      have hle := Finset.sum_le_sum (s := s.erase l0) (f := fun _ => 1) (g := g)
        (fun i hi => hge i (Finset.mem_of_mem_erase hi))
      rwa [Finset.sum_const, nsmul_eq_mul, mul_one] at hle
    have hpos : 1 ≤ s.card := Finset.one_le_card.mpr ⟨l0, hl0⟩
    omega
  refine ⟨l0, hl0, hg02, ?_⟩
  intro l hl hne
  by_contra h1
  have h2l : 2 ≤ g l := by
    have hgl := hge l hl
    omega
  have heq := huniq l hl l0 hl0 h2l hg0
  exact hne heq

private theorem knLooseRepeat_top {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (him : (knImg σ L).card = (knTop σ).card) :
    1 ≤ (knTop σ).card ∧ knImg σ L = knTop σ := by
  classical
  obtain ⟨hhappy, _⟩ := h
  obtain ⟨⟨hne, _, _⟩, hsub⟩ := hhappy
  obtain ⟨x, hx⟩ := hne
  have h1 : 1 ≤ (knImg σ L).card := by
    apply Finset.one_le_card.mpr
    exact ⟨L x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  constructor
  · omega
  · exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

private theorem knLooseRepeat_pair {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (himTop : knImg σ L = knTop σ) :
    ∃ w1 ∈ σ, ∃ w2 ∈ σ, w1 ≠ w2 ∧ L w1 = L w2 ∧
      (∀ a ∈ σ, ∀ b ∈ σ, L a = L b →
        a = b ∨ (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1)) := by
  classical
  obtain ⟨⟨_, _⟩, hcard⟩ := h
  have hfib_sum : ∑ ℓ ∈ knImg σ L, (σ.filter (fun x => L x = ℓ)).card =
      (knImg σ L).card + 1 := by
    have hfib := Finset.card_eq_sum_card_fiberwise (s := σ) (t := knImg σ L) (f := L)
      (fun x hx => Finset.mem_coe.mpr
        (Finset.mem_image.mpr ⟨x, Finset.mem_coe.mp hx, rfl⟩))
    have him : (knImg σ L).card = (knTop σ).card := by
      rw [himTop]
    omega
  have hge : ∀ ℓ ∈ knImg σ L, 1 ≤ (σ.filter (fun x => L x = ℓ)).card := by
    intro ℓ hℓ
    have hmem : ℓ ∈ σ.image L := hℓ
    obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hmem
    have hfibmem : x ∈ σ.filter (fun x => L x = ℓ) :=
      Finset.mem_filter.mpr ⟨hx, hxl⟩
    exact Finset.one_le_card.mpr ⟨x, hfibmem⟩
  obtain ⟨l0, hl0, hl02, hl1⟩ := knSum_two _ _ hge hfib_sum
  obtain ⟨w1, w2, hne, hfibeq⟩ := Finset.card_eq_two.mp hl02
  have hw1 : w1 ∈ σ ∧ L w1 = l0 := by
    have hself : w1 ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) :=
      Finset.mem_insert_self w1 {w2}
    rw [← hfibeq] at hself
    exact ⟨(Finset.mem_filter.mp hself).1, (Finset.mem_filter.mp hself).2⟩
  have hw2 : w2 ∈ σ ∧ L w2 = l0 := by
    have hself : w2 ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self w2)
    rw [← hfibeq] at hself
    exact ⟨(Finset.mem_filter.mp hself).1, (Finset.mem_filter.mp hself).2⟩
  refine ⟨w1, hw1.1, w2, hw2.1, hne, ?_, ?_⟩
  · rw [hw1.2, hw2.2]
  · intro a ha b hb hab
    have hl : L a ∈ knImg σ L := Finset.mem_image.mpr ⟨a, ha, rfl⟩
    by_cases heq : L a = l0
    · have ha' : a ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) := by
        rw [← hfibeq]
        exact Finset.mem_filter.mpr ⟨ha, heq⟩
      have hb' : b ∈ ({w1, w2} : Finset (Finset (Bool × Fin n))) := by
        rw [← hfibeq]
        exact Finset.mem_filter.mpr ⟨hb, by rw [← hab]; exact heq⟩
      rw [Finset.mem_insert, Finset.mem_singleton] at ha' hb'
      rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
      · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
      · exact Or.inl rfl
    · have h1 := hl1 (L a) hl heq
      have ha' : a ∈ σ.filter (fun x => L x = L a) :=
        Finset.mem_filter.mpr ⟨ha, rfl⟩
      have hb' : b ∈ σ.filter (fun x => L x = L a) :=
        Finset.mem_filter.mpr ⟨hb, hab.symm⟩
      obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1
      rw [hc] at ha' hb'
      have hac : a = c := Finset.mem_singleton.mp ha'
      have hbc : b = c := Finset.mem_singleton.mp hb'
      exact Or.inl (hac.trans hbc.symm)

private theorem knLooseRepeat_no_out {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (himTop : knImg σ L = knTop σ) : knOut σ L = ∅ := by
  classical
  have hchain : knChain σ := h.1.1
  ext v
  simp only [knMem_out, Finset.notMem_empty, iff_false]
  intro hv
  obtain ⟨hvn, hchainI, htopI⟩ := hv
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  obtain ⟨_, _, hischI⟩ := hchainI
  have hvt : v ⊆ knTop σ ∨ knTop σ ⊆ v := by
    have h1 : v ∈ insert v σ := Finset.mem_insert_self v σ
    have h2 : knTop σ ∈ insert v σ := Finset.mem_insert_of_mem htopmem
    rcases hischI v h1 (knTop σ) h2 with hsub | hsub
    · exact Or.inl hsub
    · exact Or.inr hsub
  rcases hvt with hsub | hsup
  · have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
    obtain ⟨x, hx, hxc⟩ := knLoose_has_level σ L h hle
    have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
    have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
    have heq : x = v := knChain_eq_of_mem_card_eq _ hischI hxv hvv hxc
    rw [heq] at hx
    exact hvn hx
  · have htopI' : knTop (insert v σ) ⊆ knTop σ := by
      rw [himTop] at htopI
      exact htopI
    have hvinsert : knTop (insert v σ) = v := knTop_insert_of_supset σ v hsup
    rw [hvinsert] at htopI'
    have heq : v = knTop σ := le_antisymm htopI' hsup
    rw [heq] at hvn
    exact hvn htopmem

private theorem knLooseRepeat_in_of_pair {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (himTop : knImg σ L = knTop σ)
    (w w' : Finset (Bool × Fin n)) (hw : w ∈ σ) (hw' : w' ∈ σ)
    (hne : w' ≠ w) (heq : L w = L w') : w ∈ knIn σ L := by
  classical
  have hchain : knChain σ := h.1.1
  have hcons : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hisch : knIsChain σ := hchain.2.2
  have himg_erase : knImg (σ.erase w) L = knTop σ := by
    apply le_antisymm
    · calc knImg (σ.erase w) L ⊆ knImg σ L :=
            Finset.image_subset_image (Finset.erase_subset w σ)
        _ = knTop σ := himTop
    · rw [← himTop]
      intro ℓ hℓ
      obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hℓ
      by_cases hxw : x = w
      · have hlw' : L w' = ℓ := by
          rw [← hxl, hxw]
          exact heq.symm
        have hwe : w' ∈ σ.erase w := Finset.mem_erase.mpr ⟨hne, hw'⟩
        exact Finset.mem_image.mpr ⟨w', hwe, hlw'⟩
      · have hxe : x ∈ σ.erase w := Finset.mem_erase.mpr ⟨hxw, hx⟩
        exact Finset.mem_image.mpr ⟨x, hxe, hxl⟩
  have hchainE : knChain (σ.erase w) := by
    refine ⟨⟨w', Finset.mem_erase.mpr ⟨hne, hw'⟩⟩, ?_, ?_⟩
    · intro x hx
      exact hcons x (Finset.mem_of_mem_erase hx)
    · intro a ha b hb
      exact hisch a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
  have hhappy : knHappy (σ.erase w) L := by
    refine ⟨hchainE, ?_⟩
    rw [himg_erase]
    exact knTop_sup_le _ (fun x hx => knMem_subset_top σ (Finset.mem_of_mem_erase hx))
  rw [knMem_in]
  refine ⟨hw, hhappy, ?_⟩
  rw [himg_erase]

private theorem knLooseRepeat_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (himTop : knImg σ L = knTop σ)
    (w1 w2 : Finset (Bool × Fin n)) (hw1 : w1 ∈ σ) (hw2 : w2 ∈ σ)
    (hne : w1 ≠ w2) (heq12 : L w1 = L w2)
    (huniq : ∀ a ∈ σ, ∀ b ∈ σ, L a = L b →
      a = b ∨ (a = w1 ∧ b = w2) ∨ (a = w2 ∧ b = w1)) :
    knIn σ L = {w1, w2} := by
  classical
  ext w
  rw [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hw
    rw [knMem_in] at hw
    obtain ⟨hwm, _, htopsub⟩ := hw
    by_contra hcon
    have hw1' : w ≠ w1 := fun he => hcon (Or.inl he)
    have hw2' : w ≠ w2 := fun he => hcon (Or.inr he)
    have hnot : L w ∉ knImg (σ.erase w) L := by
      intro hmem
      obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hmem
      have hxσ : x ∈ σ := Finset.mem_of_mem_erase hx
      have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
      have hxl' : L x = L w := hxl
      rcases huniq x hxσ w hwm hxl' with heq | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxw heq
      · exact hw2' rfl
      · exact hw1' rfl
    have hmem2 : L w ∈ knImg (σ.erase w) L := by
      have htopw : L w ∈ knTop σ := by
        rw [← himTop]
        exact Finset.mem_image.mpr ⟨w, hwm, rfl⟩
      exact htopsub htopw
    exact hnot hmem2
  · intro hw
    rcases hw with heqw | heqw
    · rw [heqw]
      exact knLooseRepeat_in_of_pair σ L h himTop w1 w2 hw1 hw2 (Ne.symm hne)
        heq12
    · rw [heqw]
      exact knLooseRepeat_in_of_pair σ L h himTop w2 w1 hw2 hw1 hne
        heq12.symm

private theorem knLooseRepeat_degree {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (him : (knImg σ L).card = (knTop σ).card) : (knG L).degree σ = 2 := by
  classical
  obtain ⟨_, himTop⟩ := knLooseRepeat_top σ L h him
  obtain ⟨w1, hw1, w2, hw2, hne, heq12, huniq⟩ :=
    knLooseRepeat_pair σ L h himTop
  have hout : (knOut σ L).card = 0 := by
    rw [knLooseRepeat_no_out σ L h himTop, Finset.card_empty]
  have hin : (knIn σ L).card = 2 := by
    rw [knLooseRepeat_in σ L h himTop w1 w2 hw1 hw2 hne heq12 huniq,
      Finset.card_pair hne]
  have hdeg := knDegree_eq σ L h.1
  omega

private theorem knLooseFresh_inj {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (him : (knImg σ L).card = (knTop σ).card + 1) :
    Set.InjOn L (↑σ : Set (Finset (Bool × Fin n))) := by
  classical
  obtain ⟨_, hcard⟩ := h
  have h2 : (σ.image L).card = σ.card := by
    have hcc : (knImg σ L).card = σ.card := by omega
    unfold knImg at hcc
    exact hcc
  exact Finset.injOn_of_card_image_eq h2

private theorem knLooseFresh_label {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (him : (knImg σ L).card = (knTop σ).card + 1) :
    ∃ ℓ, ℓ ∉ knTop σ ∧ ℓ ∈ knImg σ L ∧ knImg σ L = insert ℓ (knTop σ) := by
  classical
  have hsub : knTop σ ⊆ knImg σ L := h.1.2
  have hsd : (knImg σ L \ knTop σ).card = 1 := by
    have hunion := Finset.sdiff_union_of_subset hsub
    have hdisj : Disjoint (knImg σ L \ knTop σ) (knTop σ) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact (Finset.mem_sdiff.mp hx1).2 hx2
    have hcu := Finset.card_union_of_disjoint hdisj
    rw [hunion] at hcu
    omega
  obtain ⟨ℓ, hℓ⟩ := Finset.card_eq_one.mp hsd
  have hℓtop : ℓ ∉ knTop σ := by
    have hself : ℓ ∈ ({ℓ} : Finset (Bool × Fin n)) := Finset.mem_singleton_self ℓ
    rw [← hℓ] at hself
    exact (Finset.mem_sdiff.mp hself).2
  have hℓimg : ℓ ∈ knImg σ L := by
    have hself : ℓ ∈ ({ℓ} : Finset (Bool × Fin n)) := Finset.mem_singleton_self ℓ
    rw [← hℓ] at hself
    exact (Finset.mem_sdiff.mp hself).1
  refine ⟨ℓ, hℓtop, hℓimg, ?_⟩
  ext m
  rw [Finset.mem_insert]
  constructor
  · intro hm
    by_cases hmt : m ∈ knTop σ
    · exact Or.inr hmt
    · left
      have hmem : m ∈ knImg σ L \ knTop σ := Finset.mem_sdiff.mpr ⟨hm, hmt⟩
      rw [hℓ] at hmem
      exact Finset.mem_singleton.mp hmem
  · intro hm
    rcases hm with rfl | hm
    · exact hℓimg
    · exact hsub hm

private theorem knFresh_neg_top {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (hnc : knNoCompl L)
    (w : Finset (Bool × Fin n)) (hwσ : w ∈ σ)
    (ℓ : Bool × Fin n) (hwl : L w = ℓ) :
    knNegLabel ℓ ∉ knTop σ := by
  classical
  have hchain : knChain σ := h.1.1
  have hcons : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hisch : knIsChain σ := hchain.2.2
  have hsub : knTop σ ⊆ knImg σ L := h.1.2
  intro hmem
  have hmem2 : knNegLabel ℓ ∈ knImg σ L := hsub hmem
  obtain ⟨x, hx, hxl⟩ := Finset.mem_image.mp hmem2
  have hcomp := hisch x hx w hwσ
  have hxlw : L x = knNegLabel (L w) := by
    rw [hwl]
    exact hxl
  rcases hcomp with hsub2 | hsub2
  · have hncx := hnc x w (hcons x hx) (hcons w hwσ) hsub2
    apply hncx
    rw [hxlw, knNegLabel_invol_apply]
  · have hncx := hnc w x (hcons w hwσ) (hcons x hx) hsub2
    exact hncx hxlw

private theorem knFresh_insert_cons {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (hnc : knNoCompl L)
    (w : Finset (Bool × Fin n)) (hwσ : w ∈ σ)
    (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ) :
    knConsistent (insert ℓ (knTop σ)) := by
  classical
  have hchain : knChain σ := h.1.1
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  have hconTop : knConsistent (knTop σ) := hchain.2.1 _ htopmem
  have hnegtop : knNegLabel ℓ ∉ knTop σ :=
    knFresh_neg_top σ L h hnc w hwσ ℓ hwl
  intro l hl hnl
  rw [Finset.mem_insert] at hl hnl
  rcases hl with heq | hl
  · rw [heq] at hnl
    rcases hnl with hnl | hnl
    · have hne2 : knNegLabel ℓ ≠ ℓ := by
        obtain ⟨b, i⟩ := ℓ
        cases b <;> simp [knNegLabel]
      exact hne2 hnl
    · exact hnegtop hnl
  · rcases hnl with hnl | hnl
    · have h2 : knNegLabel ℓ = l := by
        rw [← hnl, knNegLabel_invol_apply]
      rw [h2] at hnegtop
      exact hnegtop hl
    · exact hconTop l hl hnl

private theorem knLooseFresh_out {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (hnc : knNoCompl L)
    (w : Finset (Bool × Fin n)) (hwσ : w ∈ σ)
    (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ)
    (hfresh : knImg σ L = insert ℓ (knTop σ)) :
    knOut σ L = {insert ℓ (knTop σ)} := by
  classical
  have hchain : knChain σ := h.1.1
  have hconsI : knConsistent (insert ℓ (knTop σ)) :=
    knFresh_insert_cons σ L h hnc w hwσ ℓ hwl hℓtop
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  ext v
  rw [Finset.mem_singleton]
  constructor
  · intro hv
    rw [knMem_out] at hv
    obtain ⟨hvn, hchainI, htopI⟩ := hv
    obtain ⟨_, _, hischI⟩ := hchainI
    have hsup : knTop σ ⊆ v := by
      have hcomp := hischI v (Finset.mem_insert_self v σ) (knTop σ)
        (Finset.mem_insert_of_mem htopmem)
      rcases hcomp with hsub | hsup
      · exfalso
        have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
        obtain ⟨x, hx, hxc⟩ := knLoose_has_level σ L h hle
        have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
        have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
        have heq : x = v := knChain_eq_of_mem_card_eq _ hischI hxv hvv hxc
        rw [heq] at hx
        exact hvn hx
      · exact hsup
    have hvinsert : knTop (insert v σ) = v := knTop_insert_of_supset σ v hsup
    rw [hvinsert, hfresh] at htopI
    have hsubI : insert ℓ (knTop σ) ⊆ v := by
      have hssub : knTop σ ⊂ v := by
        refine ⟨hsup, ?_⟩
        intro hsub
        have hle : v.card ≤ (knTop σ).card := Finset.card_le_card hsub
        obtain ⟨x, hx, hxc⟩ := knLoose_has_level σ L h hle
        have hxv : x ∈ insert v σ := Finset.mem_insert_of_mem hx
        have hvv : v ∈ insert v σ := Finset.mem_insert_self v σ
        have heq : x = v := knChain_eq_of_mem_card_eq _ hischI hxv hvv hxc
        rw [heq] at hx
        exact hvn hx
      obtain ⟨y, hyv, hytop⟩ := Finset.exists_of_ssubset hssub
      have hyI : y ∈ insert ℓ (knTop σ) := htopI hyv
      rw [Finset.mem_insert] at hyI
      rcases hyI with rfl | hyI
      · exact Finset.insert_subset hyv hsup
      · exact absurd hyI hytop
    exact le_antisymm htopI hsubI
  · intro heq
    rw [heq]
    have hcardI : (insert ℓ (knTop σ)).card = (knTop σ).card + 1 :=
      Finset.card_insert_of_notMem hℓtop
    have hnem : insert ℓ (knTop σ) ∉ σ := by
      intro hcon
      have hle := Finset.card_le_card (knMem_subset_top σ hcon)
      omega
    have hcompI : ∀ x ∈ σ, x ⊆ insert ℓ (knTop σ) ∨ insert ℓ (knTop σ) ⊆ x := by
      intro x hx
      exact Or.inl ((knMem_subset_top σ hx).trans (Finset.subset_insert ℓ _))
    have hchainI := knChain_insert σ hchain hconsI hcompI
    rw [knMem_out]
    refine ⟨hnem, hchainI, ?_⟩
    have htopI2 : knTop (insert (insert ℓ (knTop σ)) σ) = insert ℓ (knTop σ) := by
      apply knTop_insert_of_supset
      exact Finset.subset_insert ℓ _
    rw [htopI2, hfresh]

private theorem knLooseFresh_in_sub {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (w : Finset (Bool × Fin n)) (hw : w ∈ σ)
    (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ)
    {u : Finset (Bool × Fin n)} (hu : u ∈ knIn σ L) : u = w := by
  classical
  have hcard : σ.card = (knTop σ).card + 1 := h.2
  rw [knMem_in] at hu
  obtain ⟨hum, _, htopsub⟩ := hu
  have himg_eq : knImg (σ.erase u) L = knTop σ := by
    have hle : (knImg (σ.erase u) L).card ≤ (knTop σ).card := by
      calc (knImg (σ.erase u) L).card ≤ (σ.erase u).card := by
              unfold knImg
              exact Finset.card_image_le
        _ = σ.card - 1 := Finset.card_erase_of_mem hum
        _ = (knTop σ).card := by omega
    exact (Finset.eq_of_subset_of_card_le htopsub hle).symm
  by_contra hne2
  have hwu : w ∈ σ.erase u := Finset.mem_erase.mpr ⟨Ne.symm hne2, hw⟩
  have hmem : L w ∈ knImg (σ.erase u) L := Finset.mem_image.mpr ⟨w, hwu, rfl⟩
  rw [himg_eq, hwl] at hmem
  exact hℓtop hmem

private theorem knLooseFresh_mem_in {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (hinj : Set.InjOn L (↑σ : Set (Finset (Bool × Fin n))))
    (w : Finset (Bool × Fin n)) (hw : w ∈ σ)
    (ℓ : Bool × Fin n) (hwl : L w = ℓ) (hℓtop : ℓ ∉ knTop σ)
    (hfresh : knImg σ L = insert ℓ (knTop σ)) :
    w ∈ knIn σ L ↔ (σ.erase w).Nonempty := by
  classical
  have hchain : knChain σ := h.1.1
  have hcons : ∀ x ∈ σ, knConsistent x := hchain.2.1
  have hisch : knIsChain σ := hchain.2.2
  have hsub : knTop σ ⊆ knImg σ L := h.1.2
  have himg_erase : knImg (σ.erase w) L = knTop σ := by
    apply le_antisymm
    · intro m hm
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm
      have hxσ : x ∈ σ := Finset.mem_of_mem_erase hx
      have hxw : x ≠ w := (Finset.mem_erase.mp hx).1
      have hmemI : L x ∈ knImg σ L := Finset.mem_image.mpr ⟨x, hxσ, rfl⟩
      rw [hfresh] at hmemI
      rcases Finset.mem_insert.mp hmemI with heq | htop
      · exfalso
        have hxx : L x = L w := heq.trans hwl.symm
        have hxeq : x = w :=
          hinj (Finset.mem_coe.mpr hxσ) (Finset.mem_coe.mpr hw) hxx
        exact hxw hxeq
      · rw [← hxm]
        exact htop
    · intro m hm
      have hmemI : m ∈ knImg σ L := hsub hm
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hmemI
      by_cases hxw : x = w
      · exfalso
        subst hxw
        rw [hwl] at hxm
        rw [hxm] at hℓtop
        exact hℓtop hm
      · have hxe : x ∈ σ.erase w := Finset.mem_erase.mpr ⟨hxw, hx⟩
        exact Finset.mem_image.mpr ⟨x, hxe, hxm⟩
  constructor
  · intro hwIn
    rw [knMem_in] at hwIn
    obtain ⟨_, hhappy, _⟩ := hwIn
    exact hhappy.1.1
  · intro hne2
    have hchainE : knChain (σ.erase w) := by
      obtain ⟨w', hw'⟩ := hne2
      refine ⟨⟨w', hw'⟩, ?_, ?_⟩
      · intro x hx
        exact hcons x (Finset.mem_of_mem_erase hx)
      · intro a ha b hb
        exact hisch a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb)
    have hhappy : knHappy (σ.erase w) L := by
      refine ⟨hchainE, ?_⟩
      rw [himg_erase]
      exact knTop_sup_le _ (fun x hx => knMem_subset_top σ (Finset.mem_of_mem_erase hx))
    rw [knMem_in]
    refine ⟨hw, hhappy, ?_⟩
    rw [himg_erase]

private theorem knLooseFresh_erase_empty {n : ℕ}
    (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (w : Finset (Bool × Fin n)) (hw : w ∈ σ) :
    (σ.erase w = ∅) ↔ σ = {∅} := by
  classical
  constructor
  · intro herase
    have hsub1 : σ ⊆ {w} := by
      intro x hx
      rw [Finset.mem_singleton]
      by_contra hne
      have hmem : x ∈ σ.erase w := Finset.mem_erase.mpr ⟨hne, hx⟩
      rw [herase] at hmem
      exact Finset.notMem_empty x hmem
    have hsingle : σ = {w} := by
      apply le_antisymm hsub1
      intro x hx
      rw [Finset.mem_singleton] at hx
      rw [hx]
      exact hw
    have hcard1 : σ.card = 1 := by
      rw [hsingle, Finset.card_singleton]
    have hcard := h.2
    have htop0 : knTop σ = ∅ := by
      have hzero : (knTop σ).card = 0 := by omega
      exact Finset.card_eq_zero.mp hzero
    have hw0 : w = ∅ := by
      have hsubw : w ⊆ knTop σ := knMem_subset_top σ hw
      rw [htop0] at hsubw
      have hle : w.card ≤ (∅ : Finset (Bool × Fin n)).card :=
        Finset.card_le_card hsubw
      rw [Finset.card_empty] at hle
      have hzero : w.card = 0 := by omega
      exact Finset.card_eq_zero.mp hzero
    rw [hsingle, hw0]
  · intro hσ
    have hw0 : w = ∅ := Finset.mem_singleton.mp (by rw [← hσ]; exact hw)
    rw [hσ, hw0, Finset.erase_singleton]

private theorem knLooseFresh_degree {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knLoose σ L)
    (him : (knImg σ L).card = (knTop σ).card + 1) (hnc : knNoCompl L) :
    ((knG L).degree σ = 1 ∧ σ = {∅}) ∨ ((knG L).degree σ = 2 ∧ σ ≠ {∅}) := by
  classical
  have hinj := knLooseFresh_inj σ L h him
  obtain ⟨ℓ, hℓtop, hℓimg, hfresh⟩ := knLooseFresh_label σ L h him
  obtain ⟨w, hwσ, hwl⟩ := Finset.mem_image.mp hℓimg
  have hout : (knOut σ L).card = 1 := by
    rw [knLooseFresh_out σ L h hnc w hwσ ℓ hwl hℓtop hfresh,
      Finset.card_singleton]
  by_cases herase : σ.erase w = ∅
  · left
    have hin0 : (knIn σ L).card = 0 := by
      have hin_empty : knIn σ L = ∅ := by
        ext u
        simp only [Finset.notMem_empty, iff_false]
        intro hu
        have huw : u = w := knLooseFresh_in_sub σ L h w hwσ ℓ hwl hℓtop hu
        rw [knMem_in] at hu
        obtain ⟨_, hhappy, _⟩ := hu
        have hne2 := hhappy.1.1
        rw [huw, herase] at hne2
        exact Finset.not_nonempty_empty hne2
      rw [hin_empty, Finset.card_empty]
    rw [knDegree_eq σ L h.1, hout, hin0, add_zero]
    refine ⟨rfl, ?_⟩
    exact (knLooseFresh_erase_empty σ L h w hwσ).mp herase
  · right
    have hmem : w ∈ knIn σ L :=
      (knLooseFresh_mem_in σ L h hinj w hwσ ℓ hwl hℓtop hfresh).mpr
        (Finset.nonempty_iff_ne_empty.mpr herase)
    have hin1 : (knIn σ L).card = 1 := by
      have hsingle : knIn σ L = {w} := by
        ext u
        rw [Finset.mem_singleton]
        constructor
        · intro hu
          exact knLooseFresh_in_sub σ L h w hwσ ℓ hwl hℓtop hu
        · intro hu
          rw [hu]
          exact hmem
      rw [hsingle, Finset.card_singleton]
    rw [knDegree_eq σ L h.1, hout, hin1]
    refine ⟨rfl, ?_⟩
    intro hcon
    have herase' := (knLooseFresh_erase_empty σ L h w hwσ).mpr hcon
    exact herase herase'

private theorem knTop_singleton_empty {n : ℕ} :
    knTop ({∅} : Finset (Finset (Bool × Fin n))) = ∅ := by
  classical
  have hsup : (({∅} : Finset (Finset (Bool × Fin n))).sup id) = id ∅ :=
    Finset.sup_singleton
  have hid : id (∅ : Finset (Bool × Fin n)) = ∅ := rfl
  unfold knTop
  rw [hsup, hid]

private theorem knEmptySingleton_chain {n : ℕ} :
    knChain ({∅} : Finset (Finset (Bool × Fin n))) := by
  classical
  refine ⟨Finset.singleton_nonempty _, ?_, ?_⟩
  · intro x hx
    rw [Finset.mem_singleton] at hx
    rw [hx]
    intro l hl
    exact False.elim (Finset.notMem_empty l hl)
  · intro a ha b hb
    rw [Finset.mem_singleton] at ha hb
    rw [ha, hb]
    exact Or.inl Subset.rfl

private theorem knEmptySingleton_happy {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    knHappy ({∅} : Finset (Finset (Bool × Fin n))) L := by
  classical
  refine ⟨knEmptySingleton_chain, ?_⟩
  rw [knTop_singleton_empty]
  exact Finset.empty_subset _

private theorem knEmptySingleton_loose {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    knLoose ({∅} : Finset (Finset (Bool × Fin n))) L := by
  classical
  refine ⟨knEmptySingleton_happy L, ?_⟩
  have h1 : ({∅} : Finset (Finset (Bool × Fin n))).card = 1 :=
    Finset.card_singleton _
  have h0 : (knTop ({∅} : Finset (Finset (Bool × Fin n)))).card = 0 := by
    rw [knTop_singleton_empty, Finset.card_empty]
  omega

private theorem knOddDegree {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hnc : knNoCompl L)
    (σ : Finset (Finset (Bool × Fin n))) :
    Odd ((knG L).degree σ) ↔ σ = {∅} ∨ (knTight σ L ∧ ∅ ∉ σ) := by
  classical
  by_cases hhappy : knHappy σ L
  · obtain hcard_eq := knHappy_card_eq σ L hhappy
    rcases hcard_eq with htight_card | hloose_card
    · have htight : knTight σ L := ⟨hhappy, htight_card⟩
      have hdeg := knTight_degree σ L htight
      have hnotsingle : σ ≠ {∅} := by
        intro hcon
        rw [hcon, Finset.card_singleton, knTop_singleton_empty,
          Finset.card_empty] at htight_card
        omega
      constructor
      · intro hodd
        right
        refine ⟨htight, ?_⟩
        rcases hdeg with ⟨h1, hnem⟩ | ⟨h2, _⟩
        · exact hnem
        · exfalso
          rw [h2] at hodd
          exact (by decide : ¬ Odd 2) hodd
      · intro hdisj
        rcases hdisj with hsingle | ⟨_, hnem⟩
        · exact absurd hsingle hnotsingle
        · rcases hdeg with ⟨h1, _⟩ | ⟨_, hmem⟩
          · rw [h1]
            exact odd_one
          · exact absurd hmem hnem
    · have hloose : knLoose σ L := ⟨hhappy, hloose_card⟩
      have him_le : (knImg σ L).card ≤ σ.card := by
        unfold knImg
        exact Finset.card_image_le
      have htop_le : (knTop σ).card ≤ (knImg σ L).card :=
        Finset.card_le_card hhappy.2
      by_cases him_eq : (knImg σ L).card = (knTop σ).card
      · have hdeg2 := knLooseRepeat_degree σ L hloose him_eq
        have hnotsingle : σ ≠ {∅} := by
          intro hcon
          rw [hcon] at him_eq
          rw [knTop_singleton_empty, Finset.card_empty] at him_eq
          have himg1 : (knImg ({∅} : Finset (Finset (Bool × Fin n))) L).card = 1 := by
            unfold knImg
            rw [Finset.image_singleton, Finset.card_singleton]
          omega
        constructor
        · intro hodd
          rw [hdeg2] at hodd
          exact absurd hodd (by decide : ¬ Odd 2)
        · intro hdisj
          rcases hdisj with hsingle | ⟨htight2, _⟩
          · exact absurd hsingle hnotsingle
          · obtain ⟨_, htcard⟩ := htight2
            omega
      · have him2 : (knImg σ L).card = (knTop σ).card + 1 := by omega
        have hdeg := knLooseFresh_degree σ L hloose him2 hnc
        constructor
        · intro hodd
          rcases hdeg with ⟨h1, hsingle⟩ | ⟨h2, _⟩
          · exact Or.inl hsingle
          · exfalso
            rw [h2] at hodd
            exact absurd hodd (by decide : ¬ Odd 2)
        · intro hdisj
          rcases hdisj with hsingle | ⟨htight2, hnem⟩
          · rcases hdeg with ⟨h1, _⟩ | ⟨_, hne2⟩
            · rw [h1]
              exact odd_one
            · exact absurd hsingle hne2
          · obtain ⟨_, htcard⟩ := htight2
            omega
  · have hdeg0 := knDegree_nothappy σ L hhappy
    have hnotsingle : σ ≠ {∅} := by
      intro hcon
      rw [hcon] at hhappy
      exact hhappy (knEmptySingleton_happy L)
    constructor
    · intro hodd
      rw [hdeg0] at hodd
      exact absurd hodd (by decide : ¬ Odd (0 : ℕ))
    · intro hdisj
      rcases hdisj with hsingle | ⟨htight2, _⟩
      · exact absurd hsingle hnotsingle
      · exact absurd htight2.1 hhappy

private theorem knNegLabel_snd {n : ℕ} (m : Bool × Fin n) :
    (knNegLabel m).2 = m.2 := rfl

private theorem knNegCell_injective {n : ℕ} :
    Function.Injective (@knNegCell n) :=
  Function.Involutive.injective (fun x => knNegCell_invol x)

private theorem knNegCell_mono {n : ℕ} {x y : Finset (Bool × Fin n)}
    (h : x ⊆ y) : knNegCell x ⊆ knNegCell y := by
  classical
  intro l hl
  obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
  rw [← hml]
  exact knNegLabel_mem_negCell (h hm)

private theorem knNegCell_consistent {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) : knConsistent (knNegCell x) := by
  classical
  intro l hl hnl
  obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
  obtain ⟨m', hm', hm'l⟩ := knMem_negCell.mp hnl
  have hme : m' = l := knNegLabel_inj hm'l
  have hmem : knNegLabel m ∈ x := by
    rw [hml]
    rw [hme] at hm'
    exact hm'
  exact hcons m hm hmem

private theorem knNegTop {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (h : knChain σ) :
    knTop (σ.image knNegCell) = knNegCell (knTop σ) := by
  classical
  apply le_antisymm
  · apply knTop_sup_le
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    rw [← hxy]
    exact knNegCell_mono (knMem_subset_top σ hx)
  · have hmem : knNegCell (knTop σ) ∈ σ.image knNegCell :=
      Finset.mem_image.mpr ⟨knTop σ, knChain_top_mem σ h, rfl⟩
    exact knMem_subset_top _ hmem

private theorem knNegChain {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (h : knChain σ) : knChain (σ.image knNegCell) := by
  classical
  obtain ⟨hne, hcons, hisch⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨knNegCell x, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  · intro y hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    rw [← hxy]
    exact knNegCell_consistent (hcons x hx)
  · intro a ha b hb
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp ha
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hb
    rcases hisch x hx z hz with hsub | hsub
    · left
      rw [← hxy, ← hzy]
      exact knNegCell_mono hsub
    · right
      rw [← hxy, ← hzy]
      exact knNegCell_mono hsub

private theorem knNegTight {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hanti : knAntipodal L)
    (h : knTight σ L) (hne : ∀ x ∈ σ, x.Nonempty) :
    knTight (σ.image knNegCell) L := by
  classical
  obtain ⟨⟨hchain, hsub⟩, hcard⟩ := h
  have hchainI := knNegChain σ hchain
  have htopI : knTop (σ.image knNegCell) = knNegCell (knTop σ) :=
    knNegTop σ hchain
  have himgI : knImg (σ.image knNegCell) L = knNegCell (knImg σ L) := by
    ext ℓ
    constructor
    · intro hm
      obtain ⟨y, hy, hyl⟩ := Finset.mem_image.mp hm
      obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
      have hxL : L (knNegCell x) = knNegLabel (L x) :=
        hanti x (hchain.2.1 x hx) (hne x hx)
      rw [← hxy] at hyl
      rw [hxL] at hyl
      have hmem : knNegLabel (L x) ∈ knNegCell (knImg σ L) :=
        knNegLabel_mem_negCell (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      rwa [hyl] at hmem
    · intro hm
      obtain ⟨m, hm2, hml⟩ := knMem_negCell.mp hm
      obtain ⟨x, hx, hxm⟩ := Finset.mem_image.mp hm2
      have hxL : L (knNegCell x) = knNegLabel (L x) :=
        hanti x (hchain.2.1 x hx) (hne x hx)
      have hmemI : knNegCell x ∈ σ.image knNegCell :=
        Finset.mem_image.mpr ⟨x, hx, rfl⟩
      have hmemL : L (knNegCell x) ∈ knImg (σ.image knNegCell) L :=
        Finset.mem_image.mpr ⟨knNegCell x, hmemI, rfl⟩
      rw [hxL, hxm, hml] at hmemL
      exact hmemL
  refine ⟨⟨hchainI, ?_⟩, ?_⟩
  · rw [htopI, himgI]
    exact knNegCell_mono hsub
  · rw [htopI, knNegCell_card,
      Finset.card_image_of_injective σ knNegCell_injective]
    exact hcard

private theorem knNegImage_invol {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) :
    (σ.image knNegCell).image knNegCell = σ := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    obtain ⟨z, hz, hyz⟩ := Finset.mem_image.mp hy
    have h2 : knNegCell y = z := by
      rw [← hyz]
      exact knNegCell_invol z
    rw [← hxy, h2]
    exact hz
  · intro hx
    exact Finset.mem_image.mpr
      ⟨knNegCell x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, knNegCell_invol x⟩

private def knPosMin {n : ℕ} (σ : Finset (Finset (Bool × Fin n))) : Prop :=
  ∃ i, (true, i) ∈ knTop σ ∧ ∀ j ∈ (knTop σ).image Prod.snd, i ≤ j

open Classical in
private noncomputable def knTightSet {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) :
    Finset (Finset (Finset (Bool × Fin n))) :=
  Finset.univ.filter (fun σ => knTight σ L ∧ ∅ ∉ σ)

private theorem knMem_tightSet {n : ℕ} {σ : Finset (Finset (Bool × Fin n))}
    {L : Finset (Bool × Fin n) → Bool × Fin n} :
    σ ∈ knTightSet L ↔ knTight σ L ∧ ∅ ∉ σ := by
  classical
  unfold knTightSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private theorem knPosMin_flip {n : ℕ} (σ : Finset (Finset (Bool × Fin n)))
    (L : Finset (Bool × Fin n) → Bool × Fin n) (h : knTight σ L) :
    knPosMin σ ↔ ¬ knPosMin (σ.image knNegCell) := by
  classical
  have hchain : knChain σ := h.1.1
  have htopmem : knTop σ ∈ σ := knChain_top_mem σ hchain
  have hconTop : knConsistent (knTop σ) := hchain.2.1 _ htopmem
  have htopI : knTop (σ.image knNegCell) = knNegCell (knTop σ) :=
    knNegTop σ hchain
  have hI : (knTop (σ.image knNegCell)).image Prod.snd =
      (knTop σ).image Prod.snd := by
    rw [htopI]
    ext j
    constructor
    · intro hj
      obtain ⟨l, hl, hlj⟩ := Finset.mem_image.mp hj
      obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
      have hmj : m.2 = j := by
        rw [← hlj, ← hml, knNegLabel_snd]
      exact Finset.mem_image.mpr ⟨m, hm, hmj⟩
    · intro hj
      obtain ⟨m, hm, hmj⟩ := Finset.mem_image.mp hj
      have hmem : knNegLabel m ∈ knNegCell (knTop σ) :=
        knNegLabel_mem_negCell hm
      have hmj2 : (knNegLabel m).2 = j := by
        rw [knNegLabel_snd, hmj]
      exact Finset.mem_image.mpr ⟨knNegLabel m, hmem, hmj2⟩
  have htopne : (knTop σ).Nonempty := by
    have hpos := knTight_top_card_pos σ L h
    exact Finset.card_pos.mp (by omega)
  constructor
  · intro hP hPf
    obtain ⟨i, hi, hmin⟩ := hP
    obtain ⟨i', hi', hmin'⟩ := hPf
    rw [htopI] at hi'
    obtain ⟨m, hm, hmi⟩ := knMem_negCell.mp hi'
    have hm1 : m.1 = false := by
      have h1 : (!m.1) = true := congrArg Prod.fst hmi
      cases hm1 : m.1 <;> simp_all
    have hm2 : m.2 = i' := congrArg Prod.snd hmi
    have hmeq : m = (false, i') := Prod.ext hm1 hm2
    rw [hmeq] at hm
    have hiI : i' ∈ (knTop σ).image Prod.snd :=
      Finset.mem_image.mpr ⟨(false, i'), hm, rfl⟩
    have hiIf : i ∈ (knTop (σ.image knNegCell)).image Prod.snd := by
      rw [hI]
      exact Finset.mem_image.mpr ⟨(true, i), hi, rfl⟩
    have heq : i' = i := le_antisymm (hmin' i hiIf) (hmin i' hiI)
    have hcon : knNegLabel (true, i') ∈ knTop σ := by
      have hneg : knNegLabel (true, i') = (false, i') := rfl
      rw [hneg]
      exact hm
    rw [← heq] at hi
    exact hconTop _ hi hcon
  · intro hcon
    have hIne : ((knTop σ).image Prod.snd).Nonempty := by
      obtain ⟨l, hl⟩ := htopne
      exact ⟨l.2, Finset.mem_image.mpr ⟨l, hl, rfl⟩⟩
    have hisLeast := ((knTop σ).image Prod.snd).isLeast_min' hIne
    have hi0mem : Finset.min' ((knTop σ).image Prod.snd) hIne ∈
        (knTop σ).image Prod.snd := Finset.mem_coe.mp hisLeast.1
    have hi0le : ∀ j ∈ (knTop σ).image Prod.snd,
        Finset.min' ((knTop σ).image Prod.snd) hIne ≤ j := by
      intro j hj
      exact hisLeast.2 (Finset.mem_coe.mpr hj)
    obtain ⟨l, hl, hlj⟩ :=
      Finset.mem_image.mp hi0mem
    by_cases hlb : l.1 = true
    · refine ⟨l.2, ?_, ?_⟩
      · have hle : l = (true, l.2) := Prod.ext hlb rfl
        rw [hle] at hl
        exact hl
      · intro j hj
        rw [hlj]
        exact hi0le j hj
    · have hlf : l.1 = false := by
        cases h : l.1 <;> simp_all
      exfalso
      apply hcon
      refine ⟨l.2, ?_, ?_⟩
      · have hll : l = (false, l.2) := Prod.ext hlf rfl
        rw [htopI, knMem_negCell]
        exact ⟨(false, l.2), by rw [← hll]; exact hl, rfl⟩
      · intro j hj
        rw [hI] at hj
        rw [hlj]
        exact hi0le j hj

private theorem knPairing {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hanti : knAntipodal L) :
    Even (knTightSet L).card := by
  classical
  have hfT : ∀ σ ∈ knTightSet L, σ.image knNegCell ∈ knTightSet L := by
    intro σ hσ
    rw [knMem_tightSet] at hσ ⊢
    obtain ⟨htight, hnem⟩ := hσ
    have hne : ∀ x ∈ σ, x.Nonempty := by
      intro x hx
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      subst he
      exact hnem hx
    refine ⟨knNegTight σ L hanti htight hne, ?_⟩
    intro hcon
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hcon
    have hx0 : x = ∅ := by
      have hce : x.card = 0 := by
        have hcc := congrArg Finset.card hxe
        rwa [knNegCell_card, Finset.card_empty] at hcc
      exact Finset.card_eq_zero.mp hce
    subst hx0
    exact hnem hx
  have hinv : ∀ σ ∈ knTightSet L,
      (σ.image knNegCell).image knNegCell = σ := by
    intro σ _
    exact knNegImage_invol σ
  have hflip : ∀ σ ∈ knTightSet L,
      (knPosMin σ ↔ ¬ knPosMin (σ.image knNegCell)) := by
    intro σ hσ
    rw [knMem_tightSet] at hσ
    obtain ⟨htight, _⟩ := hσ
    exact knPosMin_flip σ L htight
  have himg_eq : ((knTightSet L).filter knPosMin).image
        (fun σ => σ.image knNegCell) =
      (knTightSet L).filter (fun σ => ¬ knPosMin σ) := by
    ext τ
    constructor
    · intro hm
      obtain ⟨σ, hσ, hστ⟩ := Finset.mem_image.mp hm
      have hσT : σ ∈ knTightSet L := Finset.mem_of_mem_filter _ hσ
      have hP : knPosMin σ := (Finset.mem_filter.mp hσ).2
      have hflipσ := (hflip σ hσT).mp hP
      have hστ' : σ.image knNegCell = τ := hστ
      rw [Finset.mem_filter, ← hστ']
      exact ⟨hfT σ hσT, hflipσ⟩
    · intro hm
      rw [Finset.mem_filter] at hm
      obtain ⟨hτT, hnP⟩ := hm
      have hfτT := hfT τ hτT
      have hP : knPosMin (τ.image knNegCell) := by
        by_contra hcon
        have hback := (hflip τ hτT).mpr hcon
        exact hnP hback
      have hmem1 : τ.image knNegCell ∈ (knTightSet L).filter knPosMin :=
        Finset.mem_filter.mpr ⟨hfτT, hP⟩
      have hinvτ : (τ.image knNegCell).image knNegCell = τ := hinv τ hτT
      exact Finset.mem_image.mpr ⟨τ.image knNegCell, hmem1, hinvτ⟩
  have hinjT1 : Set.InjOn (fun σ => σ.image knNegCell)
      (↑((knTightSet L).filter knPosMin) :
        Set (Finset (Finset (Bool × Fin n)))) := by
    intro a ha b hb hab
    have haT : a ∈ knTightSet L :=
      Finset.mem_of_mem_filter _ (Finset.mem_coe.mp ha)
    have hbT : b ∈ knTightSet L :=
      Finset.mem_of_mem_filter _ (Finset.mem_coe.mp hb)
    have hab' : a.image knNegCell = b.image knNegCell := hab
    have hcon := congrArg (fun σ => σ.image knNegCell) hab'
    rw [hinv a haT, hinv b hbT] at hcon
    exact hcon
  have hcard_img : ((knTightSet L).filter (fun σ => ¬ knPosMin σ)).card =
      ((knTightSet L).filter knPosMin).card := by
    have hci := Finset.card_image_of_injOn hinjT1
    rw [himg_eq] at hci
    exact hci
  have hunion : (knTightSet L).filter knPosMin ∪
      (knTightSet L).filter (fun σ => ¬ knPosMin σ) = knTightSet L := by
    ext σ
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨hm, _⟩ | ⟨hm, _⟩)
      · exact hm
      · exact hm
    · intro hm
      by_cases hP : knPosMin σ
      · exact Or.inl ⟨hm, hP⟩
      · exact Or.inr ⟨hm, hP⟩
  have hdisj2 : Disjoint ((knTightSet L).filter knPosMin)
      ((knTightSet L).filter (fun σ => ¬ knPosMin σ)) := by
    rw [Finset.disjoint_left]
    intro σ h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact h2.2 h1.2
  have hsplit : ((knTightSet L).filter knPosMin).card +
      ((knTightSet L).filter (fun σ => ¬ knPosMin σ)).card =
      (knTightSet L).card := by
    have hcu := Finset.card_union_of_disjoint hdisj2
    rw [hunion] at hcu
    omega
  refine ⟨((knTightSet L).filter knPosMin).card, by omega⟩

private theorem knTucker {n : ℕ}
    (L : Finset (Bool × Fin n) → Bool × Fin n) (hanti : knAntipodal L) :
    ∃ x y, knConsistent x ∧ knConsistent y ∧ x ⊆ y ∧
      L y = knNegLabel (L x) := by
  classical
  by_contra hcon
  have hnc : knNoCompl L := by
    intro x y hx hy hsub h_eq
    apply hcon
    exact ⟨x, y, hx, hy, hsub, h_eq⟩
  have hodd_eq : Finset.univ.filter (fun σ => Odd ((knG L).degree σ)) =
      insert {∅} (knTightSet L) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    rw [knOddDegree L hnc σ, knMem_tightSet]
  have hnemT : ({∅} : Finset (Finset (Bool × Fin n))) ∉ knTightSet L := by
    rw [knMem_tightSet]
    intro hcon2
    obtain ⟨htight, _⟩ := hcon2
    obtain ⟨_, hcard⟩ := htight
    rw [Finset.card_singleton, knTop_singleton_empty,
      Finset.card_empty] at hcard
    omega
  have hcardS : (Finset.univ.filter (fun σ => Odd ((knG L).degree σ))).card =
      (knTightSet L).card + 1 := by
    rw [hodd_eq, Finset.card_insert_of_notMem hnemT]
  have hevenT := knPairing L hanti
  have hoddS : Odd (Finset.univ.filter
      (fun σ => Odd ((knG L).degree σ))).card := by
    rw [hcardS]
    exact Even.add_one hevenT
  have hevenS : Even (Finset.univ.filter
      (fun σ => Odd ((knG L).degree σ))).card :=
    SimpleGraph.even_card_odd_degree_vertices (knG L)
  exact (Nat.not_even_iff_odd.mpr hoddS) hevenS

private theorem knUpper_nonempty {n k : ℕ} (hk : 0 < k) (x : KneserVertex n k) :
    x.val.Nonempty :=
  Finset.card_pos.mp (by rw [x.property]; exact hk)

private def knUpperColorFn {n k : ℕ} (hk : 0 < k) (x : KneserVertex n k) :
    Fin (n - 2 * k + 1 + 1) :=
  ⟨min (x.val.min' (knUpper_nonempty hk x)).val (n - 2 * k + 1), by omega⟩

private theorem knUpperColoring {n k : ℕ} (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneserGraph n k).Colorable (n - 2 * k + 1 + 1) := by
  classical
  refine ⟨SimpleGraph.Coloring.mk (knUpperColorFn hk) ?_⟩
  intro v w hadj
  obtain ⟨hdisj, _⟩ := hadj
  intro heq
  have hnev' : v.val.Nonempty := knUpper_nonempty hk v
  have hnew' : w.val.Nonempty := knUpper_nonempty hk w
  have e1 : (knUpperColorFn hk v).val =
      min (v.val.min' hnev').val (n - 2 * k + 1) := rfl
  have e2 : (knUpperColorFn hk w).val =
      min (w.val.min' hnew').val (n - 2 * k + 1) := rfl
  have hval : min (v.val.min' hnev').val (n - 2 * k + 1) =
      min (w.val.min' hnew').val (n - 2 * k + 1) := by
    rw [← e1, ← e2]
    exact congrArg Fin.val heq
  have hmv : v.val.min' hnev' ∈ v.val := Finset.min'_mem _ _
  have hmw : w.val.min' hnew' ∈ w.val := Finset.min'_mem _ _
  have hleV : ∀ a ∈ v.val, v.val.min' hnev' ≤ a :=
    fun a ha => (v.val.isLeast_min' hnev').2 (Finset.mem_coe.mpr ha)
  have hleW : ∀ a ∈ w.val, w.val.min' hnew' ≤ a :=
    fun a ha => (w.val.isLeast_min' hnew').2 (Finset.mem_coe.mpr ha)
  by_cases hlt : (knUpperColorFn hk v).val < n - 2 * k + 1
  · rw [e1] at hlt
    have hcN : (v.val.min' hnev').val < n - 2 * k + 1 := by omega
    have hav : (v.val.min' hnev').val = (knUpperColorFn hk v).val := by
      rw [e1]
      exact (Nat.min_eq_left (le_of_lt hcN)).symm
    have hcbN : (w.val.min' hnew').val < n - 2 * k + 1 := by omega
    have hbw : (w.val.min' hnew').val = (knUpperColorFn hk v).val := by
      have hminw : min (w.val.min' hnew').val (n - 2 * k + 1) =
          (knUpperColorFn hk v).val := by
        rw [← hval]
        exact e1.symm
      rw [← hminw]
      exact (Nat.min_eq_left (le_of_lt hcbN)).symm
    have hcn : (knUpperColorFn hk v).val < n := by omega
    have hzv : v.val.min' hnev' = ⟨(knUpperColorFn hk v).val, hcn⟩ :=
      Fin.ext hav
    have hzw : w.val.min' hnew' = ⟨(knUpperColorFn hk v).val, hcn⟩ :=
      Fin.ext hbw
    have hmem1 : (⟨(knUpperColorFn hk v).val, hcn⟩ : Fin n) ∈ v.val := hzv ▸ hmv
    have hmem2 : (⟨(knUpperColorFn hk v).val, hcn⟩ : Fin n) ∈ w.val := hzw ▸ hmw
    exact (Finset.disjoint_left.mp hdisj) hmem1 hmem2
  · have hNle : n - 2 * k + 1 ≤ (knUpperColorFn hk v).val :=
      le_of_not_gt hlt
    have hgeV : ∀ a ∈ v.val, n - 2 * k + 1 ≤ a.val := by
      intro a ha
      have h1 : v.val.min' hnev' ≤ a := hleV a ha
      have h2 : (v.val.min' hnev').val ≤ a.val := by exact_mod_cast h1
      have h3 : n - 2 * k + 1 ≤ (v.val.min' hnev').val := by omega
      omega
    have hgeW : ∀ a ∈ w.val, n - 2 * k + 1 ≤ a.val := by
      intro a ha
      have h1 : w.val.min' hnew' ≤ a := hleW a ha
      have h2 : (w.val.min' hnew').val ≤ a.val := by exact_mod_cast h1
      have h3 : n - 2 * k + 1 ≤ (w.val.min' hnew').val := by omega
      omega
    have hsubV : v.val ⊆
        Finset.univ.filter (fun a : Fin n => n - 2 * k + 1 ≤ a.val) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hgeV a ha⟩
    have hsubW : w.val ⊆
        Finset.univ.filter (fun a : Fin n => n - 2 * k + 1 ≤ a.val) := by
      intro a ha
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hgeW a ha⟩
    have hcardU : (v.val ∪ w.val).card = 2 * k := by
      have hcu := Finset.card_union_of_disjoint hdisj
      rw [hcu, v.property, w.property]
      omega
    have hcardH : (Finset.univ.filter
        (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card ≤ 2 * k - 1 := by
      have hsub : (Finset.univ.filter
          (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).image Fin.val ⊆
          Finset.Ico (n - 2 * k + 1) n := by
        intro m hm
        obtain ⟨a, ha, ham⟩ := Finset.mem_image.mp hm
        have hNa := (Finset.mem_filter.mp ha).2
        rw [Finset.mem_Ico]
        constructor
        · rw [← ham]
          exact hNa
        · rw [← ham]
          exact a.2
      have hleI := Finset.card_le_card hsub
      have hIco : (Finset.Ico (n - 2 * k + 1) n).card = n - (n - 2 * k + 1) :=
        Nat.card_Ico _ _
      have himg : (Finset.univ.filter
          (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card =
          ((Finset.univ.filter
            (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).image Fin.val).card :=
        (Finset.card_image_of_injective _ Fin.val_injective).symm
      omega
    have hleU : (v.val ∪ w.val).card ≤ (Finset.univ.filter
        (fun a : Fin n => n - 2 * k + 1 ≤ a.val)).card :=
      Finset.card_le_card (by
        intro a ha
        rw [Finset.mem_union] at ha
        rcases ha with h | h
        · exact hsubV h
        · exact hsubW h)
    omega

private def knCp {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (A : Finset (Fin n)) : ℕ :=
  if h : A.card = k then (C ⟨A, h⟩).val + 1 else 0

private theorem knCp_eq {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card = k) :
    knCp C A = (C ⟨A, h⟩).val + 1 :=
  dite_eq_left h

private theorem knCp_ne {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card ≠ k) : knCp C A = 0 :=
  dite_eq_right h

private def knPos {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Fin n) :=
  (x.filter (fun l => l.1 = true)).image Prod.snd

private def knNegIdx {n : ℕ} (x : Finset (Bool × Fin n)) : Finset (Fin n) :=
  (x.filter (fun l => l.1 = false)).image Prod.snd

private def knFp {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : ℕ :=
  (Finset.powersetCard k (knPos x)).sup (knCp C)

private def knFm {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : ℕ :=
  (Finset.powersetCard k (knNegIdx x)).sup (knCp C)

private theorem knPos_negCell {n : ℕ} (x : Finset (Bool × Fin n)) :
    knPos (knNegCell x) = knNegIdx x := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
    obtain ⟨m, hm, hml⟩ := knMem_negCell.mp
      (Finset.mem_of_mem_filter _ hl)
    have hmb : m.1 = false := by
      have h1 := congrArg Prod.fst hml
      rw [hl1] at h1
      have hfst : (knNegLabel m).1 = (!m.1) := rfl
      rw [hfst] at h1
      cases hm1 : m.1 <;> simp_all
    have hmi : m.2 = i := by
      have := congrArg Prod.snd hml
      simp only [knNegLabel] at this
      omega
    have hmem : (false, i) ∈ x.filter (fun l => l.1 = false) := by
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      rw [← hmi]
      have hme : m = (false, m.2) := Prod.ext hmb rfl
      rw [hme] at hm
      exact hm
    have himg : i ∈ knNegIdx x :=
      Finset.mem_image.mpr ⟨(false, i), hmem, rfl⟩
    exact himg
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
    have hlm : l ∈ x := Finset.mem_of_mem_filter _ hl
    have hmem : knNegLabel l ∈ knNegCell x := knNegLabel_mem_negCell hlm
    have hmemf : knNegLabel l ∈
        (knNegCell x).filter (fun l => l.1 = true) := by
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      have : (knNegLabel l).1 = true := by
        rw [knNegLabel]
        simp [hl1]
      exact this
    have himg : (knNegLabel l).2 ∈ knPos (knNegCell x) :=
      Finset.mem_image.mpr ⟨knNegLabel l, hmemf, rfl⟩
    rwa [knNegLabel_snd, hll] at himg

private theorem knNegIdx_negCell {n : ℕ} (x : Finset (Bool × Fin n)) :
    knNegIdx (knNegCell x) = knPos x := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
    obtain ⟨m, hm, hml⟩ := knMem_negCell.mp
      (Finset.mem_of_mem_filter _ hl)
    have hmb : m.1 = true := by
      have h1 := congrArg Prod.fst hml
      rw [hl1] at h1
      have hfst : (knNegLabel m).1 = (!m.1) := rfl
      rw [hfst] at h1
      cases hm1 : m.1 <;> simp_all
    have hmi : m.2 = i := by
      have h2 := congrArg Prod.snd hml
      simp only [knNegLabel] at h2
      omega
    have hmem : (true, i) ∈ x.filter (fun l => l.1 = true) := by
      rw [Finset.mem_filter]
      refine ⟨?_, rfl⟩
      have hme : m = (true, m.2) := Prod.ext hmb rfl
      rw [hme] at hm
      rwa [hmi] at hm
    exact Finset.mem_image.mpr ⟨(true, i), hmem, rfl⟩
  · intro hi
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
    have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
    have hlm : l ∈ x := Finset.mem_of_mem_filter _ hl
    have hmem : knNegLabel l ∈ knNegCell x := knNegLabel_mem_negCell hlm
    have hmemf : knNegLabel l ∈
        (knNegCell x).filter (fun l => l.1 = false) := by
      rw [Finset.mem_filter]
      refine ⟨hmem, ?_⟩
      have hfl : (knNegLabel l).1 = false := by
        rw [knNegLabel]
        simp [hl1]
      exact hfl
    have himg : (knNegLabel l).2 ∈ knNegIdx (knNegCell x) :=
      Finset.mem_image.mpr ⟨knNegLabel l, hmemf, rfl⟩
    rwa [knNegLabel_snd, hll] at himg

private theorem knFpFm {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (hk : 0 < k) {x : Finset (Bool × Fin n)} (hcons : knConsistent x)
    (heq : knFp C x = knFm C x) : knFp C x = 0 := by
  classical
  by_contra hpos
  have hpos' : 0 < knFp C x := Nat.pos_of_ne_zero hpos
  have hneP : ((knPos x).powersetCard k).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsup0 : knFp C x ≤ 0 := by
      unfold knFp
      rw [Finset.sup_le_iff]
      intro B hB
      rw [hempty] at hB
      exact absurd hB (Finset.notMem_empty B)
    omega
  obtain ⟨A, hAmem, hAmax⟩ :=
    Finset.exists_max_image _ (knCp C) hneP
  have hAsup : knFp C x = knCp C A := by
    apply le_antisymm
    · unfold knFp
      rw [Finset.sup_le_iff]
      exact hAmax
    · unfold knFp
      exact Finset.le_sup hAmem
  have hAsub : A ⊆ knPos x := (Finset.mem_powersetCard.mp hAmem).1
  have hAcard : A.card = k := by
    by_contra hne2
    have hzero : knCp C A = 0 := knCp_ne C hne2
    omega
  have hAval : (C ⟨A, hAcard⟩).val + 1 = knFp C x := by
    have hcp := knCp_eq C hAcard
    omega
  have hneM : ((knNegIdx x).powersetCard k).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsup0 : knFm C x ≤ 0 := by
      unfold knFm
      rw [Finset.sup_le_iff]
      intro B hB
      rw [hempty] at hB
      exact absurd hB (Finset.notMem_empty B)
    omega
  obtain ⟨B, hBmem, hBmax⟩ :=
    Finset.exists_max_image _ (knCp C) hneM
  have hBsup : knFm C x = knCp C B := by
    apply le_antisymm
    · unfold knFm
      rw [Finset.sup_le_iff]
      exact hBmax
    · unfold knFm
      exact Finset.le_sup hBmem
  have hBsub : B ⊆ knNegIdx x := (Finset.mem_powersetCard.mp hBmem).1
  have hBcard : B.card = k := by
    by_contra hne2
    have hzero : knCp C B = 0 := knCp_ne C hne2
    omega
  have hBval : (C ⟨B, hBcard⟩).val + 1 = knFm C x := by
    have hcp := knCp_eq C hBcard
    omega
  have hposmem : ∀ a ∈ A, (true, a) ∈ x := by
    intro a ha
    have haP : a ∈ knPos x := hAsub ha
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp haP
    have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
    have hle : l = (true, a) := Prod.ext hl1 hll
    rw [hle] at hl
    exact Finset.mem_of_mem_filter _ hl
  have hnegmem : ∀ a ∈ B, (false, a) ∈ x := by
    intro a ha
    have haP : a ∈ knNegIdx x := hBsub ha
    obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp haP
    have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
    have hle : l = (false, a) := Prod.ext hl1 hll
    rw [hle] at hl
    exact Finset.mem_of_mem_filter _ hl
  have hdisj : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ht := hposmem a ha
    have hf := hnegmem a hb
    exact hcons _ ht hf
  have hneAB : A ≠ B := by
    intro heqAB
    have hAne : A.Nonempty := Finset.card_pos.mp (by rw [hAcard]; exact hk)
    obtain ⟨a, ha⟩ := hAne
    have haB : a ∈ B := heqAB ▸ ha
    exact (Finset.disjoint_left.mp hdisj ha) haB
  have hadjG : (kneserGraph n k).Adj ⟨A, hAcard⟩ ⟨B, hBcard⟩ :=
    ⟨hdisj, fun he => hneAB (congrArg Subtype.val he)⟩
  have hCne := C.valid hadjG
  have hCeq : C ⟨A, hAcard⟩ = C ⟨B, hBcard⟩ := by
    apply Fin.ext
    omega
  exact hCne hCeq

private theorem knFp_le {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : knFp C x ≤ N := by
  unfold knFp
  rw [Finset.sup_le_iff]
  intro B _
  by_cases hB : B.card = k
  · rw [knCp_eq C hB]
    have hlt := (C ⟨B, hB⟩).isLt
    omega
  · rw [knCp_ne C hB]
    exact Nat.zero_le N

private theorem knFm_le {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) : knFm C x ≤ N := by
  unfold knFm
  rw [Finset.sup_le_iff]
  intro B _
  by_cases hB : B.card = k
  · rw [knCp_eq C hB]
    have hlt := (C ⟨B, hB⟩).isLt
    omega
  · rw [knCp_ne C hB]
    exact Nat.zero_le N

private theorem knPos_mono {n : ℕ} {x y : Finset (Bool × Fin n)}
    (h : x ⊆ y) : knPos x ⊆ knPos y := by
  classical
  intro i hi
  obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
  have hlx : l ∈ x := Finset.mem_of_mem_filter _ hl
  have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
  exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨h hlx, hl1⟩, hll⟩

private theorem knNegIdx_mono {n : ℕ} {x y : Finset (Bool × Fin n)}
    (h : x ⊆ y) : knNegIdx x ⊆ knNegIdx y := by
  classical
  intro i hi
  obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hi
  have hlx : l ∈ x := Finset.mem_of_mem_filter _ hl
  have hl1 : l.1 = false := (Finset.mem_filter.mp hl).2
  exact Finset.mem_image.mpr ⟨l, Finset.mem_filter.mpr ⟨h hlx, hl1⟩, hll⟩

private theorem knFp_mono {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {x y : Finset (Bool × Fin n)} (h : x ⊆ y) : knFp C x ≤ knFp C y := by
  classical
  unfold knFp
  rw [Finset.sup_le_iff]
  intro B hB
  have hBmem := Finset.mem_powersetCard.mp hB
  have hBmem2 : B ∈ Finset.powersetCard k (knPos y) :=
    Finset.mem_powersetCard.mpr ⟨hBmem.1.trans (knPos_mono h), hBmem.2⟩
  exact Finset.le_sup hBmem2

private theorem knFm_mono {n k N : ℕ} (C : (kneserGraph n k).Coloring (Fin N))
    {x y : Finset (Bool × Fin n)} (h : x ⊆ y) : knFm C x ≤ knFm C y := by
  classical
  unfold knFm
  rw [Finset.sup_le_iff]
  intro B hB
  have hBmem := Finset.mem_powersetCard.mp hB
  have hBmem2 : B ∈ Finset.powersetCard k (knNegIdx y) :=
    Finset.mem_powersetCard.mpr ⟨hBmem.1.trans (knNegIdx_mono h), hBmem.2⟩
  exact Finset.le_sup hBmem2

private theorem knConsistent_snd_inj {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) {l₁ l₂ : Bool × Fin n}
    (h₁ : l₁ ∈ x) (h₂ : l₂ ∈ x) (hsnd : l₁.2 = l₂.2) : l₁ = l₂ := by
  by_cases hb : l₁.1 = l₂.1
  · exact Prod.ext hb hsnd
  · exfalso
    have hnb : l₂.1 = !l₁.1 := by
      cases h₁b : l₁.1 <;> cases h₂b : l₂.1 <;> simp_all
    have hneg : l₂ = knNegLabel l₁ := by
      have e1 : l₂ = (l₂.1, l₂.2) := Prod.mk.eta.symm
      have e2 : knNegLabel l₁ = ((!l₁.1), l₁.2) := rfl
      rw [e1, e2, hnb, hsnd]
    exact hcons l₁ h₁ (hneg ▸ h₂)

private theorem knFilterPos_injOn {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) :
    Set.InjOn Prod.snd (↑(x.filter (fun l => l.1 = true)) :
      Set (Bool × Fin n)) := by
  intro a ha b hb hab
  exact knConsistent_snd_inj hcons (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp ha)) (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp hb)) hab

private theorem knFilterNeg_injOn {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) :
    Set.InjOn Prod.snd (↑(x.filter (fun l => l.1 = false)) :
      Set (Bool × Fin n)) := by
  intro a ha b hb hab
  exact knConsistent_snd_inj hcons (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp ha)) (Finset.mem_of_mem_filter _
    (Finset.mem_coe.mp hb)) hab

private theorem knConsistent_card_eq {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) :
    x.card = (knPos x).card + (knNegIdx x).card := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := x) (fun l => l.1 = true)
  have hneg : x.filter (fun l => ¬ l.1 = true) =
      x.filter (fun l => l.1 = false) := by
    apply Finset.filter_congr
    intro l _
    simp only [Bool.not_eq_true]
  rw [hneg] at hpart
  have hp : (knPos x).card = (x.filter (fun l => l.1 = true)).card := by
    unfold knPos
    exact Finset.card_image_of_injOn (knFilterPos_injOn hcons)
  have hq : (knNegIdx x).card = (x.filter (fun l => l.1 = false)).card := by
    unfold knNegIdx
    exact Finset.card_image_of_injOn (knFilterNeg_injOn hcons)
  omega

private theorem knPos_neg_disjoint {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) :
    Disjoint (knPos x) (knNegIdx x) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiP hiN
  obtain ⟨l, hl, hll⟩ := Finset.mem_image.mp hiP
  obtain ⟨m, hm, hmm⟩ := Finset.mem_image.mp hiN
  have hl1 : l.1 = true := (Finset.mem_filter.mp hl).2
  have hm1 : m.1 = false := (Finset.mem_filter.mp hm).2
  have hle : l = (true, i) := Prod.ext hl1 hll
  have hme : m = (false, i) := Prod.ext hm1 hmm
  have hlt : (true, i) ∈ x := hle ▸ Finset.mem_of_mem_filter _ hl
  have hmt : (false, i) ∈ x := hme ▸ Finset.mem_of_mem_filter _ hm
  have hneg : knNegLabel (true, i) = (false, i) := rfl
  exact hcons _ hlt (hneg ▸ hmt)

private theorem knCp_pos_of_card {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {A : Finset (Fin n)} (h : A.card = k) : 0 < knCp C A := by
  rw [knCp_eq C h]
  omega

private theorem knPos_card_lt_of_fp_zero {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (h0 : knFp C x = 0) :
    (knPos x).card < k := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcon
  have hmem : A ∈ Finset.powersetCard k (knPos x) :=
    Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩
  have hle : knCp C A ≤ knFp C x := Finset.le_sup hmem
  have hpos := knCp_pos_of_card C hAcard
  omega

private theorem knNegIdx_card_lt_of_fm_zero {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (h0 : knFm C x = 0) :
    (knNegIdx x).card < k := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hcon
  have hmem : A ∈ Finset.powersetCard k (knNegIdx x) :=
    Finset.mem_powersetCard.mpr ⟨hAsub, hAcard⟩
  have hle : knCp C A ≤ knFm C x := Finset.le_sup hmem
  have hpos := knCp_pos_of_card C hAcard
  omega

private theorem knLargeIdx_lt {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
    (f : ℕ) (hf1 : 1 ≤ f) (hfN : f ≤ n - 2 * k + 1) :
    (f - 1) + 2 * (k - 1) < n := by
  omega

private theorem knMinLt {n : ℕ} (a : ℕ) (hn : 0 < n) :
    min a (n - 1) < n := by
  have h := Nat.min_le_right a (n - 1)
  omega

private def knMinIdx {n : ℕ} (x : Finset (Bool × Fin n))
    (hne : x.Nonempty) : Fin n :=
  (x.image Prod.snd).min' (hne.image _)

private theorem knMinIdx_mem {n : ℕ} {x : Finset (Bool × Fin n)}
    (hne : x.Nonempty) : knMinIdx x hne ∈ x.image Prod.snd :=
  Finset.min'_mem _ _

private theorem knMinIdx_le {n : ℕ} {x : Finset (Bool × Fin n)}
    (hne : x.Nonempty) {j : Fin n} (hj : j ∈ x.image Prod.snd) :
    knMinIdx x hne ≤ j :=
  Finset.min'_le _ _ hj

private theorem knNegCell_image_snd {n : ℕ} (x : Finset (Bool × Fin n)) :
    (knNegCell x).image Prod.snd = x.image Prod.snd := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨l, hl, hlj⟩ := Finset.mem_image.mp hj
    obtain ⟨m, hm, hml⟩ := knMem_negCell.mp hl
    refine Finset.mem_image.mpr ⟨m, hm, ?_⟩
    rw [← hlj, ← hml]
    rfl
  · intro hj
    obtain ⟨m, hm, hmj⟩ := Finset.mem_image.mp hj
    refine Finset.mem_image.mpr ⟨knNegLabel m, knNegLabel_mem_negCell hm, ?_⟩
    rw [knNegLabel_snd, hmj]

private theorem knMinIdx_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
    (hne : x.Nonempty) (hneN : (knNegCell x).Nonempty) :
    knMinIdx (knNegCell x) hneN = knMinIdx x hne := by
  classical
  have himg := knNegCell_image_snd x
  have hiN : knMinIdx (knNegCell x) hneN ∈ x.image Prod.snd := by
    have h := knMinIdx_mem hneN
    rwa [himg] at h
  have hi : knMinIdx x hne ∈ (knNegCell x).image Prod.snd := by
    have h := knMinIdx_mem hne
    rwa [← himg] at h
  exact le_antisymm (knMinIdx_le hneN hi) (knMinIdx_le hne hiN)

private theorem knTrue_mem_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
    {i : Fin n} :
    (true, i) ∈ knNegCell x ↔ (false, i) ∈ x := by
  classical
  rw [knMem_negCell]
  constructor
  · rintro ⟨m, hm, hml⟩
    have h1 : m.1 = false := by
      have h := congrArg Prod.fst hml
      simpa [knNegLabel] using h
    have h2 : m.2 = i := by
      have h := congrArg Prod.snd hml
      simpa [knNegLabel] using h
    have hme : m = (false, i) := Prod.ext h1 h2
    rwa [hme] at hm
  · intro hm
    exact ⟨(false, i), hm, rfl⟩

private theorem knFalse_mem_negCell {n : ℕ} {x : Finset (Bool × Fin n)}
    {i : Fin n} :
    (false, i) ∈ knNegCell x ↔ (true, i) ∈ x := by
  classical
  rw [knMem_negCell]
  constructor
  · rintro ⟨m, hm, hml⟩
    have h1 : m.1 = true := by
      have h := congrArg Prod.fst hml
      simpa [knNegLabel] using h
    have h2 : m.2 = i := by
      have h := congrArg Prod.snd hml
      simpa [knNegLabel] using h
    have hme : m = (true, i) := Prod.ext h1 h2
    rwa [hme] at hm
  · intro hm
    exact ⟨(true, i), hm, rfl⟩

private def knLabSmall {n : ℕ} (x : Finset (Bool × Fin n))
    (hne : x.Nonempty) (hn : 0 < n) : Bool × Fin n :=
  (decide ((true, knMinIdx x hne) ∈ x),
    ⟨min (x.card - 1) (n - 1), knMinLt _ hn⟩)

private def knLabLargePos {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hk : 0 < k) (h2 : 2 * k ≤ n) (x : Finset (Bool × Fin n))
    (hfp : 1 ≤ knFp C x) : Bool × Fin n :=
  (true, ⟨(knFp C x - 1) + 2 * (k - 1),
    knLargeIdx_lt hk h2 _ hfp (knFp_le C x)⟩)

private def knLabLargeNeg {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hk : 0 < k) (h2 : 2 * k ≤ n) (x : Finset (Bool × Fin n))
    (hfm : 1 ≤ knFm C x) : Bool × Fin n :=
  (false, ⟨(knFm C x - 1) + 2 * (k - 1),
    knLargeIdx_lt hk h2 _ hfm (knFm_le C x)⟩)

private def knLab {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    (x : Finset (Bool × Fin n)) : Bool × Fin n :=
  if _hx : x = ∅ then (true, ⟨n - 1, by omega⟩)
  else if _hsmall : knFp C x = 0 ∧ knFm C x = 0 then
    knLabSmall x (Finset.nonempty_iff_ne_empty.mpr _hx) hn
  else if hpos : knFm C x < knFp C x then
    knLabLargePos C hk h2 x (by omega)
  else
    knLabLargeNeg C hk h2 x (by
      have hfm0 : knFm C x ≠ 0 := by
        intro h0
        apply _hsmall
        refine ⟨?_, h0⟩
        omega
      exact Nat.pos_of_ne_zero hfm0)

private theorem knLab_empty {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
    knLab C hn hk h2 ∅ = (true, ⟨n - 1, by omega⟩) := by
  unfold knLab
  simp

private theorem knLab_small {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    {x : Finset (Bool × Fin n)} (hne : x ≠ ∅)
    (hfp : knFp C x = 0) (hfm : knFm C x = 0) :
    knLab C hn hk h2 x =
      knLabSmall x (Finset.nonempty_iff_ne_empty.mpr hne) hn := by
  unfold knLab
  simp only [dite_eq_right hne,
    dite_eq_left (show knFp C x = 0 ∧ knFm C x = 0 from ⟨hfp, hfm⟩)]

private theorem knLab_large_pos {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    {x : Finset (Bool × Fin n)} (hne : x ≠ ∅)
    (hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0))
    (hpos : knFm C x < knFp C x) (hfp : 1 ≤ knFp C x) :
    knLab C hn hk h2 x = knLabLargePos C hk h2 x hfp := by
  unfold knLab
  simp only [dite_eq_right hne, dite_eq_right hlarge, dite_eq_left hpos]

private theorem knLab_large_neg {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    {x : Finset (Bool × Fin n)} (hne : x ≠ ∅)
    (hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0))
    (hneg : ¬ knFm C x < knFp C x) (hfm : 1 ≤ knFm C x) :
    knLab C hn hk h2 x = knLabLargeNeg C hk h2 x hfm := by
  unfold knLab
  simp only [dite_eq_right hne, dite_eq_right hlarge, dite_eq_right hneg]

private theorem knConsistent_bool_exact {n : ℕ} {x : Finset (Bool × Fin n)}
    (hcons : knConsistent x) {i : Fin n} (hi : i ∈ x.image Prod.snd) :
    ((true, i) ∈ x ∧ (false, i) ∉ x) ∨
      ((false, i) ∈ x ∧ (true, i) ∉ x) := by
  classical
  obtain ⟨l, hl, hli⟩ := Finset.mem_image.mp hi
  obtain ⟨b, j⟩ := l
  have hji : j = i := hli
  cases b with
  | false =>
    refine Or.inr ⟨hji ▸ hl, ?_⟩
    intro hcon
    have hcon' : (true, j) ∈ x := by rw [hji]; exact hcon
    have hneg : knNegLabel (false, j) = (true, j) := rfl
    exact hcons _ hl (hneg ▸ hcon')
  | true =>
    refine Or.inl ⟨hji ▸ hl, ?_⟩
    intro hcon
    have hcon' : (false, j) ∈ x := by rw [hji]; exact hcon
    have hpos : (true, j) ∈ x := hji ▸ hl
    have hneg : knNegLabel (true, j) = (false, j) := rfl
    exact hcons _ hpos (hneg ▸ hcon')

private theorem knLabSmall_fst {n : ℕ} {x : Finset (Bool × Fin n)}
    {hne : x.Nonempty} {hn : 0 < n} :
    (knLabSmall x hne hn).1 = decide ((true, knMinIdx x hne) ∈ x) := rfl

private theorem knLabSmall_snd_val {n : ℕ} {x : Finset (Bool × Fin n)}
    {hne : x.Nonempty} {hn : 0 < n} :
    ((knLabSmall x hne hn).2).val = min (x.card - 1) (n - 1) := rfl

private theorem knLabLargePos_fst {n k : ℕ}
    {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
    {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
    {hfp : 1 ≤ knFp C x} :
    (knLabLargePos C hk h2 x hfp).1 = true := rfl

private theorem knLabLargePos_snd_val {n k : ℕ}
    {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
    {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
    {hfp : 1 ≤ knFp C x} :
    ((knLabLargePos C hk h2 x hfp).2).val = (knFp C x - 1) + 2 * (k - 1) :=
  rfl

private theorem knLabLargeNeg_fst {n k : ℕ}
    {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
    {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
    {hfm : 1 ≤ knFm C x} :
    (knLabLargeNeg C hk h2 x hfm).1 = false := rfl

private theorem knLabLargeNeg_snd_val {n k : ℕ}
    {C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1))}
    {hk : 0 < k} {h2 : 2 * k ≤ n} {x : Finset (Bool × Fin n)}
    {hfm : 1 ≤ knFm C x} :
    ((knLabLargeNeg C hk h2 x hfm).2).val = (knFm C x - 1) + 2 * (k - 1) :=
  rfl

private theorem knNegLabel_fst {n : ℕ} (l : Bool × Fin n) :
    (knNegLabel l).1 = !l.1 := rfl

private theorem knSmall_card_le {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    {x : Finset (Bool × Fin n)} (hcons : knConsistent x)
    (hfp : knFp C x = 0) (hfm : knFm C x = 0) :
    x.card ≤ 2 * k - 2 := by
  have hp := knPos_card_lt_of_fp_zero C hfp
  have hq := knNegIdx_card_lt_of_fm_zero C hfm
  have hc := knConsistent_card_eq hcons
  omega

private theorem knSmall_val_lt {n k : ℕ} (hk : 0 < k)
    {x : Finset (Bool × Fin n)} (xne : x.Nonempty)
    (hle : x.card ≤ 2 * k - 2) :
    min (x.card - 1) (n - 1) < 2 * (k - 1) := by
  have h1 : 1 ≤ x.card := Finset.one_le_card.mpr xne
  have h2m := Nat.min_le_left (x.card - 1) (n - 1)
  omega

private theorem knSmall_val_ne {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
    {x : Finset (Bool × Fin n)} (xne : x.Nonempty)
    (hle : x.card ≤ 2 * k - 2) :
    min (x.card - 1) (n - 1) ≠ n - 1 := by
  have h1 : 1 ≤ x.card := Finset.one_le_card.mpr xne
  have h2m := Nat.min_le_left (x.card - 1) (n - 1)
  omega

private theorem knLarge_val_le {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
    (f : ℕ) (hf1 : 1 ≤ f) (hfN : f ≤ n - 2 * k + 1) :
    (f - 1) + 2 * (k - 1) ≤ n - 2 := by
  omega

private theorem knLarge_val_ne {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n)
    (f : ℕ) (hf1 : 1 ≤ f) (hfN : f ≤ n - 2 * k + 1) :
    (f - 1) + 2 * (k - 1) ≠ n - 1 := by
  have hle := knLarge_val_le hk h2 f hf1 hfN
  omega

private theorem knLarge_or_small {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N)) (hk : 0 < k)
    {x : Finset (Bool × Fin n)} (hcons : knConsistent x) :
    (knFp C x = 0 ∧ knFm C x = 0) ∨
      knFm C x < knFp C x ∨ knFp C x < knFm C x := by
  by_cases heq : knFp C x = knFm C x
  · left
    have h0 := knFpFm C hk hcons heq
    exact ⟨h0, by omega⟩
  · right
    exact lt_or_gt_of_ne (Ne.symm heq)

private theorem knLab_noCompl_empty {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n)
    {y : Finset (Bool × Fin n)} (hconsY : knConsistent y)
    (heq : knLab C hn hk h2 y =
      knNegLabel (knLab C hn hk h2 ∅)) : False := by
  classical
  by_cases hy0 : y = ∅
  · subst hy0
    have hxL := knLab_empty C hn hk h2
    rw [hxL] at heq
    have hfst : (true : Bool) = !true := congrArg Prod.fst heq
    exact (by decide : ¬ ((true : Bool) = !true)) hfst
  · have hyNonempty : y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hy0
    have hval : ((knLab C hn hk h2 y).2).val = n - 1 := by
      have h := congrArg Fin.val (congrArg Prod.snd heq)
      rw [knLab_empty C hn hk h2] at h
      exact h
    rcases knLarge_or_small C hk hconsY with ⟨hfp0, hfm0⟩ | hpos | hneg
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          min (y.card - 1) (n - 1) := by
        have hLy := knLab_small C hn hk h2 hy0 hfp0 hfm0
        simp only [hLy, knLabSmall_snd_val]
      have hne2 := knSmall_val_ne hk h2 hyNonempty
        (knSmall_card_le C hconsY hfp0 hfm0)
      omega
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          (knFp C y - 1) + 2 * (k - 1) := by
        have hlarge : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlarge hpos (by omega)
        simp only [hLy, knLabLargePos_snd_val]
      have hne2 := knLarge_val_ne hk h2 (knFp C y) (by omega) (knFp_le C y)
      omega
    · have hLyv : ((knLab C hn hk h2 y).2).val =
          (knFm C y - 1) + 2 * (k - 1) := by
        have hlarge : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlarge (by omega)
          (by omega)
        simp only [hLy, knLabLargeNeg_snd_val]
      have hne2 := knLarge_val_ne hk h2 (knFm C y) (by omega) (knFm_le C y)
      omega

private theorem knLab_noCompl {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
    knNoCompl (knLab C hn hk h2) := by
  classical
  intro x y hconsX hconsY hsub heq
  by_cases hx0 : x = ∅
  · subst hx0
    exact knLab_noCompl_empty C hn hk h2 hconsY heq
  · have hxNonempty : x.Nonempty := Finset.nonempty_iff_ne_empty.mpr hx0
    have hyne : y.Nonempty := by
      obtain ⟨l, hl⟩ := hxNonempty
      exact ⟨l, hsub hl⟩
    have hy0 : y ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hyne
    rcases knLarge_or_small C hk hconsX with ⟨hfp0, hfm0⟩ | hposX | hnegX
    · have hval := congrArg Fin.val (congrArg Prod.snd heq)
      rw [knNegLabel_snd] at hval
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hLy := knLab_small C hn hk h2 hy0 hfp0y hfm0y
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            min (y.card - 1) (n - 1) := by
          simp only [hLy, knLabSmall_snd_val]
        have hle_x := knSmall_card_le C hconsX hfp0 hfm0
        have hle_y := knSmall_card_le C hconsY hfp0y hfm0y
        have hx1 : 1 ≤ x.card := Finset.one_le_card.mpr hxNonempty
        have hy1 : 1 ≤ y.card := Finset.one_le_card.mpr hyne
        have hcardxy : x.card = y.card := by omega
        have hxy : x = y :=
          Finset.eq_of_subset_of_card_le hsub (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 y).1) := by
          have h := congrArg Prod.fst heq
          rw [hxy] at h
          exact h
        cases hbx : (knLab C hn hk h2 y).1 with
        | true =>
          rw [hbx] at hfst
          exact (by decide : ¬ ((true : Bool) = !true)) hfst
        | false =>
          rw [hbx] at hfst
          exact (by decide : ¬ ((false : Bool) = !false)) hfst
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFp C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargePos_snd_val]
        have hlt := knSmall_val_lt hk hxNonempty
          (knSmall_card_le C hconsX hfp0 hfm0)
        have hge : 2 * (k - 1) ≤ (knFp C y - 1) + 2 * (k - 1) := by
          omega
        omega
      · have hLx := knLab_small C hn hk h2 hx0 hfp0 hfm0
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hLxv : ((knLab C hn hk h2 x).2).val =
            min (x.card - 1) (n - 1) := by
          simp only [hLx, knLabSmall_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFm C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargeNeg_snd_val]
        have hlt := knSmall_val_lt hk hxNonempty
          (knSmall_card_le C hconsX hfp0 hfm0)
        have hge : 2 * (k - 1) ≤ (knFm C y - 1) + 2 * (k - 1) := by
          omega
        omega
    · have hlargeX : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by
        intro hcon; omega
      have hLx := knLab_large_pos C hn hk h2 hx0 hlargeX hposX
        (by omega)
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        omega
      · have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 x).1) :=
          congrArg Prod.fst heq
        rw [hLy, hLx, knLabLargePos_fst, knLabLargePos_fst] at hfst
        exact (by decide : ¬ ((true : Bool) = !true)) hfst
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hval := congrArg Fin.val (congrArg Prod.snd heq)
        rw [knNegLabel_snd] at hval
        have hLxv : ((knLab C hn hk h2 x).2).val =
            (knFp C x - 1) + 2 * (k - 1) := by
          simp only [hLx, knLabLargePos_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFm C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargeNeg_snd_val]
        omega
    · have hlargeX : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by
        intro hcon; omega
      have hLx := knLab_large_neg C hn hk h2 hx0 hlargeX (by omega)
        (by omega)
      rcases knLarge_or_small C hk hconsY with ⟨hfp0y, hfm0y⟩ | hposY | hnegY
      · have hfp_le : knFp C x ≤ knFp C y := knFp_mono C hsub
        have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        omega
      · have hfm_le : knFm C x ≤ knFm C y := knFm_mono C hsub
        have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_pos C hn hk h2 hy0 hlargeY hposY
          (by omega)
        have hval := congrArg Fin.val (congrArg Prod.snd heq)
        rw [knNegLabel_snd] at hval
        have hLxv : ((knLab C hn hk h2 x).2).val =
            (knFm C x - 1) + 2 * (k - 1) := by
          simp only [hLx, knLabLargeNeg_snd_val]
        have hLyv : ((knLab C hn hk h2 y).2).val =
            (knFp C y - 1) + 2 * (k - 1) := by
          simp only [hLy, knLabLargePos_snd_val]
        omega
      · have hlargeY : ¬ (knFp C y = 0 ∧ knFm C y = 0) := by
          intro hcon; omega
        have hLy := knLab_large_neg C hn hk h2 hy0 hlargeY (by omega)
          (by omega)
        have hfst : (knLab C hn hk h2 y).1 =
            !((knLab C hn hk h2 x).1) :=
          congrArg Prod.fst heq
        rw [hLy, hLx, knLabLargeNeg_fst, knLabLargeNeg_fst] at hfst
        exact (by decide : ¬ ((false : Bool) = !false)) hfst

private theorem knFp_negCell {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) :
    knFp C (knNegCell x) = knFm C x := by
  unfold knFp knFm
  rw [knPos_negCell]

private theorem knFm_negCell {n k N : ℕ}
    (C : (kneserGraph n k).Coloring (Fin N))
    (x : Finset (Bool × Fin n)) :
    knFm C (knNegCell x) = knFp C x := by
  unfold knFp knFm
  rw [knNegIdx_negCell]

private theorem knLab_antipodal {n k : ℕ}
    (C : (kneserGraph n k).Coloring (Fin (n - 2 * k + 1)))
    (hn : 0 < n) (hk : 0 < k) (h2 : 2 * k ≤ n) :
    knAntipodal (knLab C hn hk h2) := by
  classical
  intro x hcons hxne
  have hne : x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hxne
  have hcard : 0 < x.card := Finset.card_pos.mpr hxne
  have hneN : (knNegCell x).Nonempty := by
    apply Finset.card_pos.mp
    rw [knNegCell_card]
    exact hcard
  have hneN' : knNegCell x ≠ ∅ := Finset.nonempty_iff_ne_empty.mp hneN
  have hfpN : knFp C (knNegCell x) = knFm C x := knFp_negCell C x
  have hfmN : knFm C (knNegCell x) = knFp C x := knFm_negCell C x
  rcases knLarge_or_small C hk hcons with ⟨hfp0, hfm0⟩ | hpos | hneg
  · have hfpN0 : knFp C (knNegCell x) = 0 := by rw [hfpN]; exact hfm0
    have hfmN0 : knFm C (knNegCell x) = 0 := by rw [hfmN]; exact hfp0
    have hLx := knLab_small C hn hk h2 hne hfp0 hfm0
    have hLN := knLab_small C hn hk h2 hneN' hfpN0 hfmN0
    rw [hLx, hLN]
    apply Prod.ext
    · simp only [knLabSmall_fst, knNegLabel_fst, knLabSmall_fst,
        knMinIdx_negCell hxne hneN, knTrue_mem_negCell]
      rcases knConsistent_bool_exact hcons
        (knMinIdx_mem hxne) with ⟨ht, hf⟩ | ⟨hf, ht⟩
      · rw [decide_eq_false hf, decide_eq_true ht]
        rfl
      · rw [decide_eq_true hf, decide_eq_false ht]
        rfl
    · apply Fin.ext
      rw [knLabSmall_snd_val, knNegLabel_snd, knLabSmall_snd_val,
        knNegCell_card]
  · have hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by intro hcon; omega
    have hfp1 : 1 ≤ knFp C x := by omega
    have hLx := knLab_large_pos C hn hk h2 hne hlarge hpos hfp1
    have hlargeN : ¬ (knFp C (knNegCell x) = 0 ∧
        knFm C (knNegCell x) = 0) := by
      rw [hfpN, hfmN]; intro hcon; omega
    have hnegN : ¬ knFm C (knNegCell x) < knFp C (knNegCell x) := by
      rw [hfpN, hfmN]; omega
    have hfmN1 : 1 ≤ knFm C (knNegCell x) := by rw [hfmN]; omega
    have hLN := knLab_large_neg C hn hk h2 hneN' hlargeN hnegN hfmN1
    rw [hLx, hLN]
    unfold knLabLargeNeg knLabLargePos knNegLabel
    dsimp only
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [Fin.mk.injEq, hfmN]
  · have hlarge : ¬ (knFp C x = 0 ∧ knFm C x = 0) := by intro hcon; omega
    have hfm1 : 1 ≤ knFm C x := by omega
    have hLx := knLab_large_neg C hn hk h2 hne hlarge (by omega) hfm1
    have hlargeN : ¬ (knFp C (knNegCell x) = 0 ∧
        knFm C (knNegCell x) = 0) := by
      rw [hfpN, hfmN]; intro hcon; omega
    have hposN : knFm C (knNegCell x) < knFp C (knNegCell x) := by
      rw [hfpN, hfmN]; omega
    have hfpN1 : 1 ≤ knFp C (knNegCell x) := by rw [hfpN]; omega
    have hLN := knLab_large_pos C hn hk h2 hneN' hlargeN hposN hfpN1
    rw [hLx, hLN]
    unfold knLabLargeNeg knLabLargePos knNegLabel
    dsimp only
    rw [Prod.mk.injEq]
    refine ⟨rfl, ?_⟩
    rw [Fin.mk.injEq, hfpN]


private theorem knNotColorable {n k : ℕ} (hk : 0 < k) (h2 : 2 * k ≤ n) :
    ¬ (kneserGraph n k).Colorable (n - 2 * k + 1) := by
  intro hC
  obtain ⟨C⟩ := hC
  have hn : 0 < n := by omega
  obtain ⟨x, y, hconsX, hconsY, hsub, heq⟩ :=
    knTucker (knLab C hn hk h2) (knLab_antipodal C hn hk h2)
  exact knLab_noCompl C hn hk h2 x y hconsX hconsY hsub heq

/--
**Kneser–Lovász theorem.** Let $n$ and $k$ be natural numbers with $0 < k$ and $2k \le n$. The
Kneser graph $K(n, k)$, whose vertices are the $k$-element subsets of $\{0, 1, \dots, n-1\}$ and
in which two such subsets are adjacent when they are disjoint and distinct, has chromatic number
$n - 2k + 2$.

Proves `Wanted` entry `kneser_lovasz`.

Source: L. Lovasz, JCT A 25 (1978), 319-324, DOI 10.1016/0097-3165(78)90022-5.
-/
public theorem kneser_lovasz {n k : ℕ} (hk : 0 < k) (h : 2 * k ≤ n) :
    (kneserGraph n k).chromaticNumber = (n - 2 * k + 2 : ℕ∞) := by
  have hcast : (n - 2 * k + 2 : ℕ∞) =
      (((n - 2 * k + 1 : ℕ) : ℕ∞) + 1) := by
    have e1 : ((2 * k : ℕ) : ℕ∞) = 2 * (↑k : ℕ∞) := by push_cast; ring
    have e2 : ((n - 2 * k : ℕ) : ℕ∞) =
        (↑n : ℕ∞) - ((2 * k : ℕ) : ℕ∞) :=
      ENat.natCast_sub n (2 * k)
    have e4 : ((n - 2 * k + 1 : ℕ) : ℕ∞) =
        ((n - 2 * k : ℕ) : ℕ∞) + 1 := by
      push_cast
      ring
    rw [← e1, ← e2, e4]
    ring
  rw [hcast, SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable]
  refine ⟨knUpperColoring hk h, knNotColorable hk h⟩

end MathlibExt.Combinatorics.SimpleGraph.KneserLovaszWanted
