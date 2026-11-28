/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fintype.Card

/-!
# Separators and disjoint path families

Separators of vertex sets, families of disjoint paths, and the easy half of Menger's theorem.

## i. Overview

`bc16_IsSeparator G S T C` says that every walk from `S` to `T` meets `C`. A
`bc16_DisjointPathFamily` is an indexed family of vertex-disjoint paths from `S` to `T`. Each path
meets a separator, at distinct vertices for distinct paths, so the number of paths is at most the
size of any separator (`bc16_max_le_min`). An empty separator exists exactly when `T` is unreachable
from `S`.

## ii. Key results

- `bc16_hitVertex_injective` : distinct paths meet a separator at distinct vertices
- `bc16_max_le_min` : the easy half of Menger's theorem
- `bc16_empty_separator_iff_not_reachable` : empty separators and reachability

## iii. Table of contents

- A. Definitions
- B. Results

## iv. References

- K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927), 96–115.
- R. Diestel, *Graph Theory*, 5th ed., Springer (2017), §3.3.
-/

@[expose] public section

namespace StatMech.Walls

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V}

/-! ## A. Definitions -/

/-- `C` separates `S` from `T` in `G`: every walk from `S` to `T` meets `C`. -/
def bc16_IsSeparator (G : SimpleGraph V) (S T : Set V) (C : Set V) : Prop :=
  ∀ ⦃s : V⦄, s ∈ S → ∀ ⦃t : V⦄, t ∈ T → ∀ p : G.Walk s t, ∃ c ∈ C, c ∈ p.support

/-! ## B. Results -/

lemma bc16_univ_isSeparator (G : SimpleGraph V) (S T : Set V) :
    bc16_IsSeparator G S T Set.univ := by
  intro s _ t _ p
  exact ⟨s, Set.mem_univ s, p.start_mem_support⟩

lemma bc16_separator_mono {S T C C' : Set V} (h : bc16_IsSeparator G S T C)
    (hCC' : C ⊆ C') : bc16_IsSeparator G S T C' := by
  intro s hs t ht p
  obtain ⟨c, hcC, hcp⟩ := h hs ht p
  exact ⟨c, hCC' hcC, hcp⟩

lemma bc16_separator_symm {S T C : Set V} (h : bc16_IsSeparator G S T C) :
    bc16_IsSeparator G T S C := by
  intro t ht s hs p
  obtain ⟨c, hcC, hcp⟩ := h hs ht p.reverse
  refine ⟨c, hcC, ?_⟩
  rwa [Walk.support_reverse, List.mem_reverse] at hcp

/-- An indexed family of pairwise vertex-disjoint paths from `S` to `T` in `G`. -/
structure bc16_DisjointPathFamily (G : SimpleGraph V) (S T : Set V) (ι : Type*) where

  a : ι → V

  b : ι → V

  p : ∀ i, G.Walk (a i) (b i)

  ha : ∀ i, a i ∈ S

  hb : ∀ i, b i ∈ T

  hp : ∀ i, (p i).IsPath

  hdisj : ∀ ⦃i j⦄, i ≠ j → ∀ ⦃x⦄, x ∈ (p i).support → x ∉ (p j).support

lemma bc16_separator_hits_path {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) (i : ι) :
    ∃ c ∈ C, c ∈ (F.p i).support :=
  hC (F.ha i) (F.hb i) (F.p i)

/-- A vertex of the separator `C` on the `i`-th path of the family. -/
noncomputable def bc16_hitVertex {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) (i : ι) : V :=
  (bc16_separator_hits_path F hC i).choose

lemma bc16_hitVertex_mem_separator {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) (i : ι) :
    bc16_hitVertex F hC i ∈ C :=
  (bc16_separator_hits_path F hC i).choose_spec.1

lemma bc16_hitVertex_mem_support {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) (i : ι) :
    bc16_hitVertex F hC i ∈ (F.p i).support :=
  (bc16_separator_hits_path F hC i).choose_spec.2

lemma bc16_hitVertex_injective {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) :
    Function.Injective (bc16_hitVertex F hC) := by
  intro i j hij
  by_contra hne
  have hi : bc16_hitVertex F hC i ∈ (F.p i).support := bc16_hitVertex_mem_support F hC i
  have hj : bc16_hitVertex F hC j ∈ (F.p j).support := bc16_hitVertex_mem_support F hC j
  rw [hij] at hi
  exact F.hdisj hne hi hj

lemma bc16_max_le_min {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C)
    (hCfin : C.Finite) :
    (Set.univ : Set ι).ncard ≤ C.ncard := by
  classical
  refine Set.ncard_le_ncard_of_injOn (bc16_hitVertex F hC) ?_ ?_ hCfin
  · intro i _
    exact bc16_hitVertex_mem_separator F hC i
  · intro i _ j _ hij
    exact bc16_hitVertex_injective F hC hij

lemma bc16_card_le_ncard_separator {S T C : Set V} {ι : Type*} [Finite V]
    [Fintype ι] (F : bc16_DisjointPathFamily G S T ι)
    (hC : bc16_IsSeparator G S T C) :
    Fintype.card ι ≤ C.ncard := by
  have hCfin : C.Finite := Set.toFinite C
  have h := bc16_max_le_min F hC hCfin
  rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h

lemma bc16_encard_le_encard_separator {S T C : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) (hC : bc16_IsSeparator G S T C) :
    (Set.univ : Set ι).encard ≤ C.encard := by
  classical
  have hmaps : Set.MapsTo (bc16_hitVertex F hC) (Set.univ : Set ι) C := by
    intro i _
    exact bc16_hitVertex_mem_separator F hC i
  have hinj : Set.InjOn (bc16_hitVertex F hC) (Set.univ : Set ι) := by
    intro i _ j _ hij
    exact bc16_hitVertex_injective F hC hij
  exact Set.encard_le_encard_of_injOn hmaps hinj

lemma bc16_source_isSeparator (G : SimpleGraph V) (S T : Set V) :
    bc16_IsSeparator G S T S := by
  intro s hs t _ p
  exact ⟨s, hs, p.start_mem_support⟩

lemma bc16_target_isSeparator (G : SimpleGraph V) (S T : Set V) :
    bc16_IsSeparator G S T T := by
  intro s _ t ht p
  exact ⟨t, ht, p.end_mem_support⟩

lemma bc16_no_walk_of_empty_separator {S T : Set V}
    (h : bc16_IsSeparator G S T (∅ : Set V)) {s t : V} (hs : s ∈ S) (ht : t ∈ T)
    (p : G.Walk s t) : False := by
  obtain ⟨c, hc, _⟩ := h hs ht p
  exact (Set.notMem_empty c) hc

lemma bc16_empty_separator_of_no_walk {S T : Set V}
    (h : ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → IsEmpty (G.Walk s t)) :
    bc16_IsSeparator G S T (∅ : Set V) := by
  intro s hs t ht p
  exact (h hs ht).false p |>.elim

lemma bc16_empty_separator_iff_not_reachable {S T : Set V} :
    bc16_IsSeparator G S T (∅ : Set V) ↔
      ∀ ⦃s⦄, s ∈ S → ∀ ⦃t⦄, t ∈ T → ¬ G.Reachable s t := by
  constructor
  · intro h s hs t ht hr
    obtain ⟨p⟩ := hr
    exact bc16_no_walk_of_empty_separator h hs ht p
  · intro h s hs t ht p
    exact absurd p.reachable (h hs ht)

lemma bc16_exists_path_of_not_empty_separator {S T : Set V}
    (h : ¬ bc16_IsSeparator G S T (∅ : Set V)) :
    ∃ (s : V) (_ : s ∈ S) (t : V) (_ : t ∈ T) (p : G.Walk s t), p.IsPath := by
  rw [bc16_IsSeparator] at h
  push Not at h
  obtain ⟨s, hs, t, ht, p, _⟩ := h
  obtain ⟨q, hq⟩ := p.reachable.exists_isPath
  exact ⟨s, hs, t, ht, q, hq⟩

/-- The family consisting of one path. -/
def bc16_singletonFamily {S T : Set V} {s t : V} (hs : s ∈ S) (ht : t ∈ T)
    {p : G.Walk s t} (hp : p.IsPath) : bc16_DisjointPathFamily G S T (PUnit.{1}) where
  a := fun _ => s
  b := fun _ => t
  p := fun _ => p
  ha := fun _ => hs
  hb := fun _ => ht
  hp := fun _ => hp
  hdisj := by
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij

lemma bc16_one_le_ncard_separator_of_path {S T C : Set V} {s t : V}
    (hs : s ∈ S) (ht : t ∈ T) {p : G.Walk s t} (hp : p.IsPath)
    (hC : bc16_IsSeparator G S T C) (hCfin : C.Finite) :
    1 ≤ C.ncard := by
  have h := bc16_max_le_min (bc16_singletonFamily hs ht hp) hC hCfin
  rwa [Set.ncard_univ, Nat.card_unique] at h

lemma bc16_encard_le_source_target {S T : Set V} {ι : Type*}
    (F : bc16_DisjointPathFamily G S T ι) :
    (Set.univ : Set ι).encard ≤ S.encard ∧ (Set.univ : Set ι).encard ≤ T.encard :=
  ⟨bc16_encard_le_encard_separator F (bc16_source_isSeparator G S T),
   bc16_encard_le_encard_separator F (bc16_target_isSeparator G S T)⟩

end StatMech.Walls
