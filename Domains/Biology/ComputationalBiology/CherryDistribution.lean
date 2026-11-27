/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.UnrootedBinaryTreeCount
public import Mathlib.Basic.Real.Basic
import all MathlibExt.Combinatorics.Enumerative.UnrootedBinaryTreeCount
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Batteries.Tactic.OpenPrivate

/-! # Mean cherry count of uniform unrooted binary trees -/

@[expose] public section

open private cluster_mem cluster_injective two_children cluster_nonempty cluster_child_ne
  exists_child_toward no_child_of_leaf degree_label label_ne_root adj_unique_of_degree_one
  cluster_label cluster_mono cluster_root
  from MathlibExt.Combinatorics.Enumerative.UnrootedBinaryTreeCount

namespace WantedExt.Biology.ComputationalBiology.CherryDistributionWanted

open MathlibExt.Biology.Phylogenetics.UnrootedTreeCount
open scoped Nat

/-- The number of **cherries** of `T`: the two-element sets of taxa whose leaves are both
adjacent to a common vertex. -/
noncomputable def cherryCount {X : Type} (T : UnrootedBinaryTree X) : ℕ :=
  Nat.card {s : Finset X // s.card = 2 ∧ ∃ v : T.V, ∀ x ∈ s, T.G.Adj (T.label x : T.V) v}

/-- The unrooted binary phylogenetic trees on the taxa `Fin n`, up to label-preserving
isomorphism. There are `(2 n - 5)‼` of them for `n ≥ 3` (`nat_card_unrootedBinaryTree`). -/
abbrev TreeClass (n : ℕ) : Type 1 :=
  Quot (UnrootedBinaryTree.Iso (X := Fin n))

/-- The isomorphism classes containing a tree whose cherry count satisfies `P`. -/
def classesWith (n : ℕ) (P : ℕ → Prop) : Set (TreeClass n) :=
  {q | ∃ T : UnrootedBinaryTree (Fin n), Quot.mk _ T = q ∧ P (cherryCount T)}

/-- The probability, under the uniform model on `n` taxa, that the cherry count satisfies `P`:
the proportion of isomorphism classes with that property. -/
noncomputable def uniformProb (n : ℕ) (P : ℕ → Prop) : ℝ :=
  (Nat.card (classesWith n P) : ℝ) / Nat.card (TreeClass n)

/-- The mean of the cherry count under the uniform model on `n` taxa. A tree on `n` taxa has at
most `n.choose 2` cherries, so the sum runs over every possible value. -/
noncomputable def cherryMean (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n.choose 2 + 1), (k : ℝ) * uniformProb n (· = k)

private theorem cherryCount_eq_of_iso {X : Type} {T T' : UnrootedBinaryTree X}
    (h : T.Iso T') : cherryCount T = cherryCount T' := by
  obtain ⟨e, he⟩ := h
  unfold cherryCount
  apply Nat.card_congr
  refine Equiv.subtypeEquivRight fun s => ?_
  constructor
  · rintro ⟨hs, v, hv⟩
    refine ⟨hs, e v, fun x hx => ?_⟩
    rw [← he x]
    exact e.map_adj_iff.mpr (hv x hx)
  · rintro ⟨hs, v, hv⟩
    refine ⟨hs, e.symm v, fun x hx => ?_⟩
    apply e.map_adj_iff.mp
    simpa only [he, e.apply_symm_apply] using hv x hx

private theorem cherryCount_le {X : Type} [Fintype X] (T : UnrootedBinaryTree X) :
    cherryCount T ≤ (Fintype.card X).choose 2 := by
  classical
  let f : {s : Finset X // s.card = 2 ∧ ∃ v : T.V,
      ∀ x ∈ s, T.G.Adj (T.label x : T.V) v} →
      {s : Finset X // s ∈ (Finset.univ : Finset X).powersetCard 2} :=
    fun s => ⟨s.1, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, s.2.1⟩⟩
  have hf : Function.Injective f := by
    intro s t h
    apply Subtype.ext
    exact congrArg (fun z : {s : Finset X //
      s ∈ (Finset.univ : Finset X).powersetCard 2} => z.1) h
  have hc := Nat.card_le_card_of_injective f hf
  simpa only [cherryCount, Nat.card_eq_fintype_card, Fintype.card_coe,
    Finset.card_powersetCard, Finset.card_univ] using hc

private noncomputable def classCherryCount (n : ℕ) : TreeClass n → ℕ :=
  Quot.lift cherryCount fun _ _ h => cherryCount_eq_of_iso h

private theorem classCherryCount_le (n : ℕ) (q : TreeClass n) :
    classCherryCount n q ≤ n.choose 2 := by
  induction q using Quot.ind with
  | mk T => simpa only [classCherryCount, Fintype.card_fin] using cherryCount_le T

private theorem classesWith_eq (n : ℕ) (P : ℕ → Prop) :
    classesWith n P = {q | P (classCherryCount n q)} := by
  ext q
  constructor
  · rintro ⟨T, rfl, hT⟩
    exact hT
  · induction q using Quot.ind with
    | mk T => exact fun hT => ⟨T, rfl, hT⟩

private theorem finite_treeClass (n : ℕ) (hn : 0 < n) : Finite (TreeClass n) := by
  classical
  exact Finite.of_injective (quotEquivHierarchy (⟨0, hn⟩ : Fin n))
    (quotEquivHierarchy (⟨0, hn⟩ : Fin n)).injective

private theorem cherryMean_eq_sum (n : ℕ) [Fintype (TreeClass n)] :
    cherryMean n = (∑ q : TreeClass n, (classCherryCount n q : ℝ)) /
      Nat.card (TreeClass n) := by
  classical
  have hf (k : ℕ) : (k : ℝ) * (Nat.card (classesWith n (· = k)) : ℝ) =
      ∑ q ∈ (Finset.univ : Finset (TreeClass n)) with classCherryCount n q = k,
        (classCherryCount n q : ℝ) := by
    rw [classesWith_eq, Nat.card_eq_fintype_card, Fintype.card_subtype]
    calc
      (k : ℝ) *
          ↑((Finset.univ : Finset (TreeClass n)).filter (fun q => classCherryCount n q = k)).card =
          ∑ q ∈ (Finset.univ : Finset (TreeClass n)) with classCherryCount n q = k,
            (k : ℝ) := by simp [mul_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [(Finset.mem_filter.mp hq).2]
  unfold cherryMean uniformProb
  simp_rw [← mul_div_assoc, hf]
  rw [← Finset.sum_div]
  congr 1
  apply Finset.sum_fiberwise_of_maps_to
  intro q _
  exact Finset.mem_range.mpr (Nat.lt_succ_of_le (classCherryCount_le n q))

private theorem cluster_contains_pair {X : Type} [DecidableEq X]
    {S C : Finset X} {H : Finset (Finset X)} {b c : X}
    (hH : IsBinaryHierarchy S H) (hp : {b, c} ∈ H)
    (hC : C ∈ H) (hb : b ∈ C) : C = {b} ∨ c ∈ C := by
  rcases hH.2.2.2.1 C hC {b, c} hp with h | h | h
  · by_cases hc : c ∈ C
    · exact Or.inr hc
    · left
      apply Finset.Subset.antisymm _ (Finset.singleton_subset_iff.mpr hb)
      intro x hx
      rcases Finset.mem_insert.mp (h hx) with hxb | hxc
      · exact Finset.mem_singleton.mpr hxb
      · exact False.elim (hc (Finset.mem_singleton.mp hxc ▸ hx))
  · exact Or.inr (h (by simp))
  · exact False.elim (Finset.disjoint_left.mp h hb (by simp))

private def contractHierarchy {X : Type} [DecidableEq X] (b : X)
    (H : Finset (Finset X)) : Finset (Finset X) :=
  (H.image (fun C => C.erase b)).erase ∅

private theorem contractHierarchy_valid {X : Type} [DecidableEq X]
    {S : Finset X} {H : Finset (Finset X)} {b c : X}
    (hH : IsBinaryHierarchy S H) (hbc : b ≠ c) (hp : {b, c} ∈ H) :
    IsBinaryHierarchy (S.erase b) (contractHierarchy b H) := by
  have hb : b ∈ S := (hH.2.1 {b, c} hp).2 (by simp)
  have hc : c ∈ S := (hH.2.1 {b, c} hp).2 (by simp)
  have hmem (D : Finset X) : D ∈ contractHierarchy b H ↔
      D ≠ ∅ ∧ ∃ C ∈ H, C.erase b = D := by
    simp [contractHierarchy]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply (hmem _).mpr
    exact ⟨Finset.nonempty_iff_ne_empty.mp ⟨c, by simp [hc, hbc.symm]⟩,
      S, hH.1, rfl⟩
  · intro D hD
    obtain ⟨hDne, C, hC, rfl⟩ := (hmem D).mp hD
    refine ⟨Finset.nonempty_iff_ne_empty.mpr hDne, ?_⟩
    intro x hx
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
      (hH.2.1 C hC).2 (Finset.mem_of_mem_erase hx)⟩
  · intro x hx
    apply (hmem _).mpr
    refine ⟨Finset.singleton_ne_empty _, {x}, hH.2.2.1 x (Finset.mem_of_mem_erase hx), ?_⟩
    simp [(Finset.ne_of_mem_erase hx).symm]
  · intro D hD E hE
    obtain ⟨_, C, hC, rfl⟩ := (hmem D).mp hD
    obtain ⟨_, F, hF, rfl⟩ := (hmem E).mp hE
    rcases hH.2.2.2.1 C hC F hF with h | h | h
    · exact Or.inl (Finset.erase_subset_erase b h)
    · exact Or.inr (Or.inl (Finset.erase_subset_erase b h))
    · exact Or.inr (Or.inr (h.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _)))
  · intro D hD hcard
    obtain ⟨_, C, hC, rfl⟩ := (hmem D).mp hD
    have hCcard : 1 < C.card := lt_of_lt_of_le hcard (Finset.card_le_card (Finset.erase_subset _ _))
    obtain ⟨D₁, h₁, D₂, h₂, hd, hu⟩ := hH.2.2.2.2 C hC hCcard
    have key (E F : Finset X) (hE : E ∈ H) (hF : F ∈ H)
        (hef : Disjoint E F) (hefu : E ∪ F = C) : E.erase b ≠ ∅ := by
      intro he
      have hs₁ : E = {b} := by
        apply Finset.Subset.antisymm
        · intro x hx
          by_contra hxb
          have hxb : x ≠ b := by simpa using hxb
          have : x ∈ E.erase b := Finset.mem_erase.mpr ⟨hxb, hx⟩
          simp [he] at this
        · obtain ⟨x, hx⟩ := (hH.2.1 E hE).1
          have hx' : x = b := by
            by_contra hxb
            have : x ∈ E.erase b := Finset.mem_erase.mpr ⟨hxb, hx⟩
            simp [he] at this
          simpa [hx'] using hx
      subst hs₁
      have hbC : b ∈ C := hefu ▸ Finset.mem_union_left F (Finset.mem_singleton_self b)
      have hcC : c ∈ C := (cluster_contains_pair hH hp hC hbC).resolve_left (by
        intro he; simp [he] at hCcard)
      have hcF : c ∈ F := by
        rw [← hefu, Finset.mem_union] at hcC
        exact hcC.resolve_left (by simp [hbc.symm])
      have hcb : b ∉ F := Finset.disjoint_left.mp hef (by simp)
      have hFc : F = {c} := by
        rcases hH.2.2.2.1 F hF {b, c} hp with h | h | h
        · apply Finset.Subset.antisymm
          · intro x hx
            rcases Finset.mem_insert.mp (h hx) with he | he
            · exact False.elim (hcb (he ▸ hx))
            · exact he
          · exact Finset.singleton_subset_iff.mpr hcF
        · exact False.elim (hcb (h (by simp)))
        · exact False.elim (Finset.disjoint_left.mp h hcF (by simp))
      rw [← hefu, hFc] at hcard
      simp [hbc] at hcard
    have hne₁ := key D₁ D₂ h₁ h₂ hd hu
    have hne₂ := key D₂ D₁ h₂ h₁ hd.symm ((Finset.union_comm _ _).trans hu)
    refine ⟨D₁.erase b, (hmem _).mpr ⟨hne₁, D₁, h₁, rfl⟩,
      D₂.erase b, (hmem _).mpr ⟨hne₂, D₂, h₂, rfl⟩,
      hd.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _), ?_⟩
    ext x
    simp only [Finset.mem_union, Finset.mem_erase]
    rw [← hu, Finset.mem_union]
    tauto

private def expandCluster {X : Type} [DecidableEq X] (b c : X) (C : Finset X) : Finset X :=
  if c ∈ C then insert b C else C

private theorem expandCluster_erase {X : Type} [DecidableEq X]
    (b c : X) (C : Finset X) (hb : b ∉ C) : (expandCluster b c C).erase b = C := by
  unfold expandCluster
  split_ifs <;> simp [hb]

private theorem expandCluster_mono {X : Type} [DecidableEq X]
    (b c : X) {C D : Finset X} (h : C ⊆ D) : expandCluster b c C ⊆ expandCluster b c D := by
  unfold expandCluster
  by_cases hc : c ∈ C
  · simp only [hc, h hc, ite_true]
    exact Finset.insert_subset_insert b h
  · simp only [hc, ite_false]
    split_ifs
    · exact h.trans (Finset.subset_insert _ _)
    · exact h

private theorem expandCluster_union {X : Type} [DecidableEq X]
    (b c : X) (C D : Finset X) :
    expandCluster b c (C ∪ D) = expandCluster b c C ∪ expandCluster b c D := by
  ext x
  by_cases hc : c ∈ C <;> by_cases hd : c ∈ D <;>
    simp [expandCluster, hc, hd]

private theorem expandCluster_disjoint {X : Type} [DecidableEq X]
    (b c : X) {C D : Finset X} (hbC : b ∉ C) (hbD : b ∉ D) (h : Disjoint C D) :
    Disjoint (expandCluster b c C) (expandCluster b c D) := by
  by_cases hc : c ∈ C <;> by_cases hd : c ∈ D
  · exact False.elim (Finset.disjoint_left.mp h hc hd)
  · simp only [expandCluster, hc, hd, ite_true, ite_false]
    exact Finset.disjoint_insert_left.mpr ⟨hbD, h⟩
  · simp only [expandCluster, hc, hd, ite_true, ite_false]
    exact Finset.disjoint_insert_right.mpr ⟨hbC, h⟩
  · simpa only [expandCluster, hc, hd, ite_false] using h

private def expandHierarchy {X : Type} [DecidableEq X] (b c : X)
    (H : Finset (Finset X)) : Finset (Finset X) :=
  insert {b} (insert {c} (H.image (expandCluster b c)))

private theorem expandHierarchy_valid {X : Type} [DecidableEq X]
    {S : Finset X} {H : Finset (Finset X)} {b c : X}
    (hH : IsBinaryHierarchy S H) (hb : b ∉ S) (hc : c ∈ S) :
    IsBinaryHierarchy (insert b S) (expandHierarchy b c H) := by
  have hbc : b ≠ c := fun h => hb (h ▸ hc)
  have hsub (C : Finset X) (hC : C ∈ H) : b ∉ C := fun h => hb ((hH.2.1 C hC).2 h)
  have hmem (D : Finset X) : D ∈ expandHierarchy b c H ↔
      D = {b} ∨ D = {c} ∨ ∃ C ∈ H, expandCluster b c C = D := by
    simp [expandHierarchy]
  have hexp (C : Finset X) (hC : C ∈ H) :
      expandCluster b c C ∈ expandHierarchy b c H := (hmem _).mpr (Or.inr (Or.inr ⟨C, hC, rfl⟩))
  have hcontain (C : Finset X) : C ⊆ expandCluster b c C := by
    unfold expandCluster
    split_ifs
    · exact Finset.subset_insert _ _
    · exact le_rfl
  have hsing (a : X) : {a} ∈ expandHierarchy b c H →
      ∀ D ∈ expandHierarchy b c H, {a} ⊆ D ∨ D ⊆ {a} ∨ Disjoint {a} D := by
    intro _ D _
    by_cases ha : a ∈ D
    · exact Or.inl (Finset.singleton_subset_iff.mpr ha)
    · exact Or.inr (Or.inr (Finset.disjoint_singleton_left.mpr ha))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [expandCluster, hc] using hexp S hH.1
  · intro D hD
    rcases (hmem D).mp hD with rfl | rfl | ⟨C, hC, rfl⟩
    · exact ⟨Finset.singleton_nonempty _, by simp⟩
    · exact ⟨Finset.singleton_nonempty _, by simp [hc]⟩
    · refine ⟨(hH.2.1 C hC).1.mono (hcontain C), ?_⟩
      exact (expandCluster_mono b c (hH.2.1 C hC).2).trans (by simp [expandCluster, hc])
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact (hmem _).mpr (Or.inl rfl)
    · by_cases hxc : x = c
      · subst hxc; exact (hmem _).mpr (Or.inr (Or.inl rfl))
      · simpa [expandCluster, Ne.symm hxc] using hexp {x} (hH.2.2.1 x hx)
  · intro D hD E hE
    rcases (hmem D).mp hD with rfl | rfl | ⟨C, hC, rfl⟩
    · exact hsing b hD E hE
    · exact hsing c hD E hE
    · rcases (hmem E).mp hE with rfl | rfl | ⟨F, hF, rfl⟩
      · rcases hsing b hE _ hD with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
      · rcases hsing c hE _ hD with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h.symm)
      · rcases hH.2.2.2.1 C hC F hF with h | h | h
        · exact Or.inl (expandCluster_mono b c h)
        · exact Or.inr (Or.inl (expandCluster_mono b c h))
        · exact Or.inr (Or.inr (expandCluster_disjoint b c (hsub C hC) (hsub F hF) h))
  · intro D hD hcard
    rcases (hmem D).mp hD with rfl | rfl | ⟨C, hC, rfl⟩
    · simp at hcard
    · simp at hcard
    · by_cases he : C = {c}
      · subst he
        refine ⟨{b}, (hmem _).mpr (Or.inl rfl), {c}, (hmem _).mpr (Or.inr (Or.inl rfl)),
          by simp [hbc], ?_⟩
        simp [expandCluster]
      · have hcC : 1 < C.card := by
          by_contra h
          have hne := (hH.2.1 C hC).1.card_pos
          have h1 : C.card = 1 := by omega
          obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h1
          have hxc : c ≠ x := fun h => he (by simp [h])
          simp [expandCluster, hxc] at hcard
        obtain ⟨D₁, h₁, D₂, h₂, hd, hu⟩ := hH.2.2.2.2 C hC hcC
        refine ⟨expandCluster b c D₁, hexp D₁ h₁, expandCluster b c D₂, hexp D₂ h₂,
          expandCluster_disjoint b c (hsub D₁ h₁) (hsub D₂ h₂) hd, ?_⟩
        rw [← expandCluster_union, hu]

private theorem contract_expand {X : Type} [DecidableEq X]
    {S : Finset X} {H : Finset (Finset X)} {b c : X}
    (hH : IsBinaryHierarchy S H) (hb : b ∉ S) (hc : c ∈ S) :
    contractHierarchy b (expandHierarchy b c H) = H := by
  have hbc : b ≠ c := fun h => hb (h ▸ hc)
  ext D
  simp only [contractHierarchy, Finset.mem_erase, Finset.mem_image]
  constructor
  · rintro ⟨hD, E, hE, rfl⟩
    simp only [expandHierarchy, Finset.mem_insert, Finset.mem_image] at hE
    rcases hE with rfl | rfl | ⟨C, hC, rfl⟩
    · simp at hD
    · simpa [hbc] using hH.2.2.1 c hc
    · have hbC : b ∉ C := fun h => hb ((hH.2.1 C hC).2 h)
      simpa only [expandCluster_erase b c C hbC] using hC
  · intro hD
    have hbD : b ∉ D := fun h => hb ((hH.2.1 D hD).2 h)
    refine ⟨Finset.nonempty_iff_ne_empty.mp (hH.2.1 D hD).1,
      expandCluster b c D, ?_, expandCluster_erase b c D hbD⟩
    simp only [expandHierarchy, Finset.mem_insert, Finset.mem_image]
    exact Or.inr (Or.inr ⟨D, hD, rfl⟩)

private theorem expand_contract {X : Type} [DecidableEq X]
    {S : Finset X} {H : Finset (Finset X)} {b c : X}
    (hH : IsBinaryHierarchy S H) (hbc : b ≠ c) (hp : {b, c} ∈ H) :
    expandHierarchy b c (contractHierarchy b H) = H := by
  have hb : b ∈ S := (hH.2.1 {b, c} hp).2 (by simp)
  have hc : c ∈ S := (hH.2.1 {b, c} hp).2 (by simp)
  have hp' : {c, b} ∈ H := by simpa [Finset.pair_comm] using hp
  have hrestore (C : Finset X) (hC : C ∈ H) (hCb : C ≠ {b}) (hCc : C ≠ {c}) :
      expandCluster b c (C.erase b) = C := by
    by_cases hcC : c ∈ C
    · have hbC : b ∈ C := (cluster_contains_pair hH hp' hC hcC).resolve_left hCc
      simp [expandCluster, hbc.symm, hcC, Finset.insert_erase hbC]
    · have hbC : b ∉ C := fun h => hCb ((cluster_contains_pair hH hp hC h).resolve_right hcC)
      simp [expandCluster, hcC, hbC]
  ext D
  simp only [expandHierarchy, Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (rfl | rfl | ⟨E, hE, rfl⟩)
    · exact hH.2.2.1 b hb
    · exact hH.2.2.1 c hc
    · simp only [contractHierarchy, Finset.mem_erase, Finset.mem_image] at hE
      obtain ⟨hEne, C, hC, rfl⟩ := hE
      have hCb : C ≠ {b} := by rintro rfl; simp at hEne
      by_cases hCc : C = {c}
      · subst hCc; simpa [expandCluster, hbc.symm] using hp
      · simpa only [hrestore C hC hCb hCc] using hC
  · intro hD
    by_cases hDb : D = {b}
    · exact Or.inl hDb
    by_cases hDc : D = {c}
    · exact Or.inr (Or.inl hDc)
    refine Or.inr (Or.inr ⟨D.erase b, ?_, hrestore D hD hDb hDc⟩)
    simp only [contractHierarchy, Finset.mem_erase, Finset.mem_image]
    refine ⟨?_, D, hD, rfl⟩
    intro he
    have : D ⊆ {b} := by
      intro x hx
      by_cases hxb : x = b
      · simp [hxb]
      · have hx' : x ∈ D.erase b := Finset.mem_erase.mpr ⟨hxb, hx⟩
        simp [he] at hx'
    exact hDb ((Finset.Nonempty.subset_singleton_iff (hH.2.1 D hD).1).mp this)

private noncomputable def hierarchyCherryEquiv {X : Type} [DecidableEq X]
    (S : Finset X) (b c : X) (hb : b ∈ S) (hc : c ∈ S) (hbc : b ≠ c) :
    {H : Finset (Finset X) // IsBinaryHierarchy S H ∧ {b, c} ∈ H} ≃
      {H : Finset (Finset X) // IsBinaryHierarchy (S.erase b) H} where
  toFun H := ⟨contractHierarchy b H.1, contractHierarchy_valid H.2.1 hbc H.2.2⟩
  invFun H := ⟨expandHierarchy b c H.1, by
    refine ⟨?_, ?_⟩
    · have he : insert b (S.erase b) = S := Finset.insert_erase hb
      have hv := expandHierarchy_valid H.2 (Finset.notMem_erase b S)
        (Finset.mem_erase.mpr ⟨hbc.symm, hc⟩)
      simpa only [he] using hv
    · simp only [expandHierarchy, Finset.mem_insert, Finset.mem_image]
      refine Or.inr (Or.inr ⟨{c}, H.2.2.2.1 c (Finset.mem_erase.mpr ⟨hbc.symm, hc⟩), ?_⟩)
      simp [expandCluster]⟩
  left_inv H := Subtype.ext (expand_contract H.2.1 hbc H.2.2)
  right_inv H := Subtype.ext (contract_expand H.2 (Finset.notMem_erase _ _)
    (Finset.mem_erase.mpr ⟨hbc.symm, hc⟩))

private theorem nat_card_hierarchyCherry {X : Type} [DecidableEq X]
    (S : Finset X) (b c : X) (hb : b ∈ S) (hc : c ∈ S) (hbc : b ≠ c) :
    Nat.card {H : Finset (Finset X) // IsBinaryHierarchy S H ∧ {b, c} ∈ H} =
      (2 * (S.card - 1) - 3)‼ := by
  rw [Nat.card_congr (hierarchyCherryEquiv S b c hb hc hbc),
    nat_card_binaryHierarchy (S.erase b) ⟨c, Finset.mem_erase.mpr ⟨hbc.symm, hc⟩⟩,
    Finset.card_erase_of_mem hb]

private theorem cherry_iff_cluster {X : Type} [Fintype X] [DecidableEq X]
    (T : UnrootedBinaryTree X) (a b c : X) (hab : b ≠ a) (hac : c ≠ a) (hbc : b ≠ c)
    (hn : 4 ≤ Fintype.card X) :
    (∃ v, T.G.Adj (T.label b : T.V) v ∧ T.G.Adj (T.label c : T.V) v) ↔
      {b, c} ∈ clusterSet T a := by
  have hbn : (T.label b : T.V) ≠ T.label a := label_ne_root T hab
  have hcn : (T.label c : T.V) ≠ T.label a := label_ne_root T hac
  have hbcn : (T.label b : T.V) ≠ T.label c :=
    fun h => hbc (T.label.injective (Subtype.ext h))
  have hlabel (x : X) (hx : x ≠ a) (v : T.V) (hv : T.G.Adj (T.label x : T.V) v) :
      T.G.dist (T.label a) (T.label x) = T.G.dist (T.label a) v + 1 := by
    rcases T.isTree.dist_eq_dist_add_one_of_adj (T.label a) hv with h | h
    · exact h
    · exact False.elim (no_child_of_leaf T.isTree (degree_label T x) (label_ne_root T hx) hv h)
  constructor
  · rintro ⟨v, hbv, hcv⟩
    have hvs : v ≠ T.label a := by
      rintro rfl
      exact hbcn (adj_unique_of_degree_one (degree_label T a) hbv.symm hcv.symm)
    have hv3 : T.G.degree v = 3 := T.degree_eq_three v (fun h =>
      hbcn (adj_unique_of_degree_one h hbv.symm hcv.symm))
    have hbd := hlabel b hab v hbv
    have hcd := hlabel c hac v hcv
    obtain ⟨l, r, hlr, hl, hr, hdl, hdr, hall⟩ := two_children T.isTree hv3 hvs
    have hchildren (w : T.V) (hw : T.G.Adj v w)
        (hdw : T.G.dist (T.label a) w = T.G.dist (T.label a) v + 1) :
        w = T.label b ∨ w = T.label c := by
      have hb := hall (T.label b) hbv.symm hbd
      have hc := hall (T.label c) hcv.symm hcd
      have hw := hall w hw hdw
      rcases hb with hb | hb <;> rcases hc with hc | hc <;> rcases hw with hw | hw <;>
        simp_all
    have hvcl : cluster T a v = {b, c} := by
      ext x
      constructor
      · intro hx
        obtain ⟨hxa, hxb⟩ := (cluster_mem T a v x).mp hx
        have hvx : v ≠ T.label x := by
          intro h; have h1 := degree_label T x; rw [← h, hv3] at h1; omega
        obtain ⟨w, hw, hdw, hwb⟩ := exists_child_toward T.isTree.connected hxb hvx
        rcases hchildren w hw hdw with rfl | rfl
        · have hx' : x ∈ cluster T a (T.label b) := (cluster_mem T a _ x).mpr ⟨hxa, hwb⟩
          rw [cluster_label T hab] at hx'
          exact Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hx'))
        · have hx' : x ∈ cluster T a (T.label c) := (cluster_mem T a _ x).mpr ⟨hxa, hwb⟩
          rw [cluster_label T hac] at hx'
          exact Finset.mem_insert.mpr (Or.inr hx')
      · intro hx
        rcases Finset.mem_insert.mp hx with hxb | hx
        · subst x
          apply (cluster_mem T a v b).mpr
          refine ⟨hab, ?_⟩
          change T.G.dist (T.label a) v + T.G.dist v (T.label b) =
            T.G.dist (T.label a) (T.label b)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hbv.symm]
          omega
        · have he := Finset.mem_singleton.mp hx; subst x
          apply (cluster_mem T a v c).mpr
          refine ⟨hac, ?_⟩
          change T.G.dist (T.label a) v + T.G.dist v (T.label c) =
            T.G.dist (T.label a) (T.label c)
          rw [SimpleGraph.dist_eq_one_iff_adj.mpr hcv.symm]
          omega
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ _, hvcl⟩
  · intro hp
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hp
    have hvs : v ≠ T.label a := by
      intro he
      rw [he, cluster_root T a] at hv
      have : Fintype.card X - 1 = 2 := by
        have := congrArg Finset.card hv
        simpa [Finset.card_erase_of_mem (Finset.mem_univ a), hbc] using this
      omega
    have hv3 : T.G.degree v = 3 := T.degree_eq_three v (fun h => by
      obtain ⟨x, hx⟩ := T.label.surjective ⟨v, h⟩
      have hxv : (T.label x : T.V) = v := congrArg Subtype.val hx
      have hxa : x ≠ a := fun he => hvs (by rw [← hxv, he])
      rw [← hxv, cluster_label T hxa] at hv
      have := congrArg Finset.card hv
      simp [hbc] at this)
    obtain ⟨l, r, hlr, hl, hr, hdl, hdr, hall⟩ := two_children T.isTree hv3 hvs
    have hls : l ≠ T.label a := by intro he; rw [he, SimpleGraph.dist_self] at hdl; omega
    have hrs : r ≠ T.label a := by intro he; rw [he, SimpleGraph.dist_self] at hdr; omega
    have hlsub : cluster T a l ⊆ {b, c} := by
      rw [← hv]
      apply cluster_mono T a
      change T.G.dist (T.label a) v + T.G.dist v l = T.G.dist (T.label a) l
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hl]
      omega
    have hrsub : cluster T a r ⊆ {b, c} := by
      rw [← hv]
      apply cluster_mono T a
      change T.G.dist (T.label a) v + T.G.dist v r = T.G.dist (T.label a) r
      rw [SimpleGraph.dist_eq_one_iff_adj.mpr hr]
      omega
    have hlne : cluster T a l ≠ {b, c} := by rw [← hv]; exact cluster_child_ne T a hvs hl hdl
    have hrne : cluster T a r ≠ {b, c} := by rw [← hv]; exact cluster_child_ne T a hvs hr hdr
    have hsingle (w : T.V) (hws : w ≠ T.label a) (hs : cluster T a w ⊆ {b, c})
        (hne : cluster T a w ≠ {b, c}) : w = T.label b ∨ w = T.label c := by
      have hcard : (cluster T a w).card = 1 := by
        have hpos := (cluster_nonempty T a hws).card_pos
        have hlt := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hs, hne⟩)
        simp only [Finset.card_pair hbc] at hlt
        omega
      obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hcard
      have hxmem : x ∈ ({b, c} : Finset X) := hs (hx ▸ Finset.mem_singleton_self x)
      rcases Finset.mem_insert.mp hxmem with he | he
      · subst he
        exact Or.inl (cluster_injective T a hws hbn (hx.trans (cluster_label T hab).symm))
      · have he := Finset.mem_singleton.mp he; subst he
        exact Or.inr (cluster_injective T a hws hcn (hx.trans (cluster_label T hac).symm))
    rcases hsingle l hls hlsub hlne with rfl | rfl <;>
      rcases hsingle r hrs hrsub hrne with rfl | rfl
    · exact False.elim (hlr rfl)
    · exact ⟨v, hl.symm, hr.symm⟩
    · exact ⟨v, hr.symm, hl.symm⟩
    · exact False.elim (hlr rfl)

private def cherryAt {X : Type} (T : UnrootedBinaryTree X) (s : Finset X) : Prop :=
  ∃ v : T.V, ∀ x ∈ s, T.G.Adj (T.label x : T.V) v

private theorem cherryAt_iso {X : Type} {T T' : UnrootedBinaryTree X}
    (h : T.Iso T') (s : Finset X) : cherryAt T s ↔ cherryAt T' s := by
  obtain ⟨e, he⟩ := h
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨e v, fun x hx => ?_⟩
    rw [← he]
    exact e.map_adj_iff.mpr (hv x hx)
  · rintro ⟨v, hv⟩
    refine ⟨e.symm v, fun x hx => ?_⟩
    apply e.map_adj_iff.mp
    simpa only [he, e.apply_symm_apply] using hv x hx

private noncomputable def pairInClass (n : ℕ) (s : Finset (Fin n)) : TreeClass n → Prop :=
  Quot.lift (fun T => cherryAt T s) fun _ _ h => propext (cherryAt_iso h s)

open Classical in
private theorem cherryCount_eq_sum (n : ℕ) (T : UnrootedBinaryTree (Fin n)) :
    cherryCount T = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
      if cherryAt T s then 1 else 0 := by
  classical
  let e : {s : Finset (Fin n) // s.card = 2 ∧ cherryAt T s} ≃
      {s : Finset (Fin n) // s ∈ ((Finset.univ : Finset (Fin n)).powersetCard 2).filter
        (cherryAt T)} := Equiv.subtypeEquivRight fun s => by simp [Finset.mem_powersetCard]
  change Nat.card {s : Finset (Fin n) // s.card = 2 ∧ cherryAt T s} = _
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
  exact (Finset.sum_boole (R := ℕ) (cherryAt T) _).symm

open Classical in
private theorem classCherryCount_eq_sum (n : ℕ) (q : TreeClass n) :
    classCherryCount n q = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
      if pairInClass n s q then 1 else 0 := by
  classical
  induction q using Quot.ind with
  | mk T => exact cherryCount_eq_sum n T

private theorem sum_cherryCount_eq (n : ℕ) [Fintype (TreeClass n)] :
    ∑ q : TreeClass n, classCherryCount n q =
      ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 2,
        Nat.card {q : TreeClass n // pairInClass n s q} := by
  classical
  simp_rw [classCherryCount_eq_sum]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp

private theorem nat_card_pairInClass (n : ℕ) (hn : 4 ≤ n) (s : Finset (Fin n))
    (hs : s.card = 2) :
    Nat.card {q : TreeClass n // pairInClass n s q} = (2 * n - 7)‼ := by
  classical
  obtain ⟨b, c, hbc, rfl⟩ := Finset.card_eq_two.mp hs
  obtain ⟨a, ha⟩ : ∃ a : Fin n, a ∉ ({b, c} : Finset (Fin n)) := by
    have hlt : ({b, c} : Finset (Fin n)).card < (Finset.univ : Finset (Fin n)).card := by
      simp [hbc]
      omega
    obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    exact ⟨a, ha⟩
  have hba : b ≠ a := fun h => ha (h ▸ Finset.mem_insert_self b {c})
  have hca : c ≠ a := fun h => ha (h ▸ Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton_self c)))
  let e := quotEquivHierarchy a
  have hpair (q : TreeClass n) : pairInClass n {b, c} q ↔ {b, c} ∈ (e q).1 := by
    induction q using Quot.ind with
    | mk T =>
      change cherryAt T {b, c} ↔ {b, c} ∈ clusterSet T a
      have hc : cherryAt T {b, c} ↔
          ∃ v, T.G.Adj (T.label b : T.V) v ∧ T.G.Adj (T.label c : T.V) v := by
        simp [cherryAt]
      exact hc.trans (cherry_iff_cluster T a b c hba hca hbc (by simpa using hn))
  let e' : {q : TreeClass n // pairInClass n {b, c} q} ≃
      {H : Finset (Finset (Fin n)) // IsBinaryHierarchy (Finset.univ.erase a) H ∧
        {b, c} ∈ H} :=
    (e.subtypeEquiv hpair).trans (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  rw [Nat.card_congr e', nat_card_hierarchyCherry _ b c
    (Finset.mem_erase.mpr ⟨hba, Finset.mem_univ _⟩)
    (Finset.mem_erase.mpr ⟨hca, Finset.mem_univ _⟩) hbc]
  congr 1
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Mean cherry count** (McKenzie and Steel 2000, Theorem 4(b), due to Steel and Penny 1993):
under the uniform model on `n ≥ 4` taxa, `E[C_n] = n (n - 1) / (2 (2 n - 5))`.

Source: McKenzie and Steel (2000), Theorem 4(b). -/
public theorem cherryMean_eq (n : ℕ) (hn : 4 ≤ n) :
    cherryMean n = (n : ℝ) * (n - 1) / (2 * (2 * n - 5))
    := by
  classical
  let : Finite (TreeClass n) := finite_treeClass n (by omega)
  let : Fintype (TreeClass n) := Fintype.ofFinite _
  have hsum : ∑ q : TreeClass n, classCherryCount n q =
      n.choose 2 * (2 * n - 7)‼ := by
    rw [sum_cherryCount_eq]
    calc
      _ = ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard 2, (2 * n - 7)‼ := by
        apply Finset.sum_congr rfl
        intro s hs
        exact nat_card_pairInClass n hn s (Finset.mem_powersetCard.mp hs).2
      _ = _ := by simp [Finset.card_powersetCard]
  have hd : (2 * n - 5)‼ = (2 * n - 5) * (2 * n - 7)‼ := by
    have he : 2 * n - 5 = (2 * n - 6) + 1 := by omega
    rw [he, Nat.doubleFactorial_add_one]
    congr 1
  have hd0 : ((2 * n - 7)‼ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.doubleFactorial_pos (2 * n - 7)))
  have hcast : ((2 * n - 5 : ℕ) : ℝ) = 2 * (n : ℝ) - 5 := by
    rw [Nat.cast_sub (by omega : 5 ≤ 2 * n)]
    norm_num
  rw [cherryMean_eq_sum, ← Nat.cast_sum, hsum, Nat.cast_mul,
    nat_card_unrootedBinaryTree n (by omega), hd, Nat.cast_mul,
    mul_div_mul_right _ _ hd0, hcast, Nat.cast_choose_two]
  rw [div_div]

end WantedExt.Biology.ComputationalBiology.CherryDistributionWanted
