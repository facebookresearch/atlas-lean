/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib

open Finset

namespace StatMech
namespace Combinatorics

open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}





def MfmIsABSeparator (G : SimpleGraph V) (A B S : Finset V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ∀ (p : G.Walk a b), ∃ v ∈ p.support, v ∈ S




structure MfmLinkage (G : SimpleGraph V) (A B : Finset V) (n : ℕ) where
  
  src : Fin n → V
  
  tgt : Fin n → V
  
  walk : ∀ i, G.Walk (src i) (tgt i)
  src_mem : ∀ i, src i ∈ A
  tgt_mem : ∀ i, tgt i ∈ B
  isPath : ∀ i, (walk i).IsPath
  disjoint : ∀ ⦃i j⦄, i ≠ j → ∀ v, v ∈ (walk i).support → v ∉ (walk j).support










def mfm_linkage_mono {H : SimpleGraph V} (h : H ≤ G) {A B : Finset V} {n : ℕ}
    (L : MfmLinkage H A B n) : MfmLinkage G A B n where
  src := L.src
  tgt := L.tgt
  walk i := (L.walk i).mapLe h
  src_mem := L.src_mem
  tgt_mem := L.tgt_mem
  isPath i := by
    rw [Walk.isPath_def, Walk.support_mapLe_eq_support]
    exact (L.isPath i).support_nodup
  disjoint i j hij v hv := by
    rw [Walk.support_mapLe_eq_support] at hv ⊢
    exact L.disjoint hij v hv



theorem mfm_separator_mono {H : SimpleGraph V} (h : H ≤ G) {A B S : Finset V}
    (hS : MfmIsABSeparator G A B S) : MfmIsABSeparator H A B S := by
  intro a b ha hb p
  obtain ⟨v, hv, hvS⟩ := hS ha hb (p.mapLe h)
  rw [Walk.support_mapLe_eq_support] at hv
  exact ⟨v, hv, hvS⟩







theorem mfm_card_le_separator {A B : Finset V} {n : ℕ}
    (L : MfmLinkage G A B n) {S : Finset V} (hS : MfmIsABSeparator G A B S) :
    n ≤ S.card := by
  classical
  have hchoose : ∀ i : Fin n, ∃ v, v ∈ (L.walk i).support ∧ v ∈ S := by
    intro i
    obtain ⟨v, hv, hvS⟩ := hS (L.src_mem i) (L.tgt_mem i) (L.walk i)
    exact ⟨v, hv, hvS⟩
  choose f hfp hfS using hchoose
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact L.disjoint hne (f i) (hfp i) (hij ▸ hfp j)
  have hsub : (Finset.univ.image f) ⊆ S := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact hfS i
  calc n = (Finset.univ : Finset (Fin n)).card := by simp
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ S.card := Finset.card_le_card hsub









theorem mfm_separator_nonempty_of_reachable {A B S : Finset V}
    (hS : MfmIsABSeparator G A B S) {a b : V} (ha : a ∈ A) (hb : b ∈ B)
    (h : G.Reachable a b) : S.Nonempty := by
  obtain ⟨p⟩ := h
  obtain ⟨v, _, hvS⟩ := hS ha hb p
  exact ⟨v, hvS⟩



theorem mfm_isABSeparator_empty_iff {A B : Finset V} :
    MfmIsABSeparator G A B ∅ ↔ ∀ a ∈ A, ∀ b ∈ B, ¬ G.Reachable a b := by
  constructor
  · intro hS a ha b hb hr
    obtain ⟨v, hvS⟩ := mfm_separator_nonempty_of_reachable hS ha hb hr
    simp at hvS
  · intro h a b ha hb p
    exact absurd ⟨p⟩ (h a ha b hb)








theorem mfm_exists_linkage_one {A B : Finset V}
    (h : ∀ S : Finset V, MfmIsABSeparator G A B S → 1 ≤ S.card) :
    Nonempty (MfmLinkage G A B 1) := by
  classical
  by_contra hcon
  have hempty : MfmIsABSeparator G A B ∅ := by
    rw [mfm_isABSeparator_empty_iff]
    intro a ha b hb hr
    obtain ⟨p⟩ := hr
    apply hcon
    refine ⟨⟨fun _ => a, fun _ => b, fun _ => p.bypass, fun _ => ha, fun _ => hb,
      fun _ => p.bypass_isPath, ?_⟩⟩
    intro i j hij
    exact absurd (Subsingleton.elim i j) hij
  have := h ∅ hempty
  simp at this

end Combinatorics
end StatMech
