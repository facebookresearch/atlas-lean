/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Preimage
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Set.PowersetCard

@[expose] public section

namespace Set.powersetCard

variable {α β : Type*} {n k : ℕ}

def insertSuccAbove (r : Fin (n + 1))
    (s : Set.powersetCard (Fin n) k) :
    Set.powersetCard (Fin (n + 1)) (k + 1) :=
  Set.powersetCard.ofCard (s := insert r (s.val.map r.succAboveEmb)) (by
    rw [Finset.card_insert_of_notMem]
    · rw [Finset.card_map, card_eq]
    · simp)

noncomputable def eraseSuccAbove
    (s : Set.powersetCard (Fin (n + 1)) (k + 1))
    (r : Fin (n + 1)) (hr : r ∈ s) :
    Set.powersetCard (Fin n) k :=
  Set.powersetCard.ofCard
    (s := (s.val.erase r).preimage r.succAbove Fin.succAbove_right_injective.injOn) (by
    rw [Finset.card_preimage]
    have hfil : (((s.val.erase r).filter
      (fun x => x ∈ Set.range r.succAbove)).card =
      (s.val.erase r).card) := by
      apply congrArg Finset.card
      ext x
      simp [Fin.range_succAbove]
      tauto
    rw [hfil, Finset.card_erase_of_mem hr, card_eq]
    omega)

@[simp] theorem mem_insertSuccAbove_iff (r : Fin (n + 1))
    (s : Set.powersetCard (Fin n) k) (x : Fin (n + 1)) :
    x ∈ insertSuccAbove r s ↔
      x = r ∨ ∃ y ∈ s, r.succAbove y = x := by
  change x ∈ insert r (s.val.map r.succAboveEmb) ↔ _
  rw [Finset.mem_insert, Finset.mem_map]
  constructor
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨y, hy, rfl⟩
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨y, hy, rfl⟩

@[simp] theorem mem_eraseSuccAbove_iff
    (s : Set.powersetCard (Fin (n + 1)) (k + 1))
    (r : Fin (n + 1)) (hr : r ∈ s) (x : Fin n) :
    x ∈ eraseSuccAbove s r hr ↔ r.succAbove x ∈ s := by
  change x ∈ (s.val.erase r).preimage r.succAbove Fin.succAbove_right_injective.injOn ↔ _
  rw [Finset.mem_preimage, Finset.mem_erase]
  constructor
  · rintro ⟨_, hmem⟩
    exact hmem
  · intro hmem
    exact ⟨Fin.succAbove_ne _ _, hmem⟩

@[simp] theorem eraseSuccAbove_insertSuccAbove (r : Fin (n + 1))
    (s : Set.powersetCard (Fin n) k) :
    eraseSuccAbove (insertSuccAbove r s) r (by simp) = s := by
  apply SetLike.ext
  intro x
  rw [mem_eraseSuccAbove_iff, mem_insertSuccAbove_iff]
  constructor
  · rintro (heq | ⟨y, hy, heq⟩)
    · exact absurd heq (Fin.succAbove_ne _ _)
    · have hyx : y = x := Fin.succAbove_right_injective heq
      rw [hyx] at hy
      exact hy
  · intro hx
    exact Or.inr ⟨x, hx, rfl⟩

@[simp] theorem insertSuccAbove_eraseSuccAbove
    (s : Set.powersetCard (Fin (n + 1)) (k + 1))
    (r : Fin (n + 1)) (hr : r ∈ s) :
    insertSuccAbove r (eraseSuccAbove s r hr) = s := by
  apply SetLike.ext
  intro x
  rw [mem_insertSuccAbove_iff]
  constructor
  · rintro (rfl | ⟨y, hy, rfl⟩)
    · exact hr
    · rw [mem_eraseSuccAbove_iff] at hy
      exact hy
  · intro hx
    by_cases hxr : x = r
    · exact Or.inl hxr
    · obtain ⟨y, hy_eq⟩ := Fin.exists_succAbove_eq hxr
      exact Or.inr ⟨y, by rw [mem_eraseSuccAbove_iff]; rw [hy_eq]; exact hx, hy_eq⟩

theorem map_injective (f : α ↪ β) : Function.Injective (map n f) := by
  intro a b h
  apply Subtype.ext
  exact Finset.map_injective f (congrArg Subtype.val h)

theorem insertSuccAbove_injective (r : Fin (n + 1)) :
    Function.Injective
      (insertSuccAbove r :
        Set.powersetCard (Fin n) k →
          Set.powersetCard (Fin (n + 1)) (k + 1)) := by
  intro a b h
  apply SetLike.ext
  intro x
  have hmem : r.succAbove x ∈ insertSuccAbove r a ↔
    r.succAbove x ∈ insertSuccAbove r b := by rw [h]
  rw [mem_insertSuccAbove_iff, mem_insertSuccAbove_iff] at hmem
  have hne : r.succAbove x ≠ r := Fin.succAbove_ne _ _
  simp only [hne, false_or] at hmem
  have ha : (∃ y ∈ a, r.succAbove y = r.succAbove x) ↔ x ∈ a := by
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyx : y = x := Fin.succAbove_right_injective heq
      rw [hyx] at hy
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hb : (∃ y ∈ b, r.succAbove y = r.succAbove x) ↔ x ∈ b := by
    constructor
    · rintro ⟨y, hy, heq⟩
      have hyx : y = x := Fin.succAbove_right_injective heq
      rw [hyx] at hy
      exact hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  exact ha.symm.trans (hmem.trans hb)

theorem map_comp {γ : Type*} (f : α ↪ β) (g : β ↪ γ)
    (s : Set.powersetCard α n) :
    map n (f.trans g) s = map n g (map n f s) := by
  apply Subtype.ext
  simp [Finset.map_map]

@[simp] theorem map_refl (s : Set.powersetCard α n) :
    map n (Function.Embedding.refl α) s = s := by
  apply Subtype.ext
  simp [map]

@[simp] theorem map_equiv_left_inv (e : α ≃ β)
    (s : Set.powersetCard α n) :
    map n e.symm.toEmbedding (map n e.toEmbedding s) = s := by
  rw [← map_comp]
  have h : e.toEmbedding.trans e.symm.toEmbedding =
    Function.Embedding.refl α := by
    apply Function.Embedding.ext
    intro x
    simp
  rw [h, map_refl]

@[simp] theorem map_equiv_right_inv (e : α ≃ β)
    (s : Set.powersetCard β n) :
    map n e.toEmbedding (map n e.symm.toEmbedding s) = s := by
  rw [← map_comp]
  have h : e.symm.toEmbedding.trans e.toEmbedding =
    Function.Embedding.refl β := by
    apply Function.Embedding.ext
    intro x
    simp
  rw [h, map_refl]

noncomputable def mapEquiv (n : ℕ) (e : α ≃ β) : Set.powersetCard α n ≃ Set.powersetCard β n where
  toFun := Set.powersetCard.map n e.toEmbedding
  invFun := Set.powersetCard.map n e.symm.toEmbedding
  left_inv := Set.powersetCard.map_equiv_left_inv e
  right_inv := Set.powersetCard.map_equiv_right_inv e

@[simp] theorem mapEquiv_apply (e : α ≃ β) (s : Set.powersetCard α n) :
    mapEquiv n e s = Set.powersetCard.map n e.toEmbedding s :=
  rfl

@[simp] theorem mapEquiv_symm_apply (e : α ≃ β) (s : Set.powersetCard β n) :
    (mapEquiv n e).symm s = Set.powersetCard.map n e.symm.toEmbedding s :=
  rfl

@[simp] theorem mapEquiv_refl :
    mapEquiv n (Equiv.refl α) = Equiv.refl (Set.powersetCard α n) := by
  apply Equiv.ext
  intro s
  exact Set.powersetCard.map_refl s

@[simp] theorem mapEquiv_trans {γ : Type*} (e : α ≃ β) (f : β ≃ γ) :
    (mapEquiv n e).trans (mapEquiv n f) = mapEquiv n (e.trans f) := by
  apply Equiv.ext
  intro s
  exact (Set.powersetCard.map_comp e.toEmbedding f.toEmbedding s).symm

@[simp] theorem mapEquiv_symm (e : α ≃ β) :
    (mapEquiv n e).symm = mapEquiv n e.symm := by
  apply Equiv.ext
  intro s
  rfl

theorem mem_map_iff (f : α ↪ β)
    (s : Set.powersetCard α n) (y : β) :
    y ∈ map n f s ↔ ∃ x ∈ s, f x = y := by
  change y ∈ s.val.map f ↔ _
  rw [Finset.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem map_orderEmbOfFin_comp [LinearOrder α] {l : ℕ}
    (T : Set.powersetCard α k) (S : Set.powersetCard (Fin k) l) :
    let eT := T.val.orderEmbOfFin (Set.powersetCard.card_eq T);
    let eS := S.val.orderEmbOfFin (Set.powersetCard.card_eq S);
    let U := Set.powersetCard.map l eT.toEmbedding S;
    U.val.orderEmbOfFin (Set.powersetCard.card_eq U) = eS.comp eT := by
  dsimp only
  symm
  apply Finset.orderEmbOfFin_unique'
  intro x
  change _ ∈ S.val.map (T.val.orderEmbOfFin (Set.powersetCard.card_eq T)).toEmbedding
  rw [Finset.mem_map]
  exact ⟨S.val.orderEmbOfFin (Set.powersetCard.card_eq S) x,
    Finset.orderEmbOfFin_mem _ _ _, rfl⟩

end Set.powersetCard
