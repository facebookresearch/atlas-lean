/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Order.Partition.Finpartition
public import MathlibExt.Combinatorics.Finpartition.Card

/-!
# Pulling back a partition of a finite type along an embedding

For a map `f : α → β` of finite types and a partition `P` of `β` (a `Finpartition` of
`Finset.univ`), `P.comap f` is the partition of `α` whose blocks are the nonempty preimages
`f ⁻¹' B` of the blocks `B` of `P`: two points of `α` lie in the same block iff their images
lie in the same block of `P`. Restricting a partition of `Fin (n + 1)` to `Fin n` is
`comap Fin.castSucc`, and relabeling a partition by a permutation is `comap` along it.

## Main results

* `Finpartition.comap`: the pulled-back partition.
* `Finpartition.mem_comap_parts`: its blocks are the nonempty preimages of blocks.
* `Finpartition.comap_refl`, `Finpartition.comap_comap`: `comap` is functorial.
* `Finpartition.parts_comap_equiv`: along an equivalence `e`, the blocks are the images of the
  blocks under `e.symm`; so `comap` along an equivalence preserves the number of blocks
  (`Finpartition.card_parts_comap_equiv`) and every product over block sizes
  (`Finpartition.cardProd_comap_equiv`), and it is a bijection
  (`Finpartition.comap_symm_comap`).
-/

@[expose] public section

open Finset

namespace Finpartition

variable {α β γ : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype γ] [DecidableEq γ]

/-- The pull-back of a partition `P` of the finite type `β` along a map `f : α → β`:
the blocks are the nonempty preimages `f ⁻¹' B` of the blocks `B` of `P`. -/
def comap (f : α → β) (P : Finpartition (univ : Finset β)) : Finpartition (univ : Finset α) :=
  ofExistsUnique ((P.parts.image fun B ↦ univ.filter fun a ↦ f a ∈ B).erase ∅)
    (fun _ _ ↦ subset_univ _)
    (fun a _ ↦ by
      obtain ⟨B, ⟨hB, hfa⟩, hu⟩ := P.existsUnique_mem (mem_univ (f a))
      refine ⟨univ.filter fun x ↦ f x ∈ B, ⟨?_, by simp [hfa]⟩, ?_⟩
      · exact mem_erase.2 ⟨ne_empty_of_mem (a := a) (by simp [hfa]), mem_image_of_mem _ hB⟩
      · rintro C ⟨hC, haC⟩
        obtain ⟨B', hB', rfl⟩ := mem_image.1 (mem_erase.1 hC).2
        have : B' = B := hu B' ⟨hB', by simpa using haC⟩
        rw [this])
    (by simp)

/-- The blocks of `P.comap f` are the nonempty preimages of the blocks of `P`. -/
theorem mem_comap_parts {f : α → β} {P : Finpartition (univ : Finset β)} {C : Finset α} :
    C ∈ (P.comap f).parts ↔
      C.Nonempty ∧ ∃ B ∈ P.parts, (univ.filter fun a ↦ f a ∈ B) = C := by
  simp [comap, nonempty_iff_ne_empty]

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem comap_refl (P : Finpartition (univ : Finset α)) :
    P.comap id = P := by
  ext C
  simp only [mem_comap_parts, id_eq, filter_mem_eq_inter, univ_inter]
  constructor
  · rintro ⟨-, B, hB, rfl⟩
    exact hB
  · intro hC
    exact ⟨P.nonempty_of_mem_parts hC, C, hC, rfl⟩

/-- Pulling back along a composite is pulling back twice. -/
theorem comap_comap (f : α → β) (g : β → γ) (P : Finpartition (univ : Finset γ)) :
    (P.comap g).comap f = P.comap (g ∘ f) := by
  ext C
  simp only [mem_comap_parts, Function.comp_apply]
  constructor
  · rintro ⟨hC, D, ⟨-, B, hB, rfl⟩, rfl⟩
    exact ⟨hC, B, hB, by ext; simp⟩
  · rintro ⟨hC, B, hB, rfl⟩
    obtain ⟨a, ha⟩ := hC
    refine ⟨⟨a, ha⟩, univ.filter fun b ↦ g b ∈ B, ⟨⟨f a, by simpa using ha⟩, B, hB, rfl⟩, ?_⟩
    ext
    simp

/-- Along an equivalence `e`, the blocks of `P.comap e` are the images of the blocks of `P`
under `e.symm`. -/
theorem parts_comap_equiv (e : α ≃ β) (P : Finpartition (univ : Finset β)) :
    (P.comap e).parts = P.parts.map (mapEmbedding e.symm.toEmbedding).toEmbedding := by
  have hfilter : ∀ B : Finset β, (univ.filter fun a ↦ e a ∈ B) = B.map e.symm.toEmbedding := by
    intro B
    ext a
    simp
  ext C
  simp only [mem_comap_parts, hfilter, mem_map, RelEmbedding.coe_toEmbedding, mapEmbedding_apply]
  constructor
  · rintro ⟨-, B, hB, rfl⟩
    exact ⟨B, hB, rfl⟩
  · rintro ⟨B, hB, rfl⟩
    exact ⟨(P.nonempty_of_mem_parts hB).map, B, hB, rfl⟩

/-- Pulling back along an equivalence preserves the number of blocks. -/
theorem card_parts_comap_equiv (e : α ≃ β) (P : Finpartition (univ : Finset β)) :
    #(P.comap e).parts = #P.parts := by
  rw [parts_comap_equiv, card_map]

/-- Pulling back along an equivalence preserves every product over the block sizes. -/
theorem cardProd_comap_equiv {R : Type*} [CommMonoid R] (e : α ≃ β)
    (P : Finpartition (univ : Finset β)) (g : ℕ → R) :
    (P.comap e).cardProd g = P.cardProd g := by
  simp [cardProd, parts_comap_equiv]

/-- Pulling back along `e` and then along `e.symm` gives back the partition. -/
@[simp]
theorem comap_symm_comap (e : α ≃ β) (P : Finpartition (univ : Finset β)) :
    (P.comap e).comap e.symm = P := by
  rw [comap_comap, Equiv.self_comp_symm, comap_refl]

end Finpartition
