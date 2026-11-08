/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner
-/
module

public import MathlibExt.SetTheory.InfinitaryCombinatorics.Diamond
public import Mathlib.SetTheory.Cardinal.Aleph
public import Mathlib.SetTheory.Cardinal.Cofinality.Club

@[expose] public section

open Cardinal Ordinal

namespace MathlibExtTest.SetTheory.InfinitaryCombinatorics.Diamond

open MetaMathlibExt

-- Logic 4: Diamond ($\Diamond$)

/-- Sanity check: the constant `∅` sequence fails the guessing clause. -/

theorem not_guessing_const_empty.{u} (κ : Cardinal.{u})
    (β : Set.Iio κ.ord) (hβ : (β : Ordinal.{u}) ≠ 0) :
    ¬ ∀ X : Set (Set.Iio κ.ord),
        IsStationary {α : Set.Iio κ.ord |
          (Subtype.val '' X) ∩ Set.Iio (α : Ordinal.{u}) = (∅ : Set Ordinal.{u})} := by
  intro h
  have hclub : IsClub (Set.Ici β) :=
    { dirSupClosed := fun d hd hd0 _ x hx => by
        obtain ⟨y, hy⟩ := hd0
        exact le_trans (hd hy) (hx.1 hy)
      isCofinal := fun a => ⟨max a β, Set.mem_Ici.2 (le_max_right _ _), le_max_left _ _⟩ }
  obtain ⟨α, hα, hβα⟩ := h Set.univ hclub
  have h0 : (0 : Ordinal.{u}) < (β : Ordinal.{u}) := pos_of_ne_zero hβ
  have hmem : (0 : Ordinal.{u}) ∈
      (Subtype.val '' (Set.univ : Set (Set.Iio κ.ord))) ∩ Set.Iio (α : Ordinal.{u}) :=
    ⟨⟨⟨0, h0.trans β.2⟩, Set.mem_univ _, rfl⟩, h0.trans_le hβα⟩
  rw [hα] at hmem
  exact hmem

-- Logic 5: Weak Diamond ($\Diamond^-$)

theorem card_bound_is_load_bearing.{u} (κ : Cardinal.{u}) [Nonempty (Set.Iio κ.ord)] :
    ∃ A : Set.Iio κ.ord → Set (Set Ordinal.{u}),
      (∀ α : Set.Iio κ.ord, ∀ s ∈ A α, s ⊆ Set.Iio (α : Ordinal.{u})) ∧
      (∀ X : Set (Set.Iio κ.ord),
        IsStationary {α : Set.Iio κ.ord |
          (Subtype.val '' X) ∩ Set.Iio (α : Ordinal.{u}) ∈ A α}) ∧
      ¬ ∀ α : Set.Iio κ.ord, #(A α) ≤ #(Set.Iio (α : Ordinal.{u})) := by
  refine ⟨fun α => 𝒫 (Set.Iio (α : Ordinal.{u})), ?_, ?_, ?_⟩
  · intro α s hs
    exact Set.subset_of_mem_powerset hs
  · intro X t ht
    obtain ⟨a, ha, -⟩ := ht.isCofinal (Classical.arbitrary _)
    exact ⟨a, Set.mem_powerset Set.inter_subset_right, ha⟩
  · intro hbad
    have hle := hbad (Classical.arbitrary _)
    rw [mk_powerset] at hle
    exact (Cardinal.cantor _).not_ge hle

end MathlibExtTest.SetTheory.InfinitaryCombinatorics.Diamond

end
