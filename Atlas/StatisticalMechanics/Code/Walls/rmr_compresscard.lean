/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































import Code.Inequalities.ReimerCompression

open Finset
open scoped NNReal FinsetFamily

namespace StatMech.Walls

open StatMech ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]









def IsDownAtCoord (i : E) (𝒜 : Finset (ConfigSpace E)) : Prop :=
  ∀ ω ∈ 𝒜, lowerCoord i ω ∈ 𝒜






theorem isDownAtCoord_iff_image_erase_closed (i : E) (𝒜 : Finset (ConfigSpace E)) :
    IsDownAtCoord i 𝒜 ↔ ∀ s ∈ 𝒜.image cfgSupport, s.erase i ∈ 𝒜.image cfgSupport := by
  constructor
  · intro h s hs
    rw [Finset.mem_image] at hs
    obtain ⟨ω, hω, rfl⟩ := hs
    rw [← cfgSupport_lowerCoord]
    exact Finset.mem_image_of_mem _ (h ω hω)
  · intro h ω hω
    have hmem : cfgSupport ω ∈ 𝒜.image cfgSupport := Finset.mem_image_of_mem _ hω
    have hcomp := h _ hmem
    rw [← cfgSupport_lowerCoord, Finset.mem_image] at hcomp
    obtain ⟨ω', hω', heq⟩ := hcomp
    have : ω' = lowerCoord i ω := by
      have := congrArg supportCfg heq
      rwa [supportCfg_cfgSupport, supportCfg_cfgSupport] at this
    rwa [this] at hω'








theorem rmr_downCompress_card (i : E) (𝒜 : Finset (ConfigSpace E)) :
    (downCompress i 𝒜).card = 𝒜.card :=
  downCompress_card i 𝒜



theorem rmr_downCompress_idem (i : E) (𝒜 : Finset (ConfigSpace E)) :
    downCompress i (downCompress i 𝒜) = downCompress i 𝒜 :=
  downCompress_idem i 𝒜



theorem rmr_downCompress_isDownAtCoord (i : E) (𝒜 : Finset (ConfigSpace E)) :
    IsDownAtCoord i (downCompress i 𝒜) :=
  fun _ hω => downCompress_isDownAt i 𝒜 hω









theorem rmr_compressCard (i : E) (𝒜 : Finset (ConfigSpace E)) :
    (downCompress i 𝒜).card = 𝒜.card ∧
    downCompress i (downCompress i 𝒜) = downCompress i 𝒜 ∧
    IsDownAtCoord i (downCompress i 𝒜) :=
  ⟨rmr_downCompress_card i 𝒜, rmr_downCompress_idem i 𝒜, rmr_downCompress_isDownAtCoord i 𝒜⟩















theorem rmr_downCompress_eq_self_of_isDownAtCoord (i : E) (𝒜 : Finset (ConfigSpace E))
    (h : IsDownAtCoord i 𝒜) : downCompress i 𝒜 = 𝒜 := by
  have hcomp : Down.compression i (𝒜.image cfgSupport) = 𝒜.image cfgSupport := by
    rw [isDownAtCoord_iff_image_erase_closed] at h
    apply Finset.Subset.antisymm
    · intro s hs
      rw [Down.mem_compression] at hs
      rcases hs with ⟨hmem, _⟩ | ⟨hnmem, hins⟩
      · exact hmem
      · have herase := h _ hins
        by_cases hi : i ∈ s
        · rw [Finset.insert_eq_of_mem hi] at hins; exact hins
        · rw [Finset.erase_insert hi] at herase; exact absurd herase hnmem
    · intro s hs
      rw [Down.mem_compression]; exact Or.inl ⟨hs, h s hs⟩
  unfold downCompress
  rw [hcomp, Finset.image_image]
  have : (supportCfg ∘ cfgSupport) = (id : ConfigSpace E → ConfigSpace E) := by
    funext ω; simp [supportCfg_cfgSupport]
  rw [this, Finset.image_id]

omit [Fintype E] in


theorem rmr_isDownAtCoord_empty (i : E) :
    IsDownAtCoord i (∅ : Finset (ConfigSpace E)) :=
  fun ω hω => absurd hω (Finset.notMem_empty ω)



theorem rmr_isDownAtCoord_univ (i : E) :
    IsDownAtCoord i (Finset.univ : Finset (ConfigSpace E)) :=
  fun ω _ => Finset.mem_univ (lowerCoord i ω)

end StatMech.Walls
