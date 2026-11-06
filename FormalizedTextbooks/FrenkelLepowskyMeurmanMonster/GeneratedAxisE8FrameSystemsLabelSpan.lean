/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsGreedy
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsCoverageData

/-! The compact xor-span checker enumerates the genuine binary linear span. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Prepending a vector adjoins exactly its binary singleton span. -/
theorem generatedAxisE8FrameListSpan_cons (v : Fin 8 → ZMod 2)
    (l : List (Fin 8 → ZMod 2)) :
    generatedAxisE8FrameListSpan (v :: l) =
      generatedAxisE8FrameListSpan l ⊔ Submodule.span (ZMod 2) {v} := by
  have he : {w | w ∈ v :: l} = {w | w ∈ l} ∪ {v} := by ext w; simp
  simp only [generatedAxisE8FrameListSpan, he, Submodule.span_union]

/-- A binary singleton extension consists of the old subspace and its translated coset. -/
theorem generatedAxisE8Frame_mem_extension (S : Submodule (ZMod 2) (Fin 8 → ZMod 2))
    (a v : Fin 8 → ZMod 2) :
    v ∈ S ⊔ Submodule.span (ZMod 2) {a} ↔
      v ∈ S ∨ ∃ w ∈ S, a + w = v := by
  constructor
  · intro h
    obtain ⟨w, hw, z, hz, he⟩ := Submodule.mem_sup.mp h
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
    have hb : c = 0 ∨ c = 1 := by exact (by decide +kernel : ∀ c : ZMod 2, c = 0 ∨ c = 1) c
    rcases hb with hb | hb
    · have hz : z = 0 := by rw [← hc, hb, zero_smul]
      have hv : w = v := by simpa [hz] using he
      exact Or.inl (hv ▸ hw)
    · refine Or.inr ⟨w, hw, ?_⟩
      have hz : z = a := by rw [← hc, hb, one_smul]
      simpa only [hz, add_comm] using he
  · rintro (h | ⟨w, hw, he⟩)
    · exact Submodule.mem_sup_left h
    · rw [← he]
      exact Submodule.add_mem _ (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
        (Submodule.mem_sup_left hw)

/-- The finite xor-span list contains exactly the labels of the actual linear span. -/
theorem generatedAxisE8FrameSpanLabelList_mem (l : List (Fin 256)) (x : Fin 256) :
    x ∈ generatedAxisE8FrameSpanLabelList l ↔
      generatedAxisE8FrameLabelBits x ∈
        generatedAxisE8FrameListSpan (l.map generatedAxisE8FrameLabelBits) := by
  induction l generalizing x with
  | nil =>
    have hz : generatedAxisE8FrameLabelBits 0 = 0 := by ext i; simp [generatedAxisE8FrameLabelBits]
    have hn : generatedAxisE8FrameListSpan [] = ⊥ := by
      simp [generatedAxisE8FrameListSpan]
    simp only [generatedAxisE8FrameSpanLabelList, List.mem_singleton, List.map_nil,
      hn, Submodule.mem_bot]
    constructor
    · intro h; rw [h, hz]
    · intro h; exact generatedAxisE8FrameLabelEquiv.injective (h.trans hz.symm)
  | cons a l ih =>
    simp only [generatedAxisE8FrameSpanLabelList, List.mem_append, List.mem_map,
      List.map_cons, generatedAxisE8FrameListSpan_cons, generatedAxisE8Frame_mem_extension]
    constructor
    · rintro (h | ⟨y, hy, he⟩)
      · exact Or.inl ((ih x).mp h)
      · refine Or.inr ⟨generatedAxisE8FrameLabelBits y, (ih y).mp hy, ?_⟩
        rw [← generatedAxisE8FrameLabelBits_xor, he]
    · rintro (h | ⟨v, hv, he⟩)
      · exact Or.inl ((ih x).mpr h)
      · let y := generatedAxisE8FrameLabel v
        have hy : generatedAxisE8FrameLabelBits y = v := generatedAxisE8FrameLabel_right v
        refine Or.inr ⟨y, (ih y).mpr (hy ▸ hv), ?_⟩
        apply generatedAxisE8FrameLabelEquiv.injective
        change generatedAxisE8FrameLabelBits (generatedAxisE8FrameLabelXor a y) =
          generatedAxisE8FrameLabelBits x
        rw [generatedAxisE8FrameLabelBits_xor, hy, he]

/-- Encoding and then decoding a vector list returns the original intrinsic vectors. -/
theorem generatedAxisE8FrameLabel_map_inverse (l : List (Fin 8 → ZMod 2)) :
    (l.map generatedAxisE8FrameLabel).map generatedAxisE8FrameLabelBits = l := by
  rw [List.map_map]
  have he : generatedAxisE8FrameLabelBits ∘ generatedAxisE8FrameLabel = id :=
    funext generatedAxisE8FrameLabel_right
  rw [he, List.map_id]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
