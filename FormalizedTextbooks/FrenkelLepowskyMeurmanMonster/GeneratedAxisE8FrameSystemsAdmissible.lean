/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8FrameSystemsLabelSpan

/-! Generic greedy bases satisfy the exact Boolean coverage contracts. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The compact admissibility check follows from ordinary minimum and singularity facts. -/
theorem generatedAxisE8Frame_admissible_of_facts (l : List (Fin 256))
    (hc : ∀ i : Fin l.length, l[i] ∉ generatedAxisE8FrameSpanLabelList (l.take i.val) ∧
      ∀ x ∈ generatedAxisE8FrameSpanLabelList l,
        x ∉ generatedAxisE8FrameSpanLabelList (l.take i.val) → l[i] ≤ x)
    (hq : ∀ x ∈ generatedAxisE8FrameSpanLabelList l,
      generatedAxisE8FrameQuadratic (generatedAxisE8FrameLabelBits x) = 0) :
    generatedAxisE8FrameAdmissibleLabels l := by
  unfold generatedAxisE8FrameAdmissibleLabels generatedAxisE8FrameAdmissibleCheck
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]
  apply And.symm
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [getElem!_pos l i hi]
    refine ⟨?_, ?_⟩
    · rw [not_decide_eq_true]
      exact (hc ⟨i, hi⟩).1
    intro x hx
    by_cases hp : x ∈ generatedAxisE8FrameSpanLabelList (l.take i)
    · exact Or.inl hp
    · exact Or.inr ((hc ⟨i, hi⟩).2 x hx hp)
  · intro x hx
    exact (generatedAxisE8FrameSingularMask_certificate x).mpr (hq x hx)

/-- The labels of a genuine greedy singular vector basis satisfy the finite checker. -/
theorem generatedAxisE8Frame_admissible_of_greedy
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (l : List (Fin 8 → ZMod 2))
    (hl : generatedAxisE8FrameGreedyIn W l)
    (hq : ∀ v ∈ W, generatedAxisE8FrameQuadratic v = 0) :
    generatedAxisE8FrameAdmissibleLabels (l.map generatedAxisE8FrameLabel) := by
  let L := l.map generatedAxisE8FrameLabel
  have hm : L.map generatedAxisE8FrameLabelBits = l := generatedAxisE8FrameLabel_map_inverse l
  apply generatedAxisE8Frame_admissible_of_facts L
  · intro i
    have hi : i.val < l.length := by simpa only [L, List.length_map] using i.isLt
    let j : Fin l.length := ⟨i.val, hi⟩
    have hg : L[i] = generatedAxisE8FrameLabel l[j] := by simp [L, j]
    have ht : (L.take i.val).map generatedAxisE8FrameLabelBits = l.take i.val := by
      rw [List.map_take, hm]
    have hbits : generatedAxisE8FrameLabelBits L[i] = l[j] := by
      rw [hg, generatedAxisE8FrameLabel_right]
    refine ⟨?_, ?_⟩
    · intro he
      have hv := (generatedAxisE8FrameSpanLabelList_mem _ _).mp he
      rw [ht, hbits] at hv
      exact (hl.2 j).1 hv
    · intro x hx hp
      have hxW : generatedAxisE8FrameLabelBits x ∈ W := by
        apply generatedAxisE8FrameGreedyIn_span_le W l hl
        have he := (generatedAxisE8FrameSpanLabelList_mem L x).mp hx
        rwa [hm] at he
      have hpV : generatedAxisE8FrameLabelBits x ∉
          generatedAxisE8FrameListSpan (l.take i.val) := by
        intro he
        apply hp
        apply (generatedAxisE8FrameSpanLabelList_mem _ _).mpr
        rwa [ht]
      have hmin := (hl.2 j).2 _ hxW hpV
      rw [generatedAxisE8FrameLabel_left x] at hmin
      rwa [hg]
  · intro x hx
    apply hq
    apply generatedAxisE8FrameGreedyIn_span_le W l hl
    have he := (generatedAxisE8FrameSpanLabelList_mem L x).mp hx
    rwa [hm] at he

/-- Every initial segment of a genuine greedy basis retains its minimum-label property. -/
theorem generatedAxisE8FrameGreedyIn_take
    (W : Submodule (ZMod 2) (Fin 8 → ZMod 2)) (l : List (Fin 8 → ZMod 2))
    (hl : generatedAxisE8FrameGreedyIn W l) (n : ℕ) :
    generatedAxisE8FrameGreedyIn W (l.take n) := by
  refine ⟨?_, ?_⟩
  · intro v hv
    exact hl.1 v (List.mem_of_mem_take hv)
  · intro i
    have hi : i.val < l.length := by have := i.isLt; simp only [List.length_take] at this; omega
    have hn : i.val < n := by have := i.isLt; simp only [List.length_take] at this; omega
    have hg : (l.take n)[i] = l[i.val]'hi := by simp
    have ht : (l.take n).take i.val = l.take i.val := by
      rw [List.take_take, min_eq_left (Nat.le_of_lt hn)]
    rw [hg, ht]
    exact hl.2 ⟨i.val, hi⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
