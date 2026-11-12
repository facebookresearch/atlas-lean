/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


































































import Mathlib
import Code.Walls.jc2_thinthickdichotomy
import Code.Lattice.BalancePreservingContraction

open SimpleGraph Function Set
open scoped symmDiff

namespace StatMech

namespace Walls

open StatMech.Lattice











theorem jc3_mem_clip_iff {α : Type*} (K : Set α) (r c : α) :
    c ∈ K \ {r} ↔ (c ∈ K ∧ c ≠ r) := by
  simp only [Set.mem_diff, Set.mem_singleton_iff]





theorem jc3_clip_eq_iff_ne {α : Type*} (K : Set α) (r c : α) (hne : c ≠ r) :
    c ∈ K ↔ c ∈ K \ {r} := by
  simp only [Set.mem_diff, Set.mem_singleton_iff, hne, not_false_iff, and_true]


theorem jc3_ear_not_mem_clip {α : Type*} (K : Set α) (r : α) : r ∉ K \ {r} := by
  simp











theorem jc3_clip_symmDiff {α : Type*} (K : Set α) (r : α) (hr : r ∈ K) :
    K ∆ (K \ {r}) = {r} := by
  ext x
  simp only [Set.symmDiff_def, Set.mem_union, Set.mem_diff, Set.mem_singleton_iff]
  constructor
  · rintro (⟨hxK, hxd⟩ | ⟨hxd, hxK⟩)
    · 
      by_contra hne
      exact hxd ⟨hxK, hne⟩
    · 
      exact absurd hxd.1 hxK
  · 
    rintro rfl
    left
    exact ⟨hr, fun h => h.2 rfl⟩









theorem jc3_clip_ssubset {α : Type*} (K : Set α) (r : α) (hr : r ∈ K) : K \ {r} ⊂ K :=
  Set.diff_singleton_ssubset.mpr hr


theorem jc3_clip_finite {α : Type*} (K : Set α) (r : α) (hK : K.Finite) : (K \ {r}).Finite :=
  hK.subset Set.diff_subset



theorem jc3_clip_nonempty_of_two {α : Type*} (K : Set α) (r s : α) (hs : s ∈ K) (hsr : s ≠ r) :
    (K \ {r}).Nonempty :=
  ⟨s, (jc3_mem_clip_iff K r s).mpr ⟨hs, hsr⟩⟩










theorem jc3_ear_mem (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) : jc2_rightEnd c len ∈ K :=
  jc2_rightEnd_mem K c len hrun










theorem jc3_clip_symmDiff_ear (K : Set (Site 2)) (c : Site 2) (len : ℤ)
    (hrun : jc_IsTopRowRun K c len) :
    K ∆ (K \ {jc2_rightEnd c len}) = {jc2_rightEnd c len} :=
  jc3_clip_symmDiff K (jc2_rightEnd c len) (jc3_ear_mem K c len hrun)




theorem jc3_probe_mem_iff_ear (K : Set (Site 2)) (c : Site 2) (len : ℤ) (s : Site 2)
    (hne : s ≠ jc2_rightEnd c len) :
    s ∈ K ↔ s ∈ K \ {jc2_rightEnd c len} :=
  jc3_clip_eq_iff_ne K (jc2_rightEnd c len) s hne






















theorem jc3_clip_agree_of_notProbed (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (h : bpc_NotProbed r e) :
    (e.head + (-rot90Fun e.dir) ∈ K ↔ e.head + (-rot90Fun e.dir) ∈ K \ {r}) ∧
      (e.tail + (-rot90Fun e.dir) ∈ K ↔ e.tail + (-rot90Fun e.dir) ∈ K \ {r}) :=
  ⟨jc3_clip_eq_iff_ne K r _ h.1, jc3_clip_eq_iff_ne K r _ h.2⟩







theorem jc3_notProbed_iff_clip_agree_of_mem (K : Set (Site 2)) (r : Site 2) (e : Dart)
    (hr : r ∈ K) :
    bpc_NotProbed r e ↔
      ((e.head + (-rot90Fun e.dir) ∈ K ↔ e.head + (-rot90Fun e.dir) ∈ K \ {r}) ∧
        (e.tail + (-rot90Fun e.dir) ∈ K ↔ e.tail + (-rot90Fun e.dir) ∈ K \ {r})) := by
  unfold bpc_NotProbed
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨jc3_clip_eq_iff_ne K r _ h1, jc3_clip_eq_iff_ne K r _ h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · 
      
      intro heq
      exact (jc3_ear_not_mem_clip K r) (heq ▸ h1.mp (heq ▸ hr))
    · 
      intro heq
      exact (jc3_ear_not_mem_clip K r) (heq ▸ h2.mp (heq ▸ hr))











theorem jc3_domino_clip_symmDiff :
    domino ∆ (domino \ {(![1, 0] : Site 2)}) = {(![1, 0] : Site 2)} :=
  jc3_clip_symmDiff domino (![1, 0] : Site 2) (by
    
    simp [domino])



theorem jc3_unitCell_clip_self :
    unitCell \ {(![0, 0] : Site 2)} = (∅ : Set (Site 2)) := by
  
  rw [show unitCell = {(![0, 0] : Site 2)} from rfl]
  simp

end Walls

end StatMech
