/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.MergeLo
import Code.Transcription.MergeHi
import Code.Correctness.SortSliceRange

/-!
# Exact semantics of merge movement primitives

The safety layer proves that merge reads and writes stay within their allocated
backings.  Functional merge proofs additionally need the exact whole-entry
effect of those movements.  This module records that effect against the input
snapshot: a successful movement copies each key/payload pair from its original
source position and changes no position outside its destination range.

The signed, pointwise predicates below match the pointer-shaped transcription.
Natural-indexed `SortSlice.EqualOutsideRange` consequences are supplied for
the range-facing correctness layer.
-/

namespace CPythonListsort

universe u v

variable {kappa : Type u} {nu : Type v}

namespace SortSlice

/-- Exact snapshot semantics for copying a half-open signed range. -/
def CopiesRange (before after : SortSlice kappa nu)
    (dst src : Int) (count : Nat) : Prop :=
  ∀ i, i < count →
    after.read? (dst + Int.ofNat i) = before.read? (src + Int.ofNat i)

/-- Pointwise frame for a half-open signed destination range. -/
def ReadFrame (before after : SortSlice kappa nu)
    (dst : Int) (count : Nat) : Prop :=
  before.entries.size = after.entries.size ∧
    ∀ index, index < dst ∨ dst + Int.ofNat count ≤ index →
      after.read? index = before.read? index

/-- A successful write exposes its complete array update and its implied
bounds facts. -/
theorem write_eq_some_spec (slice updated : SortSlice kappa nu)
    (index : Int) (entry : SortSliceEntry kappa nu)
    (hwrite : slice.write? index entry = some updated) :
    0 ≤ index ∧ ∃ hinBounds : index.toNat < slice.entries.size,
      updated = { entries :=
        slice.entries.set index.toNat entry hinBounds } := by
  unfold write? at hwrite
  split at hwrite
  · rename_i hnonnegative
    dsimp only at hwrite
    split at hwrite
    · rename_i hinBounds
      injection hwrite with hwrite
      exact ⟨hnonnegative, hinBounds, hwrite.symm⟩
    · simp at hwrite
  · simp at hwrite

/-- The addressed whole entry has exactly the value supplied to a successful
write. -/
theorem write_read_self_of_eq_some (slice updated : SortSlice kappa nu)
    (index : Int) (entry : SortSliceEntry kappa nu)
    (hwrite : slice.write? index entry = some updated) :
    updated.read? index = some entry := by
  rcases write_eq_some_spec slice updated index entry hwrite with
    ⟨hnonnegative, hinBounds, rfl⟩
  simp [read?, hnonnegative, hinBounds]

/-- A successful write preserves every other signed whole-entry read. -/
theorem write_read_ne_of_eq_some (slice updated : SortSlice kappa nu)
    (written index : Int) (entry : SortSliceEntry kappa nu)
    (hwrite : slice.write? written entry = some updated)
    (hne : index ≠ written) :
    updated.read? index = slice.read? index := by
  rcases write_eq_some_spec slice updated written entry hwrite with
    ⟨hwritten, hinBounds, rfl⟩
  by_cases hindex : 0 ≤ index
  · have hnatne : written.toNat ≠ index.toNat := by
      intro heq
      apply hne
      have hwrittenCast := Int.toNat_of_nonneg hwritten
      have hindexCast := Int.toNat_of_nonneg hindex
      omega
    simp [read?, hindex, Array.getElem?_set_ne _ hnatne]
  · simp [read?, hindex]

/-- A successful write changes no signed read outside its singleton
destination range. -/
theorem write_readFrame_of_eq_some (slice updated : SortSlice kappa nu)
    (index : Int) (entry : SortSliceEntry kappa nu)
    (hwrite : slice.write? index entry = some updated) :
    ReadFrame slice updated index 1 := by
  refine ⟨(write_entries_size_of_eq_some slice updated index entry hwrite).symm, ?_⟩
  intro other houtside
  apply write_read_ne_of_eq_some slice updated index other entry hwrite
  intro heq
  subst other
  rcases houtside with hbefore | hafter <;> simp at *

/-- A successful single-cell shared-store copy reads from the input snapshot. -/
theorem copy_read_destination_of_eq_some (slice updated : SortSlice kappa nu)
    (dst src : Int) (hcopy : slice.copy? dst src = some updated) :
    updated.read? dst = slice.read? src := by
  simp only [copy?, copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact (write_read_self_of_eq_some slice updated dst entry hcopy).trans hread.symm

/-- A successful single-cell shared-store copy preserves every read other than
its destination. -/
theorem copy_read_ne_of_eq_some (slice updated : SortSlice kappa nu)
    (dst src index : Int) (hcopy : slice.copy? dst src = some updated)
    (hne : index ≠ dst) :
    updated.read? index = slice.read? index := by
  simp only [copy?, copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact write_read_ne_of_eq_some slice updated dst index entry hcopy hne

/-- A successful single-cell copy is framed by its singleton destination. -/
theorem copy_readFrame_of_eq_some (slice updated : SortSlice kappa nu)
    (dst src : Int) (hcopy : slice.copy? dst src = some updated) :
    ReadFrame slice updated dst 1 := by
  refine ⟨(copy_entries_size_of_eq_some slice updated dst src hcopy).symm, ?_⟩
  intro index houtside
  apply copy_read_ne_of_eq_some slice updated dst src index hcopy
  intro heq
  subst index
  rcases houtside with hbefore | hafter <;> simp at *

/-- A signed pointwise frame at a natural start implies the shared
range-facing frame predicate. -/
theorem ReadFrame.equalOutsideRange_ofNat
    {before after : SortSlice kappa nu} {start count : Nat}
    (hframe : ReadFrame before after (Int.ofNat start) count) :
    EqualOutsideRange before after start count := by
  refine ⟨hframe.1, ?_⟩
  intro otherStart otherCount hdisjoint
  apply Array.ext_getElem?
  intro offset
  simp only [sortSliceRangeEntries, Array.getElem?_extract]
  rw [← hframe.1]
  by_cases hoffset :
      offset < min (otherStart + otherCount) before.entries.size - otherStart
  · rw [if_pos hoffset, if_pos hoffset]
    have hindexOutside :
        Int.ofNat (otherStart + offset) < Int.ofNat start ∨
          Int.ofNat start + Int.ofNat count ≤
            Int.ofNat (otherStart + offset) := by
      rcases hdisjoint with hbefore | hafter
      · left
        exact Int.ofNat_lt.mpr (by omega)
      · right
        simp only [Int.ofNat_eq_natCast]
        omega
    have hread := hframe.2 (Int.ofNat (otherStart + offset)) hindexOutside
    simpa only [read?_ofNat] using hread.symm
  · rw [if_neg hoffset, if_neg hoffset]

/-- Natural-indexed external frame for a successful whole-entry write. -/
theorem write_equalOutsideRange_of_eq_some
    (slice updated : SortSlice kappa nu) (index : Int)
    (entry : SortSliceEntry kappa nu)
    (hwrite : slice.write? index entry = some updated) :
    EqualOutsideRange slice updated index.toNat 1 := by
  have hindex := (write_eq_some_spec slice updated index entry hwrite).1
  have hcast : Int.ofNat index.toNat = index := Int.toNat_of_nonneg hindex
  have hframe := write_readFrame_of_eq_some slice updated index entry hwrite
  rw [← hcast] at hframe
  exact hframe.equalOutsideRange_ofNat

private theorem copy_dst_nonnegative_of_eq_some
    (slice updated : SortSlice kappa nu) (dst src : Int)
    (hcopy : slice.copy? dst src = some updated) : 0 ≤ dst := by
  simp only [copy?, copyFrom?, bind, Option.bind] at hcopy
  split at hcopy
  · simp at hcopy
  · rename_i entry hread
    exact (write_eq_some_spec slice updated dst entry hcopy).1

/-- Natural-indexed external frame for a successful one-cell shared-store
copy. -/
theorem copy_equalOutsideRange_of_eq_some
    (slice updated : SortSlice kappa nu) (dst src : Int)
    (hcopy : slice.copy? dst src = some updated) :
    EqualOutsideRange slice updated dst.toNat 1 := by
  have hdst := copy_dst_nonnegative_of_eq_some slice updated dst src hcopy
  have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
  have hframe := copy_readFrame_of_eq_some slice updated dst src hcopy
  rw [← hcast] at hframe
  exact hframe.equalOutsideRange_ofNat

private theorem memmoveForward_correct
    (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
    (hdirection : dst ≤ src)
    (hresult : memmoveForward? count slice dst src = some updated) :
    CopiesRange slice updated dst src count ∧
      ReadFrame slice updated dst count := by
  induction count generalizing slice updated dst src with
  | zero =>
      simp only [memmoveForward?] at hresult
      injection hresult with hresult
      subst updated
      refine ⟨?_, ⟨rfl, ?_⟩⟩
      · intro i hi
        omega
      · intro index _houtside
        rfl
  | succ count ih =>
      rw [memmoveForward?] at hresult
      rcases Option.bind_eq_some_iff.mp hresult with
        ⟨afterHead, hhead, htail⟩
      rcases ih afterHead updated (dst + 1) (src + 1) (by omega) htail with
        ⟨htailCopy, htailFrame⟩
      have hheadFrame := copy_readFrame_of_eq_some slice afterHead dst src hhead
      refine ⟨?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            have hpreserved := htailFrame.2 dst (Or.inl (by omega))
            have hcopied := copy_read_destination_of_eq_some
              slice afterHead dst src hhead
            simpa using hpreserved.trans hcopied
        | succ i =>
            have hiTail : i < count := by omega
            have hcopied := htailCopy i hiTail
            have hpreserved := copy_read_ne_of_eq_some slice afterHead dst src
              (src + 1 + Int.ofNat i) hhead (by
                simp only [Int.ofNat_eq_natCast]
                omega)
            calc
              updated.read? (dst + Int.ofNat (Nat.succ i)) =
                  updated.read? (dst + 1 + Int.ofNat i) := by
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
              _ = afterHead.read? (src + 1 + Int.ofNat i) := hcopied
              _ = slice.read? (src + 1 + Int.ofNat i) := hpreserved
              _ = slice.read? (src + Int.ofNat (Nat.succ i)) := by
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
      · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
        intro index houtside
        have htailOutside :
            index < dst + 1 ∨
              (dst + 1) + Int.ofNat count ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        exact (htailFrame.2 index htailOutside).trans
          (hheadFrame.2 index hheadOutside)

private theorem memmoveBackward_correct
    (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
    (hdirection : src < dst)
    (hresult : memmoveBackward? count slice dst src = some updated) :
    CopiesRange slice updated dst src count ∧
      ReadFrame slice updated dst count := by
  induction count generalizing slice updated with
  | zero =>
      simp only [memmoveBackward?] at hresult
      injection hresult with hresult
      subst updated
      refine ⟨?_, ⟨rfl, ?_⟩⟩
      · intro i hi
        omega
      · intro index _houtside
        rfl
  | succ count ih =>
      rw [memmoveBackward?] at hresult
      rcases Option.bind_eq_some_iff.mp hresult with
        ⟨afterHead, hhead, htail⟩
      rcases ih afterHead updated htail with ⟨htailCopy, htailFrame⟩
      have hheadFrame := copy_readFrame_of_eq_some slice afterHead
        (dst + Int.ofNat count) (src + Int.ofNat count) hhead
      refine ⟨?_, ?_⟩
      · intro i hi
        by_cases hilast : i = count
        · subst i
          have hpreserved := htailFrame.2 (dst + Int.ofNat count)
            (Or.inr le_rfl)
          have hcopied := copy_read_destination_of_eq_some slice afterHead
            (dst + Int.ofNat count) (src + Int.ofNat count) hhead
          exact hpreserved.trans hcopied
        · have hiTail : i < count := by omega
          have hcopied := htailCopy i hiTail
          have hpreserved := copy_read_ne_of_eq_some slice afterHead
            (dst + Int.ofNat count) (src + Int.ofNat count)
            (src + Int.ofNat i) hhead (by
              simp only [Int.ofNat_eq_natCast]
              omega)
          exact hcopied.trans hpreserved
      · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
        intro index houtside
        have htailOutside :
            index < dst ∨ dst + Int.ofNat count ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        have hheadOutside :
            index < dst + Int.ofNat count ∨
              dst + Int.ofNat count + 1 ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl (by
              simp only [Int.ofNat_eq_natCast]
              omega)
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        exact (htailFrame.2 index htailOutside).trans
          (hheadFrame.2 index hheadOutside)

/-- Successful `memmove?` has exact snapshot semantics, including when source
and destination overlap. -/
theorem memmove_copiesRange_of_eq_some
    (slice updated : SortSlice kappa nu) (dst src : Int) (count : Nat)
    (hresult : slice.memmove? dst src count = some updated) :
    CopiesRange slice updated dst src count := by
  by_cases hdirection : dst ≤ src
  · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
    exact (memmoveForward_correct count slice updated dst src hdirection hresult).1
  · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
    exact (memmoveBackward_correct count slice updated dst src
      (lt_of_not_ge hdirection) hresult).1

/-- Successful `memmove?` changes no signed read outside its destination
range. -/
theorem memmove_readFrame_of_eq_some
    (slice updated : SortSlice kappa nu) (dst src : Int) (count : Nat)
    (hresult : slice.memmove? dst src count = some updated) :
    ReadFrame slice updated dst count := by
  by_cases hdirection : dst ≤ src
  · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
    exact (memmoveForward_correct count slice updated dst src hdirection hresult).2
  · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
    exact (memmoveBackward_correct count slice updated dst src
      (lt_of_not_ge hdirection) hresult).2

private theorem memmoveForward_dst_nonnegative_of_success
    (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
    (hcount : 0 < count)
    (hresult : memmoveForward? count slice dst src = some updated) :
    0 ≤ dst := by
  cases count with
  | zero => omega
  | succ count =>
      rw [memmoveForward?] at hresult
      rcases Option.bind_eq_some_iff.mp hresult with ⟨afterHead, hhead, _htail⟩
      exact copy_dst_nonnegative_of_eq_some slice afterHead dst src hhead

private theorem memmoveBackward_dst_nonnegative_of_success
    (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
    (hcount : 0 < count)
    (hresult : memmoveBackward? count slice dst src = some updated) :
    0 ≤ dst := by
  induction count generalizing slice updated with
  | zero => omega
  | succ count ih =>
      rw [memmoveBackward?] at hresult
      rcases Option.bind_eq_some_iff.mp hresult with
        ⟨afterHead, hhead, htail⟩
      cases count with
      | zero =>
          have hhead' : slice.copy? dst src = some afterHead := by
            simpa using hhead
          exact copy_dst_nonnegative_of_eq_some slice afterHead dst src hhead'
      | succ count =>
          exact ih afterHead updated (by omega) htail

private theorem memmove_dst_nonnegative_of_success
    (count : Nat) (slice updated : SortSlice kappa nu) (dst src : Int)
    (hcount : 0 < count)
    (hresult : slice.memmove? dst src count = some updated) :
    0 ≤ dst := by
  by_cases hdirection : dst ≤ src
  · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
    exact memmoveForward_dst_nonnegative_of_success count slice updated dst src
      hcount hresult
  · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
    exact memmoveBackward_dst_nonnegative_of_success count slice updated dst src
      hcount hresult

/-- Natural-indexed external frame for a successful same-store move.  No
disjointness premise is needed: overlap is handled by `memmove?` itself. -/
theorem memmove_equalOutsideRange_of_eq_some
    (slice updated : SortSlice kappa nu) (dst src : Int) (count : Nat)
    (hresult : slice.memmove? dst src count = some updated) :
    EqualOutsideRange slice updated dst.toNat count := by
  by_cases hcount : count = 0
  · subst count
    have hsame : updated = slice := by
      by_cases hdirection : dst ≤ src
      · rw [memmove?, memmoveDirection, if_pos hdirection] at hresult
        simpa [memmoveForward?] using hresult.symm
      · rw [memmove?, memmoveDirection, if_neg hdirection] at hresult
        simpa [memmoveBackward?] using hresult.symm
    subst updated
    exact EqualOutsideRange.refl slice dst.toNat 0
  · have hdst := memmove_dst_nonnegative_of_success count slice updated dst src
      (Nat.pos_of_ne_zero hcount) hresult
    have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
    have hframe := memmove_readFrame_of_eq_some slice updated dst src count hresult
    rw [← hcast] at hframe
    exact hframe.equalOutsideRange_ofNat

end SortSlice

namespace TempStorage

/-- Exact content frame for a natural-indexed temporary destination range. -/
structure ReadFrameNat (before after : TempStorage kappa nu)
    (dst count : Nat) : Prop where
  cellsSize : before.cells.size = after.cells.size
  backing : before.backing = after.backing
  hasValues : before.hasValues = after.hasValues
  read_eq : ∀ index, index < dst ∨ dst + count ≤ index →
    mergeLoTempRead? after index = mergeLoTempRead? before index

/-- Exact content frame for a signed-indexed temporary destination range. -/
structure ReadFrameInt (before after : TempStorage kappa nu)
    (dst : Int) (count : Nat) : Prop where
  cellsSize : before.cells.size = after.cells.size
  backing : before.backing = after.backing
  hasValues : before.hasValues = after.hasValues
  read_eq : ∀ index, index < dst ∨ dst + Int.ofNat count ≤ index →
    mergeHiTempRead? after index = mergeHiTempRead? before index

end TempStorage

/-! ## `merge_lo` temporary movement -/

/-- One successful natural-indexed temporary write is framed by its singleton
destination. -/
theorem mergeLoTempWrite_readFrameNat_of_eq_some
    (storage updated : TempStorage kappa nu) (dst : Nat)
    (entry : SortSliceEntry kappa nu)
    (hwrite : mergeLoTempWrite? storage dst entry = some updated) :
    TempStorage.ReadFrameNat storage updated dst 1 := by
  simp only [mergeLoTempWrite?] at hwrite
  split at hwrite
  · injection hwrite with hwrite
    subst updated
    refine
      { cellsSize := by simp
        backing := rfl
        hasValues := rfl
        read_eq := ?_ }
    intro index houtside
    apply mergeLoTempRead_write_ne_of_eq_some storage
      { storage with cells := storage.cells.set dst (some entry) }
      dst index entry (by simp [mergeLoTempWrite?, *])
    intro heq
    subst index
    rcases houtside with hbefore | hafter <;> omega
  · simp at hwrite

private theorem mergeLoMemcpyDataToTemp_spec
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Nat) (src : Int)
    (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    state'.data = state.data ∧
      (∀ i, i < count →
        mergeLoTempRead? state'.a (dst + i) =
          state.data.read? (src + Int.ofNat i)) ∧
      TempStorage.ReadFrameNat state.a state'.a dst count := by
  induction count generalizing state state' dst src with
  | zero =>
      simp only [mergeLoMemcpyDataToTemp?] at hcopy
      injection hcopy with hcopy
      subst state'
      refine ⟨rfl, ?_, ?_⟩
      · intro i hi
        omega
      · exact
          { cellsSize := rfl
            backing := rfl
            hasValues := rfl
            read_eq := fun _ _ => rfl }
  | succ count ih =>
      rw [mergeLoMemcpyDataToTemp?] at hcopy
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, hcopy⟩
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨storage, hwrite, htail⟩
      rcases ih { state with a := storage } state' (dst + 1) (src + 1) htail with
        ⟨hdata, htailCopy, htailFrame⟩
      have hheadFrame :=
        mergeLoTempWrite_readFrameNat_of_eq_some state.a storage dst entry hwrite
      refine ⟨hdata, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            have hpreserved := htailFrame.read_eq dst (Or.inl (by omega))
            have hwritten := mergeLoTempRead_write_self_of_eq_some
              state.a storage dst entry hwrite
            simpa using hpreserved.trans (hwritten.trans hread.symm)
        | succ i =>
            have hiTail : i < count := by omega
            have hcopied := htailCopy i hiTail
            calc
              mergeLoTempRead? state'.a (dst + Nat.succ i) =
                  state.data.read? (src + 1 + Int.ofNat i) := by
                    simpa only [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hcopied
              _ = state.data.read? (src + Int.ofNat (Nat.succ i)) := by
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
      · refine
          { cellsSize := hheadFrame.cellsSize.trans htailFrame.cellsSize
            backing := hheadFrame.backing.trans htailFrame.backing
            hasValues := hheadFrame.hasValues.trans htailFrame.hasValues
            read_eq := ?_ }
        intro index houtside
        have htailOutside :
            index < dst + 1 ∨ dst + 1 + count ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by omega)
        have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (by omega)
        exact (htailFrame.read_eq index htailOutside).trans
          (hheadFrame.read_eq index hheadOutside)

/-- A successful `merge_lo` main-to-temporary block copy leaves main data
unchanged. -/
theorem mergeLoMemcpyDataToTemp_data_eq_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Nat) (src : Int)
    (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    state'.data = state.data :=
  (mergeLoMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).1

/-- A successful `merge_lo` main-to-temporary block copy materializes exactly
the original main-data source range. -/
theorem mergeLoMemcpyDataToTemp_read_range_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Nat) (src : Int)
    (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src =
      some state')
    (i : Nat) (hi : i < count) :
    mergeLoTempRead? state'.a (dst + i) =
      state.data.read? (src + Int.ofNat i) :=
  (mergeLoMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

/-- A successful `merge_lo` main-to-temporary block copy changes no temporary
cell outside its destination range. -/
theorem mergeLoMemcpyDataToTemp_tempFrame_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Nat) (src : Int)
    (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    TempStorage.ReadFrameNat state.a state'.a dst count :=
  (mergeLoMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.2

private theorem mergeLoMemcpyTempToData_spec
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Int) (src : Nat)
    (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src =
      some state') :
    state'.a = state.a ∧
      (∀ i, i < count →
        state'.data.read? (dst + Int.ofNat i) =
          mergeLoTempRead? state.a (src + i)) ∧
      SortSlice.ReadFrame state.data state'.data dst count := by
  induction count generalizing state state' dst src with
  | zero =>
      simp only [mergeLoMemcpyTempToData?] at hcopy
      injection hcopy with hcopy
      subst state'
      refine ⟨rfl, ?_, ⟨rfl, ?_⟩⟩
      · intro i hi
        omega
      · intro index _houtside
        rfl
  | succ count ih =>
      rw [mergeLoMemcpyTempToData?] at hcopy
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, hcopy⟩
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨data, hwrite, htail⟩
      rcases ih { state with data := data } state' (dst + 1) (src + 1) htail with
        ⟨htemp, htailCopy, htailFrame⟩
      have hheadFrame := SortSlice.write_readFrame_of_eq_some
        state.data data dst entry hwrite
      refine ⟨htemp, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            have hpreserved := htailFrame.2 dst (Or.inl (by omega))
            have hwritten := SortSlice.write_read_self_of_eq_some
              state.data data dst entry hwrite
            simpa using hpreserved.trans (hwritten.trans hread.symm)
        | succ i =>
            have hiTail : i < count := by omega
            have hcopied := htailCopy i hiTail
            calc
              state'.data.read? (dst + Int.ofNat (Nat.succ i)) =
                  state'.data.read? (dst + 1 + Int.ofNat i) := by
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
              _ = mergeLoTempRead? state.a (src + Nat.succ i) := by
                    simpa only [Nat.add_assoc, Nat.add_comm,
                      Nat.add_left_comm] using hcopied
      · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
        intro index houtside
        have htailOutside :
            index < dst + 1 ∨ (dst + 1) + Int.ofNat count ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        exact (htailFrame.2 index htailOutside).trans
          (hheadFrame.2 index hheadOutside)

/-- A successful `merge_lo` temporary-to-main block copy leaves temporary
storage unchanged. -/
theorem mergeLoMemcpyTempToData_temp_eq_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Int) (src : Nat)
    (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src =
      some state') :
    state'.a = state.a :=
  (mergeLoMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).1

/-- A successful `merge_lo` temporary-to-main block copy writes exactly the
input temporary snapshot into its main destination range. -/
theorem mergeLoMemcpyTempToData_read_range_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Int) (src : Nat)
    (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src =
      some state')
    (i : Nat) (hi : i < count) :
    state'.data.read? (dst + Int.ofNat i) =
      mergeLoTempRead? state.a (src + i) :=
  (mergeLoMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

/-- Signed pointwise frame for a successful `merge_lo` temporary-to-main
block copy. -/
theorem mergeLoMemcpyTempToData_readFrame_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Int) (src : Nat)
    (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src =
      some state') :
    SortSlice.ReadFrame state.data state'.data dst count :=
  (mergeLoMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.2

/-- Natural-indexed external frame for a successful `merge_lo`
temporary-to-main block copy. -/
theorem mergeLoMemcpyTempToData_equalOutsideRange_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Int) (src : Nat)
    (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src =
      some state') :
    SortSlice.EqualOutsideRange state.data state'.data dst.toNat count := by
  cases count with
  | zero =>
      simp only [mergeLoMemcpyTempToData?] at hcopy
      injection hcopy with hcopy
      subst state'
      exact SortSlice.EqualOutsideRange.refl state.data dst.toNat 0
  | succ count =>
      have hcopyHead := hcopy
      rw [mergeLoMemcpyTempToData?] at hcopyHead
      rcases Option.bind_eq_some_iff.mp hcopyHead with ⟨entry, _hread, hcopyHead⟩
      rcases Option.bind_eq_some_iff.mp hcopyHead with ⟨data, hwrite, _htail⟩
      have hdst := (SortSlice.write_eq_some_spec state.data data dst entry hwrite).1
      have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
      have hframe := mergeLoMemcpyTempToData_readFrame_of_eq_some site hDirection
        (count + 1) state state' dst src hcopy
      rw [← hcast] at hframe
      exact hframe.equalOutsideRange_ofNat

/-! ## `merge_hi` single-cell temporary movement -/

/-- One successful signed temporary write is framed by its singleton
destination. -/
theorem mergeHiTempWrite_readFrameInt_of_eq_some
    (storage updated : TempStorage kappa nu) (dst : Int)
    (entry : SortSliceEntry kappa nu)
    (hwrite : mergeHiTempWrite? storage dst entry = some updated) :
    TempStorage.ReadFrameInt storage updated dst 1 := by
  unfold mergeHiTempWrite? at hwrite
  split at hwrite
  · rename_i hdst
    dsimp only at hwrite
    split at hwrite
    · rename_i hbound
      injection hwrite with hwrite
      subst updated
      refine
        { cellsSize := by simp
          backing := rfl
          hasValues := rfl
          read_eq := ?_ }
      intro index houtside
      apply mergeHiTempWrite_read_of_ne storage
        { storage with cells := storage.cells.set dst.toNat (some entry) }
        dst index entry (by simp [mergeHiTempWrite?, hdst, hbound])
      intro heq
      subst index
      rcases houtside with hbefore | hafter <;> simp at *
    · simp at hwrite
  · simp at hwrite

/-- A successful one-cell main-to-temporary copy leaves main data unchanged. -/
theorem mergeHiCopyDataToTemp_data_eq_of_eq_some
    (state state' : MergeState kappa nu) (dst src : Int)
    (hcopy : mergeHiCopyDataToTemp? state dst src = some state') :
    state'.data = state.data := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, _hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨storage, _hwrite, hfinal⟩
  injection hfinal with hfinal
  subst state'
  rfl

/-- Exact temporary frame for a successful one-cell main-to-temporary copy. -/
theorem mergeHiCopyDataToTemp_tempFrame_of_eq_some
    (state state' : MergeState kappa nu) (dst src : Int)
    (hcopy : mergeHiCopyDataToTemp? state dst src = some state') :
    TempStorage.ReadFrameInt state.a state'.a dst 1 := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, _hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨storage, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst state'
  exact mergeHiTempWrite_readFrameInt_of_eq_some state.a storage dst entry hwrite

/-- A successful one-cell temporary-to-main copy writes exactly the entry in
the input temporary snapshot. -/
theorem mergeHiCopyTempToData_read_destination_of_eq_some
    (state state' : MergeState kappa nu) (dst src : Int)
    (hcopy : mergeHiCopyTempToData? state dst src = some state') :
    state'.data.read? dst = mergeHiTempRead? state.a src := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨data, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst state'
  exact (SortSlice.write_read_self_of_eq_some state.data data dst entry
    hwrite).trans hread.symm

/-- A successful one-cell temporary-to-main copy preserves every other main
entry. -/
theorem mergeHiCopyTempToData_read_ne_of_eq_some
    (state state' : MergeState kappa nu) (dst src index : Int)
    (hcopy : mergeHiCopyTempToData? state dst src = some state')
    (hne : index ≠ dst) :
    state'.data.read? index = state.data.read? index := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, _hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨data, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst state'
  exact SortSlice.write_read_ne_of_eq_some state.data data dst index entry
    hwrite hne

/-- A successful one-cell temporary-to-main copy is framed by its main
destination and leaves temporary storage unchanged. -/
theorem mergeHiCopyTempToData_frame_of_eq_some
    (state state' : MergeState kappa nu) (dst src : Int)
    (hcopy : mergeHiCopyTempToData? state dst src = some state') :
    state'.a = state.a ∧ SortSlice.ReadFrame state.data state'.data dst 1 := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, _hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨data, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst state'
  exact ⟨rfl, SortSlice.write_readFrame_of_eq_some state.data data dst entry
    hwrite⟩

/-! ## `merge_hi` bulk temporary movement -/

private theorem mergeHiMemcpyDataToTemp_spec
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    state'.data = state.data ∧
      (∀ i, i < count →
        mergeHiTempRead? state'.a (dst + Int.ofNat i) =
          state.data.read? (src + Int.ofNat i)) ∧
      TempStorage.ReadFrameInt state.a state'.a dst count := by
  induction count generalizing state state' dst src with
  | zero =>
      simp only [mergeHiMemcpyDataToTemp?] at hcopy
      injection hcopy with hcopy
      subst state'
      refine ⟨rfl, ?_, ?_⟩
      · intro i hi
        omega
      · exact
          { cellsSize := rfl
            backing := rfl
            hasValues := rfl
            read_eq := fun _ _ => rfl }
  | succ count ih =>
      rw [mergeHiMemcpyDataToTemp?] at hcopy
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨afterHead, hhead, htail⟩
      rcases ih afterHead state' (dst + 1) (src + 1) htail with
        ⟨hdataTail, htailCopy, htailFrame⟩
      have hdataHead :=
        mergeHiCopyDataToTemp_data_eq_of_eq_some state afterHead dst src hhead
      have hheadFrame :=
        mergeHiCopyDataToTemp_tempFrame_of_eq_some state afterHead dst src hhead
      refine ⟨hdataTail.trans hdataHead, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            have hpreserved := htailFrame.read_eq dst (Or.inl (by omega))
            rcases mergeHiCopyDataToTemp_read_eq_some state afterHead dst src
                hhead with ⟨entry, hsource, hwritten⟩
            simpa using hpreserved.trans (hwritten.trans hsource.symm)
        | succ i =>
            have hiTail : i < count := by omega
            have hcopied := htailCopy i hiTail
            calc
              mergeHiTempRead? state'.a (dst + Int.ofNat (Nat.succ i)) =
                  mergeHiTempRead? state'.a (dst + 1 + Int.ofNat i) := by
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
              _ = afterHead.data.read? (src + 1 + Int.ofNat i) := hcopied
              _ = state.data.read? (src + Int.ofNat (Nat.succ i)) := by
                    rw [hdataHead]
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
      · refine
          { cellsSize := hheadFrame.cellsSize.trans htailFrame.cellsSize
            backing := hheadFrame.backing.trans htailFrame.backing
            hasValues := hheadFrame.hasValues.trans htailFrame.hasValues
            read_eq := ?_ }
        intro index houtside
        have htailOutside :
            index < dst + 1 ∨ (dst + 1) + Int.ofNat count ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        exact (htailFrame.read_eq index htailOutside).trans
          (hheadFrame.read_eq index hheadOutside)

/-- A successful `merge_hi` main-to-temporary block copy leaves main data
unchanged. -/
theorem mergeHiMemcpyDataToTemp_data_eq_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    state'.data = state.data :=
  (mergeHiMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).1

/-- A successful `merge_hi` main-to-temporary block copy materializes exactly
the original main-data source range. -/
theorem mergeHiMemcpyDataToTemp_read_range_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some state')
    (i : Nat) (hi : i < count) :
    mergeHiTempRead? state'.a (dst + Int.ofNat i) =
      state.data.read? (src + Int.ofNat i) :=
  (mergeHiMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

/-- Exact temporary frame for a successful `merge_hi` main-to-temporary block
copy. -/
theorem mergeHiMemcpyDataToTemp_tempFrame_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyDataToTemp? site hDirection count state dst src =
      some state') :
    TempStorage.ReadFrameInt state.a state'.a dst count :=
  (mergeHiMemcpyDataToTemp_spec site hDirection count state state' dst src
    hcopy).2.2

private theorem mergeHiMemcpyTempToData_spec
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some state') :
    state'.a = state.a ∧
      (∀ i, i < count →
        state'.data.read? (dst + Int.ofNat i) =
          mergeHiTempRead? state.a (src + Int.ofNat i)) ∧
      SortSlice.ReadFrame state.data state'.data dst count := by
  induction count generalizing state state' dst src with
  | zero =>
      simp only [mergeHiMemcpyTempToData?] at hcopy
      injection hcopy with hcopy
      subst state'
      refine ⟨rfl, ?_, ⟨rfl, ?_⟩⟩
      · intro i hi
        omega
      · intro index _houtside
        rfl
  | succ count ih =>
      rw [mergeHiMemcpyTempToData?] at hcopy
      rcases Option.bind_eq_some_iff.mp hcopy with ⟨afterHead, hhead, htail⟩
      rcases ih afterHead state' (dst + 1) (src + 1) htail with
        ⟨htempTail, htailCopy, htailFrame⟩
      rcases mergeHiCopyTempToData_frame_of_eq_some state afterHead dst src
          hhead with ⟨htempHead, hheadFrame⟩
      refine ⟨htempTail.trans htempHead, ?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            have hpreserved := htailFrame.2 dst (Or.inl (by omega))
            have hwritten := mergeHiCopyTempToData_read_destination_of_eq_some
              state afterHead dst src hhead
            simpa using hpreserved.trans hwritten
        | succ i =>
            have hiTail : i < count := by omega
            have hcopied := htailCopy i hiTail
            calc
              state'.data.read? (dst + Int.ofNat (Nat.succ i)) =
                  state'.data.read? (dst + 1 + Int.ofNat i) := by
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
              _ = mergeHiTempRead? afterHead.a (src + 1 + Int.ofNat i) :=
                    hcopied
              _ = mergeHiTempRead? state.a (src + Int.ofNat (Nat.succ i)) := by
                    rw [htempHead]
                    congr 1
                    simp only [Int.ofNat_eq_natCast]
                    omega
      · refine ⟨hheadFrame.1.trans htailFrame.1, ?_⟩
        intro index houtside
        have htailOutside :
            index < dst + 1 ∨ (dst + 1) + Int.ofNat count ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        have hheadOutside : index < dst ∨ dst + 1 ≤ index := by
          rcases houtside with hbefore | hafter
          · exact Or.inl hbefore
          · exact Or.inr (by
              simp only [Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one] at hafter ⊢
              omega)
        exact (htailFrame.2 index htailOutside).trans
          (hheadFrame.2 index hheadOutside)

/-- A successful `merge_hi` temporary-to-main block copy leaves temporary
storage unchanged. -/
theorem mergeHiMemcpyTempToData_temp_eq_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some state') :
    state'.a = state.a :=
  (mergeHiMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).1

/-- A successful `merge_hi` temporary-to-main block copy writes exactly the
input temporary snapshot into its main destination range. -/
theorem mergeHiMemcpyTempToData_read_range_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some state')
    (i : Nat) (hi : i < count) :
    state'.data.read? (dst + Int.ofNat i) =
      mergeHiTempRead? state.a (src + Int.ofNat i) :=
  (mergeHiMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.1 i hi

/-- Signed pointwise frame for a successful `merge_hi` temporary-to-main
block copy. -/
theorem mergeHiMemcpyTempToData_readFrame_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some state') :
    SortSlice.ReadFrame state.data state'.data dst count :=
  (mergeHiMemcpyTempToData_spec site hDirection count state state' dst src
    hcopy).2.2

private theorem mergeHiCopyTempToData_dst_nonnegative_of_eq_some
    (state state' : MergeState kappa nu) (dst src : Int)
    (hcopy : mergeHiCopyTempToData? state dst src = some state') :
    0 ≤ dst := by
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, _hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨data, hwrite, _hfinal⟩
  exact (SortSlice.write_eq_some_spec state.data data dst entry hwrite).1

/-- Natural-indexed external frame for a successful `merge_hi`
temporary-to-main block copy. -/
theorem mergeHiMemcpyTempToData_equalOutsideRange_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst src : Int)
    (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst src =
      some state') :
    SortSlice.EqualOutsideRange state.data state'.data dst.toNat count := by
  cases count with
  | zero =>
      simp only [mergeHiMemcpyTempToData?] at hcopy
      injection hcopy with hcopy
      subst state'
      exact SortSlice.EqualOutsideRange.refl state.data dst.toNat 0
  | succ count =>
      have hcopyHead := hcopy
      rw [mergeHiMemcpyTempToData?] at hcopyHead
      rcases Option.bind_eq_some_iff.mp hcopyHead with
        ⟨afterHead, hhead, _htail⟩
      have hdst := mergeHiCopyTempToData_dst_nonnegative_of_eq_some
        state afterHead dst src hhead
      have hcast : Int.ofNat dst.toNat = dst := Int.toNat_of_nonneg hdst
      have hframe := mergeHiMemcpyTempToData_readFrame_of_eq_some site hDirection
        (count + 1) state state' dst src hcopy
      rw [← hcast] at hframe
      exact hframe.equalOutsideRange_ofNat

/-! ## Tagged same-store and decrementing wrappers -/

/-- The site-tagged merge memmove has the same exact snapshot semantics as
the underlying shared-store primitive. -/
theorem mergeDataMemmove_copiesRange_of_eq_some
    (site : MergeMemmoveCallsite) (data updated : SortSlice kappa nu)
    (dst src : Int) (count : Nat)
    (hmove : mergeDataMemmove? site data dst src count = some updated) :
    SortSlice.CopiesRange data updated dst src count :=
  SortSlice.memmove_copiesRange_of_eq_some data updated dst src count hmove

/-- Signed external frame for a site-tagged merge memmove. -/
theorem mergeDataMemmove_readFrame_of_eq_some
    (site : MergeMemmoveCallsite) (data updated : SortSlice kappa nu)
    (dst src : Int) (count : Nat)
    (hmove : mergeDataMemmove? site data dst src count = some updated) :
    SortSlice.ReadFrame data updated dst count :=
  SortSlice.memmove_readFrame_of_eq_some data updated dst src count hmove

/-- Natural-indexed external frame for a site-tagged merge memmove. -/
theorem mergeDataMemmove_equalOutsideRange_of_eq_some
    (site : MergeMemmoveCallsite) (data updated : SortSlice kappa nu)
    (dst src : Int) (count : Nat)
    (hmove : mergeDataMemmove? site data dst src count = some updated) :
    SortSlice.EqualOutsideRange data updated dst.toNat count :=
  SortSlice.memmove_equalOutsideRange_of_eq_some data updated dst src count hmove

/-- Exact whole-entry and cursor effect of the decrementing shared-main copy
used by `merge_hi`. -/
theorem mergeHiCopyDataDecr_spec_of_eq_some
    (state : MergeState kappa nu) (dst src : Int)
    (result : MergeHiDataCursorResult kappa nu)
    (hcopy : mergeHiCopyDataDecr? state dst src = some result) :
    result.dst = dst - 1 ∧
      result.src = src - 1 ∧
      result.state.a = state.a ∧
      result.state.data.read? dst = state.data.read? src ∧
      SortSlice.ReadFrame state.data result.state.data dst 1 := by
  rw [mergeHiCopyDataDecr?] at hcopy
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨copied, hcopied, hfinal⟩
  rw [SortSlice.copyDecr?, SortSlice.copyFromDecr?] at hcopied
  rcases Option.bind_eq_some_iff.mp hcopied with ⟨data, hsingle, hcursor⟩
  rw [SortSlice.copyFrom?] at hsingle
  rcases Option.bind_eq_some_iff.mp hsingle with ⟨entry, hread, hwrite⟩
  injection hcursor with hcursor
  subst copied
  injection hfinal with hfinal
  subst result
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩
  · exact (SortSlice.write_read_self_of_eq_some state.data data dst entry
      hwrite).trans hread.symm
  · exact SortSlice.write_readFrame_of_eq_some state.data data dst entry hwrite

/-- Exact whole-entry and cursor effect of the decrementing temporary-to-main
copy used by `merge_hi`. -/
theorem mergeHiCopyTempDecr_spec_of_eq_some
    (state : MergeState kappa nu) (dst src : Int)
    (result : MergeHiDataCursorResult kappa nu)
    (hcopy : mergeHiCopyTempDecr? state dst src = some result) :
    result.dst = dst - 1 ∧
      result.src = src - 1 ∧
      result.state.a = state.a ∧
      result.state.data.read? dst = mergeHiTempRead? state.a src ∧
      SortSlice.ReadFrame state.data result.state.data dst 1 := by
  rw [mergeHiCopyTempDecr?] at hcopy
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨state', hcell, hfinal⟩
  injection hfinal with hfinal
  subst result
  rcases mergeHiCopyTempToData_frame_of_eq_some state state' dst src hcell with
    ⟨htemp, hframe⟩
  exact ⟨rfl, rfl, htemp,
    mergeHiCopyTempToData_read_destination_of_eq_some state state' dst src hcell,
    hframe⟩

/-! ## Exact materialization consequences -/

/-! ## `merge_lo` one-cell cursor wrappers -/

/-- Exact whole-entry and cursor effect of the incrementing temporary-to-main
cell copy used by ordinary `merge_lo` and the end of a gallop round. -/
theorem mergeLoCopyAIncr_spec_of_eq_some
    (machine next : MergeLoMachine kappa nu)
    (hcopy : mergeLoCopyAIncr? machine = some next) :
    next.dest = machine.dest + 1 ∧
      next.aPos = machine.aPos + 1 ∧
      next.bPos = machine.bPos ∧
      next.na = machine.na - 1 ∧
      next.nb = machine.nb ∧
      next.state.key_compare = machine.state.key_compare ∧
      next.state.a = machine.state.a ∧
      next.state.data.read? machine.dest =
        mergeLoTempRead? machine.state.a machine.aPos ∧
      SortSlice.ReadFrame machine.state.data next.state.data machine.dest 1 := by
  rw [mergeLoCopyAIncr?] at hcopy
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨data, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst next
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (SortSlice.write_read_self_of_eq_some machine.state.data data
      machine.dest entry hwrite).trans hread.symm
  · exact SortSlice.write_readFrame_of_eq_some machine.state.data data
      machine.dest entry hwrite

/-- Exact snapshot and cursor effect of the incrementing same-store B copy.
The destination reads the pre-write source even when the two cells alias. -/
theorem mergeLoCopyBIncr_spec_of_eq_some
    (machine next : MergeLoMachine kappa nu)
    (hcopy : mergeLoCopyBIncr? machine = some next) :
    next.dest = machine.dest + 1 ∧
      next.aPos = machine.aPos ∧
      next.bPos = machine.bPos + 1 ∧
      next.na = machine.na ∧
      next.nb = machine.nb - 1 ∧
      next.state.key_compare = machine.state.key_compare ∧
      next.state.a = machine.state.a ∧
      next.state.data.read? machine.dest =
        machine.state.data.read? machine.bPos ∧
      SortSlice.ReadFrame machine.state.data next.state.data machine.dest 1 := by
  rw [mergeLoCopyBIncr?] at hcopy
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨entry, hread, hcopy⟩
  rcases Option.bind_eq_some_iff.mp hcopy with ⟨data, hwrite, hfinal⟩
  injection hfinal with hfinal
  subst next
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · exact (SortSlice.write_read_self_of_eq_some machine.state.data data
      machine.dest entry hwrite).trans hread.symm
  · exact SortSlice.write_readFrame_of_eq_some machine.state.data data
      machine.dest entry hwrite

/-- Materializing the destination of a successful `merge_lo` initial-style
copy yields exactly the original main source snapshot. -/
theorem mergeLoMemcpyDataToTemp_materialized_source_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .temporary, source := .main })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Nat) (src : Int) (materialized : SortSlice kappa nu)
    (hcopy : mergeLoMemcpyDataToTemp? site hDirection count state dst src =
      some state')
    (hmaterialized : mergeLoTempRun? state'.a dst count = some materialized) :
    materialized.entries.size = count ∧
      ∀ i, i < count →
        materialized.entries[i]? =
          state.data.read? (src + Int.ofNat i) := by
  rcases mergeLoTempRun_cells_of_eq_some state'.a dst count materialized
      hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeLoMemcpyDataToTemp_read_range_of_eq_some site hDirection
    count state state' dst src hcopy i hi
  calc
    materialized.entries[i]? = state'.a.cells[dst + i]?.bind id :=
      (hcells i hi).symm
    _ = mergeLoTempRead? state'.a (dst + i) := rfl
    _ = state.data.read? (src + Int.ofNat i) := hcopied

/-- If the temporary source block is materialized, a successful `merge_lo`
copy writes that exact whole-entry array to its main destination. -/
theorem mergeLoMemcpyTempToData_materialized_source_of_eq_some
    (site : MergeLoMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count : Nat) (state state' : MergeState kappa nu)
    (dst : Int) (src : Nat) (materialized : SortSlice kappa nu)
    (hcopy : mergeLoMemcpyTempToData? site hDirection count state dst src =
      some state')
    (hmaterialized : mergeLoTempRun? state.a src count = some materialized) :
    materialized.entries.size = count ∧
      ∀ i, i < count →
        state'.data.read? (dst + Int.ofNat i) =
          materialized.entries[i]? := by
  rcases mergeLoTempRun_cells_of_eq_some state.a src count materialized
      hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeLoMemcpyTempToData_read_range_of_eq_some site hDirection
    count state state' dst src hcopy i hi
  calc
    state'.data.read? (dst + Int.ofNat i) =
        mergeLoTempRead? state.a (src + i) := hcopied
    _ = state.a.cells[src + i]?.bind id := rfl
    _ = materialized.entries[i]? := hcells i hi

/-- Materializing the prefix produced by the pinned `merge_hi` initial copy
yields exactly the original main source snapshot. -/
theorem mergeHiInitialDataToTemp_materialized_source_of_eq_some
    (count : Nat) (state state' : MergeState kappa nu) (src : Int)
    (materialized : SortSlice kappa nu)
    (hcopy : mergeHiMemcpyDataToTemp? .initialDataToTemp rfl count state 0 src =
      some state')
    (hmaterialized : initializedTempPrefix? state'.a count = some materialized) :
    materialized.entries.size = count ∧
      ∀ i, i < count →
        materialized.entries[i]? =
          state.data.read? (src + Int.ofNat i) := by
  rcases initializedTempPrefix_cells_of_eq_some state'.a count materialized
      hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeHiMemcpyDataToTemp_read_range_of_eq_some
    .initialDataToTemp rfl count state state' 0 src hcopy i hi
  calc
    materialized.entries[i]? = state'.a.cells[i]?.bind id :=
      (hcells i hi).symm
    _ = mergeHiTempRead? state'.a (Int.ofNat i) :=
      (mergeHiTempRead_ofNat state'.a i).symm
    _ = state.data.read? (src + Int.ofNat i) := by simpa using hcopied

/-- Relative to a materialized temporary prefix, a successful `merge_hi`
temporary-to-main block copy writes the exact selected temporary subrange. -/
theorem mergeHiMemcpyTempToData_materialized_source_of_eq_some
    (site : MergeHiMemcpyCallsite)
    (hDirection : site.backings =
      { destination := .main, source := .temporary })
    (count tempCount : Nat) (state state' : MergeState kappa nu)
    (dst tempSrc : Int) (materialized : SortSlice kappa nu)
    (hcopy : mergeHiMemcpyTempToData? site hDirection count state dst tempSrc =
      some state')
    (hmaterialized : initializedTempPrefix? state.a tempCount = some materialized)
    (htempSrc : 0 ≤ tempSrc)
    (hcontained : tempSrc.toNat + count ≤ tempCount) :
    materialized.entries.size = tempCount ∧
      ∀ i, i < count →
        state'.data.read? (dst + Int.ofNat i) =
          materialized.entries[tempSrc.toNat + i]? := by
  rcases initializedTempPrefix_cells_of_eq_some state.a tempCount materialized
      hmaterialized with ⟨hsize, hcells⟩
  refine ⟨hsize, ?_⟩
  intro i hi
  have hcopied := mergeHiMemcpyTempToData_read_range_of_eq_some site hDirection
    count state state' dst tempSrc hcopy i hi
  have hindex :
      tempSrc + Int.ofNat i = Int.ofNat (tempSrc.toNat + i) := by
    rw [← Int.toNat_of_nonneg htempSrc]
    simp
  calc
    state'.data.read? (dst + Int.ofNat i) =
        mergeHiTempRead? state.a (tempSrc + Int.ofNat i) := hcopied
    _ = state.a.cells[tempSrc.toNat + i]?.bind id := by
      rw [hindex, mergeHiTempRead_ofNat]
    _ = materialized.entries[tempSrc.toNat + i]? :=
      hcells (tempSrc.toNat + i) (by omega)

/-! ## Executable overlap regression -/

private def mergeMovementOverlapInput : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := some 10 },
        { key := 2, value := some 20 },
        { key := 3, value := some 30 },
        { key := 4, value := some 40 },
        { key := 5, value := some 50 }] }

/-- A rightward overlapping merge move reads every entry from the pre-move
snapshot; an increasing-address implementation would not produce this array. -/
theorem mergeDataMemmove_overlap_snapshot_regression :
    mergeDataMemmove? .loCopyBTail mergeMovementOverlapInput 1 0 4 =
      some
        { entries :=
            #[{ key := 1, value := some 10 },
              { key := 1, value := some 10 },
              { key := 2, value := some 20 },
              { key := 3, value := some 30 },
              { key := 4, value := some 40 }] } := by
  decide

end CPythonListsort
