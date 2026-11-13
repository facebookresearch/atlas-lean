/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Policy.PendingLayout
import Code.Transcription.MergeAt
import Mathlib

/-!
# Pending-layout preservation across `merge_at`

The source-admitted `merge_at` operation replaces two adjacent, nonempty
pending runs by their exact union.  Every other pending run is unchanged, and
the resulting stack still tiles the same scanned prefix.  No comparator law is
needed: the stack splice happens before the data merge and is retained by all
observable result paths.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Combining adjacent runs whose total length is signed-representable
preserves exact interval coverage. -/
theorem PendingRunsCover.mergeAdjacent
    {cursor limit : Nat} {before after : List PendingRun}
    {left right : PendingRun}
    (hcover :
      PendingRunsCover cursor limit
        (before ++ left :: right :: after))
    (hfit : left.len.toNat + right.len.toNat < 2 ^ 63) :
    PendingRunsCover cursor limit
      (before ++
        ({ left with len := left.len + right.len } : PendingRun) :: after) := by
  have hfit64 : left.len.toNat + right.len.toNat < 2 ^ 64 := by
    norm_num at hfit ⊢
    omega
  have hsum :
      (left.len + right.len).toNat =
        left.len.toNat + right.len.toNat :=
    BitVec.toNat_add_of_lt hfit64
  have hnonnegative : (left.len + right.len).Nonnegative := by
    rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt, hsum]
    norm_num at hfit ⊢
    omega
  induction before generalizing cursor with
  | nil =>
      simp only [List.nil_append, PendingRunsCover] at hcover ⊢
      rcases hcover with
        ⟨hleftBase, hleftNonnegative, hleftPositive, _, hrightBase,
          _, hrightPositive, hrightEnd, hafter⟩
      have hend :
          ({ left with len := left.len + right.len } : PendingRun).endIndex =
            right.endIndex := by
        simp only [PendingRun.endIndex]
        simp only [hsum]
        rw [hrightBase]
        simp only [PendingRun.endIndex]
        omega
      exact
        ⟨hleftBase, hnonnegative, by simp only [hsum]; omega,
          hend.le.trans hrightEnd, hend.symm ▸ hafter⟩
  | cons run before ih =>
      simp only [List.cons_append, PendingRunsCover] at hcover ⊢
      exact
        ⟨hcover.1, hcover.2.1, hcover.2.2.1, hcover.2.2.2.1,
          ih hcover.2.2.2.2⟩

/-- Any selected adjacent pair in a covered run list is nonempty and
contiguous. -/
theorem PendingRunsCover.pair_spec
    {cursor limit : Nat} {before after : List PendingRun}
    {left right : PendingRun}
    (hcover :
      PendingRunsCover cursor limit
        (before ++ left :: right :: after)) :
    left.len.Nonnegative ∧ 0 < left.len.toNat ∧
      right.len.Nonnegative ∧ 0 < right.len.toNat ∧
      left.endIndex = right.base := by
  induction before generalizing cursor with
  | nil =>
      simp only [List.nil_append, PendingRunsCover] at hcover
      rcases hcover with
        ⟨_, hleftNonnegative, hleftPositive, _, hrightBase,
          hrightNonnegative, hrightPositive, _, _⟩
      exact
        ⟨hleftNonnegative, hleftPositive, hrightNonnegative,
          hrightPositive, hrightBase.symm⟩
  | cons run before ih =>
      simp only [List.cons_append, PendingRunsCover] at hcover
      exact ih hcover.2.2.2.2

/-- A pair appearing in a valid pending layout has a sum that is representable
as a nonnegative signed `Py_ssize_t`. -/
theorem PendingLayout.pairFits
    {state : MergeState κ ν} {scanned : Nat}
    {before after : List PendingRun} {left right : PendingRun}
    (hlayout : PendingLayout state scanned)
    (hsplit :
      state.pending.toList = before ++ left :: right :: after) :
    left.len.toNat + right.len.toNat < 2 ^ 63 := by
  rcases hlayout with ⟨hlistNonnegative, _, hscanned, hcover⟩
  have htotal := hcover.totalLength
  rw [hsplit] at htotal
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons] at htotal
  have hpairLe : left.len.toNat + right.len.toNat ≤ scanned := by
    omega
  have hlistLt : state.listlen.toNat < 2 ^ 63 := by
    rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt] at hlistNonnegative
    norm_num at hlistNonnegative ⊢
    omega
  omega

/-- Setting an indexed entry and erasing its immediate successor implements
the list splice that replaces an adjacent pair by one value. -/
theorem Array.toList_set_eraseIdx_adjacent
    {α : Type u} {xs : Array α} {i : Nat}
    {before after : List α} {left right replacement : α}
    (hsplit : xs.toList = before ++ left :: right :: after)
    (hbefore : before.length = i) :
    ((xs.setIfInBounds i replacement).eraseIdxIfInBounds (i + 1)).toList =
      before ++ replacement :: after := by
  rw [Array.toList_eraseIdxIfInBounds, Array.toList_setIfInBounds]
  rw [hsplit]
  subst i
  rw [List.set_append_right before.length replacement (by omega)]
  simp only [Nat.sub_self, List.set_cons_zero]
  rw [List.eraseIdx_append_of_length_le (by omega)]
  simp

/-- Structural state fields plus the exact adjacent-pair splice are enough to
transport `PendingLayout`; merge data and comparator behavior are irrelevant. -/
private theorem pendingLayout_after_mergeAdjacent
    (state state' : MergeState κ ν) (scanned : Nat)
    (before after : List PendingRun) (left right : PendingRun)
    (hlayout : PendingLayout state scanned)
    (hsplit :
      state.pending.toList = before ++ left :: right :: after)
    (hlistlen : state'.listlen = state.listlen)
    (hbasekeys : state'.basekeys = state.basekeys)
    (hdataSize : state'.data.entries.size = state.data.entries.size)
    (hpending :
      state'.pending.toList =
        before ++
          ({ left with len := left.len + right.len } : PendingRun) :: after) :
    PendingLayout state' scanned := by
  rcases hlayout with ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩
  have hfit : left.len.toNat + right.len.toNat < 2 ^ 63 :=
    PendingLayout.pairFits
      ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩ hsplit
  rw [hsplit] at hcover
  have hmerged := hcover.mergeAdjacent hfit
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [hlistlen] using hlistNonnegative
  · simpa only [hbasekeys, hlistlen, hdataSize] using hdataBound
  · simpa only [hlistlen] using hscanned
  · simpa only [hbasekeys, hpending] using hmerged

/-- Every source-admitted `merge_at` result replaces exactly the selected
adjacent pair by its nonempty, signed-representable union, preserves every
unselected pending run, and preserves the layout of the same scanned prefix.

The theorem assumes no transitivity, consistency, or other comparator law. -/
theorem mergeAt_preserves_pendingLayout
    (state : MergeState κ ν) (scanned i : Nat)
    (result : MergeAtResult κ ν)
    (hlayout : PendingLayout state scanned)
    (hmerge : mergeAt? state i = some result) :
    ∃ before left right after,
      before.length = i ∧
      state.pending.toList = before ++ left :: right :: after ∧
      result.state.pending.toList =
        before ++
          ({ left with len := left.len + right.len } : PendingRun) :: after ∧
      left.len.Nonnegative ∧
      0 < left.len.toNat ∧
      right.len.Nonnegative ∧
      0 < right.len.toNat ∧
      left.endIndex = right.base ∧
      (left.len + right.len).toNat =
        left.len.toNat + right.len.toNat ∧
      PendingLayout result.state scanned := by
  rcases mergeAt_pending_frame_of_eq_some state i result hmerge with
    ⟨left, right, hleft, hright, hlistlen, hbasekeys, hdataSize, hpending⟩
  rcases Array.exists_pair_split_of_getElem?_eq_some hleft hright with
    ⟨before, after, hbefore, hsplit⟩
  have hresultPending :
      result.state.pending.toList =
        before ++
          ({ left with len := left.len + right.len } : PendingRun) :: after := by
    calc
      result.state.pending.toList =
          ((state.pending.setIfInBounds i
              ({ left with len := left.len + right.len } : PendingRun))
            |>.eraseIdxIfInBounds (i + 1)).toList :=
        congrArg Array.toList hpending
      _ = before ++
          ({ left with len := left.len + right.len } : PendingRun) :: after :=
        Array.toList_set_eraseIdx_adjacent hsplit hbefore
  have hcover := hlayout.2.2.2
  rw [hsplit] at hcover
  rcases hcover.pair_spec with
    ⟨hleftNonnegative, hleftPositive, hrightNonnegative, hrightPositive,
      hadjacent⟩
  have hfit : left.len.toNat + right.len.toNat < 2 ^ 63 :=
    hlayout.pairFits hsplit
  have hfit64 : left.len.toNat + right.len.toNat < 2 ^ 64 := by
    norm_num at hfit ⊢
    omega
  have hsum :
      (left.len + right.len).toNat =
        left.len.toNat + right.len.toNat :=
    BitVec.toNat_add_of_lt hfit64
  refine
    ⟨before, left, right, after, hbefore, hsplit, hresultPending,
      hleftNonnegative, hleftPositive, hrightNonnegative, hrightPositive,
      hadjacent, hsum, ?_⟩
  exact pendingLayout_after_mergeAdjacent state result.state scanned
    before after left right hlayout hsplit hlistlen hbasekeys hdataSize
    hresultPending

end CPythonListsort
