/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.TempStorageInvariant

/-!
# `merge_init` temporary-storage initialization

This is the storage projection of CPython's `merge_init`.  Fresh modeled cells
are uninitialized (`none`).  In keyed mode each logical entry consumes two raw
pointer slots from the 256-slot inline buffer; in unkeyed mode it consumes one.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Observable temporary-storage fields initialized by `merge_init`. -/
structure MergeInitTempResult (κ : Type u) (ν : Type v) where
  storage : TempStorage κ ν
  alloced : PySSize
  deriving DecidableEq, Repr

/-- Inline capacity selected by the storage part of `merge_init`, retaining the
signed 64-bit addition, division, and comparison performed by C. -/
def mergeInitTempCapacity (listSize : PySSize) (hasKeyfunc : Bool) : PySSize :=
  if hasKeyfunc then
    let requested := (listSize + 1).sdiv 2
    let inlineCap : PySSize := BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)
    if inlineCap.slt requested then inlineCap else requested
  else
    BitVec.ofNat 64 MERGESTATE_TEMP_SIZE

/-- Temporary-storage portion of pinned CPython `merge_init`. -/
def mergeInitTemp (listSize : PySSize) (hasKeyfunc : Bool) :
    MergeInitTempResult κ ν :=
  let capacity := mergeInitTempCapacity listSize hasKeyfunc
  { storage :=
      { cells := Array.replicate capacity.toNat none
        backing := .inline
        hasValues := hasKeyfunc }
    alloced := capacity }

/-- On admitted list sizes, the signed word computation agrees with the clean
natural-number formula used in the roadmap statement. -/
theorem mergeInitTempCapacity_keyed_toNat (listSize : PySSize)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    (mergeInitTempCapacity listSize true).toNat =
      min ((listSize.toNat + 1) / 2) 128 := by
  norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hmax
  let requested : PySSize := (listSize + 1).sdiv 2
  have hOneNat : (1 : PySSize).toNat = 1 := by rfl
  have hTwoNat : (2 : PySSize).toNat = 2 := by rfl
  have hListSucc : listSize.toNat + 1 < 2 ^ 63 := by
    exact lt_of_le_of_lt (Nat.add_le_add_right hmax 1) (by norm_num)
  have hAddNat : (listSize + 1).toNat = listSize.toNat + 1 := by
    rw [BitVec.toNat_add, hOneNat,
      Nat.mod_eq_of_lt (lt_trans hListSucc (by norm_num : 2 ^ 63 < 2 ^ 64))]
  have hAddMsb : (listSize + 1).msb = false := by
    rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, hAddNat]
    exact Nat.not_le_of_lt hListSucc
  have hTwoMsb : (2 : PySSize).msb = false := by decide
  have hRequestedNat : requested.toNat = (listSize.toNat + 1) / 2 := by
    rw [show requested = (listSize + 1).sdiv 2 from rfl, BitVec.toNat_sdiv]
    simp only [hAddMsb, hTwoMsb]
    change (listSize + 1).toNat / (2 : PySSize).toNat = _
    rw [hAddNat, hTwoNat]
  have hRequestedLt : requested.toNat < 2 ^ 63 := by
    rw [hRequestedNat]
    exact lt_of_le_of_lt (Nat.div_le_self _ _) hListSucc
  have hRequestedMsb : requested.msb = false := by
    rw [BitVec.msb_eq_decide, decide_eq_false_iff_not]
    exact Nat.not_le_of_lt hRequestedLt
  have hCapNat :
      (BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)).toNat = 128 := by
    norm_num [MERGESTATE_TEMP_SIZE]
  have hCapMsb :
      (BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)).msb = false := by
    rw [BitVec.msb_eq_decide, decide_eq_false_iff_not, hCapNat]
    norm_num
  simp only [mergeInitTempCapacity]
  change (if (BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2)).slt requested then
      BitVec.ofNat 64 (MERGESTATE_TEMP_SIZE / 2) else requested).toNat = _
  rw [BitVec.slt_eq_ult_of_msb_eq (hCapMsb.trans hRequestedMsb.symm)]
  simp only [BitVec.ult, decide_eq_true_eq]
  split <;> rename_i hComparison
  · rw [hCapNat, Nat.min_eq_right]
    rw [hRequestedNat] at hComparison
    omega
  · rw [hRequestedNat, Nat.min_eq_left]
    rw [hCapNat, hRequestedNat] at hComparison
    omega

@[simp]
theorem mergeInitTemp_keyed_alloced (listSize : PySSize)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    (mergeInitTemp (κ := κ) (ν := ν) listSize true).alloced.toNat =
      min ((listSize.toNat + 1) / 2) 128 := by
  simpa only [mergeInitTemp] using mergeInitTempCapacity_keyed_toNat listSize hmax

@[simp]
theorem mergeInitTemp_unkeyed_alloced (listSize : PySSize) :
    (mergeInitTemp (κ := κ) (ν := ν) listSize false).alloced.toNat = 256 := by
  simp [mergeInitTemp, mergeInitTempCapacity, MERGESTATE_TEMP_SIZE]

@[simp]
theorem mergeInitTemp_keyed_shape (listSize : PySSize)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    let init := mergeInitTemp (κ := κ) (ν := ν) listSize true
    init.storage.backing = .inline ∧
      init.storage.hasValues = true ∧
      init.storage.cells.size = min ((listSize.toNat + 1) / 2) 128 := by
  simp only [mergeInitTemp, Array.size_replicate, true_and]
  exact mergeInitTempCapacity_keyed_toNat listSize hmax

@[simp]
theorem mergeInitTemp_unkeyed_shape (listSize : PySSize) :
    let init := mergeInitTemp (κ := κ) (ν := ν) listSize false
    init.storage.backing = .inline ∧
      init.storage.hasValues = false ∧
      init.storage.cells.size = 256 := by
  simp [mergeInitTemp, mergeInitTempCapacity, MERGESTATE_TEMP_SIZE]

/-- Both constructor branches establish the temporary-storage invariant. -/
@[simp]
theorem mergeInitTemp_inv (listSize : PySSize) (hasKeyfunc : Bool)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    TempStorageInv
      (mergeInitTemp (κ := κ) (ν := ν) listSize hasKeyfunc).storage
      (mergeInitTemp (κ := κ) (ν := ν) listSize hasKeyfunc).alloced := by
  cases hasKeyfunc
  · simp [mergeInitTemp, mergeInitTempCapacity, TempStorageInv,
      TempStorage.multiplier, MERGESTATE_TEMP_SIZE]
  · have hCapacity := mergeInitTempCapacity_keyed_toNat listSize hmax
    simp [mergeInitTemp, TempStorageInv, TempStorage.multiplier, hCapacity,
      MERGESTATE_TEMP_SIZE]
    omega

end CPythonListsort
