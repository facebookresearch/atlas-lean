/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.BitVec

/-!
# CPython finite-width words

The listsort transcription represents every non-pointer `Py_ssize_t` field by
an explicit 64-bit word. Signed operations use `BitVec.slt` and
`BitVec.sle`, together with `BitVec.sshiftRight`; unsigned projections appear
only where C performs an unsigned cast or in specifications and proofs.
-/

namespace CPythonListsort

/-- The fixed-width representation of CPython's `Py_ssize_t` in this project. -/
abbrev PySSize := BitVec 64

/-- `PY_SSIZE_T_MAX` for the selected 64-bit model. -/
def PY_SSIZE_T_MAX : Nat := 2 ^ 63 - 1

/-- Size in bytes of `PyObject *` on the selected 64-bit CPython platform. -/
def PY_OBJECT_PTR_BYTES : Nat := 8

/-- Largest list length admitted by CPython's pointer-array allocation guard. -/
def PY_LIST_MAX : Nat := PY_SSIZE_T_MAX / PY_OBJECT_PTR_BYTES

/-- The `MAX_MINRUN` constant in the pinned CPython source. -/
def MAX_MINRUN : PySSize := 64

/-- The `MAX_MERGE_PENDING` constant on the selected 64-bit platform. -/
def MAX_MERGE_PENDING : Nat := 64

/-- A word denotes a nonnegative signed `Py_ssize_t`. -/
def PySSize.Nonnegative (x : PySSize) : Prop := x.msb = false

end CPythonListsort
