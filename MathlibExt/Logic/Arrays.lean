/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Logic.Function.Basic

/-!
# Theory of arrays: read-over-write

Arrays are modeled as functions from indices to values, with
`astore` a point update. This module proves the array axioms
used by SMT solvers: reading a stored index returns the stored
value, reading another index is unchanged, and arrays are
extensional. The reduction to EUF built on these axioms is
not formalized here.
-/

@[expose] public section

/-- Array select: read index `i` of array `a` (core of VER-12,
theory of arrays). Arrays are functions; `store` is a point
update. -/
def aselect {I V : Type*} (a : I → V) (i : I) : V := a i

/-- Array store: write `v` at index `i`. -/
noncomputable def astore {I V : Type*} [DecidableEq I]
    (a : I → V) (i : I) (v : V) : I → V :=
  Function.update a i v

/-- Read-over-write, same index. -/
theorem aselect_astore_same {I V : Type*} [DecidableEq I]
    (a : I → V) (i : I) (v : V) :
    aselect (astore a i v) i = v := by
  unfold aselect astore
  exact Function.update_self i v a

/-- Read-over-write, different index. -/
theorem aselect_astore_diff {I V : Type*} [DecidableEq I]
    (a : I → V) (i j : I) (v : V) (h : j ≠ i) :
    aselect (astore a i v) j = aselect a j := by
  unfold aselect astore
  exact Function.update_of_ne h v a

/-- Arrays equal on every index are equal (extensionality). -/
theorem astore_ext {I V : Type*} (a b : I → V)
    (h : ∀ i, aselect a i = aselect b i) : a = b := by
  exact funext h

end
