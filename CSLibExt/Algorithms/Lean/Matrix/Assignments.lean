/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Batteries.Data.Vector.Lemmas

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Prod
import Mathlib.Data.Fintype.Card

/-!
# Counted matrix assignments

The saved-matrix APSP algorithms share these canonical `Vector.ofFnM`
traversals. Each actual scalar assignment has one logical-write tick in the
first cost coordinate; the other two coordinates count no scalar arithmetic.
The original workers and characteristic proofs were authored by Codex and
factored from SlowAPSP without changing their execution bodies.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

private theorem ofFnM_ret {T α : Type*} [AddMonoid T] {n : Nat}
    (f : Fin n → TimeM T α) :
    (Vector.ofFnM f).ret = Vector.ofFn fun i => (f i).ret := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Vector.ofFnM_succ, TimeM.ret_bind, TimeM.ret_pure, ih,
        Vector.ofFn_succ]
      rfl

private theorem ofFnM_time {T α : Type*} [AddCommMonoid T] {n : Nat}
    (f : Fin n → TimeM T α) :
    (Vector.ofFnM f).time = ∑ i, (f i).time := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [Vector.ofFnM_succ, TimeM.time_bind, TimeM.time_pure, add_zero,
        ih, Fin.sum_univ_castSucc]

/-- Copy every saved matrix cell, charging one logical assignment per cell. -/
@[nospecialize] public def copyCells {α : Type*} {n : Nat}
    (input : Vector (Vector α n) n) :
    TimeM (Nat × (Nat × Nat)) (Vector (Vector α n) n) :=
  Vector.ofFnM fun i => Vector.ofFnM fun j => do
    TimeM.tick (1, (0, 0))
    pure ((input.get i).get j)

/-- The counted copy returns the unchanged saved matrix. -/
public theorem copyCells_ret {α : Type*} {n : Nat} (input : Vector (Vector α n) n) :
    (copyCells input).ret = input := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [copyCells, ofFnM_ret, Vector.get_eq_getElem]

/-- A counted square-matrix copy executes exactly `n²` logical assignments. -/
public theorem copyCells_time {α : Type*} {n : Nat} (input : Vector (Vector α n) n) :
    (copyCells input).time = (n ^ 2, (0, 0)) := by
  simp [copyCells, ofFnM_time, pow_two]

/-- Initialize every matrix cell to scalar zero with one assignment tick per cell. -/
@[nospecialize] public def fillCells {α : Type*} [Zero α] (n : Nat) :
    TimeM (Nat × (Nat × Nat)) (Vector (Vector α n) n) :=
  Vector.ofFnM fun (_ : Fin n) => Vector.ofFnM fun (_ : Fin n) => do
    TimeM.tick (1, (0, 0))
    pure 0

/-- The counted initialization returns the constant zero matrix. -/
public theorem fillCells_ret {α : Type*} [Zero α] (n : Nat) :
    (fillCells (α := α) n).ret = Vector.replicate n (Vector.replicate n 0) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [fillCells, ofFnM_ret]

/-- Counted square-matrix initialization executes exactly `n²` assignments. -/
public theorem fillCells_time {α : Type*} [Zero α] (n : Nat) :
    (fillCells (α := α) n).time = (n ^ 2, (0, 0)) := by
  simp [fillCells, ofFnM_time, pow_two]

end Cslib.Algorithms.Lean.Matrix
