/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Recursive
import Mathlib.Tactic.NormNum

/-! Ordinary-import consumers of the four frozen recursive-accumulation names.
Execution/time need only Add/Mul; entry/Matrix correctness needs AddCommMonoid/Mul. -/

set_option autoImplicit false

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.Matrix

universe u

example {α : Type u} [Add α] [Mul α] (k : Nat)
    (A B C : Vector (Vector α (2 ^ k)) (2 ^ k)) :
    TimeM (Nat × Nat) (Vector (Vector α (2 ^ k)) (2 ^ k)) :=
  recursiveMatrixAccumulate k A B C

example {α : Type u} [AddCommMonoid α] [Mul α] (k : Nat)
    (A B C : Vector (Vector α (2 ^ k)) (2 ^ k)) (i j : Fin (2 ^ k)) :
    ((recursiveMatrixAccumulate k A B C).ret.get i).get j =
      (C.get i).get j + ∑ t : Fin (2 ^ k), (A.get i).get t * (B.get t).get j :=
  recursiveMatrixAccumulate_apply k A B C i j

example {α : Type u} [AddCommMonoid α] [Mul α] (k : Nat)
    (A B C : Vector (Vector α (2 ^ k)) (2 ^ k)) :
    _root_.Matrix.of (fun i j => ((recursiveMatrixAccumulate k A B C).ret.get i).get j) =
      _root_.Matrix.of (fun i j => (C.get i).get j) +
        _root_.Matrix.of (fun i j => (A.get i).get j) *
          _root_.Matrix.of (fun i j => (B.get i).get j) :=
  recursiveMatrixAccumulate_ret k A B C

example {α : Type u} [Add α] [Mul α] (k : Nat)
    (A B C : Vector (Vector α (2 ^ k)) (2 ^ k)) :
    (recursiveMatrixAccumulate k A B C).time = (8 ^ k, 8 ^ k) :=
  recursiveMatrixAccumulate_time k A B C

example {α : Type u} [Add α] [Mul α]
    (A B C : Vector (Vector α (2 ^ 0)) (2 ^ 0)) :
    (recursiveMatrixAccumulate 0 A B C).time = (1, 1) :=
  recursiveMatrixAccumulate_time 0 A B C

example {α : Type u} [Add α] [Mul α]
    (A B C : Vector (Vector α (2 ^ 1)) (2 ^ 1)) :
    (recursiveMatrixAccumulate 1 A B C).time = (8, 8) :=
  recursiveMatrixAccumulate_time 1 A B C

example {α : Type u} [Add α] [Mul α]
    (A B C : Vector (Vector α (2 ^ 2)) (2 ^ 2)) :
    (recursiveMatrixAccumulate 2 A B C).time = (64, 64) :=
  recursiveMatrixAccumulate_time 2 A B C

example {α : Type u} [Add α] [Mul α]
    (A B C : Vector (Vector α (2 ^ 3)) (2 ^ 3)) :
    (recursiveMatrixAccumulate 3 A B C).time = (512, 512) :=
  recursiveMatrixAccumulate_time 3 A B C

example {α : Type u} [Add α] [Mul α] (k : Nat)
    (A B C : Vector (Vector α (2 ^ k)) (2 ^ k)) :
    (recursiveMatrixAccumulate k A B C).time = ((2 ^ k) ^ 3, (2 ^ k) ^ 3) := by
  rw [recursiveMatrixAccumulate_time]
  have h : (8 ^ k : Nat) = (2 ^ k) ^ 3 := by
    calc
      8 ^ k = (2 ^ 3) ^ k := by norm_num
      _ = (2 ^ k) ^ 3 := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [h]
