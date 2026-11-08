/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Strassen.Basic
import all CSLibExt.Algorithms.Lean.Matrix.Strassen.Basic
import Mathlib.Tactic.Ring

/-!
# Exact scalar costs of Strassen accumulation

The same seven-recursive-call computation counts `7 ^ k` multiplications and
`(25 * 7 ^ k - 22 * 4 ^ k) / 3` additions/subtractions. Every non-base
node performs22materialized block operations, and every base call performs
one multiplication and one zero- or saved-accumulator addition.
Allocation, indexing, copying, zero-fill, calls and bit costs are uncharged.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

universe u

private def additionCount : Nat → Nat
  | 0 => 1
  | k + 1 => 7 * additionCount k + 22 * 4 ^ k

private lemma run_time {R : Type u} [Zero R] [Add R] [Sub R] [Mul R] (k : Nat)
    (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    (strassenMatrixAccumulate k A B C).time = (7 ^ k, additionCount k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : 2 ^ k * 2 ^ k = 4 ^ k := by
      rw [← mul_pow]
      rfl
    simp only [strassenMatrixAccumulate, TimeM.time_bind, TimeM.time_pure, blockMap_time,
      ih, additionCount, pow_succ, h]
    apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero]
    all_goals ring

private lemma additionCount_identity (k : Nat) :
    3 * additionCount k + 22 * 4 ^ k = 25 * 7 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [additionCount, pow_succ]
    calc
      3 * (7 * additionCount k + 22 * 4 ^ k) + 22 * (4 ^ k * 4) =
          7 * (3 * additionCount k + 22 * 4 ^ k) := by ring
      _ = 25 * (7 ^ k * 7) := by rw [ih]; ring

private lemma additionCount_closed (k : Nat) :
    additionCount k = (25 * 7 ^ k - 22 * 4 ^ k) / 3 := by
  have h := additionCount_identity k
  omega

/-- The actual Strassen accumulator counts its scalar multiplications and
additions/subtractions exactly. This does not charge allocation or bit operations. -/
public theorem strassenMatrixAccumulate_time {R : Type u}
    [Zero R] [Add R] [Sub R] [Mul R] (k : Nat)
    (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    (strassenMatrixAccumulate k A B C).time =
      (7 ^ k, (25 * 7 ^ k - 22 * 4 ^ k) / 3) := by
  simpa only [additionCount_closed] using run_time k A B C

end Cslib.Algorithms.Lean.Matrix
