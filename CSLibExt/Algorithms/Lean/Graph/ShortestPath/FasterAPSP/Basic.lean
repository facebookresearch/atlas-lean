/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Multiply
public import Mathlib.Data.Nat.Log

import CSLibExt.Algorithms.Lean.Matrix.Assignments

/-!
# FASTER-APSP execution and exact selected counts

This module formalizes FASTER-APSP from Cormen, Leiserson, Rivest and Stein,
*Introduction to Algorithms*, fourth edition, section 23.1, printed page 653.

The source strict doubling loop uses saved operands and the canonical matrix
accumulator. Its return and three-coordinate time are proved on that same run.
The executor is algebraically generic; the shortest-path theorems specialize it
to signed-integer min-plus weights with infinity. The selected counts cover
copy/fill assignments (not accumulator vector updates), scalar additions and
scalar products, not full RAM, bit, allocation or space costs.
-/

set_option autoImplicit false
universe u

namespace Cslib.Algorithms.Lean.Matrix

@[no_expose] private def squareCompleted {α : Type u} [Add α] [Mul α] [Zero α]
    {n : Nat} (L : Vector (Vector α n) n) :
    TimeM (Nat × (Nat × Nat)) (Vector (Vector α n) n) := do
  let M ← fillCells (α := α) n
  let actual := matrixAccumulate L L M
  ⟨actual.ret, (0, actual.time)⟩

private lemma double_remaining_lt {n r : Nat} (hr : 0 < r)
    (hguard : r < n - 1) : n - 1 - (2 * r) < n - 1 - r := by
  omega

@[no_expose] private def squareLoop {α : Type u} [Add α] [Mul α] [Zero α]
    {n : Nat} (r : Nat) (hr : 0 < r) (L : Vector (Vector α n) n) :
    TimeM (Nat × (Nat × Nat)) (Vector (Vector α n) n) :=
  if hguard : r < n - 1 then do
    let completed ← squareCompleted L
    let nextR := 2 * r
    let nextL ← copyCells completed
    squareLoop nextR (by omega) nextL
  else pure L
termination_by n - 1 - r
decreasing_by exact double_remaining_lt hr hguard

/-- **FASTER-APSP.** Let $W$ be an $n \times n$ matrix over a type with addition, multiplication
and zero. FASTER-APSP copies $W$ into a matrix $L$ and sets $r = 1$. While $r < n - 1$, it fills
a new $n \times n$ matrix $M$ with zeros, sets each entry to
$M_{ij} = 0 + L_{i0} L_{0j} + \dots + L_{i,n-1} L_{n-1,j}$ (adding the terms from left to right),
copies $M$ into $L$ and doubles $r$. It returns the final $L$. The run also records three counts:
one assignment for each matrix cell copied or filled with zero, and one scalar addition and one
scalar multiplication for each term added to an entry of $M$. -/
@[nospecialize] public def fasterAPSP {α : Type u} [Add α] [Mul α] [Zero α]
    {n : Nat} (W : Vector (Vector α n) n) :
    TimeM (Nat × (Nat × Nat)) (Vector (Vector α n) n) := do
  let saved ← copyCells W
  squareLoop 1 (by decide) saved

private def asMatrix {α : Type u} {n : Nat} (A : Vector (Vector α n) n) :
    Matrix (Fin n) (Fin n) α := Matrix.of fun i j => (A.get i).get j

private lemma squareCompleted_ret {α : Type u} [Semiring α] {n : Nat}
    (L : Vector (Vector α n) n) :
    asMatrix (squareCompleted L).ret = asMatrix L * asMatrix L := by
  simp only [squareCompleted, TimeM.ret_bind, fillCells_ret]
  have hz : Matrix.of (fun (_i _j : Fin n) => (0 : α)) = 0 := rfl
  simpa [asMatrix, Vector.get_eq_getElem, hz] using
    matrixAccumulate_ret L L (Vector.replicate n (Vector.replicate n 0))

private lemma squareCompleted_time {α : Type u} [Add α] [Mul α] [Zero α] {n : Nat}
    (L : Vector (Vector α n) n) :
    (squareCompleted L).time = (n ^ 2, (n ^ 3, n ^ 3)) := by
  simp only [squareCompleted, TimeM.time_bind, fillCells_time,
    matrixAccumulate_time]
  simp

private lemma square_guard_iff (n j : Nat) :
    2 ^ j < n - 1 ↔ j < Nat.clog 2 (n - 1) :=
  (Nat.lt_clog_iff_pow_lt (by decide)).symm

private lemma squareLoop_ret {α : Type u} [Semiring α] {n : Nat}
    (k j : Nat) (hjk : j + k = Nat.clog 2 (n - 1))
    (L : Vector (Vector α n) n) :
    asMatrix (squareLoop (2 ^ j) (Nat.pow_pos (by decide)) L).ret =
      asMatrix L ^ (2 ^ k) := by
  induction k generalizing j L with
  | zero =>
    have hguard : ¬ 2 ^ j < n - 1 := by
      rw [square_guard_iff]
      omega
    rw [squareLoop, dite_eq_right hguard]
    simp
  | succ k ih =>
    have hguard : 2 ^ j < n - 1 := by
      rw [square_guard_iff]
      omega
    rw [squareLoop, dite_eq_left hguard]
    simp only [TimeM.ret_bind, copyCells_ret]
    have hdouble : 2 * 2 ^ j = 2 ^ (j + 1) := by
      simp [pow_succ, Nat.mul_comm]
    simp only [hdouble]
    rw [ih (j + 1) (by omega), squareCompleted_ret]
    rw [← pow_two, ← pow_mul]
    congr 1
    simp [pow_succ, Nat.mul_comm]

private lemma squareLoop_time {α : Type u} [Add α] [Mul α] [Zero α] {n : Nat}
    (k j : Nat) (hjk : j + k = Nat.clog 2 (n - 1))
    (L : Vector (Vector α n) n) :
    (squareLoop (2 ^ j) (Nat.pow_pos (by decide)) L).time =
      (2 * k * n ^ 2, (k * n ^ 3, k * n ^ 3)) := by
  induction k generalizing j L with
  | zero =>
    have hguard : ¬ 2 ^ j < n - 1 := by
      rw [square_guard_iff]
      omega
    rw [squareLoop, dite_eq_right hguard]
    simp
    rfl
  | succ k ih =>
    have hguard : 2 ^ j < n - 1 := by
      rw [square_guard_iff]
      omega
    rw [squareLoop, dite_eq_left hguard]
    simp only [TimeM.time_bind, squareCompleted_time, copyCells_time,
      copyCells_ret]
    have hdouble : 2 * 2 ^ j = 2 ^ (j + 1) := by
      simp [pow_succ, Nat.mul_comm]
    simp only [hdouble]
    rw [ih (j + 1) (by omega)]
    simp [Nat.add_mul, Nat.mul_add, Nat.mul_assoc]
    omega

/-- **FASTER-APSP returns a power of the input matrix.** Let $\alpha$ be a semiring, let $W$ be
an $n \times n$ matrix over $\alpha$, and let $k = \lceil \log_2 (n - 1) \rceil$ be the least
natural number with $n - 1 \le 2^k$ (so $k = 0$ when $n \le 2$). The matrix returned by
FASTER-APSP on $W$ is the matrix power $W^{2^k}$, with products computed in $\alpha$. -/
public theorem fasterAPSP_ret {α : Type u} [Semiring α] {n : Nat}
    (W : Vector (Vector α n) n) :
    Matrix.of (fun i j => ((fasterAPSP W).ret.get i).get j) =
      Matrix.of (fun i j => (W.get i).get j) ^ (2 ^ Nat.clog 2 (n - 1)) := by
  change asMatrix (fasterAPSP W).ret = asMatrix W ^ (2 ^ Nat.clog 2 (n - 1))
  simp only [fasterAPSP, TimeM.ret_bind, copyCells_ret]
  simpa using squareLoop_ret (Nat.clog 2 (n - 1)) 0 (by simp) W

/-- **Operation counts of FASTER-APSP.** Let $\alpha$ be a type with addition, multiplication and
zero, let $W$ be an $n \times n$ matrix over $\alpha$, and let $k = \lceil \log_2 (n - 1) \rceil$ be
the least natural number with $n - 1 \le 2^k$. On input $W$, FASTER-APSP performs exactly
$n^2 + 2 k n^2$ copy and fill assignments, $k n^3$ scalar additions and $k n^3$ scalar
multiplications.

Assignments count the matrix cells copied or filled with zero; the accumulator vector updates
inside the matrix multiplications are not counted. -/
public theorem fasterAPSP_time {α : Type u} [Add α] [Mul α] [Zero α] {n : Nat}
    (W : Vector (Vector α n) n) :
    (fasterAPSP W).time =
      (n ^ 2 + 2 * Nat.clog 2 (n - 1) * n ^ 2,
        (Nat.clog 2 (n - 1) * n ^ 3, Nat.clog 2 (n - 1) * n ^ 3)) := by
  simp only [fasterAPSP, TimeM.time_bind, copyCells_time, copyCells_ret]
  have htime := squareLoop_time (Nat.clog 2 (n - 1)) 0 (by simp) W
  simp only [Nat.pow_zero] at htime
  rw [htime]
  simp

end Cslib.Algorithms.Lean.Matrix
