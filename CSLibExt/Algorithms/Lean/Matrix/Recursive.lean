/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Data.Matrix.Mul
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# Recursive matrix accumulation

The eight-call procedure of CLRS, fourth edition, section 4.1, pages 81–84,
adds `A * B` to the saved incoming square accumulator `C`. Dimensions are exact
powers of two, including the singleton base. Partitioning uses bounded offsets
into the whole arrays, without copying quadrants or a separate combine pass.

Scalar multiplications and accumulator additions are counted separately on the
actual run. Indexing, calls, vector updates and allocation are uncharged; this
does not establish full RAM/bit complexity or physical in-place heap updates.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

universe u

open Cslib.Algorithms.Lean

@[no_expose] private def updateEntry {α : Type u} [Add α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) (i k j : Fin n) :
    TimeM (Nat × Nat) (_root_.Vector (_root_.Vector α n) n) := do
  let product := (A.get i).get k * (B.get k).get j
  TimeM.tick (1, 1)
  pure (C.set i.val ((C.get i).set j.val ((C.get i).get j + product)))

private lemma updateEntry_get {α : Type u} [Add α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) (i k j x y : Fin n) :
    ((updateEntry A B C i k j).ret.get x).get y =
      if x = i ∧ y = j then (C.get x).get y + (A.get i).get k * (B.get k).get j
      else (C.get x).get y := by
  by_cases hx : x = i
  · subst x
    by_cases hy : y = j
    · subst y
      simp [updateEntry, Vector.get_eq_getElem]
    · simp [updateEntry, Vector.get_eq_getElem, Fin.val_inj, hy, Ne.symm hy]
  · simp [updateEntry, Vector.get_eq_getElem, Fin.val_inj, hx, Ne.symm hx]

private lemma updateEntry_time {α : Type u} [Add α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) (i k j : Fin n) :
    (updateEntry A B C i k j).time = (1, 1) := rfl

@[no_expose] private def accumulateBlock {α : Type u} [Add α] [Mul α] {n : Nat}
    (A B : _root_.Vector (_root_.Vector α n) n) :
    (depth r t c : Nat) → r + 2 ^ depth ≤ n → t + 2 ^ depth ≤ n →
      c + 2 ^ depth ≤ n → _root_.Vector (_root_.Vector α n) n →
      TimeM (Nat × Nat) (_root_.Vector (_root_.Vector α n) n)
  | 0, r, t, c, hr, ht, hc, C =>
    updateEntry A B C ⟨r, by simp only [pow_zero] at hr; omega⟩
      ⟨t, by simp only [pow_zero] at ht; omega⟩
      ⟨c, by simp only [pow_zero] at hc; omega⟩
  | depth + 1, r, t, c, hr, ht, hc, C => do
    have hpow : 0 < (2 ^ depth : Nat) := Nat.pow_pos (by decide)
    have hr' : r + 2 ^ depth + 2 ^ depth ≤ n := by
      simpa [pow_succ, Nat.mul_two, Nat.add_assoc] using hr
    have ht' : t + 2 ^ depth + 2 ^ depth ≤ n := by
      simpa [pow_succ, Nat.mul_two, Nat.add_assoc] using ht
    have hc' : c + 2 ^ depth + 2 ^ depth ≤ n := by
      simpa [pow_succ, Nat.mul_two, Nat.add_assoc] using hc
    -- CLRS lines 8–11: the lower inner half, in the printed quadrant order.
    let C ← accumulateBlock A B depth r t c (by omega) (by omega) (by omega) C
    let C ← accumulateBlock A B depth r t (c + 2 ^ depth)
      (by omega) (by omega) (by omega) C
    let C ← accumulateBlock A B depth (r + 2 ^ depth) t c
      (by omega) (by omega) (by omega) C
    let C ← accumulateBlock A B depth (r + 2 ^ depth) t (c + 2 ^ depth)
      (by omega) (by omega) (by omega) C
    -- CLRS lines 12–15: the upper inner half, retaining all preceding updates.
    let C ← accumulateBlock A B depth r (t + 2 ^ depth) c
      (by omega) (by omega) (by omega) C
    let C ← accumulateBlock A B depth r (t + 2 ^ depth) (c + 2 ^ depth)
      (by omega) (by omega) (by omega) C
    let C ← accumulateBlock A B depth (r + 2 ^ depth) (t + 2 ^ depth) c
      (by omega) (by omega) (by omega) C
    accumulateBlock A B depth (r + 2 ^ depth) (t + 2 ^ depth) (c + 2 ^ depth)
      (by omega) (by omega) (by omega) C

@[no_expose] private def blockProduct {α : Type u} [AddCommMonoid α] [Mul α] {n : Nat}
    (A B : _root_.Vector (_root_.Vector α n) n) (width t : Nat)
    (ht : t + width ≤ n) (x y : Fin n) : α :=
  ∑ z : Fin width,
    (A.get x).get ⟨t + z.val, by have := z.isLt; omega⟩ *
      (B.get ⟨t + z.val, by have := z.isLt; omega⟩).get y

private lemma blockProduct_add {α : Type u} [AddCommMonoid α] [Mul α] {n : Nat}
    (A B : _root_.Vector (_root_.Vector α n) n) (a b t : Nat)
    (ht : t + (a + b) ≤ n) (x y : Fin n) :
    blockProduct A B (a + b) t ht x y =
      blockProduct A B a t (by omega) x y +
      blockProduct A B b (t + a) (by omega) x y := by
  have h := Fin.sum_univ_add (fun z : Fin (a + b) =>
    (A.get x).get ⟨t + z.val, by have := z.isLt; omega⟩ *
      (B.get ⟨t + z.val, by have := z.isLt; omega⟩).get y)
  simpa only [blockProduct, Fin.val_castAdd, Fin.val_natAdd, Nat.add_assoc] using h

private abbrev inside (width r c x y : Nat) : Prop :=
  r ≤ x ∧ x < r + width ∧ c ≤ y ∧ y < c + width

private lemma fourQuadrants {α : Type u} [Add α] (width r c x y : Nat) (v p : α) :
    let v₁ := if inside width r c x y then v + p else v
    let v₂ := if inside width r (c + width) x y then v₁ + p else v₁
    let v₃ := if inside width (r + width) c x y then v₂ + p else v₂
    let v₄ := if inside width (r + width) (c + width) x y then v₃ + p else v₃
    v₄ = if inside (width + width) r c x y then v + p else v := by
  classical
  simp only [inside]
  split_ifs <;> first | omega | rfl

private lemma accumulateBlock_zero_get {α : Type u} [AddCommMonoid α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) (r t c : Nat)
    (hr : r + 2 ^ 0 ≤ n) (ht : t + 2 ^ 0 ≤ n) (hc : c + 2 ^ 0 ≤ n)
    (x y : Fin n) :
    ((accumulateBlock A B 0 r t c hr ht hc C).ret.get x).get y =
      if inside (2 ^ 0) r c x.val y.val then
        (C.get x).get y + blockProduct A B (2 ^ 0) t ht x y
      else (C.get x).get y := by
  have hrn : r < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr
  have hcn : c < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hc
  by_cases hx : x.val = r
  · have hxr : x = ⟨r, hrn⟩ := Fin.ext hx
    subst x
    by_cases hy : y.val = c
    · have hyc : y = ⟨c, hcn⟩ := Fin.ext hy
      subst y
      simp [accumulateBlock, updateEntry_get, blockProduct, inside]
    · have hy' : ¬ inside 1 r c r y.val := by simp only [inside]; omega
      simp only [pow_zero]
      rw [ite_eq_right hy']
      simp [accumulateBlock, updateEntry_get, Fin.ext_iff, hy]
  · have hx' : ¬ inside 1 r c x.val y.val := by simp only [inside]; omega
    simp only [pow_zero]
    rw [ite_eq_right hx']
    simp [accumulateBlock, updateEntry_get, Fin.ext_iff, hx]

private lemma accumulateBlock_get {α : Type u} [AddCommMonoid α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) (depth r t c : Nat)
    (hr : r + 2 ^ depth ≤ n) (ht : t + 2 ^ depth ≤ n) (hc : c + 2 ^ depth ≤ n)
    (x y : Fin n) :
    ((accumulateBlock A B depth r t c hr ht hc C).ret.get x).get y =
      if inside (2 ^ depth) r c x.val y.val then
        (C.get x).get y + blockProduct A B (2 ^ depth) t ht x y
      else (C.get x).get y := by
  induction depth generalizing r t c C with
  | zero => exact accumulateBlock_zero_get A B C r t c hr ht hc x y
  | succ depth ih =>
    simp only [accumulateBlock, TimeM.ret_bind, ih]
    rw [fourQuadrants, fourQuadrants]
    simp only [pow_succ, Nat.mul_two, blockProduct_add]
    split_ifs <;> simp [add_assoc]

private lemma accumulateBlock_time {α : Type u} [Add α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) (depth r t c : Nat)
    (hr : r + 2 ^ depth ≤ n) (ht : t + 2 ^ depth ≤ n) (hc : c + 2 ^ depth ≤ n) :
    (accumulateBlock A B depth r t c hr ht hc C).time = (8 ^ depth, 8 ^ depth) := by
  induction depth generalizing r t c C with
  | zero => simp [accumulateBlock, updateEntry_time]
  | succ depth ih =>
    simp only [accumulateBlock, TimeM.time_bind, ih]
    simp [pow_succ, Prod.add_def]
    omega

/-- **Recursive matrix multiply-accumulate.** Let $\alpha$ be a type with an addition and a
multiplication, let $k$ be a natural number and $n = 2^k$, and let $A$, $B$, $C$ be $n \times n$
matrices over $\alpha$, stored as vectors of rows. The procedure adds the product of $A$ and $B$
to the accumulator $C$ by the eight-call recursion of CLRS. When $n = 1$, writing $a$, $b$, $c$
for the single entries of $A$, $B$, $C$, it replaces $c$ by $c + ab$. Otherwise it splits each
matrix $M$ into four $(n/2) \times (n/2)$ quadrants $M_{11}$ (top left), $M_{12}$ (top right),
$M_{21}$ (bottom left) and $M_{22}$ (bottom right), and updates, in this order,
$C_{11} \gets C_{11} + A_{11} B_{11}$, $C_{12} \gets C_{12} + A_{11} B_{12}$,
$C_{21} \gets C_{21} + A_{21} B_{11}$, $C_{22} \gets C_{22} + A_{21} B_{12}$, then
$C_{11} \gets C_{11} + A_{12} B_{21}$, $C_{12} \gets C_{12} + A_{12} B_{22}$,
$C_{21} \gets C_{21} + A_{22} B_{21}$, $C_{22} \gets C_{22} + A_{22} B_{22}$, each by a
recursive call on the accumulator left by the previous one. It returns the final accumulator
together with two counters: the number of scalar multiplications and the number of accumulator
additions.

Only these two operations are charged; calls, indexing and allocation are free. -/
public def recursiveMatrixAccumulate {α : Type u} [Add α] [Mul α] (k : Nat)
    (A B C : _root_.Vector (_root_.Vector α (2 ^ k)) (2 ^ k)) :
    TimeM (Nat × Nat) (_root_.Vector (_root_.Vector α (2 ^ k)) (2 ^ k)) :=
  accumulateBlock A B k 0 0 0 (by simp) (by simp) (by simp) C

@[expose] public section

/-- **Entries of the recursive matrix multiply-accumulate.** Let $\alpha$ be an additive
commutative monoid with a multiplication, let $k$ be a natural number and $n = 2^k$, and let
$A = (a_{ij})$, $B = (b_{ij})$, $C = (c_{ij})$ be $n \times n$ matrices over $\alpha$, with
indices running from $0$ to $n - 1$. For all indices $i, j < n$, entry $(i, j)$ of the matrix
returned by the recursive multiply-accumulate procedure on $A$, $B$, $C$ equals
$c_{ij} + \sum_{t < n} a_{it} b_{tj}$. -/
theorem recursiveMatrixAccumulate_apply {α : Type u} [AddCommMonoid α] [Mul α] (k : Nat)
    (A B C : _root_.Vector (_root_.Vector α (2 ^ k)) (2 ^ k)) (i j : Fin (2 ^ k)) :
    ((recursiveMatrixAccumulate k A B C).ret.get i).get j =
      (C.get i).get j + ∑ t : Fin (2 ^ k), (A.get i).get t * (B.get t).get j := by
  have h := accumulateBlock_get A B C k 0 0 0 (by simp) (by simp) (by simp) i j
  simpa [recursiveMatrixAccumulate, inside, blockProduct] using h

/-- **Correctness of the recursive matrix multiply-accumulate.** Let $\alpha$ be an additive
commutative monoid with a multiplication, let $k$ be a natural number and $n = 2^k$, and let
$A = (a_{ij})$, $B = (b_{ij})$, $C$ be $n \times n$ matrices over $\alpha$, with indices running
from $0$ to $n - 1$. Viewed as a matrix, the result returned by the recursive multiply-accumulate
procedure on $A$, $B$, $C$ equals $C + AB$, where $AB$ is the matrix product with entries
$(AB)_{ij} = \sum_{t < n} a_{it} b_{tj}$. -/
theorem recursiveMatrixAccumulate_ret {α : Type u} [AddCommMonoid α] [Mul α] (k : Nat)
    (A B C : _root_.Vector (_root_.Vector α (2 ^ k)) (2 ^ k)) :
    _root_.Matrix.of (fun i j => ((recursiveMatrixAccumulate k A B C).ret.get i).get j) =
      _root_.Matrix.of (fun i j => (C.get i).get j) +
        _root_.Matrix.of (fun i j => (A.get i).get j) *
          _root_.Matrix.of (fun i j => (B.get i).get j) := by
  ext i j
  exact recursiveMatrixAccumulate_apply k A B C i j

/-- **Operation count of the recursive matrix multiply-accumulate.** Let $\alpha$ be a type with
an addition and a multiplication, let $k$ be a natural number and $n = 2^k$, and let $A$, $B$,
$C$ be $n \times n$ matrices over $\alpha$. The recursive multiply-accumulate procedure on $A$,
$B$, $C$ performs exactly $8^k$ scalar multiplications and exactly $8^k$ accumulator additions.
Since $8^k = n^3$, each count is the cube of the dimension.

Calls, indexing and allocation are uncharged. -/
theorem recursiveMatrixAccumulate_time {α : Type u} [Add α] [Mul α] (k : Nat)
    (A B C : _root_.Vector (_root_.Vector α (2 ^ k)) (2 ^ k)) :
    (recursiveMatrixAccumulate k A B C).time = (8 ^ k, 8 ^ k) :=
  accumulateBlock_time A B C k 0 0 0 (by simp) (by simp) (by simp)

end

end Cslib.Algorithms.Lean.Matrix
