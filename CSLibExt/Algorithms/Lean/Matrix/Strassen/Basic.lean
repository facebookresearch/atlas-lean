/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.GroupWithZero.Nat
import Batteries.Data.Vector.Lemmas
import Mathlib.Algebra.BigOperators.Fin

/-!
# Strassen's matrix accumulator

The displayed seven-recursive-call procedure in CLRS, fourth edition, Section4.2
(printed pages86–89) updates the saved matrix `C` to `C + A * B`.
Its dimension is `2 ^ k`; at `k = 0` it executes one multiplication and
one saved-accumulator addition.

Each materialized scalar addition or subtraction emits `(0, 1)`, and each
scalar multiplication emits `(1, 0)`, in the canonical CSLib `TimeM`.
The ten `S` constructions and twelve saved-`C` operations require22block
operations per non-base call. The source's later18-operation summary omits
four saved-accumulator additions; this implementation counts all displayed
operations, including seven recursive zero-accumulator base additions.
Indexing, allocation, copying, zero-fill and call overhead are uncharged.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

universe u

@[no_expose] private def blockMap {R : Type u} {n : Nat} (op : R → R → R)
    (A B : Vector (Vector R n) n) :
    TimeM (Nat × Nat) (Vector (Vector R n) n) :=
  (A.zipWith (fun a b => a.zipWith Prod.mk b) B).mapM fun row =>
    row.mapM fun ab => do
      TimeM.tick (0, 1)
      pure (op ab.1 ab.2)

@[no_expose] private def halfEquiv (k : Nat) : Fin (2 ^ k) ⊕ Fin (2 ^ k) ≃ Fin (2 ^ (k + 1)) :=
  finSumFinEquiv.trans (finCongr (by rw [pow_succ]; omega))

@[no_expose] private def quadrant {R : Type u} (k : Nat)
    (M : Vector (Vector R (2 ^ (k + 1))) (2 ^ (k + 1))) (r c : Bool) :
    Vector (Vector R (2 ^ k)) (2 ^ k) :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    (M.get (halfEquiv k (if r then Sum.inr i else Sum.inl i))).get
      (halfEquiv k (if c then Sum.inr j else Sum.inl j))

@[no_expose] private def joinBlocks {R : Type u} (k : Nat)
    (a b c d : Vector (Vector R (2 ^ k)) (2 ^ k)) :
    Vector (Vector R (2 ^ (k + 1))) (2 ^ (k + 1)) :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    match (halfEquiv k).symm i, (halfEquiv k).symm j with
    | Sum.inl x, Sum.inl y => (a.get x).get y
    | Sum.inl x, Sum.inr y => (b.get x).get y
    | Sum.inr x, Sum.inl y => (c.get x).get y
    | Sum.inr x, Sum.inr y => (d.get x).get y

/-- Execute the seven-call Strassen procedure, adding `A * B` to saved `C`.
The returned pair counts actual scalar multiplications and additions/subtractions. -/
public def strassenMatrixAccumulate {R : Type u} [Zero R] [Add R] [Sub R] [Mul R] :
    (k : Nat) → (A B C : Vector (Vector R (2 ^ k)) (2 ^ k)) →
      TimeM (Nat × Nat) (Vector (Vector R (2 ^ k)) (2 ^ k))
  | 0, A, B, C => do
    TimeM.tick (1, 0)
    let p := (A.get 0).get 0 * (B.get 0).get 0
    TimeM.tick (0, 1)
    pure #v[#v[(C.get 0).get 0 + p]]
  | k + 1, A, B, C => do
    let a₁₁ := quadrant k A false false
    let a₁₂ := quadrant k A false true
    let a₂₁ := quadrant k A true false
    let a₂₂ := quadrant k A true true
    let b₁₁ := quadrant k B false false
    let b₁₂ := quadrant k B false true
    let b₂₁ := quadrant k B true false
    let b₂₂ := quadrant k B true true
    let s₁ ← blockMap (· - ·) b₁₂ b₂₂
    let s₂ ← blockMap (· + ·) a₁₁ a₁₂
    let s₃ ← blockMap (· + ·) a₂₁ a₂₂
    let s₄ ← blockMap (· - ·) b₂₁ b₁₁
    let s₅ ← blockMap (· + ·) a₁₁ a₂₂
    let s₆ ← blockMap (· + ·) b₁₁ b₂₂
    let s₇ ← blockMap (· - ·) a₁₂ a₂₂
    let s₈ ← blockMap (· + ·) b₂₁ b₂₂
    let s₉ ← blockMap (· - ·) a₁₁ a₂₁
    let s₁₀ ← blockMap (· + ·) b₁₁ b₁₂
    let z := Vector.replicate (2 ^ k) (Vector.replicate (2 ^ k) (0 : R))
    let p₁ ← strassenMatrixAccumulate k a₁₁ s₁ z
    let p₂ ← strassenMatrixAccumulate k s₂ b₂₂ z
    let p₃ ← strassenMatrixAccumulate k s₃ b₁₁ z
    let p₄ ← strassenMatrixAccumulate k a₂₂ s₄ z
    let p₅ ← strassenMatrixAccumulate k s₅ s₆ z
    let p₆ ← strassenMatrixAccumulate k s₇ s₈ z
    let p₇ ← strassenMatrixAccumulate k s₉ s₁₀ z
    let c₁₁ ← blockMap (· + ·) (quadrant k C false false) p₅
    let c₁₁ ← blockMap (· + ·) c₁₁ p₄
    let c₁₁ ← blockMap (· - ·) c₁₁ p₂
    let c₁₁ ← blockMap (· + ·) c₁₁ p₆
    let c₁₂ ← blockMap (· + ·) (quadrant k C false true) p₁
    let c₁₂ ← blockMap (· + ·) c₁₂ p₂
    let c₂₁ ← blockMap (· + ·) (quadrant k C true false) p₃
    let c₂₁ ← blockMap (· + ·) c₂₁ p₄
    let c₂₂ ← blockMap (· + ·) (quadrant k C true true) p₅
    let c₂₂ ← blockMap (· + ·) c₂₂ p₁
    let c₂₂ ← blockMap (· - ·) c₂₂ p₃
    let c₂₂ ← blockMap (· - ·) c₂₂ p₇
    pure (joinBlocks k c₁₁ c₁₂ c₂₁ c₂₂)

private lemma list_mapM_ret {α : Type u} {β : Type u}
    (f : α → TimeM (Nat × Nat) β) (xs : List α) :
    (xs.mapM f).ret = xs.map (fun x => (f x).ret) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.mapM_cons, ih]

private lemma list_mapM_time {α : Type u} {β : Type u}
    (f : α → TimeM (Nat × Nat) β) (c : Nat × Nat) (hf : ∀ x, (f x).time = c)
    (xs : List α) : (xs.mapM f).time = (xs.length * c.1, xs.length * c.2) := by
  rcases c with ⟨p, q⟩
  induction xs with
  | nil =>
    simp
    rfl
  | cons x xs ih => simp [List.mapM_cons, ih, hf, Nat.succ_mul, Nat.add_comm]

private lemma vector_mapM_ret {α : Type u} {β : Type u} {n : Nat}
    (f : α → TimeM (Nat × Nat) β) (xs : Vector α n) :
    (xs.mapM f).ret = xs.map (fun x => (f x).ret) := by
  apply Vector.toArray_inj.mp
  have h := congrArg TimeM.ret (Vector.toArray_mapM (f := f) (xs := xs))
  change (xs.mapM f).ret.toArray = (xs.toArray.mapM f).ret at h
  rw [h]
  simp [Array.mapM_eq_mapM_toList, list_mapM_ret, ← List.map_toArray]

private lemma vector_mapM_time {α : Type u} {β : Type u} {n : Nat}
    (f : α → TimeM (Nat × Nat) β) (c : Nat × Nat) (hf : ∀ x, (f x).time = c)
    (xs : Vector α n) : (xs.mapM f).time = (n * c.1, n * c.2) := by
  have h := congrArg TimeM.time (Vector.toArray_mapM (f := f) (xs := xs))
  change (xs.mapM f).time = (xs.toArray.mapM f).time at h
  rw [h]
  simp [Array.mapM_eq_mapM_toList, list_mapM_time f c hf, xs.size_toArray]

private lemma blockMap_get {R : Type u} {n : Nat} (op : R → R → R)
    (A B : Vector (Vector R n) n) (i j : Fin n) :
    ((blockMap op A B).ret.get i).get j = op ((A.get i).get j) ((B.get i).get j) := by
  simp [blockMap, vector_mapM_ret, Vector.get_eq_getElem]

private lemma blockMap_time {R : Type u} {n : Nat} (op : R → R → R)
    (A B : Vector (Vector R n) n) : (blockMap op A B).time = (0, n * n) := by
  unfold blockMap
  let f : R × R → TimeM (Nat × Nat) R := fun ab => do
    TimeM.tick (0, 1)
    pure (op ab.1 ab.2)
  have hf : ∀ ab, (f ab).time = (0, 1) := fun _ => rfl
  have hr : ∀ row : Vector (R × R) n, (row.mapM f).time = (0, n) := by
    intro row
    simpa only [Nat.mul_zero, Nat.mul_one] using vector_mapM_time f (0, 1) hf row
  simpa only [Nat.mul_zero] using
    vector_mapM_time (fun row => row.mapM f) (0, n) hr
      (A.zipWith (fun a b => a.zipWith Prod.mk b) B)

end Cslib.Algorithms.Lean.Matrix
