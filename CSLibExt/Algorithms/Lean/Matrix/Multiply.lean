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
# Matrix accumulation by ordered scalar updates

The rectangular `i-j-k` loop from CLRS, fourth edition, Section 14.2, page 374,
adds `A * B` to the incoming accumulator `C`. Its square specialization is the
`MATRIX-MULTIPLY` procedure of Section 4.1, page 81.
To compute only `A * B`, initialize `C` to zero before calling; that optional
initialization is outside this worker's scalar-update cost model.

The saved output uses fixed-size, array-backed vectors. The current row is
threaded through the column and inner loops and written back to `C` once per
row, so a uniquely owned row is updated in place rather than copied out of
`C` for every scalar update. All three forward scans carry the fully evaluated
timed accumulator and recurse directly. Each actual scalar product and
accumulator addition contributes one tick to its corresponding cost component.
Indexing, vector updates, allocation and loop control are outside this scalar
cost model.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.Matrix

universe u

open Cslib.Algorithms.Lean

@[no_expose] private def updateCell {α : Type u} [Add α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q)
    (row : Vector α r) (j : Fin r) (k : Fin q) :
    TimeM (Nat × Nat) (Vector α r) := do
  let product := Ai.get k * (B.get k).get j
  TimeM.tick (1, 1)
  pure (row.set j.val (row.get j + product))

private theorem updateCell_time {α : Type u} [Add α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q)
    (row : Vector α r) (j : Fin r) (k : Fin q) :
    (updateCell Ai B row j k).time = (1, 1) := by
  rfl

private theorem updateCell_get {α : Type u} [Add α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q)
    (row : Vector α r) (j : Fin r) (k : Fin q) (y : Fin r) :
    (updateCell Ai B row j k).ret.get y =
      if y = j then row.get y + Ai.get k * (B.get k).get j else row.get y := by
  change (row.set j.val (row.get j + Ai.get k * (B.get k).get j)).get y = _
  by_cases hy : y = j
  · subst y
    simp [Vector.get_eq_getElem]
  · simp [Vector.get_eq_getElem, Fin.val_inj, hy, Ne.symm hy]

@[no_expose] private def scanK {α : Type u} [Add α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q) (j : Fin r) :
    (fuel k : Nat) → k + fuel ≤ q →
      TimeM (Nat × Nat) (Vector α r) → TimeM (Nat × Nat) (Vector α r)
  | 0, _, _, state => state
  | fuel + 1, k, h, state =>
    scanK Ai B j fuel (k + 1) (by omega) (do
      let row ← state
      updateCell Ai B row j ⟨k, by omega⟩)

@[no_expose] private def scanJ {α : Type u} [Add α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q) :
    (fuel j : Nat) → j + fuel ≤ r →
      TimeM (Nat × Nat) (Vector α r) → TimeM (Nat × Nat) (Vector α r)
  | 0, _, _, state => state
  | fuel + 1, j, h, state =>
    scanJ Ai B fuel (j + 1) (by omega)
      (scanK Ai B ⟨j, by omega⟩ q 0 (by omega) state)

@[no_expose] private def scanRows {α : Type u} [Add α] [Mul α] {p q r : Nat}
    (A : Vector (Vector α q) p) (B : Vector (Vector α r) q) :
    (fuel i : Nat) → i + fuel ≤ p →
      TimeM (Nat × Nat) (Vector (Vector α r) p) →
      TimeM (Nat × Nat) (Vector (Vector α r) p)
  | 0, _, _, state => state
  | fuel + 1, i, h, state =>
    scanRows A B fuel (i + 1) (by omega) (do
      let C ← state
      let row ← scanJ (A.get ⟨i, by omega⟩) B r 0 (by omega)
        (pure (C.get ⟨i, by omega⟩))
      pure (C.set i row))

private theorem scanK_time {α : Type u} [Add α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q) (j : Fin r)
    (fuel k : Nat) (h : k + fuel ≤ q) (state : TimeM (Nat × Nat) (Vector α r)) :
    (scanK Ai B j fuel k h state).time = state.time + (fuel, fuel) := by
  induction fuel generalizing k state with
  | zero => simp [scanK]
  | succ fuel ih =>
    simp [scanK, ih, updateCell_time, add_comm, add_left_comm]

private theorem scanJ_time {α : Type u} [Add α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q)
    (fuel j : Nat) (h : j + fuel ≤ r) (state : TimeM (Nat × Nat) (Vector α r)) :
    (scanJ Ai B fuel j h state).time = state.time + (fuel * q, fuel * q) := by
  induction fuel generalizing j state with
  | zero => simp [scanJ]
  | succ fuel ih =>
    simp [scanJ, ih, scanK_time, Nat.succ_mul, add_assoc, add_comm]

private theorem scanRows_time {α : Type u} [Add α] [Mul α] {p q r : Nat}
    (A : Vector (Vector α q) p) (B : Vector (Vector α r) q)
    (fuel i : Nat) (h : i + fuel ≤ p)
    (state : TimeM (Nat × Nat) (Vector (Vector α r) p)) :
    (scanRows A B fuel i h state).time =
      state.time + (fuel * r * q, fuel * r * q) := by
  induction fuel generalizing i state with
  | zero => simp [scanRows]
  | succ fuel ih =>
    simp [scanRows, ih, scanJ_time, Nat.succ_mul, Nat.add_mul,
      add_assoc, add_comm, Nat.mul_assoc]

@[no_expose] private def prefixProduct {α : Type u} [AddCommMonoid α] [Mul α]
    {q r : Nat} (Ai : Vector α q) (B : Vector (Vector α r) q) (j : Fin r)
    (count : Nat) (h : count ≤ q) : α :=
  ∑ k : Fin count, Ai.get ⟨k.val, lt_of_lt_of_le k.isLt h⟩ *
    (B.get ⟨k.val, lt_of_lt_of_le k.isLt h⟩).get j

private theorem prefixProduct_succ {α : Type u} [AddCommMonoid α] [Mul α]
    {q r : Nat} (Ai : Vector α q) (B : Vector (Vector α r) q) (j : Fin r)
    (count : Nat) (h : count + 1 ≤ q) :
    prefixProduct Ai B j (count + 1) h =
      prefixProduct Ai B j count (by omega) +
        Ai.get ⟨count, by omega⟩ * (B.get ⟨count, by omega⟩).get j := by
  simp only [prefixProduct, Fin.sum_univ_castSucc]
  rfl

private theorem scanK_spec {α : Type u} [AddCommMonoid α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q) (j : Fin r)
    (fuel k : Nat) (h : k + fuel ≤ q)
    (initial : Vector α r) (state : TimeM (Nat × Nat) (Vector α r))
    (hstate : ∀ y : Fin r, state.ret.get y =
      if y = j then initial.get y + prefixProduct Ai B j k (by omega)
      else initial.get y) :
    ∀ y : Fin r, (scanK Ai B j fuel k h state).ret.get y =
      if y = j then initial.get y + prefixProduct Ai B j (k + fuel) (by omega)
      else initial.get y := by
  induction fuel generalizing k state with
  | zero => simpa [scanK] using hstate
  | succ fuel ih =>
    let current : TimeM (Nat × Nat) (Vector α r) := do
      let row ← state
      updateCell Ai B row j ⟨k, by omega⟩
    have hcurrent : ∀ y : Fin r, current.ret.get y =
        if y = j then initial.get y + prefixProduct Ai B j (k + 1) (by omega)
        else initial.get y := by
      intro y
      by_cases hy : y = j
      · subst y
        simp [current, updateCell_get, hstate, prefixProduct_succ, add_assoc]
      · simp [current, updateCell_get, hstate, hy]
    simpa [scanK, current, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (k + 1) (by omega) current hcurrent

private theorem scanJ_spec {α : Type u} [AddCommMonoid α] [Mul α] {q r : Nat}
    (Ai : Vector α q) (B : Vector (Vector α r) q)
    (fuel j : Nat) (h : j + fuel ≤ r)
    (initial : Vector α r) (state : TimeM (Nat × Nat) (Vector α r))
    (hstate : ∀ y : Fin r, state.ret.get y =
      if y.val < j then initial.get y + prefixProduct Ai B y q le_rfl
      else initial.get y) :
    ∀ y : Fin r, (scanJ Ai B fuel j h state).ret.get y =
      if y.val < j + fuel then initial.get y + prefixProduct Ai B y q le_rfl
      else initial.get y := by
  induction fuel generalizing j state with
  | zero => simpa [scanJ] using hstate
  | succ fuel ih =>
    let column : Fin r := ⟨j, by omega⟩
    let current := scanK Ai B column q 0 (by omega) state
    have hinner := scanK_spec Ai B column q 0 (by omega) state.ret state (by
      intro y
      simp [prefixProduct])
    have hcurrent : ∀ y : Fin r, current.ret.get y =
        if y.val < j + 1 then initial.get y + prefixProduct Ai B y q le_rfl
        else initial.get y := by
      intro y
      have inner := hinner y
      by_cases hy : y.val = j
      · have hj : y = column := Fin.ext hy
        subst y
        simpa [current, column, hstate] using inner
      · have hj : y ≠ column := fun he => hy (congrArg Fin.val he)
        have hlt : y.val < j + 1 ↔ y.val < j := by omega
        simpa [current, hj, hstate, hlt] using inner
    simpa [scanJ, current, column, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (j + 1) (by omega) current hcurrent

private theorem scanRows_spec {α : Type u} [AddCommMonoid α] [Mul α] {p q r : Nat}
    (A : Vector (Vector α q) p) (B : Vector (Vector α r) q)
    (fuel i : Nat) (h : i + fuel ≤ p)
    (initial : Vector (Vector α r) p) (state : TimeM (Nat × Nat) (Vector (Vector α r) p))
    (hstate : ∀ (x : Fin p) (y : Fin r), (state.ret.get x).get y =
      if x.val < i then (initial.get x).get y + prefixProduct (A.get x) B y q le_rfl
      else (initial.get x).get y) :
    ∀ (x : Fin p) (y : Fin r), ((scanRows A B fuel i h state).ret.get x).get y =
      if x.val < i + fuel then (initial.get x).get y + prefixProduct (A.get x) B y q le_rfl
      else (initial.get x).get y := by
  induction fuel generalizing i state with
  | zero => simpa [scanRows] using hstate
  | succ fuel ih =>
    let index : Fin p := ⟨i, by omega⟩
    let row := scanJ (A.get index) B r 0 (by omega) (pure (state.ret.get index))
    let current : TimeM (Nat × Nat) (Vector (Vector α r) p) := do
      let C ← state
      let row ← scanJ (A.get index) B r 0 (by omega) (pure (C.get index))
      pure (C.set i row)
    have columns := scanJ_spec (A.get index) B r 0 (by omega) (state.ret.get index)
      (pure (state.ret.get index)) (by simp)
    have hcurrent : ∀ (x : Fin p) (y : Fin r), (current.ret.get x).get y =
        if x.val < i + 1 then (initial.get x).get y + prefixProduct (A.get x) B y q le_rfl
        else (initial.get x).get y := by
      intro x y
      have hget : (current.ret.get x).get y =
          if x = index then row.ret.get y else (state.ret.get x).get y := by
        simp only [current, TimeM.ret_bind, TimeM.ret_pure]
        by_cases hx : x = index
        · subst x
          simp [Vector.get_eq_getElem, index, row]
        · have hxi : x.val ≠ i := fun he => hx (Fin.ext he)
          simp only [Vector.get_eq_getElem, ne_eq, Ne.symm hxi, not_false_eq_true,
            Vector.getElem_set_ne, right_eq_ite_iff, index]
          intro he
          exact False.elim (hxi (congrArg Fin.val he))
      rw [hget]
      by_cases hx : x.val = i
      · have hi : x = index := Fin.ext hx
        subst x
        simpa [row, index, hstate, y.isLt] using columns y
      · have hi : x ≠ index := fun he => hx (congrArg Fin.val he)
        have hlt : x.val < i + 1 ↔ x.val < i := by omega
        simpa [hi, hlt] using hstate x y
    simpa [scanRows, current, index, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      ih (i + 1) (by omega) current hcurrent

private theorem scanJ_zero_inner {α : Type u} [Add α] [Mul α] {r : Nat}
    (Ai : Vector α 0) (B : Vector (Vector α r) 0)
    (fuel j : Nat) (h : j + fuel ≤ r)
    (state : TimeM (Nat × Nat) (Vector α r)) :
    scanJ Ai B fuel j h state = state := by
  induction fuel generalizing j with
  | zero => rfl
  | succ fuel ih => simp [scanJ, scanK, ih]

private theorem scanRows_zero_inner {α : Type u} [Add α] [Mul α] {p r : Nat}
    (A : Vector (Vector α 0) p) (B : Vector (Vector α r) 0)
    (fuel i : Nat) (h : i + fuel ≤ p)
    (state : TimeM (Nat × Nat) (Vector (Vector α r) p)) :
    scanRows A B fuel i h state = state := by
  induction fuel generalizing i state with
  | zero => rfl
  | succ fuel ih =>
    simp only [scanRows, scanJ_zero_inner]
    rw [ih]
    apply TimeM.ext <;> simp [Vector.get_eq_getElem]

/-- Add the rectangular product `A * B` to the saved incoming accumulator `C`.
The increasing `i-j-k` traversal charges one scalar multiplication and one scalar
addition at each actual cell update. -/
public def rectangularMatrixAccumulate {α : Type u} [Add α] [Mul α]
    {p q r : Nat} (A : _root_.Vector (_root_.Vector α q) p)
    (B : _root_.Vector (_root_.Vector α r) q) (C : _root_.Vector (_root_.Vector α r) p) :
    TimeM (Nat × Nat) (_root_.Vector (_root_.Vector α r) p) :=
  scanRows A B p 0 (by omega) (pure C)

/-- Square specialization of `rectangularMatrixAccumulate`, with no extra traversal. -/
public def matrixAccumulate {α : Type u} [Add α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) :
    TimeM (Nat × Nat) (_root_.Vector (_root_.Vector α n) n) :=
  rectangularMatrixAccumulate A B C

@[expose] public section

/-- Every output entry is its incoming accumulator plus the canonical finite product sum. -/
theorem rectangularMatrixAccumulate_apply {α : Type u} [AddCommMonoid α] [Mul α]
    {p q r : Nat} (A : _root_.Vector (_root_.Vector α q) p)
    (B : _root_.Vector (_root_.Vector α r) q) (C : _root_.Vector (_root_.Vector α r) p)
    (i : Fin p) (j : Fin r) :
    ((rectangularMatrixAccumulate A B C).ret.get i).get j =
      (C.get i).get j + ∑ k : Fin q, (A.get i).get k * (B.get k).get j := by
  simpa [rectangularMatrixAccumulate, i.isLt, prefixProduct] using
    scanRows_spec A B p 0 (by omega) C (pure C) (by simp) i j

/-- The saved vector output refines accumulation using canonical matrix multiplication. -/
theorem rectangularMatrixAccumulate_ret {α : Type u} [AddCommMonoid α] [Mul α]
    {p q r : Nat} (A : _root_.Vector (_root_.Vector α q) p)
    (B : _root_.Vector (_root_.Vector α r) q) (C : _root_.Vector (_root_.Vector α r) p) :
    Matrix.of (fun i j => ((rectangularMatrixAccumulate A B C).ret.get i).get j) =
      Matrix.of (fun i j => (C.get i).get j) +
        Matrix.of (fun i k => (A.get i).get k) * Matrix.of (fun k j => (B.get k).get j) := by
  ext i j
  exact rectangularMatrixAccumulate_apply A B C i j

/-- Exact multiplication and accumulator-addition counts of the actual rectangular run. -/
theorem rectangularMatrixAccumulate_time {α : Type u} [Add α] [Mul α]
    {p q r : Nat} (A : _root_.Vector (_root_.Vector α q) p)
    (B : _root_.Vector (_root_.Vector α r) q) (C : _root_.Vector (_root_.Vector α r) p) :
    (rectangularMatrixAccumulate A B C).time = (p * q * r, p * q * r) := by
  simpa [rectangularMatrixAccumulate, Nat.mul_right_comm] using
    scanRows_time A B p 0 (by omega) (pure C)

/-- A zero inner dimension preserves the entire incoming accumulator at zero scalar cost. -/
theorem rectangularMatrixAccumulate_zero_inner {α : Type u} [Add α] [Mul α]
    {p r : Nat} (A : _root_.Vector (_root_.Vector α 0) p)
    (B : _root_.Vector (_root_.Vector α r) 0) (C : _root_.Vector (_root_.Vector α r) p) :
    rectangularMatrixAccumulate A B C = (pure C : TimeM (Nat × Nat) _) := by
  exact scanRows_zero_inner A B p 0 (by omega) (pure C)

/-- Square accumulation returns the incoming matrix plus its canonical square product. -/
theorem matrixAccumulate_ret {α : Type u} [AddCommMonoid α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) :
    Matrix.of (fun i j => ((matrixAccumulate A B C).ret.get i).get j) =
      Matrix.of (fun i j => (C.get i).get j) +
        Matrix.of (fun i k => (A.get i).get k) * Matrix.of (fun k j => (B.get k).get j) :=
  rectangularMatrixAccumulate_ret A B C

/-- The square wrapper emits exactly `n^3` ticks in each scalar-operation component. -/
theorem matrixAccumulate_time {α : Type u} [Add α] [Mul α] {n : Nat}
    (A B C : _root_.Vector (_root_.Vector α n) n) :
    (matrixAccumulate A B C).time = (n ^ 3, n ^ 3) := by
  simpa [matrixAccumulate, pow_succ] using rectangularMatrixAccumulate_time A B C

end

end Cslib.Algorithms.Lean.Matrix
