/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Cslib.Algorithms.Lean.TimeM
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Vector.Basic

/-!
# Matrix-chain parenthesization

Bottom-up interval dynamic programming for the matrix-chain ordering problem from CLRS,
fourth edition, Section 14.2. The implementation returns an optimal scalar-multiplication
count and a full parenthesization; it does not multiply matrices.

The abstract cost counts one event per candidate split and one per reconstructed tree node.
Allocation, bounded access, comparison, and natural-number arithmetic are free in this model.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace Cslib.Algorithms.Lean.MatrixChain

open Cslib.Algorithms.Lean

/-- A full binary parenthesization whose leaves name input matrices. -/
public inductive Parenthesization (n : Nat) where
  /-- One matrix at its original bounded index. -/
  | matrix (index : Fin n)
  /-- Multiply two fully parenthesized subchains. -/
  | multiply (left right : Parenthesization n)
deriving DecidableEq, Repr

namespace Parenthesization

/-- Matrix indices in left-to-right leaf order. -/
@[expose] public def matrixIndices {n : Nat} : Parenthesization n → List (Fin n)
  | .matrix index => [index]
  | .multiply left right => matrixIndices left ++ matrixIndices right

/-- Number of rows of the product represented by a parenthesization. -/
@[expose] public def rows {n : Nat}
    (dimensions : Vector Nat (n + 1)) : Parenthesization n → Nat
  | .matrix index => dimensions.get index.castSucc
  | .multiply left _ => rows dimensions left

/-- Number of columns of the product represented by a parenthesization. -/
@[expose] public def cols {n : Nat}
    (dimensions : Vector Nat (n + 1)) : Parenthesization n → Nat
  | .matrix index => dimensions.get index.succ
  | .multiply _ right => cols dimensions right

/-- Every multiplication node has matching inner dimensions. -/
@[expose] public def DimensionCompatible {n : Nat} (dimensions : Vector Nat (n + 1)) :
    Parenthesization n → Prop
  | .matrix _ => True
  | .multiply left right =>
      DimensionCompatible dimensions left ∧ DimensionCompatible dimensions right ∧
        cols dimensions left = rows dimensions right

/-- A parenthesization uses every input matrix exactly once in order and is dimension-valid. -/
@[expose] public def IsValid {n : Nat} (dimensions : Vector Nat (n + 1))
    (tree : Parenthesization n) : Prop :=
  tree.matrixIndices = List.finRange n ∧ tree.DimensionCompatible dimensions

end Parenthesization

/-- Scalar multiplications performed by a parenthesization. -/
@[expose] public def scalarMultiplicationCost {n : Nat}
    (dimensions : Vector Nat (n + 1)) :
    Parenthesization n → Nat
  | .matrix _ => 0
  | .multiply left right =>
      scalarMultiplicationCost dimensions left + scalarMultiplicationCost dimensions right +
        left.rows dimensions * left.cols dimensions * right.cols dimensions

/-- Abstract events charged by matrix-chain ordering and reconstruction. -/
public structure Cost where
  /-- Split candidates evaluated by the dynamic program. -/
  candidateEvaluations : Nat
  /-- Tree constructors emitted during reconstruction. -/
  reconstructionNodes : Nat
deriving DecidableEq, Repr

public instance : Zero Cost := ⟨⟨0, 0⟩⟩

public instance : Add Cost where
  add left right :=
    ⟨left.candidateEvaluations + right.candidateEvaluations,
      left.reconstructionNodes + right.reconstructionNodes⟩

/-- Total charged events. -/
@[expose] public def Cost.total (cost : Cost) : Nat :=
  cost.candidateEvaluations + cost.reconstructionNodes

@[simp] private theorem zero_candidateEvaluations :
    (0 : Cost).candidateEvaluations = 0 := rfl

@[simp] private theorem zero_reconstructionNodes :
    (0 : Cost).reconstructionNodes = 0 := rfl

@[simp] private theorem add_candidateEvaluations (left right : Cost) :
    (left + right).candidateEvaluations =
      left.candidateEvaluations + right.candidateEvaluations := rfl

@[simp] private theorem add_reconstructionNodes (left right : Cost) :
    (left + right).reconstructionNodes =
      left.reconstructionNodes + right.reconstructionNodes := rfl

/-- An optimum scalar cost and one parenthesization attaining it. -/
public structure Result (n : Nat) where
  /-- Minimum scalar-multiplication count. -/
  optimalCost : Nat
  /-- Reconstructed optimal parenthesization. -/
  parenthesization : Parenthesization n
deriving DecidableEq, Repr

def matrixChainOrderRaw {n : Nat} (dimensions : Vector Nat (n + 1)) (hn : 0 < n) :
    TimeM Cost (Option (Result n)) :=
  let Cell := Nat × (Option (Fin n) × Parenthesization n)
  let Table := Vector (Vector (Option Cell) n) n
  let tableGet (table : Table) (i j : Fin n) : Option Cell :=
    (table.get i).get j
  let tableSet (table : Table) (i j : Fin n) (value : Option Cell) : Table :=
    table.set i.val ((table.get i).set j.val value)
  let initialTable : Table :=
    Vector.ofFn fun i => Vector.ofFn fun j =>
      if i = j then some (0, none, .matrix i) else none
  let rec scanSplits (table : Table) (i j : Fin n) :
      (count : Nat) → i.val + count ≤ j.val → TimeM Cost (Option Cell)
    | 0, _ => pure none
    | count + 1, hCount => do
        let best ← scanSplits table i j count (by omega)
        TimeM.tick ⟨1, 0⟩
        let k : Fin n := ⟨i.val + count, by omega⟩
        let next : Fin n := ⟨i.val + count + 1, by omega⟩
        let result := match tableGet table i k, tableGet table next j with
          | some left, some right =>
              let candidate : Cell :=
                (left.1 + right.1 +
                  dimensions.get i.castSucc * dimensions.get k.succ * dimensions.get j.succ,
                  some k, .multiply left.2.2 right.2.2)
              match best with
              | none => some candidate
              | some current => if candidate.1 < current.1 then some candidate else best
          | _, _ => best
        pure result
  let rec fillStarts (length : Nat) (hLength : 2 ≤ length) (hLengthN : length ≤ n) :
      (count : Nat) → count ≤ n - length + 1 → Table → TimeM Cost Table
    | 0, _, table => pure table
    | count + 1, hCount, table => do
        let table ← fillStarts length hLength hLengthN count (by omega) table
        let i : Fin n := ⟨count, by omega⟩
        let j : Fin n := ⟨count + length - 1, by omega⟩
        let best ← scanSplits table i j (length - 1) (by
          change count + (length - 1) ≤ count + length - 1
          omega)
        let result := match best with
          | some cell => tableSet table i j (some cell)
          | none => table
        pure result
  let rec fillLengths : (count : Nat) → count ≤ n - 1 → TimeM Cost Table
    | 0, _ => pure initialTable
    | count + 1, hCount => do
        let table ← fillLengths count (by omega)
        let length := count + 2
        fillStarts length (by omega) (by omega) (n - length + 1) (by omega) table
  let buildTable : TimeM Cost Table := fillLengths (n - 1) (by omega)
  let rec reconstruct? (table : Table) :
      (fuel : Nat) → (i j : Fin n) → i.val ≤ j.val →
        TimeM Cost (Option (Parenthesization n))
    | 0, _, _, _ => pure none
    | fuel + 1, i, j, hij => do
        TimeM.tick ⟨0, 1⟩
        if i = j then
          pure (some (.matrix i))
        else
          match tableGet table i j with
          | some cell =>
              match cell.2.1 with
              | some k =>
                  if hSplit : i.val ≤ k.val ∧ k.val < j.val then
                    let next : Fin n := ⟨k.val + 1, by omega⟩
                    have hNext : next.val ≤ j.val := by
                      change k.val + 1 ≤ j.val
                      omega
                    let left ← reconstruct? table fuel i k hSplit.1
                    let right ← reconstruct? table fuel next j hNext
                    pure <| match left, right with
                      | some leftTree, some rightTree => some (.multiply leftTree rightTree)
                      | _, _ => none
                  else
                    pure none
              | none => pure none
          | none => pure none
  do
    let table ← buildTable
    let first : Fin n := ⟨0, hn⟩
    let last : Fin n := ⟨n - 1, by omega⟩
    match tableGet table first last with
    | none => pure none
    | some cell => do
        let tree? ← reconstruct? table n first last (by simp [first, last])
        match tree? with
        | none => pure none
        | some tree => pure (some { optimalCost := cell.1, parenthesization := tree })

end Cslib.Algorithms.Lean.MatrixChain
