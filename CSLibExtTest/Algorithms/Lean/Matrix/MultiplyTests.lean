/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Multiply
public meta import CSLibExt.Algorithms.Lean.Matrix.Multiply
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Data.Matrix.Basic
public meta import Mathlib.Algebra.Ring.Rat

/-!
# Matrix accumulation regression tests

Each fixture calls the actual saved-accumulator worker and checks its complete
output and both scalar counters. Matrix scalars detect reversal of multiplication
operands; expression scalars have no zero or additive laws and detect update order.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Matrix

universe u

open Cslib.Algorithms.Lean Cslib.Algorithms.Lean.Matrix

private meta def verify {α : Type u} [DecidableEq α] {p r : Nat} (label : String)
    (actual : TimeM (Nat × Nat) (Vector (Vector α r) p))
    (expected : Vector (Vector α r) p) (cost : Nat × Nat) : IO Unit := do
  unless decide (actual.ret = expected) do
    throw <| IO.userError s!"{label}: wrong saved accumulator"
  unless actual.time == cost do
    throw <| IO.userError s!"{label}: scalar counts {actual.time}, expected {cost}"
  IO.println s!"{label}: {p}x{r} output checked, scalar counts {actual.time}"

private meta def runTests : IO Unit := do
  let A : Vector (Vector Int 3) 2 := #v[#v[1, 2, 3], #v[-1, 0, 4]]
  let B : Vector (Vector Int 2) 3 := #v[#v[5, -2], #v[1, 3], #v[2, 1]]
  let C : Vector (Vector Int 2) 2 := #v[#v[10, 20], #v[30, 40]]
  verify "signed rectangular" (rectangularMatrixAccumulate A B C)
    #v[#v[23, 27], #v[33, 46]] (12, 12)

  let A : Vector (Vector Rat 2) 1 := #v[#v[1 / 2, -3 / 2]]
  let B : Vector (Vector Rat 2) 2 := #v[#v[2, 1 / 3], #v[-2, 2 / 3]]
  let C : Vector (Vector Rat 2) 1 := #v[#v[1 / 4, -1 / 6]]
  verify "fractional rectangular" (rectangularMatrixAccumulate A B C)
    #v[#v[17 / 4, -1]] (4, 4)

  let A : Vector (Vector Int 0) 2 := #v[#v[], #v[]]
  let B : Vector (Vector Int 3) 0 := #v[]
  let C : Vector (Vector Int 3) 2 := #v[#v[1, 2, 3], #v[4, 5, 6]]
  verify "empty inner, six saved entries" (rectangularMatrixAccumulate A B C) C (0, 0)

  let A : Vector (Vector Int 4) 0 := #v[]
  let B : Vector (Vector Int 3) 4 := Vector.replicate 4 (Vector.replicate 3 7)
  let C : Vector (Vector Int 3) 0 := #v[]
  verify "empty outer" (rectangularMatrixAccumulate A B C) C (0, 0)

  let A : Vector (Vector Int 4) 3 := Vector.replicate 3 (Vector.replicate 4 7)
  let B : Vector (Vector Int 0) 4 := Vector.replicate 4 #v[]
  let C : Vector (Vector Int 0) 3 := #v[#v[], #v[], #v[]]
  verify "empty columns, three saved rows" (rectangularMatrixAccumulate A B C) C (0, 0)

  let A : Vector (Vector Int 1) 1 := #v[#v[7]]
  let B : Vector (Vector Int 1) 1 := #v[#v[6]]
  let C : Vector (Vector Int 1) 1 := #v[#v[5]]
  verify "singleton square" (matrixAccumulate A B C) #v[#v[47]] (1, 1)
  let square := matrixAccumulate A B C
  let rectangle := rectangularMatrixAccumulate A B C
  unless decide (square.ret = rectangle.ret) && square.time == rectangle.time do
    throw <| IO.userError "square wrapper changed the timed result"

  let C : Vector (Vector Int 0) 0 := #v[]
  verify "empty square" (matrixAccumulate C C C) C (0, 0)

  -- Noncommutative addition (list concatenation): the inner scan must
  -- accumulate in increasing column order, i.e. (C + P₀) + P₁, not
  -- (C + P₁) + P₀.
  letI : Add (List Int) := ⟨List.append⟩
  letI : Mul (List Int) := ⟨List.append⟩
  let A : Vector (Vector (List Int) 2) 1 := #v[#v[[1], [2]]]
  let B : Vector (Vector (List Int) 1) 2 := #v[#v[[10]], #v[[20]]]
  let C : Vector (Vector (List Int) 1) 1 := #v[#v[[100]]]
  verify "noncommutative addition order" (rectangularMatrixAccumulate A B C)
    #v[#v[[100, 1, 10, 2, 20]]] (2, 2)

  let Z : Vector (Vector Int 2) 2 := #v[#v[0, 0], #v[0, 0]]
  let C : Vector (Vector Int 2) 2 := #v[#v[1, 2], #v[3, 4]]
  verify "zero factors do not skip updates" (matrixAccumulate Z Z C) C (8, 8)

  let X : Matrix (Fin 2) (Fin 2) Int := Matrix.of fun i j =>
    if i = 0 ∧ j = 1 then 1 else 0
  let Y : Matrix (Fin 2) (Fin 2) Int := Matrix.of fun i j =>
    if i = 1 ∧ j = 0 then 1 else 0
  let I : Matrix (Fin 2) (Fin 2) Int := 1
  let O : Matrix (Fin 2) (Fin 2) Int := 0
  let D₁ : Matrix (Fin 2) (Fin 2) Int := Matrix.of fun i j =>
    if i = j then if i = 0 then 2 else 1 else 0
  let D₂ : Matrix (Fin 2) (Fin 2) Int := Matrix.of fun i j =>
    if i = j then if i = 0 then 2 else 3 else 0
  let A : Vector (Vector (Matrix (Fin 2) (Fin 2) Int) 2) 2 := #v[#v[X, O], #v[I, Y]]
  let B : Vector (Vector (Matrix (Fin 2) (Fin 2) Int) 2) 2 := #v[#v[Y, I], #v[O, X]]
  let C : Vector (Vector (Matrix (Fin 2) (Fin 2) Int) 2) 2 := #v[#v[I, O], #v[O, I]]
  verify "noncommutative matrix scalars" (matrixAccumulate A B C)
    #v[#v[D₁, X], #v[Y, D₂]] (8, 8)

#eval runTests

meta section

private structure OrderedScalar where
  expression : String
deriving DecidableEq

private instance : Add OrderedScalar := ⟨fun x y => ⟨s!"({x.expression}+{y.expression})"⟩⟩
private instance : Mul OrderedScalar := ⟨fun x y => ⟨s!"{x.expression}*{y.expression}"⟩⟩

private def atom (s : String) : OrderedScalar := ⟨s⟩

private meta def runLawFreeTests : IO Unit := do
  let A : Vector (Vector OrderedScalar 2) 1 := #v[#v[atom "a0", atom "a1"]]
  let B : Vector (Vector OrderedScalar 2) 2 :=
    #v[#v[atom "b00", atom "b01"], #v[atom "b10", atom "b11"]]
  let C : Vector (Vector OrderedScalar 2) 1 := #v[#v[atom "c0", atom "c1"]]
  verify "law-free ordered rectangle" (rectangularMatrixAccumulate A B C)
    #v[#v[atom "((c0+a0*b00)+a1*b10)", atom "((c1+a0*b01)+a1*b11)"]] (4, 4)

  let A : Vector (Vector OrderedScalar 2) 2 :=
    #v[#v[atom "a00", atom "a01"], #v[atom "a10", atom "a11"]]
  let B : Vector (Vector OrderedScalar 2) 2 :=
    #v[#v[atom "b00", atom "b01"], #v[atom "b10", atom "b11"]]
  let C : Vector (Vector OrderedScalar 2) 2 :=
    #v[#v[atom "c00", atom "c01"], #v[atom "c10", atom "c11"]]
  verify "law-free ordered square" (matrixAccumulate A B C)
    #v[#v[atom "((c00+a00*b00)+a01*b10)", atom "((c01+a00*b01)+a01*b11)"],
      #v[atom "((c10+a10*b00)+a11*b10)", atom "((c11+a10*b01)+a11*b11)"]] (8, 8)

  let A : Vector (Vector OrderedScalar 0) 2 := #v[#v[], #v[]]
  let B : Vector (Vector OrderedScalar 3) 0 := #v[]
  let C : Vector (Vector OrderedScalar 3) 2 :=
    #v[#v[atom "c00", atom "c01", atom "c02"], #v[atom "c10", atom "c11", atom "c12"]]
  verify "law-free empty inner, six saved entries" (rectangularMatrixAccumulate A B C) C (0, 0)

#eval runLawFreeTests

end

end CSLibExtTest.Algorithms.Matrix
