/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Recursive
public import Mathlib.Data.Rat.Defs
public meta import CSLibExt.Algorithms.Lean.Matrix.Recursive
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Data.Matrix.Mul

/-! Populated source-boundary fixtures for saved recursive matrix accumulation.
The oracle is canonical Matrix multiplication, not another recursive implementation.
Codex authored these tests under Adam Kiezun's explicit producer selection. -/

set_option autoImplicit false

open Cslib.Algorithms.Lean.Matrix

meta section

private def verify {α : Type*} [Add α] [Mul α] [BEq α] [Repr α] (k : Nat)
    (label : String) (A B C expected : Vector (Vector α (2 ^ k)) (2 ^ k))
    (counts : Nat × Nat) : IO Unit := do
  let run := recursiveMatrixAccumulate k A B C
  unless run.ret == expected do
    throw <| IO.userError s!"{label}: output {reprStr run.ret}, expected {reprStr expected}"
  unless run.time == counts do
    throw <| IO.userError s!"{label}: cost {reprStr run.time}, expected {reprStr counts}"
  IO.println s!"{label}: {reprStr run.ret}; cost {reprStr run.time}"

private def oracle {α : Type*} [AddCommMonoid α] [Mul α] {n : Nat}
    (A B C : Vector (Vector α n) n) : Vector (Vector α n) n :=
  let a := _root_.Matrix.of (fun i j => (A.get i).get j)
  let b := _root_.Matrix.of (fun i j => (B.get i).get j)
  let c := _root_.Matrix.of (fun i j => (C.get i).get j)
  Vector.ofFn (fun i => Vector.ofFn (fun j => (c + a * b) i j))

private def runTests : IO Unit := do
  verify (α := Int) 0 "singleton positive" #v[#v[7]] #v[#v[6]] #v[#v[5]]
    #v[#v[47]] (1, 1)
  verify (α := Int) 0 "singleton signed" #v[#v[-3]] #v[#v[7]] #v[#v[5]]
    #v[#v[-16]] (1, 1)
  verify (α := Int) 1 "all eight quadrants" #v[#v[1, 2], #v[3, 4]]
    #v[#v[5, 6], #v[7, 8]] #v[#v[10, 20], #v[30, 40]]
    #v[#v[29, 42], #v[73, 90]] (8, 8)
  verify (α := ℚ) 1 "rational" #v[#v[1 / 2, -3 / 2], #v[2, 0]]
    #v[#v[2, 1 / 3], #v[-2, 2 / 3]] #v[#v[1 / 4, -1 / 6], #v[3, 4]]
    #v[#v[17 / 4, -1], #v[7, 14 / 3]] (8, 8)
  let A : Vector (Vector Int (2 ^ 2)) (2 ^ 2) :=
    #v[#v[1, -2, 3, 4], #v[5, 6, -7, 8], #v[-9, 10, 11, -12], #v[13, -14, 15, 16]]
  let B : Vector (Vector Int (2 ^ 2)) (2 ^ 2) :=
    #v[#v[2, 3, -4, 5], #v[6, -7, 8, 9], #v[-10, 11, 12, -13], #v[14, 15, -16, 17]]
  let C := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => Int.ofNat (100 + 10 * i.val + j.val)))
  verify 2 "distinct signed offsets" A B C (oracle A B C) (64, 64)
  let A := Vector.ofFn (fun i : Fin (2 ^ 3) => Vector.ofFn
    (fun j : Fin (2 ^ 3) => Int.ofNat (i.val * 8 + j.val + 1)))
  let B := Vector.ofFn (fun i : Fin (2 ^ 3) => Vector.ofFn
    (fun j : Fin (2 ^ 3) => ((i.val + j.val) % 5 : Int) - 2))
  let C := Vector.ofFn (fun i : Fin (2 ^ 3) => Vector.ofFn
    (fun j : Fin (2 ^ 3) => Int.ofNat (100 + 10 * i.val + j.val)))
  verify 3 "complete asymmetric depth three" A B C (oracle A B C) (512, 512)
  let Z : Vector (Vector Int (2 ^ 1)) (2 ^ 1) := Vector.replicate _ (Vector.replicate _ 0)
  let C : Vector (Vector Int (2 ^ 1)) (2 ^ 1) := #v[#v[1, 2], #v[3, 4]]
  verify 1 "zero factors no skipping" Z Z C C (8, 8)
  let Z : Vector (Vector Int (2 ^ 2)) (2 ^ 2) := Vector.replicate _ (Vector.replicate _ 0)
  let C := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => Int.ofNat (10 * i.val + j.val + 1)))
  verify 2 "deeper zero factors no skipping" Z Z C C (64, 64)
  let I := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => if i = j then (1 : Int) else 0))
  let B := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => Int.ofNat (10 * i.val + j.val + 1)))
  let C := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => Int.ofNat (100 + 10 * i.val + j.val)))
  verify 2 "identity with saved C" I B C (oracle I B C) (64, 64)
  let A := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => if i.val + j.val = 3 then (i.val + 1 : Nat) else 0))
  let A : Vector (Vector Int (2 ^ 2)) (2 ^ 2) := A.map (fun row => row.map Int.ofNat)
  let B := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => 7 * (i.val : Int) - 3 * (j.val : Int) + 2))
  let C := Vector.ofFn (fun i : Fin (2 ^ 2) => Vector.ofFn
    (fun j : Fin (2 ^ 2) => (i.val : Int) - (j.val : Int)))
  verify 2 "asymmetric anti diagonal" A B C (oracle A B C) (64, 64)
  let shared : Vector (Vector Int (2 ^ 1)) (2 ^ 1) := #v[#v[1, 2], #v[3, 4]]
  verify 1 "same immutable input" shared shared shared (oracle shared shared shared) (8, 8)
  letI : Mul Nat := ⟨fun a b => a + b + 1⟩
  verify (α := Nat) 1 "no distributivity" #v[#v[1, 2], #v[3, 4]]
    #v[#v[5, 6], #v[7, 8]] #v[#v[10, 20], #v[30, 40]]
    #v[#v[27, 39], #v[51, 63]] (8, 8)
  letI : BEq (_root_.Matrix (Fin 2) (Fin 2) Int) := ⟨fun a b =>
    a 0 0 == b 0 0 && a 0 1 == b 0 1 && a 1 0 == b 1 0 && a 1 1 == b 1 1⟩
  letI : Repr (_root_.Matrix (Fin 2) (Fin 2) Int) := ⟨fun a _ =>
    repr (a 0 0, a 0 1, a 1 0, a 1 1)⟩
  let O : _root_.Matrix (Fin 2) (Fin 2) Int := 0
  let I : _root_.Matrix (Fin 2) (Fin 2) Int := fun i j => if i = j then 1 else 0
  let X : _root_.Matrix (Fin 2) (Fin 2) Int := fun i j => if i = 0 ∧ j = 1 then 1 else 0
  let Y : _root_.Matrix (Fin 2) (Fin 2) Int := fun i j => if i = 1 ∧ j = 0 then 1 else 0
  let E : _root_.Matrix (Fin 2) (Fin 2) Int := fun i j =>
    if i = 0 ∧ j = 0 then 2 else if i = 1 ∧ j = 1 then 1 else 0
  let F : _root_.Matrix (Fin 2) (Fin 2) Int := fun i j =>
    if i = 0 ∧ j = 0 then 2 else if i = 1 ∧ j = 1 then 3 else 0
  verify 1 "noncommuting matrix scalars" #v[#v[X, O], #v[I, Y]]
    #v[#v[Y, I], #v[O, X]] #v[#v[I, O], #v[O, I]] #v[#v[E, X], #v[Y, F]] (8, 8)
  letI : Add String := ⟨fun a b => "(" ++ a ++ "+" ++ b ++ ")"⟩
  letI : Mul String := ⟨fun a b => "(" ++ a ++ "*" ++ b ++ ")"⟩
  verify (α := String) 1 "law free recorded update order" #v[#v["a", "b"], #v["c", "d"]]
    #v[#v["e", "f"], #v["g", "h"]] #v[#v["x", "y"], #v["z", "w"]]
    #v[#v["((x+(a*e))+(b*g))", "((y+(a*f))+(b*h))"],
      #v["((z+(c*e))+(d*g))", "((w+(c*f))+(d*h))"]] (8, 8)

#eval runTests

end
