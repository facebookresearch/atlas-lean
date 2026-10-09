/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Strassen
public meta import CSLibExt.Algorithms.Lean.Matrix.Strassen
public meta import Cslib.Algorithms.Lean.TimeM
public meta import Mathlib.Data.Matrix.Block
public meta import Mathlib.Data.Int.Basic

/-!
# Strassen execution regression tests

Every fixture runs the retained executor and checks all returned entries and both
scalar counters. The CLRS fourth-edition exercise 4.2-1 matrices are copied from
printed page 89. Signed dense and zero-factor cases exercise every depth from
one through four. Matrix-valued scalars detect recursive operand reversal; the
expression carrier has only the four operations, with no algebraic laws.

Retained Lean was authored by Codex at Adam Kiezun's explicit selection.
-/

set_option autoImplicit false

namespace CSLibExtTest.Algorithms.Matrix.Strassen

universe u

open Cslib.Algorithms.Lean.TimeM
open Cslib.Algorithms.Lean.Matrix

private meta def verify {R : Type u} [BEq R] [Repr R] (label : String)
    (actual expected : R) : IO Unit := do
  unless actual == expected do
    throw (IO.userError s!"{label}: actual={repr actual}, expected={repr expected}")
  IO.println s!"{label}: {repr actual}"

private meta def reference {n : Nat} (C A B : Vector (Vector Int n) n) :
    Vector (Vector Int n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    (C.get i).get j + ((Matrix.of fun i j => (A.get i).get j) *
      Matrix.of fun i j => (B.get i).get j) i j

private meta def dense (n : Nat) (entry : Int → Int → Int) : Vector (Vector Int n) n :=
  Vector.ofFn fun i => Vector.ofFn fun j => entry i.val j.val

private meta def mat (a b c d : Int) : Matrix (Fin 2) (Fin 2) Int :=
  Matrix.of fun i j => if i.val == 0 then (if j.val == 0 then a else b)
    else (if j.val == 0 then c else d)

private meta def entries (M : Matrix (Fin 2) (Fin 2) Int) : Vector Int 4 :=
  #v[M 0 0, M 0 1, M 1 0, M 1 1]

private meta def recursiveNoncommutative :
    Cslib.Algorithms.Lean.TimeM (Nat × Nat)
      (Vector (Vector (Matrix (Fin 2) (Fin 2) Int) 2) 2) :=
  strassenMatrixAccumulate 1
    #v[#v[mat 0 1 0 0, mat 0 0 1 0], #v[mat 1 0 0 0, mat 0 0 0 1]]
    #v[#v[mat 0 0 1 0, mat 1 0 0 0], #v[mat 0 0 0 1, mat 0 1 0 0]]
    #v[#v[mat 11 12 13 14, mat 21 22 23 24],
      #v[mat 31 32 33 34, mat 41 42 43 44]]

meta section

private structure NoLaws where
  text : String
  deriving BEq, Repr

private instance : Zero NoLaws := ⟨⟨"0"⟩⟩
private instance : Add NoLaws := ⟨fun a b => ⟨s!"A({a.text},{b.text})"⟩⟩
private instance : Sub NoLaws := ⟨fun a b => ⟨s!"S({a.text},{b.text})"⟩⟩
private instance : Mul NoLaws := ⟨fun a b => ⟨s!"M({a.text},{b.text})"⟩⟩

private def runLawFreeTests : IO Unit := do
  let singleton := strassenMatrixAccumulate 0
    #v[#v[⟨"a"⟩]] #v[#v[⟨"b"⟩]] (#v[#v[⟨"c"⟩]] : Vector (Vector NoLaws 1) 1)
  verify "law-free singleton expression" singleton.ret #v[#v[⟨"A(c,M(a,b))"⟩]]
  verify "law-free singleton counts" singleton.time (1, 1)
  let zero := strassenMatrixAccumulate 0
    (#v[#v[0]] : Vector (Vector NoLaws 1) 1) #v[#v[0]] #v[#v[0]]
  verify "law-free zero is not optimized" zero.ret #v[#v[⟨"A(0,M(0,0))"⟩]]
  verify "law-free zero counts" zero.time (1, 1)
  let a : Vector NoLaws 4 := #v[⟨"a11"⟩, ⟨"a12"⟩, ⟨"a21"⟩, ⟨"a22"⟩]
  let b : Vector NoLaws 4 := #v[⟨"b11"⟩, ⟨"b12"⟩, ⟨"b21"⟩, ⟨"b22"⟩]
  let c : Vector NoLaws 4 := #v[⟨"c11"⟩, ⟨"c12"⟩, ⟨"c21"⟩, ⟨"c22"⟩]
  let p₁ := (0 : NoLaws) + a[0] * (b[1] - b[3])
  let p₂ := (0 : NoLaws) + (a[0] + a[1]) * b[3]
  let p₃ := (0 : NoLaws) + (a[2] + a[3]) * b[0]
  let p₄ := (0 : NoLaws) + a[3] * (b[2] - b[0])
  let p₅ := (0 : NoLaws) + (a[0] + a[3]) * (b[0] + b[3])
  let p₆ := (0 : NoLaws) + (a[1] - a[3]) * (b[2] + b[3])
  let p₇ := (0 : NoLaws) + (a[0] - a[2]) * (b[0] + b[1])
  let actual := strassenMatrixAccumulate 1
    #v[#v[a[0], a[1]], #v[a[2], a[3]]] #v[#v[b[0], b[1]], #v[b[2], b[3]]]
    #v[#v[c[0], c[1]], #v[c[2], c[3]]]
  verify "law-free all four source expressions including seven zero adds" actual.ret
    #v[#v[(((c[0] + p₅) + p₄) - p₂) + p₆, (c[1] + p₁) + p₂],
      #v[(c[2] + p₃) + p₄, (((c[3] + p₅) + p₁) - p₃) - p₇]]
  verify "law-free recursive counts" actual.time (7, 29)
  verify "law-free zero is not an identity" (((0 : NoLaws) + a[0]) == a[0]) false
  verify "law-free addition is not associative"
    (((a[0] + a[1]) + a[2]) == (a[0] + (a[1] + a[2]))) false
  verify "law-free multiplication is not commutative" (a[0] * a[1] == a[1] * a[0]) false

private def runTests (args : List String := []) : IO Unit := do
  let singleton := strassenMatrixAccumulate 0
    #v[#v[3]] #v[#v[-4]] (#v[#v[7]] : Vector (Vector Int 1) 1)
  let A : Vector (Vector Int 2) 2 := #v[#v[1, 3], #v[7, 5]]
  let B : Vector (Vector Int 2) 2 := #v[#v[6, 8], #v[4, 2]]
  let source := strassenMatrixAccumulate 1 A B (Vector.replicate 2 (Vector.replicate 2 0))
  let saved := strassenMatrixAccumulate 1 A B #v[#v[9, -3], #v[2, 17]]
  let signed := strassenMatrixAccumulate 1
    #v[#v[2, -1], #v[-3, 4]] #v[#v[-5, 6], #v[7, -8]]
    (#v[#v[7, -6], #v[5, -4]] : Vector (Vector Int 2) 2)
  let nc := recursiveNoncommutative
  if args == ["wrong-count"] then
    verify "executor wrong-count" source.time (7, 25)
  else if args == ["wrong-saved-C"] then
    verify "executor wrong-saved-C" saved.ret #v[#v[18, 14], #v[62, 66]]
  else if args == ["wrong-sign"] then
    verify "executor wrong-sign" signed.ret #v[#v[-10, -14], #v[48, -54]]
  else if args == ["wrong-operand-order"] then
    verify "executor wrong-operand-order" (nc.ret.map (·.map entries))
      #v[#v[#v[11, 12, 14, 15], #v[22, 23, 23, 24]],
        #v[#v[31, 32, 34, 35], #v[42, 43, 43, 44]]]
  else
    verify "singleton all saved entries" singleton.ret #v[#v[-5]]
    verify "singleton counts" singleton.time (1, 1)
    verify "CLRS exercise all four entries" source.ret #v[#v[18, 14], #v[62, 66]]
    verify "CLRS exercise counts" source.time (7, 29)
    verify "CLRS exercise nonzero saved C" saved.ret #v[#v[27, 11], #v[64, 83]]
    verify "CLRS exercise saved C counts" saved.time (7, 29)
    verify "mixed signed all four entries" signed.ret #v[#v[-10, 14], #v[48, -54]]
    verify "mixed signed counts" signed.time (7, 29)
    for (k, cost) in [(1, (7, 29)), (2, (49, 291)), (3, (343, 2389)), (4, (2401, 18131))] do
      let n := 2 ^ k
      let A := dense n fun i j => 3 * i - 2 * j + 1
      let B := dense n fun i j => i + 4 * j - 3
      let C := dense n fun i j => 11 + i - j
      let actual := strassenMatrixAccumulate k A B C
      verify s!"depth {k} signed dense all entries" actual.ret (reference C A B)
      verify s!"depth {k} signed dense counts" actual.time cost
      let Z : Vector (Vector Int n) n := Vector.replicate n (Vector.replicate n 0)
      let C := dense n fun i j => 10 * i + j + 1
      let actual := strassenMatrixAccumulate k Z Z C
      verify s!"depth {k} zero factors all saved entries" actual.ret C
      verify s!"depth {k} zero factors counts not skipped" actual.time cost
    let h : Int := 10 ^ 45
    let C : Vector (Vector Int 2) 2 := #v[#v[3, 5], #v[7, 11]]
    let A : Vector (Vector Int 2) 2 := #v[#v[h, -h], #v[h + 1, h - 1]]
    let B : Vector (Vector Int 2) 2 := #v[#v[h, 1], #v[h, -1]]
    let actual := strassenMatrixAccumulate 1 A B C
    verify "large unbounded integers all four entries" actual.ret (reference C A B)
    verify "large unbounded integers counts" actual.time (7, 29)
    verify "recursive matrix scalars all sixteen entries" (nc.ret.map (·.map entries))
      #v[#v[#v[12, 12, 13, 14], #v[21, 22, 23, 25]],
        #v[#v[31, 32, 33, 35], #v[42, 42, 43, 44]]]
    verify "recursive matrix scalar abstract counts" nc.time (7, 29)
    runLawFreeTests

#eval runTests

end

end CSLibExtTest.Algorithms.Matrix.Strassen
