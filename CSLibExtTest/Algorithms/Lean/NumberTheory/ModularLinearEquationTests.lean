/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.NumberTheory.ModularLinearEquation
meta import CSLibExt.Algorithms.Lean.NumberTheory.ModularLinearEquation

/-! Runtime checks for the ordered modular-linear-equation solver. -/

namespace Cslib.Algorithms.Lean.ModularLinearEquationTests

open Cslib.Algorithms.Lean.ModularLinearEquation

private structure Case where
  name : String
  a : Nat
  b : Int
  n : Nat
  ha : 0 < a
  hn : 0 < n
  expected : Array Nat
  expectedTime : Nat

private def cases : Array Case := #[
  ⟨"CLRS printed 926", 14, 30, 100, by decide, by decide, #[95, 45], 29⟩,
  ⟨"equal operands", 5, 5, 5, by decide, by decide, #[0, 1, 2, 3, 4], 26⟩,
  ⟨"negative b", 14, -30, 100, by decide, by decide, #[5, 55], 29⟩,
  ⟨"shifted b", 14, 130, 100, by decide, by decide, #[45, 95], 29⟩,
  ⟨"no solution", 6, 5, 12, by decide, by decide, #[], 13⟩,
  ⟨"coprime inverse", 3, 1, 7, by decide, by decide, #[5], 26⟩,
  ⟨"modulus one", 4, -17, 1, by decide, by decide, #[0], 14⟩,
  ⟨"large gcd", 12, 24, 12, by decide, by decide,
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11], 47⟩,
  ⟨"a exceeds modulus", 114, 30, 100, by decide, by decide, #[95, 45], 29⟩
]

private def check (name : String) (condition : Bool) : IO Unit :=
  unless condition do throw <| IO.userError s!"failed: {name}"

private def runCases : IO Unit := do
  for c in cases do
    let actual := modularLinearEquationSolver c.a c.b c.n c.ha c.hn
    check s!"{c.name} output: {actual.ret}" (actual.ret == c.expected)
    check s!"{c.name} time: {actual.time}" (actual.time == c.expectedTime)

private def expectFailure (name : String) (action : IO Unit) : IO Unit := do
  let failed ← try
    action
    pure false
  catch _ =>
    pure true
  check s!"control did not fail: {name}" failed

private def runControls : IO Unit := do
  let source := modularLinearEquationSolver 14 30 100 (by decide) (by decide)
  expectFailure "sorted rather than source order" <|
    check "wrong order" (source.ret == #[45, 95])
  runCases
  let signed := modularLinearEquationSolver 14 (-30) 100 (by decide) (by decide)
  expectFailure "wrong signed residue" <|
    check "wrong signed residue" (signed.ret == #[95, 45])
  runCases
  expectFailure "wrong cardinality" <|
    check "wrong cardinality" (source.ret == #[95])
  runCases
  expectFailure "wrong arithmetic count" <|
    check "wrong arithmetic count" (source.time == 28)
  runCases

private example
    (a : Nat) (b : Int) (n : Nat) (ha : 0 < a) (hn : 0 < n) (x : Nat) :
    x ∈ (modularLinearEquationSolver a b n ha hn).ret.toList ↔
      x < n ∧ Int.ModEq (n : Int) ((a : Int) * (x : Int)) b :=
  modularLinearEquationSolver_mem_iff a b n ha hn x

private example :
    (modularLinearEquationSolver 4 (-17) 1 (by decide) (by decide)).ret.size =
      if (Nat.gcd 4 1 : Int) ∣ -17 then Nat.gcd 4 1 else 0 :=
  modularLinearEquationSolver_length 4 (-17) 1 (by decide) (by decide)

private def runAll : IO Unit := do
  runCases
  runControls
  IO.println "U110 fixtures=9 controls=4 fullRestores=4"

#eval runAll

end Cslib.Algorithms.Lean.ModularLinearEquationTests
