/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep01Block15

/-! Every physical source output follows from sixteen complete bounded integer certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem generatedAxisGlobalOddRoot00SpinStep01_blocks (b : Fin 16) (n : Fin 256) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot00Spin00
      (generatedAxisGlobalOddSpinOutputBlock b n) =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin01 (generatedAxisGlobalOddSpinOutputBlock b
      n) := by
  fin_cases b
  · exact generatedAxisGlobalOddRoot00SpinStep01Block00_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block01_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block02_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block03_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block04_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block05_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block06_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block07_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block08_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block09_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block10_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block11_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block12_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block13_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block14_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep01Block15_certificate n

/-- Every physical spin output has the exact original numerator and denominator. -/
theorem generatedAxisGlobalOddRoot00SpinStep01_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 0 generatedAxisGlobalOddRoot00Spin00 k =
      8 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin01 k := by
  let b : Fin 16 := ⟨k.val / 256, by have hk := k.isLt; omega⟩
  let n : Fin 256 := ⟨k.val % 256, Nat.mod_lt _ (by decide)⟩
  have hi : generatedAxisGlobalOddSpinOutputBlock b n = k :=
    generatedAxisGlobalOddSpinOutputBlock_roundtrip k
  simpa only [hi] using generatedAxisGlobalOddRoot00SpinStep01_blocks b n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
