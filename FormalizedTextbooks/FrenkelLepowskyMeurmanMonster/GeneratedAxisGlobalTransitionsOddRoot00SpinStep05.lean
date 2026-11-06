/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep05Block15

/-! Every physical source output follows from sixteen complete bounded integer certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem generatedAxisGlobalOddRoot00SpinStep05_blocks (b : Fin 16) (n : Fin 256) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 7 generatedAxisGlobalOddRoot00Spin04
      (generatedAxisGlobalOddSpinOutputBlock b n) =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin05 (generatedAxisGlobalOddSpinOutputBlock b
      n) := by
  fin_cases b
  · exact generatedAxisGlobalOddRoot00SpinStep05Block00_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block01_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block02_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block03_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block04_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block05_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block06_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block07_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block08_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block09_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block10_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block11_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block12_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block13_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block14_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep05Block15_certificate n

/-- Every physical spin output has the exact original numerator and denominator. -/
theorem generatedAxisGlobalOddRoot00SpinStep05_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 7 generatedAxisGlobalOddRoot00Spin04 k =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin05 k := by
  let b : Fin 16 := ⟨k.val / 256, by have hk := k.isLt; omega⟩
  let n : Fin 256 := ⟨k.val % 256, Nat.mod_lt _ (by decide)⟩
  have hi : generatedAxisGlobalOddSpinOutputBlock b n = k :=
    generatedAxisGlobalOddSpinOutputBlock_roundtrip k
  simpa only [hi] using generatedAxisGlobalOddRoot00SpinStep05_blocks b n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
