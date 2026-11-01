/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep02Block15

/-! Every physical source output follows from sixteen complete bounded integer certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem generatedAxisGlobalOddRoot00SpinStep02_blocks (b : Fin 16) (n : Fin 256) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 9 generatedAxisGlobalOddRoot00Spin01
      (generatedAxisGlobalOddSpinOutputBlock b n) =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin02 (generatedAxisGlobalOddSpinOutputBlock b
      n) := by
  fin_cases b
  · exact generatedAxisGlobalOddRoot00SpinStep02Block00_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block01_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block02_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block03_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block04_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block05_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block06_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block07_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block08_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block09_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block10_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block11_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block12_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block13_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block14_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep02Block15_certificate n

/-- Every physical spin output has the exact original numerator and denominator. -/
theorem generatedAxisGlobalOddRoot00SpinStep02_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 9 generatedAxisGlobalOddRoot00Spin01 k =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin02 k := by
  let b : Fin 16 := ⟨k.val / 256, by have hk := k.isLt; omega⟩
  let n : Fin 256 := ⟨k.val % 256, Nat.mod_lt _ (by decide)⟩
  have hi : generatedAxisGlobalOddSpinOutputBlock b n = k :=
    generatedAxisGlobalOddSpinOutputBlock_roundtrip k
  simpa only [hi] using generatedAxisGlobalOddRoot00SpinStep02_blocks b n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
