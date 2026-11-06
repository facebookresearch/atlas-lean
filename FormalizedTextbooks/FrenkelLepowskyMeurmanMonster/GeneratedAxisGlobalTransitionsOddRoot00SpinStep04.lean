/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStep04Block15

/-! Every physical source output follows from sixteen complete bounded integer certificates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

private theorem generatedAxisGlobalOddRoot00SpinStep04_blocks (b : Fin 16) (n : Fin 256) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 7 generatedAxisGlobalOddRoot00Spin03
      (generatedAxisGlobalOddSpinOutputBlock b n) =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin04 (generatedAxisGlobalOddSpinOutputBlock b
      n) := by
  fin_cases b
  · exact generatedAxisGlobalOddRoot00SpinStep04Block00_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block01_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block02_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block03_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block04_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block05_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block06_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block07_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block08_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block09_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block10_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block11_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block12_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block13_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block14_certificate n
  · exact generatedAxisGlobalOddRoot00SpinStep04Block15_certificate n

/-- Every physical spin output has the exact original numerator and denominator. -/
theorem generatedAxisGlobalOddRoot00SpinStep04_certificate (k : Fin 4096) :
    (1 : ℤ) * generatedAxisGlobalOddSpinPrimitive 7 generatedAxisGlobalOddRoot00Spin03 k =
      1 * (1 : ℤ) * generatedAxisGlobalOddRoot00Spin04 k := by
  let b : Fin 16 := ⟨k.val / 256, by have hk := k.isLt; omega⟩
  let n : Fin 256 := ⟨k.val % 256, Nat.mod_lt _ (by decide)⟩
  have hi : generatedAxisGlobalOddSpinOutputBlock b n = k :=
    generatedAxisGlobalOddSpinOutputBlock_roundtrip k
  simpa only [hi] using generatedAxisGlobalOddRoot00SpinStep04_blocks b n

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
