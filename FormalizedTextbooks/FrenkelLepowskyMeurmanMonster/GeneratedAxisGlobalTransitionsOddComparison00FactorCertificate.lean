/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparisonTensorFactors
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00TensorData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot00SpinStateData

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock08
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock09
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock12
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock13
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock14
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddComparison00FactorBlock15

/-! Complete original signed-translation and four-input source-sign factor certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 2000000 in
/-- All 4096 original coefficients follow from sixteen independently checked physical blocks. -/
theorem generatedAxisGlobalOddComparison00Spin_certificate (i : Fin 4096) :
    generatedAxisGlobalOddComparisonSpinInteger 0 generatedAxisGlobalOddRoot00Spin12 i =
      generatedAxisGlobalOddComparison00Spin i := by
  have blocks (b : Fin 16) (j : Fin 256) :
      generatedAxisGlobalOddComparisonSpinInteger 0
          generatedAxisGlobalOddRoot00Spin12 ⟨256 * b.val + j.val, by omega⟩ =
        generatedAxisGlobalOddComparison00Spin ⟨256 * b.val + j.val, by omega⟩ := by
    fin_cases b
    · exact generatedAxisGlobalOddComparison00FactorBlock00 j
    · exact generatedAxisGlobalOddComparison00FactorBlock01 j
    · exact generatedAxisGlobalOddComparison00FactorBlock02 j
    · exact generatedAxisGlobalOddComparison00FactorBlock03 j
    · exact generatedAxisGlobalOddComparison00FactorBlock04 j
    · exact generatedAxisGlobalOddComparison00FactorBlock05 j
    · exact generatedAxisGlobalOddComparison00FactorBlock06 j
    · exact generatedAxisGlobalOddComparison00FactorBlock07 j
    · exact generatedAxisGlobalOddComparison00FactorBlock08 j
    · exact generatedAxisGlobalOddComparison00FactorBlock09 j
    · exact generatedAxisGlobalOddComparison00FactorBlock10 j
    · exact generatedAxisGlobalOddComparison00FactorBlock11 j
    · exact generatedAxisGlobalOddComparison00FactorBlock12 j
    · exact generatedAxisGlobalOddComparison00FactorBlock13 j
    · exact generatedAxisGlobalOddComparison00FactorBlock14 j
    · exact generatedAxisGlobalOddComparison00FactorBlock15 j
  let b : Fin 16 := ⟨i.val / 256, by omega⟩
  let j : Fin 256 := ⟨i.val % 256, Nat.mod_lt _ (by decide)⟩
  have hi : (⟨256 * b.val + j.val, by omega⟩ : Fin 4096) = i := by
    apply Fin.ext
    dsimp [b, j]
    omega
  have h := blocks b j
  simpa only [hi] using h

set_option maxHeartbeats 20000000 in
/-- Every original physical spatial coordinate has its actual code sign. -/
theorem generatedAxisGlobalOddComparison00Spatial_certificate (i : Fin 24) :
    generatedAxisGlobalOddComparisonSpatialInteger 0
        generatedAxisGlobalOddRoot00Spatial12 i =
      generatedAxisGlobalOddComparison00Spatial i := by
  revert i
  decide +kernel

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
