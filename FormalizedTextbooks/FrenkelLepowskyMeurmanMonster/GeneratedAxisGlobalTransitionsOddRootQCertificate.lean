/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache03
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache04
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache05
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache06
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache07
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRootQCache08

/-! Complete phase-correct actual extraspecial conjugation for all nine original odd root words. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- All nine original root words have their 24 complete coordinate images checked by the kernel. -/
theorem generatedAxisGlobalOddRootQCache_certificate (k : Fin 9) (i : Fin 24) :
    generatedAxisGlobalOddSourceFastWord (generatedAxisGlobalOddSourceRootWords k)
      (qCoordinateGenerator i) = generatedAxisGlobalOddRootQCache k i := by
  fin_cases k
  · exact generatedAxisGlobalOddRootQCache00_certificate i
  · exact generatedAxisGlobalOddRootQCache01_certificate i
  · exact generatedAxisGlobalOddRootQCache02_certificate i
  · exact generatedAxisGlobalOddRootQCache03_certificate i
  · exact generatedAxisGlobalOddRootQCache04_certificate i
  · exact generatedAxisGlobalOddRootQCache05_certificate i
  · exact generatedAxisGlobalOddRootQCache06_certificate i
  · exact generatedAxisGlobalOddRootQCache07_certificate i
  · exact generatedAxisGlobalOddRootQCache08_certificate i

/-- The complete compact source evaluator equals the actual action on every Q element. -/
theorem generatedAxisGlobalOddRootQFast_all_actual (k : Fin 9) (q : Q) :
    spinConjugation (generatedAxisGlobalOddSourceRootFiber k).val.1 q =
      generatedAxisGlobalOddRootQFast k q := by
  rw [generatedAxisGlobalOddSourceFastRoot_actual]
  exact generatedAxisGlobalOddRootQFast_actual k
    (generatedAxisGlobalOddRootQCache_certificate k) q

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
