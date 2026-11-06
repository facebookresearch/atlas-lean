/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQCacheCertificate00
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQCacheCertificate01
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQCacheCertificate02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddFourthQCacheCertificate03

/-! The checked complete original coordinate images of all four comparisons. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false

/-- Every coordinate cache is the entire actual source image. -/
theorem generatedAxisGlobalOddFourthQCache_certificate (k : Fin 4) (i : Fin 24) :
    generatedAxisGlobalOddFourthQImage k (qCoordinateGenerator i) =
      generatedAxisGlobalOddFourthQCache k i := by
  fin_cases k
  · exact generatedAxisGlobalOddFourthQCache00_certificate i
  · exact generatedAxisGlobalOddFourthQCache01_certificate i
  · exact generatedAxisGlobalOddFourthQCache02_certificate i
  · exact generatedAxisGlobalOddFourthQCache03_certificate i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
