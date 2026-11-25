/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.CharacteristicPolynomial

namespace MathlibExt.Combinatorics.MatroidHodgeTheoryWanted.CharacteristicPolynomialTest

open MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted
open MathlibExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted

/- A loop makes the empty and singleton subsets cancel, even at rank zero. -/
example : charPolyCoeff (Matroid.loopyOn (Set.univ : Set (Fin 1))) 0 = 0 := by
  classical
  simp [charPolyCoeff, finRank, Matroid.eRk_loopyOn]
  decide

/- The top two coefficients of the three-element free matroid have opposite signs. -/
private abbrev booleanThree := Matroid.freeOn (Set.univ : Set (Fin 3))

example : charPolyCoeff booleanThree 3 = 1 ∧ charPolyCoeff booleanThree 2 = -3 := by
  classical
  simp [charPolyCoeff, finRank, booleanThree, Matroid.eRk_freeOn]
  decide

example : charPolyAbsCoeff booleanThree 4 = 0 := by
  simp [charPolyAbsCoeff, booleanThree, finRank]

end MathlibExt.Combinatorics.MatroidHodgeTheoryWanted.CharacteristicPolynomialTest
