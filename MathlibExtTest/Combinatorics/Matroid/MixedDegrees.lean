/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Matroid.MixedDegrees

namespace MathlibExt.Combinatorics.MatroidHodgeTheoryWanted.MixedDegreesTest

open MathlibExt.Combinatorics.Matroid.Chow
open MathlibExt.Combinatorics.MatroidCharacteristicPolynomialLogConcaveAMR156Problem0026Wanted
open MathlibExt.Combinatorics.MatroidReducedCharacteristicPolynomialWanted

private abbrev booleanThree := Matroid.freeOn (Set.univ : Set (Fin 3))

private instance booleanThreeLoopless : booleanThree.Loopless :=
  Matroid.loopless_iff_forall_not_isLoop.mpr fun e _ => Matroid.freeOn_not_isLoop _ e

private theorem booleanThree_rank : booleanThree.eRank = 3 := by
  simp [booleanThree, Matroid.eRank_freeOn]

/- For the rank-three Boolean matroid, the reduced polynomial is (λ - 1)².
Its middle coefficient gives the genuinely mixed product, and its constant gives β². -/
example (deg : ChowRing booleanThree →ₗ[ℝ] ℝ) (hd : IsDegreeMap booleanThree 2 deg) :
    deg (alphaClass booleanThree 0 * betaClass booleanThree 0) = 2 ∧
      deg (betaClass booleanThree 0 ^ 2) = 1 := by
  classical
  have h (k : ℕ) (hk : k ≤ 2) :=
    reducedCharPolyCoeff_eq_deg booleanThree 2 booleanThree_rank deg hd 0 (Set.mem_univ _) k hk
  have hc : reducedCharPolyCoeff booleanThree 1 = 2 ∧ reducedCharPolyCoeff booleanThree 2 = 1 := by
    simp [reducedCharPolyCoeff, charPolyCoeff, finRank, booleanThree, Matroid.eRk_freeOn,
      Finset.sum_range_succ]
    decide
  exact ⟨by simpa [hc.1] using (h 1 (by decide)).symm,
    by simpa [hc.2] using (h 2 (by decide)).symm⟩

end MathlibExt.Combinatorics.MatroidHodgeTheoryWanted.MixedDegreesTest
