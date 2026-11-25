/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Partition.RegularCubicOverlined

open MetaMathlibExt PowerSeries

namespace MetaMathlibExt.regularCubicOverlinedCount_four_prime_mod_four

local instance fivePrime : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_nonsquare : legendreSym 5 (-2) = -1 := by
  apply (legendreSym.eq_neg_one_iff 5).mpr
  change ¬ ∃ x : ZMod 5, (-2 : ZMod 5) = x * x
  decide

-- One prime-square step takes the constant coefficient to index 37.
example : regularCubicOverlinedCount 4 37 ≡ 2 [ZMOD 4] := by
  have h := (regularCubicOverlinedCount_four_prime_mod_four 5 (by decide) five_nonsquare 1).1 0
  simpa (disch := decide) [coeff_zero_eq_constantCoeff, constantCoeff_qEulerProduct] using h

-- The first and last admissible nonzero residue classes at p = 5.
example : regularCubicOverlinedCount 4 57 ≡ 0 [ZMOD 4] ∧
    regularCubicOverlinedCount 4 117 ≡ 0 [ZMOD 4] := by
  have h := (regularCubicOverlinedCount_four_prime_mod_four 5 (by decide) five_nonsquare 0).2
  exact ⟨h 0 1 (by decide) (by decide), h 0 4 (by decide) (by decide)⟩

end MetaMathlibExt.regularCubicOverlinedCount_four_prime_mod_four
