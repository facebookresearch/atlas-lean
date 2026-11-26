/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.HibiSymmetricHStarUnimodal
import Mathlib.Tactic.NormNum

/-! # Tests for the weighted-simplex counterexample to Hibi's conjecture -/

namespace MathlibExtTest.Combinatorics.HibiSymmetricHStarUnimodal

open MathlibExt.Combinatorics MetaMathlibExt

example : (interior (weightedSimplex ![1, 1, 1, 1, 1, 3])).Nonempty :=
  hibiWeightedSimplex_hStar.1

noncomputable section

private def numerator : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (LatticePointEnumerator.latticeEnumerator 6
    (weightedSimplex ![1, 1, 1, 1, 1, 3]) n : ℤ)) * (1 - PowerSeries.X) ^ 7

-- Check the strict dip in the numerator defined from the geometric lattice counts.
example : PowerSeries.coeff 2 numerator = 2 ∧ PowerSeries.coeff 3 numerator = 1 ∧
    PowerSeries.coeff 4 numerator = 2 := by
  unfold numerator
  rw [hibiWeightedSimplex_hStar.2]
  norm_num only [Polynomial.coeff_coe, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_ofNat_mul]
  decide

end

end MathlibExtTest.Combinatorics.HibiSymmetricHStarUnimodal
