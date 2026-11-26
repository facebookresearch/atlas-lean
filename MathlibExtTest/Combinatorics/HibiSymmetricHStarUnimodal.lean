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

open MathlibExt.Combinatorics MetaMathlibExt Polynomial
open MathlibExt.Combinatorics.HibiSymmetricHStarUnimodalOWR741Problem003Wanted

example : (interior (weightedSimplex ![1, 1, 1, 1, 1, 3])).Nonempty :=
  hibiWeightedSimplex_interior_nonempty

example : ¬ hibiSymmetricUnimodal := hibiSymmetricUnimodal_refuted

-- Taking the convex hull of a single integral point preserves that point.
example : latticePolytope ({0} : Finset (Fin 1 → ℤ)) = ({0} : Set (Fin 1 → ℝ)) := by
  simp [latticePolytope, convexHull_singleton]
  rfl

example : IsHStarPolynomial (weightedSimplex ![1, 1, 1, 1, 1, 3])
    (1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6) :=
  hibiWeightedSimplex_hStar

noncomputable section

private def numerator : PowerSeries ℤ :=
  PowerSeries.mk (fun n => (LatticePointEnumerator.latticeEnumerator 6
    (weightedSimplex ![1, 1, 1, 1, 1, 3]) n : ℤ)) * (1 - PowerSeries.X) ^ 7

-- Check the strict dip in the numerator defined from the geometric lattice counts.
example : PowerSeries.coeff 2 numerator = 2 ∧ PowerSeries.coeff 3 numerator = 1 ∧
    PowerSeries.coeff 4 numerator = 2 := by
  unfold numerator
  have h := hibiWeightedSimplex_hStar
  simp only [IsHStarPolynomial, ehrhart_eq_latticeEnumerator, Fintype.card_fin] at h
  rw [h]
  norm_num only [Polynomial.coeff_coe, Polynomial.coeff_add, Polynomial.coeff_one,
    Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_ofNat_mul]
  decide

end

end MathlibExtTest.Combinatorics.HibiSymmetricHStarUnimodal
