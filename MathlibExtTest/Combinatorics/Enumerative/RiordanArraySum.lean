/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RiordanArraySum

open PowerSeries

namespace MetaMathlibExt

variable {R : Type*} [CommRing R]

-- The zeroth row has a single entry.
example (d h f : PowerSeries R) (hh : constantCoeff h = 0) :
    coeff 0 (d * f.subst h) = coeff 0 d * coeff 0 f := by
  simpa using (riordan_array_sum_eq_coeff_subst d h f hh 0).symm

-- Substituting X² leaves only the constant and linear terms of f in degree two.
example (d f : PowerSeries R) :
    coeff 2 (d * f.subst (X ^ 2)) = coeff 2 d * coeff 0 f + coeff 0 d * coeff 1 f := by
  rw [← riordan_array_sum_eq_coeff_subst d (X ^ 2) f (by simp)]
  simp [Finset.sum_range_succ, ← pow_mul, coeff_mul_X_pow']

end MetaMathlibExt
