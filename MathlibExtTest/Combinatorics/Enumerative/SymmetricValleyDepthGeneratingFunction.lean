/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.SymmetricValleyDepthGeneratingFunction
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.Ring

/-! # Initial coefficients of the symmetric valley depth generating function -/

open MetaMathlibExt PowerSeries

namespace MathlibExtTest.SymmetricValleyDepthGeneratingFunction

-- The first valley is 212 at size five. Size eight includes 21212 with two overlapping valleys.
example :
    X ^ 9 ∣ PowerSeries.mk
      (fun n => ((∑ c : Composition n, symmetricValleyDepthSum c.blocks : ℕ) : ℤ)) -
        (X ^ 5 + 2 * X ^ 6 + 7 * X ^ 7 + 17 * X ^ 8) := by
  let Q : ℤ⟦X⟧ := (1 - 2 * X) ^ 2 * (1 - X ^ 3) * (1 - X ^ 2) ^ 2
  have hQ : IsUnit Q := isUnit_iff_constantCoeff.mpr (by simp [Q])
  rw [← hQ.dvd_mul_right, sub_mul, symmetricValleyDepthSum_compositions_genFun,
    X_pow_dvd_iff]
  intro n hn
  dsimp [Q]
  ring_nf
  simp [map_add, map_sub, coeff_mul_ofNat, coeff_X_pow, show ∀ k ≥ 9, n ≠ k by omega]

end MathlibExtTest.SymmetricValleyDepthGeneratingFunction
