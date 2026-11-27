/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MockThetaCoefficients

open PowerSeries MetaMathlibExt

-- The smallest odd prime has one ordinary row.
example : ramanujanThetaMonomial 1 1 3 =
    ramanujanThetaMonomial 1 6 3 + X * ramanujanThetaMonomial 1 9 27 := by
  simpa [Finset.sum_range_succ] using (ramanujanPsi_p_dissection 3 (by decide) (by decide)).1

-- At five the last ordinary row has shift one, and the central row has shift three.
example : ramanujanThetaMonomial 1 1 3 =
    ramanujanThetaMonomial 1 15 10 + X * ramanujanThetaMonomial 1 20 5 +
      X ^ 3 * ramanujanThetaMonomial 1 25 75 := by
  simpa [Finset.sum_range_succ] using (ramanujanPsi_p_dissection 5 (by decide) (by decide)).1

example (m : ℕ) (hm : m ≤ 1) : ¬ (m ^ 2 + m) / 2 ≡ 3 [MOD 5] :=
  (ramanujanPsi_p_dissection 5 (by decide) (by decide)).2 m hm

-- Both signed indices contribute to the first coefficient when the arguments coincide.
example : coeff 1 (ramanujanThetaMonomial (-1) 1 1) = -2 := by
  simp only [ramanujanThetaMonomial, coeff_mk]
  decide
