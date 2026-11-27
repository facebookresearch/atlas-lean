/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DucciCoefficientReduction

open MathlibExt.NumberTheory.DucciWanted

-- With k = 0 and b = 0, both ends of the binomial row contribute.
example : ((ducciCoeff 4 4 1 : ℤ) : ZMod 3) = 2 :=
  (ducciCoeff_reduce_mod 3 0 4 4 0 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- Here p divides n₁. The middle summand vanishes modulo p and the endpoints cancel.
example : ((ducciCoeff 8 16 1 : ℤ) : ZMod 2) = 0 :=
  (ducciCoeff_reduce_mod 2 2 2 4 0 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- At b = n₁ - 1, two nonzero terms in the residue class contribute.
example : ((ducciCoeff 9 15 7 : ℤ) : ZMod 3) = 2 :=
  (ducciCoeff_reduce_mod 3 1 3 5 2 (by decide) (by decide) (by decide) (by decide)).trans (by decide)

-- At the same boundary, the residue class can also miss the entire range.
example : ((ducciCoeff 9 3 7 : ℤ) : ZMod 3) = 0 :=
  (ducciCoeff_reduce_mod 3 1 3 1 2 (by decide) (by decide) (by decide) (by decide)).trans (by decide)
