/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.WeightedDavenportInterval

open MetaMathlibExt

-- At the smallest divisor, every nonzero residue is an allowed weight.
example : weightedDavenport (Finset.Icc 1 7) (ZMod 8) = 2 :=
  weightedDavenport_zmod_Icc_of_dvd 2 8 (by decide) (by decide) (by decide)

-- For equal divisor and modulus, only the weight one is available.
example : weightedDavenport (Finset.Icc 1 1) (ZMod 5) = 5 :=
  weightedDavenport_zmod_Icc_of_dvd 5 5 (by decide) (by decide) (by decide)

-- Here the upper endpoint is strictly larger than the uniform weight 12 / 3 = 4.
example : weightedDavenport (Finset.Icc 1 5) (ZMod 12) = 3 :=
  weightedDavenport_zmod_Icc_of_dvd 3 12 (by decide) (by decide) (by decide)
