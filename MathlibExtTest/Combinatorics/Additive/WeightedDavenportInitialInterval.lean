/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.WeightedDavenportInitialInterval

open MetaMathlibExt

-- The modulus is divisible by the maximum weight.
example : weightedDavenport (Finset.Icc 1 2) (ZMod 8) = ((4 : ℕ) : ℕ∞) := by
  change weightedDavenport (Finset.Icc 1 2) (ZMod 8) = ((8 ⌈/⌉ 2 : ℕ) : ℕ∞)
  exact weightedDavenport_zmod_Icc 8 2 (by decide) (by decide)

-- A nonzero remainder rounds the length up.
example : weightedDavenport (Finset.Icc 1 2) (ZMod 7) = ((4 : ℕ) : ℕ∞) := by
  change weightedDavenport (Finset.Icc 1 2) (ZMod 7) = ((7 ⌈/⌉ 2 : ℕ) : ℕ∞)
  exact weightedDavenport_zmod_Icc 7 2 (by decide) (by decide)

-- The largest allowed interval of weights gives constant two.
example : weightedDavenport (Finset.Icc 1 4) (ZMod 5) = ((2 : ℕ) : ℕ∞) := by
  change weightedDavenport (Finset.Icc 1 4) (ZMod 5) = ((5 ⌈/⌉ 4 : ℕ) : ℕ∞)
  exact weightedDavenport_zmod_Icc 5 4 (by decide) (by decide)
