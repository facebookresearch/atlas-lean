/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.EssentialDimensionSymmetricLowerBound

open MathlibExt.FieldTheory.EssentialDimensionSymmetric
open MathlibExt.FieldTheory.EssentialDimensionSymmetricWanted

-- Each pair of roots contributes one parameter, including when one root is left over.
example (r : ℕ) : r ≤ edSn (2 * r) := by
  simpa using buhlerReichsteinDuncanLowerBound_wanted (2 * r)

example (r : ℕ) : r ≤ edSn (2 * r + 1) := by
  have h := buhlerReichsteinDuncanLowerBound_wanted (2 * r + 1)
  omega
