/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.DeclaredFriisLink

@[expose] public section

open PhyslibExt.Electromagnetism.DeclaredFriisLink Real

namespace PhyslibExtTest.Electromagnetism.DeclaredFriisLink

/-- Concrete link: `Pt = 8`, unit gains, `r = 1`, `λ = 2` composes
through the declared flux and aperture to the Friis value. -/
example : (8 : ℝ) * 1 / (4 * π * 1 ^ 2) * (1 * 2 ^ 2 / (4 * π)) =
    8 * 1 * 1 * (2 / (4 * π * 1)) ^ 2 :=
  receivedPower_eq_friis (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) rfl rfl rfl

end PhyslibExtTest.Electromagnetism.DeclaredFriisLink
