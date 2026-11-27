/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.ScottishBook112

/-! # Tests for `MathlibExt.GroupTheory.ScottishBook112` -/

namespace MathlibExtTest.ScottishBook112

open MathlibExt.GroupTheory.ScottishBook112Wanted

universe u

-- Extract the counterexample in an arbitrary universe. Each element admits a conjugator,
-- and each candidate for a common conjugator fails on some element.
example : ∃ (G : Type u) (_ : Group G) (α : MulAut G),
    (∀ x : G, ∃ g : G, α x = g * x * g⁻¹) ∧
      ∀ g : G, ∃ x : G, α x ≠ g * x * g⁻¹ := by
  by_contra! h
  exact scottishBook112_refuted fun G _ α hα => h G _ α hα

end MathlibExtTest.ScottishBook112
