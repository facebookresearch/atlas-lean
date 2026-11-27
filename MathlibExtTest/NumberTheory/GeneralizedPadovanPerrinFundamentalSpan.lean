/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GeneralizedPadovanPerrinFundamentalSpan

open MetaMathlibExt

-- Order zero gives the empty generating family, hence the zero solution space.
example (k₁ k₂ : ℤ) : (padovanPerrinRecurrence k₁ k₂ 0 0).solSpace = ⊥ := by
  rw [padovanPerrin_solSpace_eq_span_fundamental]
  simp

-- At order three, combine the first and last fundamental solutions over the integers.
example :
    (2 : ℤ) • padovanPerrinFundamental (1 : ℤ) 1 1 2 1 +
      (3 : ℤ) • padovanPerrinFundamental (1 : ℤ) 1 1 2 3 ∈
        (padovanPerrinRecurrence (1 : ℤ) 1 1 2).solSpace := by
  rw [padovanPerrin_solSpace_eq_span_fundamental]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(0 : Fin 3), rfl⟩))
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨(2 : Fin 3), rfl⟩))
