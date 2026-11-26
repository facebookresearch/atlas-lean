/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ArchDatumRLinearCombination

import Mathlib.Tactic.Ring

@[expose] public section

namespace LanglandsTunnell.Converse

/-- `exactSource` consumer with the original binders of the linear-combination statement. -/
example {P : RealArchParam} (D₁ D₂ : ArchDatumR P) (c₁ c₂ : ℂ) :
    ∃ D : ArchDatumR P, D.W = fun g => c₁ * D₁.W g + c₂ * D₂.W g :=
  ArchDatumR.exists_lincomb D₁ D₂ c₁ c₂

/-- The difference of two Whittaker functions of real archimedean data is again one. -/
example {P : RealArchParam} (D₁ D₂ : ArchDatumR P) :
    ∃ D : ArchDatumR P, ∀ g, D.W g = D₁.W g - D₂.W g := by
  obtain ⟨D, hD⟩ := ArchDatumR.exists_lincomb D₁ D₂ 1 (-1)
  exact ⟨D, fun g => by simp only [hD]; ring⟩

end LanglandsTunnell.Converse
