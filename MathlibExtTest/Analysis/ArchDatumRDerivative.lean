/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ArchDatumRDerivative

@[expose] public section

namespace LanglandsTunnell.Converse

/-- `exactSource` consumer with the original binders of the Whittaker lift statement. -/
example (P : RealArchParam) (d : ArchDatumR P)
    (X : Matrix (Fin 2) (Fin 2) ℝ) :
    ∃ d' : ArchDatumR P, ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 →
      d'.W g = fderivWithin ℝ (ArchR.asPi d.W) ArchR.glSet
        (Matrix.of.symm g) (Matrix.of.symm (g * X)) :=
  ArchDatumR.exists_W_eq_fderivWithin_mul P d X

/-- Along the zero matrix the derivative datum has Whittaker function zero on invertible
matrices. -/
example (P : RealArchParam) (d : ArchDatumR P) :
    ∃ d' : ArchDatumR P, ∀ g : Matrix (Fin 2) (Fin 2) ℝ, g.det ≠ 0 → d'.W g = 0 := by
  obtain ⟨d', hd'⟩ := ArchDatumR.exists_W_eq_fderivWithin_mul P d 0
  exact ⟨d', fun g hg => by rw [hd' g hg, mul_zero]; exact map_zero _⟩

end LanglandsTunnell.Converse
