/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.MellinArchDatum

@[expose] public section

open LanglandsTunnell LanglandsTunnell.Converse AutomorphicForm MeasureTheory

/-- `exactSource` consumer with the original binders. -/
example {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (u₁ u₂ : ℂ) (c : ZMod 2) (hP : P₂ = RealArchParam.principal u₁ c u₂ c)
    (hpar : ∀ τ : ℝ, τ ≠ 0 →
      D.W (ArchR.diagOne (-τ)) = (-1 : ℂ) ^ c.val * D.W (ArchR.diagOne τ))
    (hDW0 : ∀ (r : Matrix.specialOrthogonalGroup (Fin 2) ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * specialOrthogonalToGL r : GL (Fin 2) ℝ) :
          Matrix (Fin 2) (Fin 2) ℝ) = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    (hDnz : ∃ g : GL (Fin 2) ℝ, D.W (g : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0)
    (x₀ : ℝ) :
    ∃ x : ℝ, x₀ < x ∧
      MellinConvergent (fun τ : ℝ => D.W (ArchR.diagOne τ)) (x : ℂ) ∧
      mellin (fun τ : ℝ => D.W (ArchR.diagOne τ)) (x : ℂ) ≠ 0 :=
  D.exists_lt_mellin_W_diagOne_ne_zero_of_weightZero_of_parity
    u₁ u₂ c hP hpar hDW0 hDnz x₀

/-- Boundary: if the diagonal values all vanish, the Mellin transform
vanishes, so a nonvanishing hypothesis is essential. -/
example {P₂ : RealArchParam} (D : ArchDatumR P₂)
    (h0 : ∀ τ : ℝ, D.W (ArchR.diagOne τ) = 0) (s : ℂ) :
    mellin (fun τ : ℝ => D.W (ArchR.diagOne τ)) s = 0 := by
  simp [mellin, h0]
