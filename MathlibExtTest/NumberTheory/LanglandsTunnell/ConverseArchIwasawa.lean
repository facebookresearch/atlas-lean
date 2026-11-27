/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LanglandsTunnell.ConverseArchIwasawa

@[expose] public section

open LanglandsTunnell LanglandsTunnell.Converse

open LanglandsTunnell.Converse.ArchR in
/-- Consumer with the original binders. -/
example {P : RealArchParam} (D : ArchDatumR P)
    (hDW0 : ∀ (r : AutomorphicForm.rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ)
          = D.W (x : Matrix (Fin 2) (Fin 2) ℝ))
    {c : ℝ} (hc : c ≠ 0) (x : ℝ) {y₁ y₂ : ℝ} (hy₁ : y₁ ≠ 0) (hy₂ : 0 < y₂) (θ : ℝ) :
    D.W (ArchR.diagOne c * !![y₁ * Real.cos θ + x * y₂ * Real.sin θ,
         -(y₁ * Real.sin θ) + x * y₂ * Real.cos θ;
         y₂ * Real.sin θ, y₂ * Real.cos θ]) =
      psi (c * x) * (centralChar P y₂ * ((|y₂| : ℝ) : ℂ))
        * D.W (ArchR.diagOne (c * y₁ / y₂)) :=
  ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
    D hDW0 hc x hy₁ hy₂ θ

/-- Concrete example: the zero datum is an archimedean datum, is
invariant under the row-isometry subgroup, and the evaluation holds. -/
example (P : RealArchParam) :
    True := by
  let D : ArchDatumR P := {
    W := fun _ => 0
    smooth := contDiffOn_const
    unip_law := fun _ _ => by simp
    central_law := fun _ _ _ => by simp
    zetaEntire := fun _ _ _ _ => 0
    zetaEntire_differentiable := fun _ _ _ => differentiable_const 0
    zeta_abscissa := 0
    zeta_integrable := fun g u a s _ _ => by
      rw [show ArchR.zetaIntegrand (fun _ => (0 : ℂ)) g u a s = 0 from
        funext fun _ => by simp [ArchR.zetaIntegrand]]
      exact MeasureTheory.integrable_zero _ _ _
    zeta_eq := fun _ _ _ _ _ _ => by simp [ArchR.zetaIntegrand]
    functional_equation := fun _ _ _ _ _ => by simp
    zetaEntire_finiteOrder := fun _ _ _ _ _ => ⟨0, 0, fun _ _ _ => by simp⟩
    decay_top := fun _ _ => ⟨0, fun _ _ _ _ => by
      rw [show ArchR.asPi (fun _ => (0 : ℂ)) = fun _ => 0 from rfl]
      simp⟩
    decay_zero := fun _ => ⟨0, 0, fun _ _ _ _ _ => by
      rw [show ArchR.asPi (fun _ => (0 : ℂ)) = fun _ => 0 from rfl]
      simp⟩ }
  have _h := ArchDatumR.W_diagOne_mul_iwasawa_eq_psi_mul_centralChar_mul_W_diagOne_of_weightZero
    (P := P) D (fun _ _ => rfl) (c := 1) one_ne_zero 0 (y₁ := 1) (y₂ := 1)
    one_ne_zero one_pos 0
  trivial
