/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.AutomorphicForm.RationalStrongApproximation

@[expose] public section

open IsDedekindDomain NumberField NumberField.AdelicLevel AutomorphicForm

namespace RationalStrongApproximationTest

/-- Consumer with the source's statement and binders, for every fundamental set `D`. -/
theorem exactSource (D : Set (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ))
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2)
      (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ)
      (h u : Matrix.GeneralLinearGroup (Fin 2)
        (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      u ∈ (AutomorphicForm.productionPinsCompact ℚ D).U N ∧
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 ∧
        (∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = NumberField.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * h * u :=
  exists_mem_productionPinsCompact_U_mul_eq_rat D hN g

/-- The factor `u` has identity infinite part and finite part in the level at `N`. -/
example (D : Set (AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ)) {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥)
    (g : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h u : AutomorphicForm.AdelicGL2 (𝓞 ℚ) ℚ),
      glFin (𝓞 ℚ) ℚ u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glArch (𝓞 ℚ) ℚ u = 1 ∧
        glFin (𝓞 ℚ) ℚ h = 1 ∧ g = globalPoints (𝓞 ℚ) ℚ γ * h * u := by
  obtain ⟨γ, h, u, hu, hh, -, hg⟩ := exists_mem_productionPinsCompact_U_mul_eq_rat D hN g
  exact ⟨γ, h, u, ((mem_productionPinsCompact_U_iff ℚ D N u).mp hu).1,
    ((mem_productionPinsCompact_U_iff ℚ D N u).mp hu).2, hh, hg⟩

/-- Over the finite adeles alone, the level at `N` is reached from every matrix. -/
example {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    ∃ γ : GL (Fin 2) ℚ,
      glFin (𝓞 ℚ) ℚ (globalPoints (𝓞 ℚ) ℚ γ) * g ∈ finiteLevelOne (𝓞 ℚ) ℚ N :=
  exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat hN g

/-- The component at an infinite place reads off the entries at that place. -/
example (w : InfinitePlace ℚ) (g : GL (Fin 2) (InfiniteAdeleRing ℚ)) (i j : Fin 2) :
    (archComponent ℚ w g : Matrix (Fin 2) (Fin 2) w.Completion) i j =
      (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing ℚ)) i j w :=
  archComponent_apply ℚ w g i j

end RationalStrongApproximationTest
