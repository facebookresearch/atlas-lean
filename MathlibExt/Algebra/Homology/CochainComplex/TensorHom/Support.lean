/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Homology.CochainComplex.TensorHom.Coordinates

/-!
# Support of the native tensor total

A zero module factor makes its actual tensor object zero. Native
degreewise coproduct uniqueness then removes a total term when every
factor pair in that degree has a zero factor. This gives the actual
sum of upper support bounds without changing the tensor totalization.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v w

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]
  (P : CochainComplex (ModuleCat.{v} R) ℤ) (Q : CochainComplex (ModuleCat.{w} R) ℤ)

/-- A native total term is zero when every original degree pair has a zero factor. -/
theorem complexAt_isZero_X_of_factor_terms (n : ℤ)
    (h : ∀ i j : ℤ, i + j = n → IsZero (P.X i) ∨ IsZero (Q.X j)) :
    IsZero ((complexAt R P Q).X n) := by
  let F : ModuleCat.{v} R ⥤ ModuleCat.{w} R ⥤ ModuleCat.{max v w} R :=
    ModuleCat.tensorBifunctorAt R
  let Y : ModuleCat.{max v w} R := (HomologicalComplex.mapBifunctor P Q F (.up ℤ)).X n
  have hcomponents : ∀ (i j : ℤ) (hij : i + j = n),
      HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) i j n hij ≫ 𝟙 Y =
        HomologicalComplex.ιMapBifunctor P Q F (.up ℤ) i j n hij ≫ (0 : Y ⟶ Y) := by
    intro i j hij
    have hsource : IsZero ((F.obj (P.X i)).obj (Q.X j)) := by
      rcases h i j hij with hP | hQ
      · exact ((ModuleCat.tensorBifunctorAt R).flip.obj (Q.X j)).map_isZero hP
      · exact ((ModuleCat.tensorBifunctorAt R).obj (P.X i)).map_isZero hQ
    exact hsource.eq_of_src _ _
  have hid : (𝟙 Y : Y ⟶ Y) = 0 :=
    HomologicalComplex.mapBifunctor.hom_ext
      (K₁ := P) (K₂ := Q) (F := F) (c := .up ℤ) hcomponents
  exact (CategoryTheory.Limits.IsZero.iff_id_eq_zero Y).mpr hid

/-- The original native tensor total vanishes above the sum of its factor support bounds. -/
theorem complexAt_isZero_X_above (a b n : ℤ)
    (hP : ∀ i, a < i → IsZero (P.X i))
    (hQ : ∀ j, b < j → IsZero (Q.X j)) (hn : a + b < n) :
    IsZero ((complexAt R P Q).X n) := by
  apply complexAt_isZero_X_of_factor_terms R P Q n
  intro i j hij
  by_cases hi : a < i
  · exact Or.inl (hP i hi)
  · exact Or.inr (hQ j (by omega))

end CochainComplex.ModuleTensor
