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
# Upper support bounds for tensor cochain totals

Let `P` and `Q` be cochain complexes over a commutative ring, with independent carrier
universes. Their degree-`n` tensor total is the direct sum of `P^i ⊗ Q^j` over `i + j = n`.

If every such pair has a zero factor, the total degree is zero. In particular, upper vanishing
bounds `a` for `P` and `b` for `Q` give upper vanishing bound `a + b` for their tensor total.
-/

@[expose] public section

noncomputable section

open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct

universe u v w

namespace CochainComplex.ModuleTensor

variable (R : Type u) [CommRing R]
  (P : CochainComplex (ModuleCat.{v} R) ℤ) (Q : CochainComplex (ModuleCat.{w} R) ℤ)

/-- A tensor-total degree is zero when every cell has a zero factor.

If for every pair `i + j = n` either `P^i` or `Q^j` is a zero object, then degree `n` of
`complexAt R P Q` is zero. -/
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

/-- Tensor-total upper bound is the sum of the factor bounds.

If `P^i` is zero for `a < i` and `Q^j` is zero for `b < j`, then the tensor total is zero in
every integer degree `n > a + b`. -/
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
