/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaces

/-!
# Tests for nerve-pullback coefficient-bar faces

These clients pin the component and degree face--face identities, the
zeroth-face corner, reduction along the identity nerve map, and raised
universes. No other simplicial identity or downstream chain construction is
tested or claimed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarFacesTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j)
    (σ : X _⦋n + 2⦌) :
    (nervePullbackCoefficientFaceHom φ M j.succ σ ≫
        nervePullbackCoefficientFaceHom φ M i (X.δ j.succ σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_δ_apply (S := X) hij σ)) =
    nervePullbackCoefficientFaceHom φ M i.castSucc σ ≫
      nervePullbackCoefficientFaceHom φ M j
        (X.δ i.castSucc σ) :=
  nervePullbackCoefficientFaceHom_faceFace φ M i j hij σ

variable [HasCoproducts.{max uG vG} A]

example {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    nervePullbackCoefficientFace φ M j.succ ≫
        nervePullbackCoefficientFace φ M i =
      nervePullbackCoefficientFace φ M i.castSucc ≫
        nervePullbackCoefficientFace φ M j :=
  nervePullbackCoefficientFace_comp_face φ M i j hij

end Generic

section ZerothFaceCorner

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (σ : X _⦋n + 2⦌) :
    (nervePullbackCoefficientFaceHom φ M
          (0 : Fin (n + 2)).succ σ ≫
        nervePullbackCoefficientFaceHom φ M (0 : Fin (n + 2))
          (X.δ (0 : Fin (n + 2)).succ σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_δ_apply (S := X) (by simp) σ)) =
    nervePullbackCoefficientFaceHom φ M
        (0 : Fin (n + 2)).castSucc σ ≫
      nervePullbackCoefficientFaceHom φ M (0 : Fin (n + 2))
        (X.δ (0 : Fin (n + 2)).castSucc σ) :=
  nervePullbackCoefficientFaceHom_faceFace φ M 0 0 (by simp) σ

end ZerothFaceCorner

section IdentityNerve

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable [HasCoproducts.{max uG vG} A]
variable (M : G ⥤ A)

omit [HasCoproducts.{max uG vG} A] in
private theorem identityNerve_faceHom {n : ℕ} (i : Fin (n + 2))
    (F : (CategoryTheory.nerve G) _⦋n + 1⦌) :
    nervePullbackCoefficientFaceHom
        (𝟙 (CategoryTheory.nerve G)) M i F =
      coefficientFaceHom M i F := by
  unfold nervePullbackCoefficientFaceHom
  change coefficientFaceHom M i F ≫ eqToHom _ = coefficientFaceHom M i F
  rw [eqToHom_refl, Category.comp_id]

private theorem identityNerve_face {n : ℕ} (i : Fin (n + 2)) :
    nervePullbackCoefficientFace (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarFace M i := by
  unfold nervePullbackCoefficientFace coefficientBarFace
  apply Sigma.map'_eq rfl
  intro F
  rw [identityNerve_faceHom M]
  exact Category.comp_id _

example {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    coefficientBarFace M j.succ ≫ coefficientBarFace M i =
      coefficientBarFace M i.castSucc ≫ coefficientBarFace M j := by
  rw [← identityNerve_face M j.succ, ← identityNerve_face M i,
    ← identityNerve_face M i.castSucc, ← identityNerve_face M j]
  exact nervePullbackCoefficientFace_comp_face
    (𝟙 (CategoryTheory.nerve G)) M i j hij

end IdentityNerve

section RaisedUniverses

variable {G : Type 1} [Category.{1} G]
variable {A : Type 2} [Category.{1} A]
variable {X : SSet.{1}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j)
    (σ : X _⦋n + 2⦌) :
    (nervePullbackCoefficientFaceHom φ M j.succ σ ≫
        nervePullbackCoefficientFaceHom φ M i (X.δ j.succ σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_δ_apply (S := X) hij σ)) =
    nervePullbackCoefficientFaceHom φ M i.castSucc σ ≫
      nervePullbackCoefficientFaceHom φ M j
        (X.δ i.castSucc σ) :=
  nervePullbackCoefficientFaceHom_faceFace φ M i j hij σ

variable [HasCoproducts.{1} A]

example {n : ℕ} (i j : Fin (n + 2)) (hij : i ≤ j) :
    nervePullbackCoefficientFace φ M j.succ ≫
        nervePullbackCoefficientFace φ M i =
      nervePullbackCoefficientFace φ M i.castSucc ≫
        nervePullbackCoefficientFace φ M j :=
  nervePullbackCoefficientFace_comp_face φ M i j hij

end RaisedUniverses

#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom_faceFace
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientFace_comp_face

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarFacesTests
