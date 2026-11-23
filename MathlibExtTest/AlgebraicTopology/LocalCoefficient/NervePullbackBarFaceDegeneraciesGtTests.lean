/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesGt

/-!
# Tests for the remaining pulled-back mixed identity

These clients pin the `δ_comp_σ_of_gt` component and degree-map laws,
including their least boundary-index instance, identity-nerve reduction, and
raised universes. They make no degeneracy--degeneracy or chain-level claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesGtTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (σ : X _⦋n + 1⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j.castSucc σ ≫
        nervePullbackCoefficientFaceHom φ M i.succ
          (X.σ j.castSucc σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 1))
        (SSet.δ_comp_σ_of_gt_apply (S := X) hji σ)) =
    nervePullbackCoefficientFaceHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j (X.δ i σ) :=
  nervePullbackCoefficientHom_face_degeneracy_of_gt φ M i j hji σ

variable [HasCoproducts.{max uG vG} A]

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    nervePullbackCoefficientDegeneracy φ M j.castSucc ≫
        nervePullbackCoefficientFace φ M i.succ =
      nervePullbackCoefficientFace φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j :=
  nervePullbackCoefficient_face_degeneracy_of_gt φ M i j hji

end Generic

section BoundaryIndex

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example (σ : X _⦋1⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M
          (0 : Fin 1).castSucc σ ≫
        nervePullbackCoefficientFaceHom φ M
          (1 : Fin 2).succ (X.σ (0 : Fin 1).castSucc σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M 1)
        (SSet.δ_comp_σ_of_gt_apply (S := X) (by simp) σ)) =
    nervePullbackCoefficientFaceHom φ M (1 : Fin 2) σ ≫
      nervePullbackCoefficientDegeneracyHom φ M (0 : Fin 1)
        (X.δ (1 : Fin 2) σ) :=
  nervePullbackCoefficientHom_face_degeneracy_of_gt φ M 1 0 (by simp) σ

variable [HasCoproducts.{max uG vG} A]

example :
    nervePullbackCoefficientDegeneracy (n := 1) φ M
        (0 : Fin 1).castSucc ≫
      nervePullbackCoefficientFace φ M (1 : Fin 2).succ =
    nervePullbackCoefficientFace φ M (1 : Fin 2) ≫
      nervePullbackCoefficientDegeneracy φ M (0 : Fin 1) :=
  nervePullbackCoefficient_face_degeneracy_of_gt φ M 1 0 (by simp)

end BoundaryIndex

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

omit [HasCoproducts.{max uG vG} A] in
private theorem identityNerve_degeneracyHom {n : ℕ} (i : Fin (n + 1))
    (F : (CategoryTheory.nerve G) _⦋n⦌) :
    nervePullbackCoefficientDegeneracyHom
        (𝟙 (CategoryTheory.nerve G)) M i F =
      coefficientDegeneracyHom M i F := by
  unfold nervePullbackCoefficientDegeneracyHom
  change coefficientDegeneracyHom M i F ≫ eqToHom _ =
    coefficientDegeneracyHom M i F
  rw [eqToHom_refl, Category.comp_id]

private theorem identityNerve_face {n : ℕ} (i : Fin (n + 2)) :
    nervePullbackCoefficientFace (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarFace M i := by
  unfold nervePullbackCoefficientFace coefficientBarFace
  apply Sigma.map'_eq rfl
  intro F
  rw [identityNerve_faceHom M]
  exact Category.comp_id _

private theorem identityNerve_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy
        (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarDegeneracy M i := by
  unfold nervePullbackCoefficientDegeneracy coefficientBarDegeneracy
  apply Sigma.map'_eq rfl
  intro F
  rw [identityNerve_degeneracyHom M]
  exact Category.comp_id _

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    coefficientBarDegeneracy M j.castSucc ≫ coefficientBarFace M i.succ =
      coefficientBarFace M i ≫ coefficientBarDegeneracy M j := by
  rw [← identityNerve_degeneracy M j.castSucc,
    ← identityNerve_face M i.succ,
    ← identityNerve_face M i, ← identityNerve_degeneracy M j]
  exact nervePullbackCoefficient_face_degeneracy_of_gt
    (𝟙 (CategoryTheory.nerve G)) M i j hji

end IdentityNerve

section RaisedUniverses

variable {G : Type 1} [Category.{1} G]
variable {A : Type 2} [Category.{1} A]
variable {X : SSet.{1}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) (σ : X _⦋n + 1⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j.castSucc σ ≫
        nervePullbackCoefficientFaceHom φ M i.succ
          (X.σ j.castSucc σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 1))
        (SSet.δ_comp_σ_of_gt_apply (S := X) hji σ)) =
    nervePullbackCoefficientFaceHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j (X.δ i σ) :=
  nervePullbackCoefficientHom_face_degeneracy_of_gt φ M i j hji σ

variable [HasCoproducts.{1} A]

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hji : j.castSucc < i) :
    nervePullbackCoefficientDegeneracy φ M j.castSucc ≫
        nervePullbackCoefficientFace φ M i.succ =
      nervePullbackCoefficientFace φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j :=
  nervePullbackCoefficient_face_degeneracy_of_gt φ M i j hji

end RaisedUniverses

#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientHom_face_degeneracy_of_gt
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficient_face_degeneracy_of_gt

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesGtTests
