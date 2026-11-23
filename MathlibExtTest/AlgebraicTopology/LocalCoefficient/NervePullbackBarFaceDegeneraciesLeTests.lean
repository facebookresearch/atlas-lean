/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesLe

/-!
# Tests for ordered and cancelling pulled-back bar identities

These clients pin `δ_comp_σ_of_le`, `δ_comp_σ_self`, and
`δ_comp_σ_succ` at component and degree-map level, including the degree-zero
corner, identity nerve reduction, and raised universes. No later simplicial
identity or chain-level construction is claimed.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesLeTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) (σ : X _⦋n + 1⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j.succ σ ≫
        nervePullbackCoefficientFaceHom φ M i.castSucc
          (X.σ j.succ σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 1))
        (SSet.δ_comp_σ_of_le_apply (S := X) hij σ)) =
    nervePullbackCoefficientFaceHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j (X.δ i σ) :=
  nervePullbackCoefficientHom_face_degeneracy_of_le φ M i j hij σ

example {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M i σ ≫
        nervePullbackCoefficientFaceHom φ M i.castSucc (X.σ i σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_σ_self_apply (S := X) i σ)) =
    𝟙 (nervePullbackCoefficientFamily φ M n σ) :=
  nervePullbackCoefficientHom_face_degeneracy_self φ M i σ

example {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M i σ ≫
        nervePullbackCoefficientFaceHom φ M i.succ (X.σ i σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M n)
        (SSet.δ_comp_σ_succ_apply (S := X) i σ)) =
    𝟙 (nervePullbackCoefficientFamily φ M n σ) :=
  nervePullbackCoefficientHom_face_degeneracy_succ φ M i σ

variable [HasCoproducts.{max uG vG} A]

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    nervePullbackCoefficientDegeneracy φ M j.succ ≫
        nervePullbackCoefficientFace φ M i.castSucc =
      nervePullbackCoefficientFace φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j :=
  nervePullbackCoefficient_face_degeneracy_of_le φ M i j hij

example {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy φ M i ≫
      nervePullbackCoefficientFace φ M i.castSucc = 𝟙 _ :=
  nervePullbackCoefficient_face_degeneracy_self φ M i

example {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy φ M i ≫
      nervePullbackCoefficientFace φ M i.succ = 𝟙 _ :=
  nervePullbackCoefficient_face_degeneracy_succ φ M i

end Generic

section DegreeZero

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

example (σ : X _⦋0⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M (0 : Fin 1) σ ≫
        nervePullbackCoefficientFaceHom φ M
          (0 : Fin 1).castSucc (X.σ 0 σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M 0)
        (SSet.δ_comp_σ_self_apply (S := X) (0 : Fin 1) σ)) =
    𝟙 (nervePullbackCoefficientFamily φ M 0 σ) :=
  nervePullbackCoefficientHom_face_degeneracy_self φ M 0 σ

example (σ : X _⦋0⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M (0 : Fin 1) σ ≫
        nervePullbackCoefficientFaceHom φ M
          (0 : Fin 1).succ (X.σ 0 σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M 0)
        (SSet.δ_comp_σ_succ_apply (S := X) (0 : Fin 1) σ)) =
    𝟙 (nervePullbackCoefficientFamily φ M 0 σ) :=
  nervePullbackCoefficientHom_face_degeneracy_succ φ M 0 σ

example :
    nervePullbackCoefficientDegeneracy (n := 0) φ M 0 ≫
      nervePullbackCoefficientFace φ M (0 : Fin 1).castSucc = 𝟙 _ :=
  nervePullbackCoefficient_face_degeneracy_self φ M 0

example :
    nervePullbackCoefficientDegeneracy (n := 0) φ M 0 ≫
      nervePullbackCoefficientFace φ M (0 : Fin 1).succ = 𝟙 _ :=
  nervePullbackCoefficient_face_degeneracy_succ φ M 0

end DegreeZero

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
    (hij : i ≤ j.castSucc) :
    coefficientBarDegeneracy M j.succ ≫
        coefficientBarFace M i.castSucc =
      coefficientBarFace M i ≫ coefficientBarDegeneracy M j := by
  rw [← identityNerve_degeneracy M j.succ,
    ← identityNerve_face M i.castSucc,
    ← identityNerve_face M i, ← identityNerve_degeneracy M j]
  exact nervePullbackCoefficient_face_degeneracy_of_le
    (𝟙 (CategoryTheory.nerve G)) M i j hij

example {n : ℕ} (i : Fin (n + 1)) :
    coefficientBarDegeneracy M i ≫ coefficientBarFace M i.castSucc = 𝟙 _ := by
  rw [← identityNerve_degeneracy M i, ← identityNerve_face M i.castSucc]
  exact nervePullbackCoefficient_face_degeneracy_self
    (𝟙 (CategoryTheory.nerve G)) M i

example {n : ℕ} (i : Fin (n + 1)) :
    coefficientBarDegeneracy M i ≫ coefficientBarFace M i.succ = 𝟙 _ := by
  rw [← identityNerve_degeneracy M i, ← identityNerve_face M i.succ]
  exact nervePullbackCoefficient_face_degeneracy_succ
    (𝟙 (CategoryTheory.nerve G)) M i

end IdentityNerve

section SigmaHelper

universe w v u

variable {A : Type u} [Category.{v} A]
variable {I₀ I₁ : Type w} [HasCoproducts.{w} A]
variable {X₀ : I₀ → A} {X₁ : I₁ → A}

example (p : I₀ → I₁) (q : I₁ → I₀)
    (hp : ∀ a, X₀ a ⟶ X₁ (p a))
    (hq : ∀ b, X₁ b ⟶ X₀ (q b))
    (hidx : ∀ a, q (p a) = a)
    (hhom : ∀ a, (hp a ≫ hq (p a)) ≫
      eqToHom (congrArg X₀ (hidx a)) = 𝟙 (X₀ a)) :
    Sigma.map' p hp ≫ Sigma.map' q hq = 𝟙 _ :=
  Sigma.map'_comp_id p q hp hq hidx hhom

end SigmaHelper

section RaisedUniverses

variable {G : Type 1} [Category.{1} G]
variable {A : Type 2} [Category.{1} A]
variable {X : SSet.{1}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{1} A]

example {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1))
    (hij : i ≤ j.castSucc) :
    nervePullbackCoefficientDegeneracy φ M j.succ ≫
        nervePullbackCoefficientFace φ M i.castSucc =
      nervePullbackCoefficientFace φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j :=
  nervePullbackCoefficient_face_degeneracy_of_le φ M i j hij

example {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy φ M i ≫
      nervePullbackCoefficientFace φ M i.castSucc = 𝟙 _ :=
  nervePullbackCoefficient_face_degeneracy_self φ M i

example {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy φ M i ≫
      nervePullbackCoefficientFace φ M i.succ = 𝟙 _ :=
  nervePullbackCoefficient_face_degeneracy_succ φ M i

end RaisedUniverses

#print axioms CategoryTheory.Limits.Sigma.map'_comp_id
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientHom_face_degeneracy_of_le
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientHom_face_degeneracy_self
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientHom_face_degeneracy_succ
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficient_face_degeneracy_of_le
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficient_face_degeneracy_self
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficient_face_degeneracy_succ

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarFaceDegeneraciesLeTests
