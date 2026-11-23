/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarDegeneracies

/-! # Tests for nerve-pullback coefficient-bar degeneracies -/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open CategoryTheory.CategoryHomology
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarDegeneraciesTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j σ ≫
        nervePullbackCoefficientDegeneracyHom φ M i.castSucc (X.σ j σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 2))
        (SSet.σ_comp_σ_apply (S := X) hij σ)) =
    nervePullbackCoefficientDegeneracyHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j.succ (X.σ i σ) :=
  nervePullbackCoefficientDegeneracyHom_degeneracyDegeneracy
    φ M i j hij σ

variable [HasCoproducts.{max uG vG} A]

example {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    nervePullbackCoefficientDegeneracy φ M j ≫
        nervePullbackCoefficientDegeneracy φ M i.castSucc =
      nervePullbackCoefficientDegeneracy φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j.succ :=
  nervePullbackCoefficientDegeneracy_comp_degeneracy φ M i j hij

end Generic

section DegreeZero

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{max uG vG} A]

example (σ : X _⦋0⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M (0 : Fin 1) σ ≫
        nervePullbackCoefficientDegeneracyHom φ M
          (0 : Fin 1).castSucc (X.σ 0 σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M 2)
        (SSet.σ_comp_σ_apply (S := X) (show (0 : Fin 1) ≤ 0 by simp) σ)) =
    nervePullbackCoefficientDegeneracyHom φ M (0 : Fin 1) σ ≫
      nervePullbackCoefficientDegeneracyHom φ M
        (0 : Fin 1).succ (X.σ 0 σ) :=
  nervePullbackCoefficientDegeneracyHom_degeneracyDegeneracy
    φ M 0 0 (by simp) σ

example :
    nervePullbackCoefficientDegeneracy (n := 0) φ M 0 ≫
        nervePullbackCoefficientDegeneracy φ M (0 : Fin 1).castSucc =
      nervePullbackCoefficientDegeneracy φ M 0 ≫
        nervePullbackCoefficientDegeneracy φ M (0 : Fin 1).succ :=
  nervePullbackCoefficientDegeneracy_comp_degeneracy φ M 0 0 (by simp)

end DegreeZero

section IdentityNerve

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable [HasCoproducts.{max uG vG} A]
variable (M : G ⥤ A)

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

private theorem identityNerve_degeneracy {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientDegeneracy
        (𝟙 (CategoryTheory.nerve G)) M i =
      coefficientBarDegeneracy M i := by
  unfold nervePullbackCoefficientDegeneracy coefficientBarDegeneracy
  apply Sigma.map'_eq rfl
  intro F
  rw [identityNerve_degeneracyHom M]
  exact Category.comp_id _

example {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    coefficientBarDegeneracy M j ≫
        coefficientBarDegeneracy M i.castSucc =
      coefficientBarDegeneracy M i ≫
        coefficientBarDegeneracy M j.succ := by
  rw [← identityNerve_degeneracy M j,
    ← identityNerve_degeneracy M i.castSucc,
    ← identityNerve_degeneracy M i,
    ← identityNerve_degeneracy M j.succ]
  exact nervePullbackCoefficientDegeneracy_comp_degeneracy
    (𝟙 (CategoryTheory.nerve G)) M i j hij

end IdentityNerve

section RaisedUniverses

variable {G : Type 1} [Category.{1} G]
variable {A : Type 2} [Category.{1} A]
variable {X : SSet.{1}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) (σ : X _⦋n⦌) :
    (nervePullbackCoefficientDegeneracyHom φ M j σ ≫
        nervePullbackCoefficientDegeneracyHom φ M i.castSucc (X.σ j σ)) ≫
      eqToHom (congrArg (nervePullbackCoefficientFamily φ M (n + 2))
        (SSet.σ_comp_σ_apply (S := X) hij σ)) =
    nervePullbackCoefficientDegeneracyHom φ M i σ ≫
      nervePullbackCoefficientDegeneracyHom φ M j.succ (X.σ i σ) :=
  nervePullbackCoefficientDegeneracyHom_degeneracyDegeneracy
    φ M i j hij σ

variable [HasCoproducts.{1} A]

example {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) :
    nervePullbackCoefficientDegeneracy φ M j ≫
        nervePullbackCoefficientDegeneracy φ M i.castSucc =
      nervePullbackCoefficientDegeneracy φ M i ≫
        nervePullbackCoefficientDegeneracy φ M j.succ :=
  nervePullbackCoefficientDegeneracy_comp_degeneracy φ M i j hij

end RaisedUniverses

#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom_degeneracyDegeneracy
#print axioms
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracy_comp_degeneracy

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarDegeneraciesTests
