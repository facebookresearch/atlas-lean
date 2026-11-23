/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarCore

/-!
# Tests for the nerve-pullback coefficient-bar core

These clients cover the independent-universe API, naturality orientations,
component and degree maps, coproduct formulas, the generic composite helper,
and the identity nerve map. They make no simplicial-identity or chain-level
claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarCoreTests

universe vG uG vA uA

section Generic

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

example (n : ℕ) : X _⦋n⦌ → A :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily φ M n

example {n : ℕ} (i : Fin (n + 2)) (σ : X _⦋n + 1⦌) :
    (CategoryTheory.nerve G).δ i (φ.app _ σ) =
      φ.app _ (X.δ i σ) :=
  CategoryTheory.CategoryHomology.nervePullback_face_index φ i σ

example {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    (CategoryTheory.nerve G).σ i (φ.app _ σ) =
      φ.app _ (X.σ i σ) :=
  CategoryTheory.CategoryHomology.nervePullback_degeneracy_index φ i σ

example {n : ℕ} (i : Fin (n + 2)) (σ : X _⦋n + 1⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily
        φ M (n + 1) σ ⟶
      CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily
        φ M n (X.δ i σ) :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom φ M i σ

example {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily
        φ M n σ ⟶
      CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily
        φ M (n + 1) (X.σ i σ) :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom φ M i σ

example {n : ℕ} (σ : X _⦋n + 1⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom
        φ M (0 : Fin (n + 2)) σ =
      M.map ((show ComposableArrows G (n + 1) from φ.app _ σ).map' 0 1) ≫
        eqToHom (congrArg (fun F => M.obj F.left)
          (CategoryTheory.CategoryHomology.nervePullback_face_index
            φ (0 : Fin (n + 2)) σ)) := by
  rfl

variable [HasCoproducts.{max uG vG} A]

example (n : ℕ) : A :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientObj φ M n

example {n : ℕ} (σ : X _⦋n⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily φ M n σ ⟶
      CategoryTheory.CategoryHomology.nervePullbackCoefficientObj φ M n :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientι φ M σ

example {n : ℕ} {Z : A}
    (f g : CategoryTheory.CategoryHomology.nervePullbackCoefficientObj
      φ M n ⟶ Z)
    (h : ∀ σ,
      CategoryTheory.CategoryHomology.nervePullbackCoefficientι φ M σ ≫ f =
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι φ M σ ≫ g) :
    f = g :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficient_hom_ext φ M f g h

example {n : ℕ} (i : Fin (n + 2)) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientObj
        φ M (n + 1) ⟶
      CategoryTheory.CategoryHomology.nervePullbackCoefficientObj φ M n :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientFace φ M i

example {n : ℕ} (i : Fin (n + 1)) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientObj φ M n ⟶
      CategoryTheory.CategoryHomology.nervePullbackCoefficientObj
        φ M (n + 1) :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracy φ M i

example {n : ℕ} (i : Fin (n + 2)) (σ : X _⦋n + 1⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι φ M σ ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientFace φ M i =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom
          φ M i σ ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          φ M (X.δ i σ) :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientι_face φ M i σ

example {n : ℕ} (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientι φ M σ ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracy
          φ M i =
      CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom
          φ M i σ ≫
        CategoryTheory.CategoryHomology.nervePullbackCoefficientι
          φ M (X.σ i σ) :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientι_degeneracy
    φ M i σ

end Generic

section IdentityNerve

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable [HasCoproducts.{max uG vG} A]
variable (M : G ⥤ A)

example (n : ℕ) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily
        (𝟙 (CategoryTheory.nerve G)) M n =
      CategoryTheory.CategoryHomology.coefficientBarFamily M n :=
  rfl

example (n : ℕ) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientObj
        (𝟙 (CategoryTheory.nerve G)) M n =
      CategoryTheory.CategoryHomology.coefficientBarObj M n :=
  rfl

end IdentityNerve

section SigmaComposite

universe w v u

variable {A : Type u} [Category.{v} A]
variable {I₀ I₁ I₁' I₂ : Type w} [HasCoproducts.{w} A]
variable {X₀ : I₀ → A} {X₁ : I₁ → A} {X₁' : I₁' → A} {X₂ : I₂ → A}

example (p : I₀ → I₁) (q : I₁ → I₂)
    (hp : ∀ a, X₀ a ⟶ X₁ (p a)) (hq : ∀ b, X₁ b ⟶ X₂ (q b))
    (p' : I₀ → I₁') (q' : I₁' → I₂)
    (hp' : ∀ a, X₀ a ⟶ X₁' (p' a))
    (hq' : ∀ b, X₁' b ⟶ X₂ (q' b))
    (hidx : ∀ a, q (p a) = q' (p' a))
    (hhom : ∀ a, (hp a ≫ hq (p a)) ≫
      eqToHom (congrArg X₂ (hidx a)) = hp' a ≫ hq' (p' a)) :
    Sigma.map' p hp ≫ Sigma.map' q hq =
      Sigma.map' p' hp' ≫ Sigma.map' q' hq' :=
  Sigma.map'_comp_eq p q hp hq p' q' hp' hq' hidx hhom

end SigmaComposite

section RaisedUniverses

variable {G : Type 1} [Category.{1} G]
variable {A : Type 2} [Category.{1} A]
variable {X : SSet.{1}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)
variable [HasCoproducts.{1} A]

example (n : ℕ) : A :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientObj φ M n

example {n : ℕ} (i : Fin (n + 2)) :
    CategoryTheory.CategoryHomology.nervePullbackCoefficientObj
        φ M (n + 1) ⟶
      CategoryTheory.CategoryHomology.nervePullbackCoefficientObj φ M n :=
  CategoryTheory.CategoryHomology.nervePullbackCoefficientFace φ M i

end RaisedUniverses

#print axioms CategoryTheory.Limits.Sigma.map'_comp_eq
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientFamily
#print axioms CategoryTheory.CategoryHomology.nervePullback_face_index
#print axioms CategoryTheory.CategoryHomology.nervePullback_degeneracy_index
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientFaceHom
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracyHom
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientObj
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientι
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficient_hom_ext
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientFace
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientDegeneracy
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientι_face
#print axioms CategoryTheory.CategoryHomology.nervePullbackCoefficientι_degeneracy

end MathlibExtTest.AlgebraicTopology.LocalCoefficient.NervePullbackBarCoreTests
