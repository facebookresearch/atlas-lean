/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.CategoryHomology.BarConstruction

/-!
# Pulling the coefficient bar back along a nerve map

For a simplicial map `φ : X ⟶ nerve G` and a covariant coefficient functor
`M : G ⥤ A`, this file defines the degree family indexed by simplices of `X`,
the corresponding coproduct objects, and their face and degeneracy maps.
The component maps reuse the landed category-homology coefficient bar and
transport only across the named naturality equalities of `φ`.

This is deliberately only the core construction. It makes no simplicial-
identity, simplicial-object, chain-complex, homology, local-system, or plus-
construction claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace CategoryTheory.Limits.Sigma

universe w v u

variable {A : Type u} [Category.{v} A]

/-- Compare two composites of maps between coproducts when their final index
maps agree pointwise and their component composites agree after the induced
transport. -/
theorem map'_comp_eq
    {I₀ I₁ I₁' I₂ : Type w} [HasCoproducts.{w} A]
    {X₀ : I₀ → A} {X₁ : I₁ → A} {X₁' : I₁' → A} {X₂ : I₂ → A}
    (p : I₀ → I₁) (q : I₁ → I₂)
    (hp : ∀ a, X₀ a ⟶ X₁ (p a)) (hq : ∀ b, X₁ b ⟶ X₂ (q b))
    (p' : I₀ → I₁') (q' : I₁' → I₂)
    (hp' : ∀ a, X₀ a ⟶ X₁' (p' a))
    (hq' : ∀ b, X₁' b ⟶ X₂ (q' b))
    (hidx : ∀ a, q (p a) = q' (p' a))
    (hhom : ∀ a, (hp a ≫ hq (p a)) ≫
      eqToHom (congrArg X₂ (hidx a)) = hp' a ≫ hq' (p' a)) :
    Sigma.map' p hp ≫ Sigma.map' q hq =
      Sigma.map' p' hp' ≫ Sigma.map' q' hq' := by
  apply Sigma.hom_ext
  intro a
  have transport_ι {x y : I₂} (h : x = y) :
      eqToHom (congrArg X₂ h) ≫ Sigma.ι X₂ y = Sigma.ι X₂ x := by
    subst y
    exact Category.id_comp _
  have hι : eqToHom (congrArg X₂ (hidx a)) ≫
      Sigma.ι X₂ (q' (p' a)) = Sigma.ι X₂ (q (p a)) :=
    transport_ι (hidx a)
  have hL₁ : Sigma.ι X₀ a ≫ Sigma.map' p hp =
      hp a ≫ Sigma.ι X₁ (p a) := by
    exact Sigma.ι_comp_map' p hp a
  have hL₂ : Sigma.ι X₁ (p a) ≫ Sigma.map' q hq =
      hq (p a) ≫ Sigma.ι X₂ (q (p a)) := by
    exact Sigma.ι_comp_map' q hq (p a)
  have hR₁ : Sigma.ι X₀ a ≫ Sigma.map' p' hp' =
      hp' a ≫ Sigma.ι X₁' (p' a) := by
    exact Sigma.ι_comp_map' p' hp' a
  have hR₂ : Sigma.ι X₁' (p' a) ≫ Sigma.map' q' hq' =
      hq' (p' a) ≫ Sigma.ι X₂ (q' (p' a)) := by
    exact Sigma.ι_comp_map' q' hq' (p' a)
  calc
    Sigma.ι X₀ a ≫ (Sigma.map' p hp ≫ Sigma.map' q hq) =
        (Sigma.ι X₀ a ≫ Sigma.map' p hp) ≫ Sigma.map' q hq :=
      (Category.assoc _ _ _).symm
    _ = (hp a ≫ Sigma.ι X₁ (p a)) ≫ Sigma.map' q hq := by
      exact congrArg (fun k => k ≫ Sigma.map' q hq) hL₁
    _ = hp a ≫ (Sigma.ι X₁ (p a) ≫ Sigma.map' q hq) :=
      Category.assoc _ _ _
    _ = hp a ≫ (hq (p a) ≫ Sigma.ι X₂ (q (p a))) := by
      exact congrArg (fun k => hp a ≫ k) hL₂
    _ = (hp a ≫ hq (p a)) ≫ Sigma.ι X₂ (q (p a)) :=
      (Category.assoc _ _ _).symm
    _ = ((hp a ≫ hq (p a)) ≫
          eqToHom (congrArg X₂ (hidx a))) ≫
            Sigma.ι X₂ (q' (p' a)) := by
      calc
        _ = (hp a ≫ hq (p a)) ≫
            (eqToHom (congrArg X₂ (hidx a)) ≫
              Sigma.ι X₂ (q' (p' a))) := by rw [hι]
        _ = _ := (Category.assoc _ _ _).symm
    _ = (hp' a ≫ hq' (p' a)) ≫
          Sigma.ι X₂ (q' (p' a)) := by
      exact congrArg (fun k => k ≫ Sigma.ι X₂ (q' (p' a))) (hhom a)
    _ = hp' a ≫ (hq' (p' a) ≫ Sigma.ι X₂ (q' (p' a))) :=
      Category.assoc _ _ _
    _ = hp' a ≫ (Sigma.ι X₁' (p' a) ≫ Sigma.map' q' hq') := by
      exact congrArg (fun k => hp' a ≫ k) hR₂.symm
    _ = (hp' a ≫ Sigma.ι X₁' (p' a)) ≫ Sigma.map' q' hq' :=
      (Category.assoc _ _ _).symm
    _ = (Sigma.ι X₀ a ≫ Sigma.map' p' hp') ≫ Sigma.map' q' hq' := by
      exact congrArg (fun k => k ≫ Sigma.map' q' hq') hR₁.symm
    _ = Sigma.ι X₀ a ≫
          (Sigma.map' p' hp' ≫ Sigma.map' q' hq') :=
      Category.assoc _ _ _

end CategoryTheory.Limits.Sigma

namespace CategoryTheory.CategoryHomology

universe vG uG vA uA

variable {G : Type uG} [Category.{vG} G]
variable {A : Type uA} [Category.{vA} A]
variable {X : SSet.{max uG vG}}
variable (φ : X ⟶ CategoryTheory.nerve G) (M : G ⥤ A)

/-- The coefficient family on degree-`n` simplices obtained by restricting
the category-homology coefficient bar along `φ`. -/
def nervePullbackCoefficientFamily (n : ℕ) : X _⦋n⦌ → A :=
  fun σ => coefficientBarFamily M n (φ.app _ σ)

/-- Naturality of `φ` on a face, oriented from the nerve face to the image of
the face in `X`. -/
theorem nervePullback_face_index {n : ℕ} (i : Fin (n + 2))
    (σ : X _⦋n + 1⦌) :
    (CategoryTheory.nerve G).δ i (φ.app _ σ) =
      φ.app _ (X.δ i σ) := by
  exact (ConcreteCategory.congr_hom
    (φ.naturality (SimplexCategory.δ i).op) σ).symm

/-- Naturality of `φ` on a degeneracy, oriented from the nerve degeneracy to
the image of the degeneracy in `X`. -/
theorem nervePullback_degeneracy_index {n : ℕ} (i : Fin (n + 1))
    (σ : X _⦋n⦌) :
    (CategoryTheory.nerve G).σ i (φ.app _ σ) =
      φ.app _ (X.σ i σ) := by
  exact (ConcreteCategory.congr_hom
    (φ.naturality (SimplexCategory.σ i).op) σ).symm

/-- Coefficient morphism on one face summand of the restricted bar. -/
def nervePullbackCoefficientFaceHom {n : ℕ} (i : Fin (n + 2))
    (σ : X _⦋n + 1⦌) :
    nervePullbackCoefficientFamily φ M (n + 1) σ ⟶
      nervePullbackCoefficientFamily φ M n (X.δ i σ) :=
  coefficientFaceHom M i (φ.app _ σ) ≫
    eqToHom (congrArg (fun F => M.obj F.left)
      (nervePullback_face_index φ i σ))

/-- Coefficient morphism on one degeneracy summand of the restricted bar. -/
def nervePullbackCoefficientDegeneracyHom {n : ℕ}
    (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    nervePullbackCoefficientFamily φ M n σ ⟶
      nervePullbackCoefficientFamily φ M (n + 1) (X.σ i σ) :=
  coefficientDegeneracyHom M i (φ.app _ σ) ≫
    eqToHom (congrArg (fun F => M.obj F.left)
      (nervePullback_degeneracy_index φ i σ))

variable [HasCoproducts.{max uG vG} A]

/-- Degree-`n` coproduct object of the restricted coefficient bar. -/
noncomputable abbrev nervePullbackCoefficientObj (n : ℕ) : A :=
  ∐ nervePullbackCoefficientFamily φ M n

/-- Inclusion of the summand indexed by a degree-`n` simplex. -/
noncomputable abbrev nervePullbackCoefficientι {n : ℕ}
    (σ : X _⦋n⦌) :
    nervePullbackCoefficientFamily φ M n σ ⟶
      nervePullbackCoefficientObj φ M n :=
  Sigma.ι (nervePullbackCoefficientFamily φ M n) σ

/-- Morphisms out of a restricted coefficient object are determined on its
simplex summands. -/
theorem nervePullbackCoefficient_hom_ext {n : ℕ} {Z : A}
    (f g : nervePullbackCoefficientObj φ M n ⟶ Z)
    (h : ∀ σ, nervePullbackCoefficientι φ M σ ≫ f =
      nervePullbackCoefficientι φ M σ ≫ g) :
    f = g :=
  Sigma.hom_ext f g h

/-- Face map between degree objects of the restricted coefficient bar. -/
def nervePullbackCoefficientFace {n : ℕ} (i : Fin (n + 2)) :
    nervePullbackCoefficientObj φ M (n + 1) ⟶
      nervePullbackCoefficientObj φ M n :=
  Sigma.map' (f := nervePullbackCoefficientFamily φ M n)
    (g := nervePullbackCoefficientFamily φ M (n + 1))
    (fun σ => X.δ i σ) (nervePullbackCoefficientFaceHom φ M i)

/-- Degeneracy map between degree objects of the restricted coefficient bar. -/
def nervePullbackCoefficientDegeneracy {n : ℕ} (i : Fin (n + 1)) :
    nervePullbackCoefficientObj φ M n ⟶
      nervePullbackCoefficientObj φ M (n + 1) :=
  Sigma.map' (f := nervePullbackCoefficientFamily φ M (n + 1))
    (g := nervePullbackCoefficientFamily φ M n)
    (fun σ => X.σ i σ) (nervePullbackCoefficientDegeneracyHom φ M i)

/-- Formula for a restricted face map on a simplex summand. -/
@[reassoc (attr := simp)]
theorem nervePullbackCoefficientι_face {n : ℕ} (i : Fin (n + 2))
    (σ : X _⦋n + 1⦌) :
    nervePullbackCoefficientι φ M σ ≫
        nervePullbackCoefficientFace φ M i =
      nervePullbackCoefficientFaceHom φ M i σ ≫
        nervePullbackCoefficientι φ M (X.δ i σ) := by
  exact Sigma.ι_comp_map' _ _ σ

/-- Formula for a restricted degeneracy map on a simplex summand. -/
@[reassoc (attr := simp)]
theorem nervePullbackCoefficientι_degeneracy {n : ℕ}
    (i : Fin (n + 1)) (σ : X _⦋n⦌) :
    nervePullbackCoefficientι φ M σ ≫
        nervePullbackCoefficientDegeneracy φ M i =
      nervePullbackCoefficientDegeneracyHom φ M i σ ≫
        nervePullbackCoefficientι φ M (X.σ i σ) := by
  exact Sigma.ι_comp_map' _ _ σ

end CategoryTheory.CategoryHomology
