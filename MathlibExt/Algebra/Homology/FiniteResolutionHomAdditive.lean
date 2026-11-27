/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionHomotopyFunctor

/-!
# Additive finite-resolution comparison maps

Let P be preadditive, A abelian and i : P → A additive. Zero and addition of augmented
comparisons use the zero and sum resolving chain maps, over the corresponding zero and sum base
maps. Source and target transport preserve these operations.

If i is full faithful and every resolving image is projective, the chosen comparisons of zero
and sums are homotopic to zero and sums of comparisons. Their homotopy classes are therefore
additive, and every chosen family of finite resolutions gives an additive homotopy-category
functor.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uP vP uQ vQ uA vA uB vB

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive]
variable {X₁ X₂ : A}
variable {R₁ : FiniteResolution i X₁} {R₂ : FiniteResolution i X₂}
variable {f g : X₁ ⟶ X₂}

namespace Hom

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. The zero chain map R₁.complex →
R₂.complex is an augmented comparison over the zero morphism X₁ → X₂. -/
def zero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    Hom R₁ R₂ (0 : X₁ ⟶ X₂) where
  map := 0
  augmentation_comm := by simp

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. Adding the chain maps φ+ψ gives
an augmented comparison over f+g, since i is additive and both augmentation squares commute. -/
def add (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) : Hom R₁ R₂ (f + g) where
  map := φ.map + ψ.map
  augmentation_comm := by
    simp only [CategoryTheory.Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, φ.augmentation_comm, ψ.augmentation_comm]

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. The resolving chain map of the
zero augmented comparison is exactly zero. -/
theorem zero_map (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    (Hom.zero R₁ R₂).map = (0 : R₁.complex ⟶ R₂.complex) :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. In every resolution degree n ∈
ℕ, the component of the zero augmented comparison is the zero morphism R₁,ₙ → R₂,ₙ. -/
theorem zero_map_f (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) (n : ℕ) :
    (Hom.zero R₁ R₂).map.f n = 0 :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. The resolving chain map of the
sum comparison is the sum φ.map+ψ.map. -/
theorem add_map (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) :
    (φ.add ψ).map = φ.map + ψ.map :=
  rfl

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. For every n ∈ ℕ, the degree-n
component of the sum comparison is φₙ+ψₙ. -/
theorem add_map_f (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) (n : ℕ) :
    (φ.add ψ).map.f n = φ.map.f n + ψ.map.f n :=
  rfl

section SourceChange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {j : Q ⥤ A} [j.Additive]
variable (F : P ⥤ Q) [F.Additive] (e : F ⋙ j ≅ i)

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. Let Q be preadditive, j : Q → A
additive, and F : P → Q additive with compatibility e : j ∘ F ≅ i. Source transport sends the
zero augmented comparison to the zero comparison of the F-image resolutions. -/
theorem mapSource_zero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    (Hom.zero R₁ R₂).mapSource F e = Hom.zero (R₁.mapSource F e) (R₂.mapSource F e) := by
  apply Hom.ext
  change (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (0 : R₁.complex ⟶ R₂.complex) = 0
  simp only [CategoryTheory.Functor.map_zero]

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. Let Q be preadditive, j : Q → A
additive, and F : P → Q additive with compatibility e : j ∘ F ≅ i. Source transport sends φ+ψ to
the sum of the source-transported augmented comparisons. -/
theorem mapSource_add (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) :
    (φ.add ψ).mapSource F e = (φ.mapSource F e).add (ψ.mapSource F e) := by
  apply Hom.ext
  change (F.mapHomologicalComplex (ComplexShape.down ℕ)).map (φ.map + ψ.map) =
    (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map +
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ.map
  exact CategoryTheory.Functor.map_add (F.mapHomologicalComplex (ComplexShape.down ℕ))

end SourceChange

section TargetChange

variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : P ⥤ B} [j.Additive]
variable (H : A ⥤ B) [H.Additive] [H.PreservesHomology] (e : i ⋙ H ≅ j)

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. Let B be abelian, j : P → B
additive, and H : A → B additive and homology-preserving, with compatibility e : H ∘ i ≅ j.
Target transport sends the zero augmented comparison to the zero comparison of the
target-changed resolutions, after identifying H(0)=0. -/
theorem mapTarget_zero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    HEq ((Hom.zero R₁ R₂).mapTarget H e)
      (Hom.zero (R₁.mapTarget H e) (R₂.mapTarget H e)) :=
  Hom.hext _ _ rfl rfl (by simp only [CategoryTheory.Functor.map_zero]) HEq.rfl

/-- Let P be preadditive, A abelian and i : P → A additive. Let R₁,R₂ be finite resolutions of
X₁,X₂, and let φ,ψ be augmented comparisons over f,g : X₁ → X₂. Let B be abelian, j : P → B
additive, and H : A → B additive and homology-preserving, with compatibility e : H ∘ i ≅ j.
Target transport sends φ+ψ to the sum of their target-changed comparisons, after identifying
H(f+g)=H(f)+H(g). -/
theorem mapTarget_add (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) :
    HEq ((φ.add ψ).mapTarget H e) ((φ.mapTarget H e).add (ψ.mapTarget H e)) :=
  Hom.hext _ _ rfl rfl (CategoryTheory.Functor.map_add H (f := f) (g := g)) HEq.rfl

end TargetChange

end Hom

section ChosenComparisons

variable [i.Full] [i.Faithful]

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. The
chosen augmented comparison over the zero base morphism is homotopic to the zero chain map. -/
def comparisonHomotopyZero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R₁ R₂ (0 : X₁ ⟶ X₂) hproj).map
      (0 : R₁.complex ⟶ R₂.complex) :=
  comparisonHomotopy (comparisonHom R₁ R₂ (0 : X₁ ⟶ X₂) hproj) (Hom.zero R₁ R₂) hproj

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. For f,g :
X₁ → X₂, the chosen comparison over f+g is homotopic to the sum of the chosen comparison chain
maps over f and g. -/
def comparisonHomotopyAdd (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (f g : X₁ ⟶ X₂) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R₁ R₂ (f + g) hproj).map
      ((comparisonHom R₁ R₂ f hproj).map + (comparisonHom R₁ R₂ g hproj).map) :=
  comparisonHomotopy (comparisonHom R₁ R₂ (f + g) hproj)
    ((comparisonHom R₁ R₂ f hproj).add (comparisonHom R₁ R₂ g hproj)) hproj

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. The
homotopy class of the chosen comparison over zero is the zero morphism between the two
resolution complexes. -/
theorem comparisonHom_quotient_zero
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom R₁ R₂ (0 : X₁ ⟶ X₂) hproj).map = 0 := by
  simpa only [CategoryTheory.Functor.map_zero] using
    HomotopyCategory.eq_of_homotopy _ _ (comparisonHomotopyZero R₁ R₂ hproj)

/-- Let P be preadditive, A abelian and i : P → A additive full faithful. Let R₁,R₂ be finite
resolutions of X₁,X₂ and f : X₁ → X₂. A comparison is a chain map of resolving complexes whose
image commutes with augmentation. Assume i(P₀) is projective for every object P₀ of P. The
homotopy class of the chosen comparison over f+g equals the sum of the classes of the chosen
comparisons over f and g. -/
theorem comparisonHom_quotient_add
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (f g : X₁ ⟶ X₂) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom R₁ R₂ (f + g) hproj).map =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
          (comparisonHom R₁ R₂ f hproj).map +
        (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
          (comparisonHom R₁ R₂ g hproj).map := by
  simpa only [CategoryTheory.Functor.map_add] using
    HomotopyCategory.eq_of_homotopy _ _ (comparisonHomotopyAdd R₁ R₂ f g hproj)

/-- Let P be preadditive, A abelian and i : P → A additive full faithful, with i(P₀) projective for
every resolving object P₀. For a family of finite resolutions R(X) of all X∈A, the functor X ↦
[R(X).complex] to the homotopy category is additive on base morphisms. -/
instance finiteResolutionHomotopyFunctorAdditive
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (finiteResolutionHomotopyFunctor R hproj).Additive where
  map_add {X Y f g} := comparisonHom_quotient_add (R X) (R Y) f g hproj

end ChosenComparisons

end CategoryTheory.Abelian.FiniteResolution

end
