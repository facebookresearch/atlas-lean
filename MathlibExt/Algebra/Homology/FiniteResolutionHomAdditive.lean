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
# Additivity of original augmented comparison maps and resolution functors

Zero and addition of comparison maps use the original zero and sum chain
maps. Additivity of the resolving and single-complex functors proves their
augmentation squares. Source and target change preserve these operations.

Constructive comparison uniqueness gives zero and addition homotopies for
the existing chosen lifts. Their stock quotient images are therefore zero
and additive, which earns the public additive instance for the existing
given-family finite-resolution homotopy functor.
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

/-- The original zero chain map is an augmented comparison over the zero
base morphism. -/
def zero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    Hom R₁ R₂ (0 : X₁ ⟶ X₂) where
  map := 0
  augmentation_comm := by simp

/-- Add two original augmented comparison maps by their original sum chain
map and the sum of their base morphisms. -/
def add (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) : Hom R₁ R₂ (f + g) where
  map := φ.map + ψ.map
  augmentation_comm := by
    simp only [CategoryTheory.Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add, φ.augmentation_comm, ψ.augmentation_comm]

/-- The entire zero comparison chain map is the original zero morphism. -/
theorem zero_map (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    (Hom.zero R₁ R₂).map = (0 : R₁.complex ⟶ R₂.complex) :=
  rfl

/-- Every zero comparison component is the original zero component. -/
theorem zero_map_f (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) (n : ℕ) :
    (Hom.zero R₁ R₂).map.f n = 0 :=
  rfl

/-- Addition retains the entire original sum chain map. -/
theorem add_map (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) :
    (φ.add ψ).map = φ.map + ψ.map :=
  rfl

/-- Addition retains each original sum comparison component. -/
theorem add_map_f (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) (n : ℕ) :
    (φ.add ψ).map.f n = φ.map.f n + ψ.map.f n :=
  rfl

section SourceChange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {j : Q ⥤ A} [j.Additive]
variable (F : P ⥤ Q) [F.Additive] (e : F ⋙ j ≅ i)

/-- Source change preserves the full zero augmented comparison. -/
theorem mapSource_zero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    (Hom.zero R₁ R₂).mapSource F e = Hom.zero (R₁.mapSource F e) (R₂.mapSource F e) := by
  apply Hom.ext
  change (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
      (0 : R₁.complex ⟶ R₂.complex) = 0
  simp only [CategoryTheory.Functor.map_zero]

/-- Source change preserves the full sum augmented comparison. -/
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

/--
Target change preserves the zero comparison, with its base map identified by the original functor
zero-map equation.
-/
theorem mapTarget_zero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) :
    HEq ((Hom.zero R₁ R₂).mapTarget H e)
      (Hom.zero (R₁.mapTarget H e) (R₂.mapTarget H e)) :=
  Hom.hext _ _ rfl rfl (by simp only [CategoryTheory.Functor.map_zero]) HEq.rfl

/--
Target change preserves the sum comparison, with its base map identified by the original functor
additivity equation.
-/
theorem mapTarget_add (φ : Hom R₁ R₂ f) (ψ : Hom R₁ R₂ g) :
    HEq ((φ.add ψ).mapTarget H e) ((φ.mapTarget H e).add (ψ.mapTarget H e)) :=
  Hom.hext _ _ rfl rfl (CategoryTheory.Functor.map_add H (f := f) (g := g)) HEq.rfl

end TargetChange

end Hom

section ChosenComparisons

variable [i.Full] [i.Faithful]

/-- The same original chosen lift of zero is homotopic to the zero comparison chain map. -/
def comparisonHomotopyZero (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R₁ R₂ (0 : X₁ ⟶ X₂) hproj).map
      (0 : R₁.complex ⟶ R₂.complex) :=
  comparisonHomotopy (comparisonHom R₁ R₂ (0 : X₁ ⟶ X₂) hproj) (Hom.zero R₁ R₂) hproj

/--
The same original chosen lift of a sum is homotopic to the sum of the original chosen comparison
chain maps.
-/
def comparisonHomotopyAdd (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (f g : X₁ ⟶ X₂) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R₁ R₂ (f + g) hproj).map
      ((comparisonHom R₁ R₂ f hproj).map + (comparisonHom R₁ R₂ g hproj).map) :=
  comparisonHomotopy (comparisonHom R₁ R₂ (f + g) hproj)
    ((comparisonHom R₁ R₂ f hproj).add (comparisonHom R₁ R₂ g hproj)) hproj

/-- The original chosen zero lift maps to zero in the stock quotient. -/
theorem comparisonHom_quotient_zero
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom R₁ R₂ (0 : X₁ ⟶ X₂) hproj).map = 0 := by
  simpa only [CategoryTheory.Functor.map_zero] using
    HomotopyCategory.eq_of_homotopy _ _ (comparisonHomotopyZero R₁ R₂ hproj)

/-- The original chosen sum lift maps to the sum of the original chosen
quotient maps. -/
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

/-- The existing given-family resolution functor is additive by the
constructed comparison addition homotopy and the stock additive quotient. -/
instance finiteResolutionHomotopyFunctorAdditive
    (R : ∀ X : A, FiniteResolution i X) (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (finiteResolutionHomotopyFunctor R hproj).Additive where
  map_add {X Y f g} := comparisonHom_quotient_add (R X) (R Y) f g hproj

end ChosenComparisons

end CategoryTheory.Abelian.FiniteResolution

end
