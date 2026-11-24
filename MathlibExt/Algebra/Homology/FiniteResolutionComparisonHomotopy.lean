/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.FiniteResolutionHomTransport

/-!
# Homotopies between original augmented finite-resolution comparisons

Two original augmented comparison maps over the same morphism are homotopic when their resolving
images are projective and the resolving functor is fully faithful. The homotopy is constructed
from the augmentation squares by Mathlib's projective-resolution lifting homotopy and pulled back
to the original resolving complexes.

This gives identity and composition homotopies for the existing chosen comparisons and their
naturality under source and target change. Source change derives projectivity of its image terms
from the original compatibility isomorphism. All finite complexes, augmentations, and bounds
remain those of the existing finite-resolution constructors.
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
variable {X₁ X₂ X₃ : A}
variable {R₁ : FiniteResolution i X₁} {R₂ : FiniteResolution i X₂}
variable {R₃ : FiniteResolution i X₃}
variable {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}

/--
Construct a homotopy from the two original augmentation squares. Projectivity is required only for
the terms of these resolutions.
-/
def comparisonHomotopyOfProjectiveTerms [i.Full] [i.Faithful]
    (φ ψ : Hom R₁ R₂ f)
    (h₁ : ∀ n : ℕ, Projective (i.obj (R₁.complex.X n)))
    (h₂ : ∀ n : ℕ, Projective (i.obj (R₂.complex.X n))) :
    Homotopy φ.map ψ.map := by
  let Q₁ : ProjectiveResolution X₁ :=
    { complex := R₁.mappedComplex
      projective := h₁
      π := R₁.augmentation
      quasiIso := R₁.quasiIso }
  let Q₂ : ProjectiveResolution X₂ :=
    { complex := R₂.mappedComplex
      projective := h₂
      π := R₂.augmentation
      quasiIso := R₂.quasiIso }
  apply i.preimageHomotopy
  exact ProjectiveResolution.liftHomotopy f (P := Q₁) (Q := Q₂)
    ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.map)
    ((i.mapHomologicalComplex (ComplexShape.down ℕ)).map ψ.map)
    φ.augmentation_comm ψ.augmentation_comm

/-- Original comparison uniqueness under the existing projective-image
hypothesis used by `comparisonHom`. -/
def comparisonHomotopy [i.Full] [i.Faithful] (φ ψ : Hom R₁ R₂ f)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) : Homotopy φ.map ψ.map :=
  comparisonHomotopyOfProjectiveTerms φ ψ
    (fun n => hproj (R₁.complex.X n)) (fun n => hproj (R₂.complex.X n))

/--
The original chosen comparison of an identity is homotopic to the identity map of the same
original complex.
-/
def comparisonHomotopyId [i.Full] [i.Faithful] (R : FiniteResolution i X₁)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R R (𝟙 X₁) hproj).map (𝟙 R.complex) :=
  comparisonHomotopy (comparisonHom R R (𝟙 X₁) hproj) (Hom.id R) hproj

/--
The original chosen comparison of a composite is homotopic to the composite of the same original
chosen comparison maps.
-/
def comparisonHomotopyComp [i.Full] [i.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (R₃ : FiniteResolution i X₃) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    Homotopy (comparisonHom R₁ R₃ (f ≫ g) hproj).map
      ((comparisonHom R₁ R₂ f hproj).map ≫ (comparisonHom R₂ R₃ g hproj).map) :=
  comparisonHomotopy (comparisonHom R₁ R₃ (f ≫ g) hproj)
    ((comparisonHom R₁ R₂ f hproj).comp (comparisonHom R₂ R₃ g hproj)) hproj

/--
The original chosen identity comparison becomes the identity under the stock homotopy-category
quotient.
-/
theorem comparisonHom_quotient_id [i.Full] [i.Faithful] (R : FiniteResolution i X₁)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom R R (𝟙 X₁) hproj).map =
      𝟙 ((HomotopyCategory.quotient P (ComplexShape.down ℕ)).obj R.complex) := by
  simpa only [CategoryTheory.Functor.map_id] using
    HomotopyCategory.eq_of_homotopy _ _ (comparisonHomotopyId R hproj)

/-- The original chosen comparisons preserve composition in the stock
homotopy category, with their original literal forward maps. -/
theorem comparisonHom_quotient_comp [i.Full] [i.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (R₃ : FiniteResolution i X₃) (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
        (comparisonHom R₁ R₃ (f ≫ g) hproj).map =
      (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
          (comparisonHom R₁ R₂ f hproj).map ≫
        (HomotopyCategory.quotient P (ComplexShape.down ℕ)).map
          (comparisonHom R₂ R₃ g hproj).map := by
  simpa only [CategoryTheory.Functor.map_comp] using
    HomotopyCategory.eq_of_homotopy _ _ (comparisonHomotopyComp R₁ R₂ R₃ f g hproj)

section SourceChange

variable {Q : Type uQ} [Category.{vQ} Q] [Preadditive Q]
variable {j : Q ⥤ A} [j.Additive]
variable (F : P ⥤ Q) [F.Additive] (e : F ⋙ j ≅ i)

/-- Stock additive homotopy transport has the exact original source-changed
augmented comparison maps as its endpoints. -/
def Hom.mapSourceHomotopy (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map) :
    Homotopy (φ.mapSource F e).map (ψ.mapSource F e).map :=
  F.mapHomotopy h

/-- The source-transported homotopy component is the source image of the original homotopy component. -/
theorem Hom.mapSourceHomotopy_hom (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map)
    (n m : ℕ) : (Hom.mapSourceHomotopy F e φ ψ h).hom n m = F.map (h.hom n m) :=
  rfl

/--
The compatibility isomorphism transports projectivity of each original resolving image to the
source-changed resolving image term.
-/
theorem mapSource_projective_term (R : FiniteResolution i X₁) (n : ℕ)
    (h : Projective (i.obj (R.complex.X n))) :
    Projective (j.obj ((R.mapSource F e).complex.X n)) :=
  Projective.of_iso (e.app (R.complex.X n)).symm h

/--
Compare a transported original augmented map with any augmented map over the same base morphism.
Projectivity of the changed terms is derived from the original compatibility and original term
projectivity.
-/
def sourceComparisonHomotopy [j.Full] [j.Faithful]
    (φ : Hom R₁ R₂ f) (ψ : Hom (R₁.mapSource F e) (R₂.mapSource F e) f)
    (h₁ : ∀ n : ℕ, Projective (i.obj (R₁.complex.X n)))
    (h₂ : ∀ n : ℕ, Projective (i.obj (R₂.complex.X n))) :
    Homotopy (φ.mapSource F e).map ψ.map :=
  comparisonHomotopyOfProjectiveTerms (φ.mapSource F e) ψ
    (fun n => mapSource_projective_term F e R₁ n (h₁ n))
    (fun n => mapSource_projective_term F e R₂ n (h₂ n))

/--
The transported original chosen comparison is homotopic to the existing chosen comparison for the
source-changed finite resolutions. The global target-image hypothesis belongs to that existing
chosen-map API.
-/
def comparisonHomotopySourceChange [i.Full] [i.Faithful] [j.Full] [j.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) (f : X₁ ⟶ X₂)
    (hprojP : ∀ P₀ : P, Projective (i.obj P₀))
    (hprojQ : ∀ Q₀ : Q, Projective (j.obj Q₀)) :
    Homotopy ((comparisonHom R₁ R₂ f hprojP).mapSource F e).map
      (comparisonHom (R₁.mapSource F e) (R₂.mapSource F e) f hprojQ).map :=
  sourceComparisonHomotopy F e (comparisonHom R₁ R₂ f hprojP)
    (comparisonHom (R₁.mapSource F e) (R₂.mapSource F e) f hprojQ)
    (fun n => hprojP (R₁.complex.X n)) (fun n => hprojP (R₂.complex.X n))

end SourceChange

section TargetChange

variable {B : Type uB} [Category.{vB} B] [Abelian B]
variable {j : P ⥤ B} [j.Additive]
variable (H : A ⥤ B) [H.Additive] [H.PreservesHomology] (e : i ⋙ H ≅ j)

/--
Target change retains the original homotopy between its unchanged comparison chain maps. Homology
preservation is used by the changed finite resolutions in the endpoint types.
-/
def Hom.mapTargetHomotopy (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map) :
    Homotopy (φ.mapTarget H e).map (ψ.mapTarget H e).map :=
  h

/-- Every original homotopy component is retained under target change. -/
theorem Hom.mapTargetHomotopy_hom (φ ψ : Hom R₁ R₂ f) (h : Homotopy φ.map ψ.map)
    (n m : ℕ) : (Hom.mapTargetHomotopy H e φ ψ h).hom n m = h.hom n m :=
  rfl

/--
Compare the target transport with any original augmented map over the mapped base morphism.
Projectivity of the target resolving images is an explicit termwise requirement.
-/
def targetComparisonHomotopy [j.Full] [j.Faithful]
    (φ : Hom R₁ R₂ f)
    (ψ : Hom (R₁.mapTarget H e) (R₂.mapTarget H e) (H.map f))
    (h₁ : ∀ n : ℕ, Projective (j.obj (R₁.complex.X n)))
    (h₂ : ∀ n : ℕ, Projective (j.obj (R₂.complex.X n))) :
    Homotopy (φ.mapTarget H e).map ψ.map :=
  comparisonHomotopyOfProjectiveTerms (φ.mapTarget H e) ψ h₁ h₂

/--
Naturality of the existing chosen comparisons under target change, with the original
projective-image hypotheses for both chosen APIs.
-/
def comparisonHomotopyTargetChange [i.Full] [i.Faithful] [j.Full] [j.Faithful]
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂) (f : X₁ ⟶ X₂)
    (hprojA : ∀ P₀ : P, Projective (i.obj P₀))
    (hprojB : ∀ P₀ : P, Projective (j.obj P₀)) :
    Homotopy ((comparisonHom R₁ R₂ f hprojA).mapTarget H e).map
      (comparisonHom (R₁.mapTarget H e) (R₂.mapTarget H e) (H.map f) hprojB).map :=
  targetComparisonHomotopy H e (comparisonHom R₁ R₂ f hprojA)
    (comparisonHom (R₁.mapTarget H e) (R₂.mapTarget H e) (H.map f) hprojB)
    (fun n => hprojB (R₁.complex.X n)) (fun n => hprojB (R₂.complex.X n))

end TargetChange

end CategoryTheory.Abelian.FiniteResolution

end
