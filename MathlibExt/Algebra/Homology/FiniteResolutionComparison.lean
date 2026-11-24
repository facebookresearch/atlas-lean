/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.CategoryTheory.ExactCategory.FiniteResolving
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Comparison maps for finite resolutions

This file packages morphisms between finite resolutions together with their
augmentation square.  When the image of every resolving object is projective,
Mathlib's projective-resolution comparison maps produce such morphisms.  For
two resolutions of the same object, fullness and faithfulness lift the
ambient comparison homotopy equivalence back to the source category.

The projectivity, fullness, and faithfulness assumptions are explicit.  No
generic comparison for a nonprojective resolving image, Euler independence,
additivity, or inverse on `K₀` is asserted.

## Main declarations

* `CategoryTheory.Abelian.FiniteResolution.Hom`
* `CategoryTheory.Abelian.FiniteResolution.Hom.id`
* `CategoryTheory.Abelian.FiniteResolution.Hom.comp`
* `CategoryTheory.Abelian.FiniteResolution.toProjectiveResolution`
* `CategoryTheory.Abelian.FiniteResolution.comparisonHom`
* `CategoryTheory.Abelian.FiniteResolution.comparisonHomotopyEquiv`
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe vP uP vA uA

namespace CategoryTheory.Abelian.FiniteResolution

variable {P : Type uP} [Category.{vP} P] [Preadditive P]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {i : P ⥤ A} [i.Additive]

/-- A morphism of finite resolutions over `f : X₁ ⟶ X₂`.

The augmentation equation is oriented as mapped source chain map followed by
the target augmentation, equal to the source augmentation followed by the
degree-zero single-complex map of `f`. -/
structure Hom {X₁ X₂ : A}
    (R₁ : FiniteResolution i X₁) (R₂ : FiniteResolution i X₂)
    (f : X₁ ⟶ X₂) where
  /-- The source chain map. -/
  map : R₁.complex ⟶ R₂.complex
  /-- Compatibility with the two augmentations. -/
  augmentation_comm :
    (i.mapHomologicalComplex (ComplexShape.down ℕ)).map map ≫
        R₂.augmentation =
      R₁.augmentation ≫ (ChainComplex.single₀ A).map f

namespace Hom

variable {X₁ X₂ X₃ : A}
variable {R₁ : FiniteResolution i X₁} {R₂ : FiniteResolution i X₂}
variable {R₃ : FiniteResolution i X₃}
variable {f : X₁ ⟶ X₂} {g : X₂ ⟶ X₃}

/-- The identity morphism of a finite resolution. -/
def id (R : FiniteResolution i X₁) : Hom R R (𝟙 X₁) where
  map := 𝟙 R.complex
  augmentation_comm := by simp

/-- Composition of morphisms of finite resolutions. -/
def comp (φ : Hom R₁ R₂ f) (ψ : Hom R₂ R₃ g) :
    Hom R₁ R₃ (f ≫ g) where
  map := φ.map ≫ ψ.map
  augmentation_comm := by
    simp only [Functor.map_comp]
    rw [Category.assoc, ψ.augmentation_comm]
    rw [← Category.assoc, φ.augmentation_comm]
    rw [Category.assoc, ← Functor.map_comp]

end Hom

/-- Regard a finite resolution whose mapped terms are projective as a
projective resolution in the target abelian category. -/
noncomputable def toProjectiveResolution {X : A}
    (R : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    ProjectiveResolution X where
  complex := R.mappedComplex
  projective n := hproj (R.complex.X n)
  π := R.augmentation
  quasiIso := R.quasiIso

/--
A morphism of target objects induces a comparison morphism between finite resolutions when their
mapped terms are projective and `i` is fully faithful.
-/
noncomputable def comparisonHom [i.Full] [i.Faithful]
    {X₁ X₂ : A} (R₁ : FiniteResolution i X₁)
    (R₂ : FiniteResolution i X₂) (f : X₁ ⟶ X₂)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) : Hom R₁ R₂ f := by
  let F := i.mapHomologicalComplex (ComplexShape.down ℕ)
  let Q₁ := R₁.toProjectiveResolution hproj
  let Q₂ := R₂.toProjectiveResolution hproj
  let φ : R₁.complex ⟶ R₂.complex :=
    F.preimage (ProjectiveResolution.lift f Q₁ Q₂)
  have hφ : F.map φ = ProjectiveResolution.lift f Q₁ Q₂ :=
    F.map_preimage _
  refine { map := φ, augmentation_comm := ?_ }
  change F.map φ ≫ R₂.augmentation = _
  rw [hφ]
  exact ProjectiveResolution.lift_commutes f Q₁ Q₂

/-- Two finite resolutions of the same object are homotopy equivalent in the
source when their mapped terms are projective and `i` is fully faithful. -/
noncomputable def comparisonHomotopyEquiv [i.Full] [i.Faithful]
    {X : A} (R₁ R₂ : FiniteResolution i X)
    (hproj : ∀ P₀ : P, Projective (i.obj P₀)) :
    HomotopyEquiv R₁.complex R₂.complex := by
  let F := i.mapHomologicalComplex (ComplexShape.down ℕ)
  let Q₁ := R₁.toProjectiveResolution hproj
  let Q₂ := R₂.toProjectiveResolution hproj
  let eA : HomotopyEquiv (F.obj R₁.complex) (F.obj R₂.complex) :=
    ProjectiveResolution.homotopyEquiv Q₁ Q₂
  let hom : R₁.complex ⟶ R₂.complex := F.preimage eA.hom
  let inv : R₂.complex ⟶ R₁.complex := F.preimage eA.inv
  refine
    { hom := hom
      inv := inv
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · apply i.preimageHomotopy
    simpa [F, hom, inv] using eA.homotopyHomInvId
  · apply i.preimageHomotopy
    simpa [F, hom, inv] using eA.homotopyInvHomId

end CategoryTheory.Abelian.FiniteResolution

end
