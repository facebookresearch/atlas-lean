/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Bundled comparison maps of projective resolutions

This file packages Mathlib's existing lift of a morphism between projective
resolutions together with its augmentation equation.  The bundled identity,
composition, and transport of resolution morphisms, together with their
extensionality and coherence laws, need only the zero-object and
zero-morphism structure already required by Mathlib's
`ProjectiveResolution`; the noncanonical `liftHom` is the only
construction here that uses that the category is abelian.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory

universe v u

namespace CategoryTheory.ProjectiveResolution

section HomAlgebra

variable {C : Type u} [Category.{v} C] [Limits.HasZeroObject C]
  [Limits.HasZeroMorphisms C]

namespace Hom

/-- Two morphisms of projective resolutions over the same morphism of
resolved objects are equal once their underlying chain maps are equal;
the remaining field is a proof. -/
@[ext]
theorem ext {Z Z' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {f : Z ⟶ Z'} {φ ψ : Hom P P' f}
    (h : φ.hom = ψ.hom) : φ = ψ := by
  cases φ
  cases ψ
  cases h
  rfl

/-- The identity morphism of a projective resolution, over the identity
of the resolved object. -/
def id {Z : C} (P : ProjectiveResolution Z) : Hom P P (𝟙 Z) where
  hom := 𝟙 P.complex
  hom_f_zero_comp_π_f_zero := by
    rw [HomologicalComplex.id_f, Functor.map_id,
      HomologicalComplex.id_f, Category.id_comp, Category.comp_id]

@[simp]
theorem id_hom {Z : C} (P : ProjectiveResolution Z) :
    (Hom.id P).hom = 𝟙 P.complex :=
  rfl

/-- The composition of morphisms of projective resolutions, over the
composition of the resolved morphisms. -/
def comp {Z Z' Z'' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {P'' : ProjectiveResolution Z''}
    {f : Z ⟶ Z'} {g : Z' ⟶ Z''}
    (φ : Hom P P' f) (ψ : Hom P' P'' g) : Hom P P'' (f ≫ g) where
  hom := φ.hom ≫ ψ.hom
  hom_f_zero_comp_π_f_zero := by
    rw [HomologicalComplex.comp_f, Category.assoc,
      ψ.hom_f_zero_comp_π_f_zero, ← Category.assoc,
      φ.hom_f_zero_comp_π_f_zero, Category.assoc,
      ← HomologicalComplex.comp_f, ← Functor.map_comp]

@[simp]
theorem comp_hom {Z Z' Z'' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {P'' : ProjectiveResolution Z''}
    {f : Z ⟶ Z'} {g : Z' ⟶ Z''}
    (φ : Hom P P' f) (ψ : Hom P' P'' g) :
    (φ.comp ψ).hom = φ.hom ≫ ψ.hom :=
  rfl

/-- Transport a morphism of projective resolutions along an equality of
the resolved morphisms. The underlying chain map is unchanged. -/
def cast {Z Z' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {f f' : Z ⟶ Z'}
    (φ : Hom P P' f) (h : f = f') : Hom P P' f' where
  hom := φ.hom
  hom_f_zero_comp_π_f_zero := by
    rw [← h]
    exact φ.hom_f_zero_comp_π_f_zero

@[simp]
theorem cast_hom {Z Z' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {f f' : Z ⟶ Z'}
    (φ : Hom P P' f) (h : f = f') :
    (φ.cast h).hom = φ.hom :=
  rfl

@[simp]
theorem cast_rfl {Z Z' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {f : Z ⟶ Z'} (φ : Hom P P' f) :
    φ.cast rfl = φ :=
  rfl

@[simp]
theorem cast_cast {Z Z' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {f f' f'' : Z ⟶ Z'}
    (φ : Hom P P' f) (h : f = f') (h' : f' = f'') :
    (φ.cast h).cast h' = φ.cast (h.trans h') := by
  ext
  simp

/-- Left unit law for morphisms of projective resolutions: composing the
identity morphism with a morphism, transported along `Category.id_comp`,
is the morphism itself. -/
theorem id_comp {Z Z' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {f : Z ⟶ Z'} (φ : Hom P P' f) :
    ((Hom.id P).comp φ).cast (Category.id_comp f) = φ := by
  ext
  simp

/-- Right unit law for morphisms of projective resolutions: composing a
morphism with the identity morphism, transported along
`Category.comp_id`, is the morphism itself. -/
theorem comp_id {Z Z' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {f : Z ⟶ Z'} (φ : Hom P P' f) :
    (φ.comp (Hom.id P')).cast (Category.comp_id f) = φ := by
  ext
  simp

/-- Associativity for morphisms of projective resolutions, transported
along `Category.assoc` of the resolved morphisms. -/
theorem assoc {Z Z' Z'' Z''' : C} {P : ProjectiveResolution Z}
    {P' : ProjectiveResolution Z'} {P'' : ProjectiveResolution Z''}
    {P''' : ProjectiveResolution Z'''} {f : Z ⟶ Z'} {g : Z' ⟶ Z''}
    {h : Z'' ⟶ Z'''} (φ : Hom P P' f) (ψ : Hom P' P'' g)
    (χ : Hom P'' P''' h) :
    ((φ.comp ψ).comp χ).cast (Category.assoc f g h) =
      φ.comp (ψ.comp χ) := by
  ext
  simp

end Hom

end HomAlgebra

section LiftHom

variable {C : Type u} [Category.{v} C] [Abelian C]

set_option backward.isDefEq.respectTransparency false in
/-- The standard lift of a morphism, bundled as an augmentation-compatible
morphism of projective resolutions. -/
noncomputable def liftHom
    {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    ProjectiveResolution.Hom P Q f where
  hom := ProjectiveResolution.lift f P Q
  hom_f_zero_comp_π_f_zero := by
    simpa only [ChainComplex.single₀_map_f_zero] using
      ProjectiveResolution.lift_commutes_zero f P Q

@[simp]
theorem liftHom_hom {X Y : C} (f : X ⟶ Y)
    (P : ProjectiveResolution X) (Q : ProjectiveResolution Y) :
    (liftHom f P Q).hom = ProjectiveResolution.lift f P Q :=
  rfl

end LiftHom

end CategoryTheory.ProjectiveResolution

namespace CategoryTheory.Functor

universe v' u'

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [Preadditive C]
variable {D : Type u'} [Category.{v'} D] [HasZeroObject D] [Preadditive D]
  [CategoryWithHomology D]

set_option backward.isDefEq.respectTransparency.types false in
/-- Map an explicitly bundled morphism of projective resolutions. -/
noncomputable def mapProjectiveResolutionHom (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] [F.PreservesHomology]
    {X Y : C} {P : ProjectiveResolution X} {Q : ProjectiveResolution Y}
    {f : X ⟶ Y} (φ : ProjectiveResolution.Hom P Q f) :
    ProjectiveResolution.Hom (F.mapProjectiveResolution P)
      (F.mapProjectiveResolution Q) (F.map f) where
  hom := (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom
  hom_f_zero_comp_π_f_zero := by
    have hφ := φ.hom_comp_π
    change φ.hom ≫ Q.π = P.π ≫
      (HomologicalComplex.single C (ComplexShape.down ℕ) 0).map f at hφ
    have hn := (HomologicalComplex.singleMapHomologicalComplex F
      (ComplexShape.down ℕ) 0).hom.naturality f
    change (F.mapHomologicalComplex (ComplexShape.down ℕ)).map
          ((HomologicalComplex.single C (ComplexShape.down ℕ) 0).map f) ≫
        (HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.down ℕ) 0).hom.app Y =
      (HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.down ℕ) 0).hom.app X ≫
        (HomologicalComplex.single D (ComplexShape.down ℕ) 0).map (F.map f) at hn
    have h : (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom ≫
          ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π ≫
            (HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.down ℕ) 0).hom.app Y) =
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫
            (HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.down ℕ) 0).hom.app X) ≫
          (HomologicalComplex.single D (ComplexShape.down ℕ) 0).map (F.map f) := by
      rw [← Category.assoc, ← Functor.map_comp, hφ, Functor.map_comp,
        Category.assoc, hn, ← Category.assoc]
    change ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom ≫
      ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map Q.π ≫
        (HomologicalComplex.singleMapHomologicalComplex F
          (ComplexShape.down ℕ) 0).hom.app Y)).f 0 =
      (((F.mapHomologicalComplex (ComplexShape.down ℕ)).map P.π ≫
          (HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.down ℕ) 0).hom.app X) ≫
        (HomologicalComplex.single D (ComplexShape.down ℕ) 0).map (F.map f)).f 0
    exact HomologicalComplex.congr_hom h 0

@[simp]
theorem mapProjectiveResolutionHom_hom (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] [F.PreservesHomology]
    {X Y : C} {P : ProjectiveResolution X} {Q : ProjectiveResolution Y}
    {f : X ⟶ Y} (φ : ProjectiveResolution.Hom P Q f) :
    (F.mapProjectiveResolutionHom φ).hom =
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).map φ.hom :=
  rfl

@[simp]
theorem mapProjectiveResolutionHom_id (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] [F.PreservesHomology]
    {X : C} (P : ProjectiveResolution X) :
    (F.mapProjectiveResolutionHom (ProjectiveResolution.Hom.id P)).cast
        (F.map_id X) =
      ProjectiveResolution.Hom.id (F.mapProjectiveResolution P) := by
  apply ProjectiveResolution.Hom.ext
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).map_id P.complex

@[simp]
theorem mapProjectiveResolutionHom_comp (F : C ⥤ D) [F.Additive]
    [F.PreservesProjectiveObjects] [F.PreservesHomology]
    {X Y Z : C} {P : ProjectiveResolution X} {Q : ProjectiveResolution Y}
    {S : ProjectiveResolution Z} {f : X ⟶ Y} {g : Y ⟶ Z}
    (φ : ProjectiveResolution.Hom P Q f)
    (ψ : ProjectiveResolution.Hom Q S g) :
    (F.mapProjectiveResolutionHom (φ.comp ψ)).cast (F.map_comp f g) =
      (F.mapProjectiveResolutionHom φ).comp (F.mapProjectiveResolutionHom ψ) := by
  apply ProjectiveResolution.Hom.ext
  exact (F.mapHomologicalComplex (ComplexShape.down ℕ)).map_comp φ.hom ψ.hom

end CategoryTheory.Functor

end
