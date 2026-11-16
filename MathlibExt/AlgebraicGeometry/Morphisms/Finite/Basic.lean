/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/AlgebraicGeometry/Morphisms/Finite/Basic.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Flat.EquationalCriterion

/-!
# Sections of finite morphisms

For a finite morphism `f : X ⟶ Spec R`, the global sections `Γ(X, ⊤)` form a finite
`R`-module. `AlgebraicGeometry.Scheme.Hom.moduleFinite_appTop` states this for an existing
`R`-algebra structure compatible with the map of global sections. It transports Mathlib's
`Scheme.Hom.finite_appTop` across the canonical isomorphism `R ≅ Γ(Spec R, ⊤)`.

This finiteness is used to compute the rank of a finite morphism over a field as the dimension
of its global sections.

If `g : Y ⟶ S` is moreover flat and locally of finite presentation (finite locally free), its
sections `Γ(Y, g⁻¹ U)` over an affine open `U` of `S` form a projective `Γ(S, U)`-module
(`AlgebraicGeometry.Scheme.Hom.projective_app`).

Finite, flat, locally finite type and locally finitely presented morphisms each respect
isomorphisms (`MathlibExt.isFinite_respectsIso`, `MathlibExt.flat_respectsIso`,
`MathlibExt.locallyOfFiniteType_respectsIso` and
`MathlibExt.locallyOfFinitePresentation_respectsIso`).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- A finite morphism to the spectrum of a commutative ring has module-finite global sections,
for any `R`-algebra structure on `Γ(X, ⊤)` given by the map of global sections. -/
theorem Scheme.Hom.moduleFinite_appTop {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of R)) [IsFinite f] [Algebra R Γ(X, ⊤)]
    (hf : algebraMap R Γ(X, ⊤) = ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appTop).hom) :
    Module.Finite R Γ(X, ⊤) := by
  rw [← RingHom.finite_algebraMap, hf]
  exact (RingHom.finite_respectsIso.cancel_left_isIso _ _).mpr f.finite_appTop

/-- The sections of a finite, flat, locally finitely presented morphism `g : Y ⟶ S` over an affine
open `U` of `S` form a projective module over `Γ(S, U)`. -/
theorem Scheme.Hom.projective_app {Y S : Scheme.{u}} (g : Y ⟶ S) [IsFinite g] [Flat g]
    [LocallyOfFinitePresentation g] (U : S.affineOpens) :
    letI := (g.app U).hom.toAlgebra
    Module.Projective Γ(S, U) Γ(Y, g ⁻¹ᵁ U) := by
  have hflat := g.flat_appLE U.2 (U.2.preimage g) le_rfl
  have hfp := g.finitePresentation_appLE U.2 (U.2.preimage g) le_rfl
  rw [Scheme.Hom.appLE_eq_app] at hflat hfp
  have hfin := g.finite_app U U.2
  algebraize [(g.app U).hom]
  have := Module.FinitePresentation.of_finite_of_finitePresentation (R := Γ(S, U))
    (S := Γ(Y, g ⁻¹ᵁ U))
  exact Module.Flat.projective_of_finitePresentation

end AlgebraicGeometry

namespace MathlibExt

open AlgebraicGeometry

universe u

/-- Finite morphisms of schemes respect isomorphisms. -/
instance isFinite_respectsIso :
    MorphismProperty.RespectsIso (@IsFinite : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

/-- Flat morphisms of schemes respect isomorphisms. -/
instance flat_respectsIso :
    MorphismProperty.RespectsIso (@Flat : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

/-- Morphisms of schemes locally of finite type respect isomorphisms. -/
instance locallyOfFiniteType_respectsIso :
    MorphismProperty.RespectsIso (@LocallyOfFiniteType : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

/-- Morphisms of schemes locally of finite presentation respect isomorphisms. -/
instance locallyOfFinitePresentation_respectsIso :
    MorphismProperty.RespectsIso
      (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
  MorphismProperty.respectsIso_of_isStableUnderComposition
    (fun _ _ f (_ : IsIso f) ↦ inferInstance)

end MathlibExt
