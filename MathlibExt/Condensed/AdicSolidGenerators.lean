/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.RingTheory.Ideal.Basic
public import MathlibExt.Condensed.SolidAnalyticModules

/-!
# Actual adic localizations and completed analytic generators

Scalar multiplication is by constant continuous functions on every actual
section module. Localization is the literal sequential colimit of those
endomorphisms on the free profinite modules. Complete objects are detected
by all shifts of all localized profinite generators, not only global
sections of the unit. Completion is characterized by its actual unit and
that fixed derived-Hom test.

The finite-cone/retract hull uses native distinguished triangles in the
actual derived module category. Its DG/Ind enhancement is a separate
normalized model, not an ordinary Ind of this homotopy category.

Anschuetz--Mann, arXiv:2403.01951v2, Definitions2.3-2.4.
Generic localization/reflection theory is source integration; these are
original native topological-coefficient adapters.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.AdicSolidGenerators

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open GeometricScalarRestriction SolidAnalyticModules TopologicalRings

attribute [local instance] HasDerivedCategory.standard

variable (A : Type 1) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Constants viewed in the actual section-ring object. -/
def geometricScalar (a : A) (S : CompHaus.{0}ᵒᵖ) : (ringSheaf A).obj.obj S :=
  constantScalars A A (RingHom.id A) S a

/-- The prescribed scalar endomorphism of an actual geometric module. -/
def scalarEnd (a : A) (M : GeometricModules A) : M ⟶ M := ⟨
  { app S := by
      letI : CommRing ((ringSheaf A).obj.obj S) :=
        inferInstanceAs (CommRing C(S.unop, A))
      exact ConcreteCategory.ofHom
        { toFun x := geometricScalar A a S • x
          map_add' x y := smul_add _ _ _
          map_smul' r x := smul_comm _ _ _ }
    naturality {S T} f := by
      apply ModuleCat.hom_ext
      ext x
      change geometricScalar A a T •
        (M.val.restrictₛₗ f x) =
          M.val.restrictₛₗ f (geometricScalar A a S • x)
      have h := (M.val.restrictₛₗ f).map_smulₛₗ (geometricScalar A a S) x
      change M.val.restrictₛₗ f (geometricScalar A a S • x) =
        geometricScalar A a T • M.val.restrictₛₗ f x at h
      exact h.symm }⟩

/-- Constants commute with every actual module-sheaf morphism. -/
theorem scalarEnd_naturality (a : A) {M N : GeometricModules A} (f : M ⟶ N) :
    scalarEnd A a M ≫ f = f ≫ scalarEnd A a N := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext S
  apply ModuleCat.hom_ext
  ext x
  change (f.val.app S) (geometricScalar A a S • x) =
    geometricScalar A a S • (f.val.app S) x
  exact (f.val.app S).hom.map_smul _ _

/-- Actual localization of the given sheaf module at the specified scalar. -/
def localization (a : A) (M : GeometricModules A) : GeometricModules A :=
  colimit (Functor.ofSequence (X := fun _ : ℕ ↦ M)
    (fun _ ↦ scalarEnd A a M))

/-- The actual localized measuring object for each profinite test. -/
def localizedFree (a : A) (S : Profinite.{0}) : GeometricDerived A :=
  (DerivedCategory.singleFunctor (GeometricModules A) 0).obj
    (localization A a (freeProfinite A S))

/-- All local measuring objects detect genuine internal a-completeness. -/
def IsCompleteAt (K : GeometricDerived A) (a : A) : Prop :=
  ∀ (S : Profinite.{0}) (n : ℤ) (f : (localizedFree A a S)⟦n⟧ ⟶ K), f = 0

/-- Actual derived ideal-completeness, with every generator tested. -/
def IsComplete (I : Ideal A) (K : GeometricDerived A) : Prop :=
  ∀ a ∈ I, IsCompleteAt A K a

/-- The unit-normalized reflector onto these actual complete objects. -/
structure CompletionModel (I : Ideal A) where
  functor : GeometricDerived A ⥤ GeometricDerived A
  unit : 𝟭 (GeometricDerived A) ⟶ functor
  complete : ∀ K, IsComplete A I (functor.obj K)
  universal : ∀ (K L : GeometricDerived A), IsComplete A I L →
    Function.Bijective (fun f : functor.obj K ⟶ L ↦ unit.app K ≫ f)

/-- The exact completed analytic measuring generator of Definition2.4. -/
def completedGenerator (S : Subring A) (E : RestrictionInput A S)
    (L : AnalyticReflection A S E) (I : Ideal A) (C : CompletionModel A I)
    (T : Profinite.{0}) : GeometricDerived A :=
  C.functor.obj (analyticGenerator A S E L T)

/-- The genuine finite stable/retract closure of the displayed generators. -/
def FiniteHull (G : Profinite.{0} → GeometricDerived A)
    (K : GeometricDerived A) : Prop :=
  ∀ P : GeometricDerived A → Prop,
    (∀ T, P (G T)) →
    (∀ Z, IsZero Z → P Z) →
    (∀ (X : GeometricDerived A) (n : ℤ), P X → P (X⟦n⟧)) →
    (∀ T : Triangle (GeometricDerived A), T ∈ distTriang (GeometricDerived A) →
      P T.obj₁ → P T.obj₂ → P T.obj₃) →
    (∀ X Y (i : X ⟶ Y) (r : Y ⟶ X), i ≫ r = 𝟙 X → P Y → P X) → P K

end MathlibExt.Condensed.AdicSolidGenerators
