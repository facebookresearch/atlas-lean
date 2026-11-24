/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import MathlibExt.CategoryTheory.DGSource.DGCochainCategory
public import MathlibExt.CategoryTheory.DGQuasiFunctorModels
public import MathlibExt.Condensed.AdicSolidGenerators

/-!
# Actual DG models for completed solid analytic modules

Geometric module morphisms are linear over the actual coefficient ring,
via constant continuous scalars. The source enrichment uses the actual
native cochain Hom complex, differential and signed composition. The
compact dictionary maps into actual K-injective cochains, is quasi-fully
faithful on full Hom complexes and covers the exact completed generator
hull. It therefore retains derived mapping data.

Modified modules are the actual cofibrant right DG modules of this small
compact model, rather than ordinary Ind of its H0 category. Almost-local
modules are defined by full DG-Hom orthogonality to actual ideal-annihilated
cohomology on every module component.

Anschuetz--Mann, arXiv:2403.01951v2, Definition2.4/Section4.2.
Completed DG source ports retain TauCeti Apache2.0/revision attribution
in their imported files. The dictionary/provider constructions are explicit;
no v-descent or affine geometric comparison is assumed in their definition.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.GeometricDGModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open GeometricScalarRestriction SolidAnalyticModules AdicSolidGenerators

attribute [local instance] HasDerivedCategory.standard

variable (A : Type 1) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

instance restriction_faithful (R : Type 1) [CommRing R] (φ : R →+* A) :
    (restriction A R φ).Faithful where
  map_injective {M N} f g h := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.Hom.ext
    funext S
    apply (ModuleCat.restrictScalars (constantScalars A R φ S)).map_injective
    exact congrArg (fun q ↦ q.hom.app S) h

/-- The actual coefficient action transported through the faithful scalar restriction. -/
@[instance_reducible] def homModule (M N : GeometricModules A) : Module A (M ⟶ N) := by
  letI : SMul A (M ⟶ N) := ⟨fun a f ↦ f ≫ scalarEnd A a N⟩
  let F := restriction A A (RingHom.id A)
  exact Function.Injective.module A F.mapAddHom F.map_injective (by
    intro a f
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext S
    apply ModuleCat.hom_ext
    ext x
    rfl)

/-- Geometric A-linearity is fixed by the actual sectionwise constant action. -/
instance geometricLinear : Linear A (GeometricModules A) where
  homModule := homModule A
  smul_comp X Y Z a f g := by
    change (f ≫ scalarEnd A a Y) ≫ g = (f ≫ g) ≫ scalarEnd A a Z
    rw [Category.assoc, scalarEnd_naturality, ← Category.assoc]
  comp_smul X Y Z f a g := by
    change f ≫ (g ≫ scalarEnd A a Z) = (f ≫ g) ≫ scalarEnd A a Z
    exact (Category.assoc _ _ _).symm

/-- Native K-injective cochains retain their full source linear-Hom enrichment. -/
abbrev InjectiveCochains := DGFullSubcategory
  (fun K : CochainComplex (GeometricModules A) ℤ ↦ K.IsKInjective)

/-- A genuinely small DG dictionary for the actual completed generator hull. -/
structure CompactDGModel (G : Profinite.{0} → GeometricDerived A) where
  objects : Type 1
  [category : DGCategory A objects]
  realization : EnrichedFunctor (CochainComplex (ModuleCat.{1} A) ℤ)
    objects (InjectiveCochains A)
  quasi_fully_faithful : ∀ (X Y : objects), QuasiIso (realization.map X Y)
  image : ∀ X : objects,
    FiniteHull A G (DerivedCategory.Q.obj (realization.obj X).obj)
  covers : ∀ K : GeometricDerived A, FiniteHull A G K →
    ∃ X : objects, Nonempty (DerivedCategory.Q.obj (realization.obj X).obj ≅ K)

attribute [instance] CompactDGModel.category

/-- The actual DG module realization of the modified category. -/
abbrev ModifiedModules {G : Profinite.{0} → GeometricDerived A}
    (M : CompactDGModel A G) := DGDerivedModules A M.objects

/-- Almost zero means the actual ideal kills every component cohomology module. -/
def AlmostZero {C : Type 1} [DGCategory A C]
    (I : Ideal A) (M : RightModule A C) : Prop :=
  ∀ (x : Cᵒᵖ) (n : ℤ) (a : A), a ∈ I →
    ∀ z : ((HomologicalComplex.homologyFunctor (ModuleCat.{1} A)
      (ComplexShape.up ℤ) n).obj (M.toEnrichedFunctor.obj x)), a • z = 0

/-- Full DG-Hom orthogonality to the actual almost-zero cofibrant modules. -/
def IsAlmostLocal {C : Type 1} [DGCategory A C]
    (I : Ideal A) (M : RightModule A C) : Prop :=
  ∀ N : RightModule A C, IsCofibrantModule N → AlmostZero A I N →
    ∀ n : ℤ, IsZero
      ((HomologicalComplex.homologyFunctor (ModuleCat.{1} A)
        (ComplexShape.up ℤ) n).obj (dgHomComplex A N M))

/-- The full DG model of modified almost modules, with genuine mapping complexes. -/
abbrev AlmostModifiedModules {G : Profinite.{0} → GeometricDerived A}
    (M : CompactDGModel A G) (I : Ideal A) :=
  DGFullSubcategory (fun K : RightModule A M.objects ↦
    IsCofibrantModule K ∧ IsAlmostLocal A I K)

/-- An almost localization of the modified modules: an `A`-linear DG functor onto cofibrant
almost-local modules, with a unit at every module which is a closed module map, DG-natural, and
whose cone is almost zero on every component. Hence the value at `X` is the almost localization of
`X` (Mann, Lemma 2.2.22): almost-local and receiving an almost isomorphism from `X`, so that
precomposition with the unit identifies maps into almost-local modules. -/
structure AlmostLocalization {G : Profinite.{0} → GeometricDerived A}
    (M : CompactDGModel A G) (I : Ideal A) where
  /-- The localization functor. -/
  functor : EnrichedFunctor (CochainComplex (ModuleCat.{1} A) ℤ)
    (ModifiedModules A M) (AlmostModifiedModules A M I)
  /-- The unit `X → L X`, a closed module map. -/
  unit : ∀ X : ModifiedModules A M, X.obj ⟶ (functor.obj X).obj
  /-- The unit is natural for homogeneous maps of every degree. -/
  unit_natural : ∀ (X Y : ModifiedModules A M) (n : ℤ) (a : DGHom A n X Y),
    dgComp A (C := RightModule A M.objects) (X := X.obj) (Y := (functor.obj X).obj)
        (Z := (functor.obj Y).obj)
        ((DGFunctor.homEquivDGCycles A X.obj (functor.obj X).obj (unit X)).val)
        (functor.dgMap n a) (zero_add n) =
      dgComp A (C := RightModule A M.objects) (X := X.obj) (Y := Y.obj)
        (Z := (functor.obj Y).obj) a
        ((DGFunctor.homEquivDGCycles A Y.obj (functor.obj Y).obj (unit Y)).val) (add_zero n)
  /-- The cone of the unit is almost zero on every component. -/
  almost_cone : ∀ (X : ModifiedModules A M) (x : M.objectsᵒᵖ) (n : ℤ) (a : A), a ∈ I →
    ∀ z : ((HomologicalComplex.homologyFunctor (ModuleCat.{1} A) (ComplexShape.up ℤ) n).obj
      (CochainComplex.mappingCone (moduleComponent (unit X) x))), a • z = 0

end MathlibExt.Condensed.GeometricDGModules
