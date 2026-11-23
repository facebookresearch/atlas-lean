/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-!
# Actual enriched global-section base-change comparisons

The raw RΓ map is the actual global DG pullback with its fixed
structure unit. The scalar-extension comparison is its transpose
under the previously normalized all-degree enriched adjunction.
Both module replacements retain their actual augmentation, and
every source homogeneous component is fixed. A basis permutation
or a freely named cohomology comparison cannot satisfy the contract.

O-compactness supplies the required quasi-isomorphism for perfect E
through a separate theorem/construction request. This module does
not provide that theorem by a model hypothesis.
Reference: PTVV arXiv:1111.3209v4, §2.1, Definition 2.1 and the
global-section projection/base-change argument on pp.30--33.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} {M : AffineModuleFibration N S}
    {U : RegularUnitSystem M} {Q : AlgebraReplacementFunctor k} {L : CochainLiftModel k}
    {V : NerveLiftModel L} {X : Prestack k}

/-- A closed homogeneous module map is converted by the native DG natural-transformation equivalence. -/
def closedModuleMap {R : Type u} [CommRing R] {C : DGCat R} {P Z : RightModule R C}
    (f : DGHom R 0 P Z) (h : dgDifferential R 0 f = 0) : P ⟶ Z :=
  (DGFunctor.homEquivDGCycles R P Z).symm ⟨f, (mem_dgCycles R).mpr h⟩

/-- Restriction retains exactly the actual target coefficient-module value. -/
def restrictionValueIso {A A' : SAlg k} {f : A ⟶ A'}
    (R : RestrictionModel (coefficientLargeMap L N f))
    (Z : RightModule (LargeScalar k) (coefficientLarge L N A')) :
    value (coefficientLarge L N A) (coefficientObject L N A) (R.functor.obj Z) ≅
      value (coefficientLarge L N A') (coefficientObject L N A') Z :=
  eqToIso (by rw [R.object_eq]; rfl)

/-- A displayed target equality transports the same actual source pullback map. -/
def gammaTargetBaseChange (B : FamilyModel M U Q L V X) {A A' : SAlg k} (f : A ⟶ A')
    (E : (B.model A).category) (E' : (B.model A').category)
    (h : (B.pullback A A' f).obj E = E') :
    value (coefficientLarge L N A) (coefficientObject L N A) (gamma B A E) ⟶
      value (coefficientLarge L N A') (coefficientObject L N A') (gamma B A' E') :=
  (gammaValueIso B A E).hom ≫ globalHomBaseChange B f E ≫
    eqToHom (congrArg (globalHom (B.model A')) h) ≫ (gammaValueIso B A' E').inv

/-- The base-change arrow is normalized by the actual enriched adjunction and both augmentations. -/
structure GlobalBaseChangeModel (B : FamilyModel M U Q L V X)
    {A A' : SAlg k} (f : A ⟶ A') (E : (B.model A).category)
    (E' : (B.model A').category) (h : (B.pullback A A' f).obj E = E')
    (P : ModuleReplacement (gamma B A E))
    (Z : ModuleReplacement (gamma B A' E'))
    (R : RestrictionModel (coefficientLargeMap L N f))
    (D : ExtensionModel (coefficientLargeMap L N f) R) where
  unit : DGHom (LargeScalar k) 0 P.module
    (R.functor.obj (gamma B A' E'))
  unit_closed : dgDifferential (LargeScalar k) 0 unit = 0
  unit_normalized : ∀ (n : ℤ)
    (m : (value (coefficientLarge L N A) (coefficientObject L N A) P.module).X n),
    ((restrictionValueIso R _).hom.f n).hom
      (mapValue (coefficientLarge L N A) (coefficientObject L N A) unit (add_zero n) m) =
    ((gammaTargetBaseChange B f E E' h).f n).hom
      (((moduleComponent P.augmentation (op (coefficientObject L N A))).f n).hom m)
  map : DGHom (LargeScalar k) 0
    (D.functor.obj (⟨P.module, P.cofibrant⟩ : DGDerivedModules (LargeScalar k)
      (coefficientLarge L N A))).obj Z.module
  closed : dgDifferential (LargeScalar k) 0 map = 0
  normalized : ((D.homIso ⟨P.module, P.cofibrant⟩
      (gamma B A' E')).hom.f 0).hom
    (dgComp (LargeScalar k) map
      ((DGFunctor.homEquivDGCycles (LargeScalar k) Z.module
        (gamma B A' E')) Z.augmentation).val (by omega)) = unit

/-- Source base-change validity concerns this exact module map, not an assumed result field. -/
def IsBaseChangeQuasiIso {B : FamilyModel M U Q L V X} {A A' : SAlg k} {f : A ⟶ A'}
    {E : (B.model A).category} {E' : (B.model A').category}
    {h : (B.pullback A A' f).obj E = E'} {P : ModuleReplacement (gamma B A E)}
    {Z : ModuleReplacement (gamma B A' E')}
    {R : RestrictionModel (coefficientLargeMap L N f)}
    {D : ExtensionModel (coefficientLargeMap L N f) R}
    (G : GlobalBaseChangeModel B f E E' h P Z R D) : Prop :=
  QuasiIso (moduleComponent (closedModuleMap G.map G.closed) (op (coefficientObject L N A')))

/-- Generic restriction evaluates at the displayed actual coefficient object. -/
def restrictionPointValueIso {R₀ : Type u} [CommRing R₀]
    {C D₀ : DGCat R₀} {c : C} {d : D₀} (f : C ⟶ D₀) (hc : f.obj c = d)
    (R : RestrictionModel f) (Z : RightModule R₀ D₀) :
    value C c (R.functor.obj Z) ≅ value D₀ d Z :=
  eqToIso (by rw [R.object_eq]; dsimp only [restrictModule, value, EnrichedFunctor.comp,
    EnrichedFunctor.op]; rw [hc])

/-- Generic enriched scalar extension is fixed by a displayed actual source cochain map. -/
structure EnrichedModuleBaseChangeModel {R₀ : Type u} [CommRing R₀]
    (C D₀ : DGCat R₀) (c : C) (d : D₀) (f : C ⟶ D₀)
    (hc : f.obj c = d) {P₀ : RightModule R₀ C} {Z₀ : RightModule R₀ D₀}
    (P : ModuleReplacement P₀) (Z : ModuleReplacement Z₀)
    (R : RestrictionModel f) (D : ExtensionModel f R)
    (g : value C c P₀ ⟶ value D₀ d Z₀) where
  unit : DGHom R₀ 0 P.module (R.functor.obj Z₀)
  unit_closed : dgDifferential R₀ 0 unit = 0
  unit_normalized : ∀ (n : ℤ) (m : (value C c P.module).X n),
    ((restrictionPointValueIso f hc R Z₀).hom.f n).hom
      (mapValue C c unit (add_zero n) m) =
    (g.f n).hom (((moduleComponent P.augmentation (op c)).f n).hom m)
  map : DGHom R₀ 0 (D.functor.obj (⟨P.module, P.cofibrant⟩ : DGDerivedModules R₀ C)).obj Z.module
  closed : dgDifferential R₀ 0 map = 0
  normalized : ((D.homIso ⟨P.module, P.cofibrant⟩ Z₀).hom.f 0).hom
      (dgComp R₀ map ((DGFunctor.homEquivDGCycles R₀ Z.module Z₀) Z.augmentation).val (by omega)) = unit

/-- Quasi-isomorphism concerns this exact normalized map on actual coefficient-module values. -/
def IsEnrichedBaseChangeQuasiIso {R₀ : Type u} [CommRing R₀]
    {C D₀ : DGCat R₀} {c : C} {d : D₀} {f : C ⟶ D₀} {hc : f.obj c = d}
    {P₀ : RightModule R₀ C} {Z₀ : RightModule R₀ D₀}
    {P : ModuleReplacement P₀} {Z : ModuleReplacement Z₀}
    {R : RestrictionModel f} {D : ExtensionModel f R} {g : value C c P₀ ⟶ value D₀ d Z₀}
    (B : EnrichedModuleBaseChangeModel C D₀ c d f hc P Z R D g) : Prop :=
  QuasiIso (moduleComponent (closedModuleMap B.map B.closed) (op d))

end MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange
