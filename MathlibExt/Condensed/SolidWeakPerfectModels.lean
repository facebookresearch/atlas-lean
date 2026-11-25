/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Condensed.SolidTorsionFrobeniusModels
public import MathlibExt.CategoryTheory.DGScalarExtensionModels
public import MathlibExt.CategoryTheory.DGAlgebraCategoryModels

/-!
# Actual discrete-unit induction and weakly almost perfect coefficients

The ordinary coefficient algebra is the actual endomorphism algebra of
the degree-zero scalar complex. It has one coefficient object. Induction
into the solid compact dictionary is fixed on that actual scalar unit
and every scalar endomorphism, with the native full DG Hom adjunction.

Weakly almost perfect means an epsilon-retract of an almost-localized
perfect discrete coefficient module, for every epsilon in the actual
almost ideal. Finite cells are used only in the one-object ordinary
coefficient category; arbitrary profinite measuring objects are not
classified as perfect by this definition.

Sources: Mann, arXiv:2206.02022v1, Definitions 3.7.1(c), 3.7.6(b)
and 3.9.15; Proposition 3.7.5. This supplies the source perfect-object
language without assuming completion of a solid monoidal provider.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace MathlibExt.Condensed.SolidWeakPerfectModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.CategoryTheory.DGScalarExtensionModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicGeometry.AffineUntiltingGeometry
open LocalSolidCoefficientModels SolidTorsionFrobeniusModels
open GeometricScalarRestriction SolidAnalyticModules
open CochainComplex.HomComplex

attribute [local instance] HasDerivedCategory.standard

/-- The actual ordinary degree-zero coefficient complex. -/
abbrev scalarComplex (R : Type 1) [CommRing R] :=
  (CochainComplex.singleFunctor (ModuleCat.{1} R) 0).obj (ModuleCat.of R R)

/-- The actual one-object ordinary coefficient DG category, on the native scalar unit monoid. -/
def discreteCoefficientCategory (R : Type 1) [CommRing R] : DGCat R :=
  algebraCategory (Mon.trivial (Cochains R))

/-- The actual scalar endomorphism of the coefficient object. -/
def scalarEnd (R : Type 1) [CommRing R] (a : R) :
    DGHom (C := discreteCoefficientCategory R) R 0 PUnit.unit PUnit.unit :=
by
  change (𝟙_ (Cochains R)).X 0
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
    (𝟙_ (ModuleCat.{1} R))).inv a

variable (p : ℕ) [Fact p.Prime] (P : AffineUntilting p)
  (π : Pseudouniformizer p P) (M : TorsionModel p P π)

/-- Scalar-unit induction into an actual DG category,
with the complete native adjunction. -/
structure UnitInductionData (R : Type 1) [CommRing R] (C : DGCat R) where
  unit : C
  functor : discreteCoefficientCategory R ⟶ C
  object_eq : ∀ x, functor.obj x = unit
  scalars : ∀ a : R, HEq (functor.dgMap 0 (scalarEnd R a)) (a • dgId R unit)
  restriction : MathlibExt.CategoryTheory.DGScalarExtensionModels.RestrictionModel
    (C := discreteCoefficientCategory R) (D := C) functor
  extension : MathlibExt.CategoryTheory.DGScalarExtensionModels.ExtensionModel
    (C := discreteCoefficientCategory R) (D := C) functor restriction

/-- The raw source unit-induction data on the actual compact dictionary. -/
abbrev UnitData := UnitInductionData (TorsionRing p P π)
  (DGCat.of (TorsionRing p P π) M.compact.objects)

/-- Geometric unit normalization uses the actual compact realization
and geometric coefficient unit. -/
def IsGeometricUnit (U : UnitData p P π M) : Prop :=
  Nonempty (DerivedCategory.Q.obj (torsionComplex p P π M U.unit) ≅
    unitObject (TorsionRing p P π))

/-- The actual ordinary-coefficient unit is locked to its native geometric realization. -/
abbrev UnitInductionModel := {U : UnitData p P π M // IsGeometricUnit p P π M U}

/-- Induction is the native actual module extension from the one coefficient object. -/
def UnitInductionModel.induce (U : UnitInductionModel p P π M)
    (T : DGDerivedModules (TorsionRing p P π)
      (discreteCoefficientCategory (TorsionRing p P π))) :
    DGDerivedModules (TorsionRing p P π) M.compact.objects := U.val.extension.functor.obj T

/-- Almost equivalence is tested on all actual component mapping cones and homology modules. -/
def IsAlmostEquivalence {X Y : RightModule (TorsionRing p P π) M.compact.objects}
    (f : X ⟶ Y) : Prop :=
  ∀ (x : M.compact.objectsᵒᵖ) (n : ℤ) (a : TorsionRing p P π),
    a ∈ torsionAlmostIdeal p P π M.almost →
    ∀ z : ((HomologicalComplex.homologyFunctor (ModuleCat.{1} (TorsionRing p P π))
      (ComplexShape.up ℤ) n).obj (CochainComplex.mappingCone (moduleComponent f x))), a • z = 0

/-- The actual source weakly almost perfect condition, with every epsilon retained. -/
def IsWeaklyAlmostPerfect (U : UnitInductionModel p P π M)
    (X : TorsionCategory p P π M) : Prop :=
  ∀ a : TorsionRing p P π, a ∈ torsionAlmostIdeal p P π M.almost →
    ∃ T : DGDerivedModules (TorsionRing p P π)
      (discreteCoefficientCategory (TorsionRing p P π)),
      IsPerfectModule (discreteCoefficientCategory (TorsionRing p P π)) T.obj ∧
      ∃ (Y : TorsionCategory p P π M)
        (e : (U.induce p P π M T).obj ⟶ Y.obj), IsAlmostEquivalence p P π M e ∧
        ∃ (i : DGHom (TorsionRing p P π) 0 X Y) (r : DGHom (TorsionRing p P π) 0 Y X),
          dgDifferential (TorsionRing p P π) 0 i = 0 ∧
          dgDifferential (TorsionRing p P π) 0 r = 0 ∧
          dgComp (TorsionRing p P π) i r (by omega) - a • dgId (TorsionRing p P π) X ∈
            dgBoundaries (TorsionRing p P π) X X

end MathlibExt.Condensed.SolidWeakPerfectModels
