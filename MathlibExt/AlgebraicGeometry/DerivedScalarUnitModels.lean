/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalSectionBaseChange

/-!
# Native scalar units and actual cochain modules

The scalar DG category is the literal one-object algebra of the native
cochain tensor unit. An object-selector functor is fixed by the actual
enriched identity map. A cochain's scalar module is the restricted
representable Hom from that unit, and its value comparison evaluates
the actual homogeneous cochain on the native unit element one.

These source-normalized scalar models give the precise k-linear trace
domain needed for orientations; no unrelated vector space is chosen.
Generic selectors/comparison assembly are separate construction inputs.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGAlgebraCategoryModels
open MathlibExt.Algebra.Homology.DGCyclicBarModels
open CochainComplex.HomComplex

universe u v
variable {R : Type u} [CommRing R]

/-- The actual scalar DG algebra is the native cochain tensor-unit monoid. -/
def scalarAlgebra (R : Type u) [CommRing R] : DGAlgebra R := Mon.mk (𝟙_ (Cochains R))

/-- The actual one-object scalar DG category. -/
def scalarCategory (R : Type u) [CommRing R] : DGCat R := algebraCategory (scalarAlgebra R)

/-- A unit selector fixes the object and the entire enriched scalar identity map. -/
structure UnitFunctorModel (C : Type v) [DGCategory R C] (o : C) where
  functor : EnrichedFunctor (Cochains R) (scalarCategory R) C
  object_eq : ∀ x : scalarCategory R, functor.obj x = o
  map_eq : ∀ x y : scalarCategory R, HEq (functor.map x y) (eId (Cochains R) o)

/-- The genuine scalar module of a cochain complex, using its restricted representable. -/
def cochainModule (U : UnitFunctorModel (R := R) (Cochains R) (𝟙_ (Cochains R)))
    (K : Cochains R) : RightModule R (scalarCategory R) :=
  ⟨U.functor.op.comp (Cochains R) (dgRepresentable R K)⟩

/-- Its value is exactly native Hom from the cochain tensor unit. -/
def unitHomIso (U : UnitFunctorModel (R := R) (Cochains R) (𝟙_ (Cochains R)))
    (K : Cochains R) :
    ((cochainModule U K).toEnrichedFunctor.obj (op PUnit.unit)) ≅
      dgHomComplex R (𝟙_ (Cochains R)) K :=
  eqToIso (by dsimp only [cochainModule, EnrichedFunctor.comp, EnrichedFunctor.op]; rw [U.object_eq]; rfl)

/-- A unit-Hom comparison is fixed on every homogeneous cochain by evaluation on one. -/
structure UnitEvaluationModel (K : Cochains R) where
  comparison : dgHomComplex R (𝟙_ (Cochains R)) K ≅ K
  normalized : ∀ (n : ℤ) (f : Cochain (𝟙_ (Cochains R)) K n),
    (comparison.hom.f n).hom f =
      (f.v 0 n (zero_add n)).hom
        ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat.{u} R))).inv 1)

/-- The scalar-module value is compared with the same actual cochain complex. -/
def cochainValueIso (U : UnitFunctorModel (R := R) (Cochains R) (𝟙_ (Cochains R)))
    (K : Cochains R) (E : UnitEvaluationModel K) :
    (cochainModule U K).toEnrichedFunctor.obj (op PUnit.unit) ≅ K :=
  unitHomIso U K ≪≫ E.comparison

end MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
