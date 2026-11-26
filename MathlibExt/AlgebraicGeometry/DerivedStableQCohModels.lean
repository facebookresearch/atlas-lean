/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels

/-!
# Native DG stability for a full QCoh enhancement

The coherent nerve by itself sees nonpositive Hom complexes. Actual
shift and cone representability in the DG Yoneda module category ties
every positive Hom degree to the same stable category. These contracts
use the fixed native cochain/module shift and cone, with all homogeneous
actions retained. Arbitrary raw categorical enhancements are not
asserted to admit these extra source comparisons.

References: Keller, Deriving DG categories, §2; PTVV1111.3209v4 conventions.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedStableQCohModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels

universe u
variable {k : Type u} [CommRing k]
    {N : MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle.ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {X : Prestack k} (G : QCohEnhancement M U X)

/-- A native DG shift is represented in the actual full Yoneda module category. -/
structure RepresentedShift (V : G.category) (n : ℤ) where
  shift : ModuleShiftModel (⟨dgRepresentable (LargeScalar k) V⟩ : RightModule (LargeScalar k) G.category) n
  object : G.category
  representation : (⟨dgRepresentable (LargeScalar k) object⟩ : RightModule (LargeScalar k) G.category) ⟶
    shift.module
  weak : ∀ P : G.categoryᵒᵖ, QuasiIso (moduleComponent representation P)

/-- A native DG cone is represented, with all module action and cone block normalizations. -/
structure RepresentedCone {V W : G.category} (a : DGHom (LargeScalar k) 0 V W)
    (ha : a ∈ dgCycles (LargeScalar k) V W) where
  cone : ModuleConeModel (yonedaArrow a ha)
  object : G.category
  representation : (⟨dgRepresentable (LargeScalar k) object⟩ : RightModule (LargeScalar k) G.category) ⟶
    cone.module
  weak : ∀ P : G.categoryᵒᵖ, QuasiIso (moduleComponent representation P)

/-- Genuine pretriangulated closure of the same native DG enhancement. -/
structure StableQCohModel where
  zero : G.category
  zero_hom : ∀ P : G.category, IsZero (dgHomComplex (LargeScalar k) P zero)
  shift : ∀ (V : G.category) (n : ℤ), RepresentedShift G V n
  cone : ∀ (V W : G.category) (a : DGHom (LargeScalar k) 0 V W)
    (ha : a ∈ dgCycles (LargeScalar k) V W), RepresentedCone G a ha

end MathlibExt.AlgebraicGeometry.DerivedStableQCohModels
