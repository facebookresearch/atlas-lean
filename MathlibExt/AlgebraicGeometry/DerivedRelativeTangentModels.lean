/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
public import MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
public import MathlibExt.CategoryTheory.DGModuleConeShiftModels
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone

/-!
# Actual dual tangent differentials and relative tangent fibres

The tangent differential is the completed native dual mate of the
normalized cotangent differential. The relative tangent is represented
by the actual module cone shifted by -1. Its inclusion and canonical
degree-minus-one nullhomotopy are fixed on every representable Hom
complex by the native mapping-cocone projections.

The induced isotropic arrow is the actual difference i·h-c·b of the
isotropic homotopy and canonical fibre homotopy. Closure follows from
the native graded Leibniz rule. Neither a shifted equivalence nor an
intersection nondegeneracy conclusion is included in the fibre model.

Reference: PTVV1111.3209v4 Definitions 2.7--2.8, pp.38--39.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open CochainComplex.HomComplex

universe u
variable {k : Type u} [CommRing k]
    {N : MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle.ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {X : Prestack k} {G : QCohEnhancement M U X} (H : CoherentMonoidalEnhancement G)

/-- The completed dual mate for these actual perfect pairings. -/
def dualDifferential {LX LY : G.category} (d : DGHom (LargeScalar k) 0 LY LX)
    (hd : d ∈ dgCycles (LargeScalar k) LY LX)
    (DX : PerfectDual H.monoidal LX) (DY : PerfectDual H.monoidal LY) :
    (ForgetEnrichment.of _ DX.object : Closed G) ⟶ ForgetEnrichment.of _ DY.object := by
  letI := H.monoidal.monoidal
  let x : Closed G := ForgetEnrichment.of _ LX
  let y : Closed G := ForgetEnrichment.of _ LY
  let tx : Closed G := ForgetEnrichment.of _ DX.object
  let ty : Closed G := ForgetEnrichment.of _ DY.object
  let a : y ⟶ x := dgClosedHomOf (LargeScalar k) d hd
  let coev : 𝟙_ (Closed G) ⟶ ty ⊗ y :=
    eqToHom H.monoidal.unit_eq ≫ coevaluation H.monoidal DY ≫
      eqToHom (H.monoidal.tensor_obj DY.object LY).symm
  let ev : x ⊗ tx ⟶ 𝟙_ (Closed G) :=
    eqToHom (H.monoidal.tensor_obj LX DX.object) ≫ evaluation H.monoidal DX ≫
      eqToHom H.monoidal.unit_eq.symm
  exact (λ_ tx).inv ≫ (coev ⊗ₘ 𝟙 tx) ≫
    (α_ ty y tx).hom ≫ (𝟙 ty ⊗ₘ (a ⊗ₘ 𝟙 tx)) ≫
    (𝟙 ty ⊗ₘ ev) ≫ (ρ_ ty).hom

/-- The actual tangent differential is this literal closed native mate. -/
def tangentDifferential {LX LY : G.category} (d : DGHom (LargeScalar k) 0 LY LX)
    (hd : d ∈ dgCycles (LargeScalar k) LY LX)
    (DX : PerfectDual H.monoidal LX) (DY : PerfectDual H.monoidal LY) :
    DGHom (LargeScalar k) 0 DX.object DY.object :=
  dgClosedHom (LargeScalar k) (dualDifferential H d hd DX DY)

/-- The fixed closed arrow gives its actual native module Yoneda map. -/
def yonedaArrow {T V : G.category} (a : DGHom (LargeScalar k) 0 T V)
    (ha : a ∈ dgCycles (LargeScalar k) T V) :
    (⟨dgRepresentable (LargeScalar k) T⟩ : RightModule (LargeScalar k) G.category) ⟶
      (⟨dgRepresentable (LargeScalar k) V⟩ : RightModule (LargeScalar k) G.category) :=
  (dgRepresentableNatTransEquiv (LargeScalar k) T V).symm ⟨a, ha⟩

/-- The actual value comparison for cone[-1], using only the native shift isomorphism. -/
def coconeValue {T V : G.category} {a : DGHom (LargeScalar k) 0 T V}
    {ha : a ∈ dgCycles (LargeScalar k) T V} (C : ModuleConeModel (yonedaArrow a ha))
    (S : ModuleShiftModel C.module (-1)) (P : G.categoryᵒᵖ) :
    S.module.toEnrichedFunctor.obj P ≅
      CochainComplex.mappingCocone (moduleComponent (yonedaArrow a ha) P) :=
  S.valueIso P ≪≫ (shiftFunctor (Cochains (LargeScalar k)) (-1)).mapIso (C.valueIso P)

/-- The relative tangent is the full represented actual cone[-1] module.
Both native projection blocks are fixed at every object and every degree. -/
structure RelativeTangent {T V : G.category} (a : DGHom (LargeScalar k) 0 T V)
    (ha : a ∈ dgCycles (LargeScalar k) T V) where
  cone : ModuleConeModel (yonedaArrow a ha)
  shift : ModuleShiftModel cone.module (-1)
  object : G.category
  representation : (⟨dgRepresentable (LargeScalar k) object⟩ : RightModule (LargeScalar k) G.category) ⟶
    shift.module
  weak : ∀ P : G.categoryᵒᵖ, QuasiIso (moduleComponent representation P)
  inclusion : DGHom (LargeScalar k) 0 object T
  inclusion_closed : inclusion ∈ dgCycles (LargeScalar k) object T
  inclusion_value : ∀ (P : G.categoryᵒᵖ),
    moduleComponent (yonedaArrow inclusion inclusion_closed) P =
      moduleComponent representation P ≫ (coconeValue cone shift P).hom ≫
        CochainComplex.mappingCocone.fst (moduleComponent (yonedaArrow a ha) P)
  nullhomotopy : DGHom (LargeScalar k) (-1) object V
  nullhomotopy_value : ∀ (P : G.categoryᵒᵖ),
    dgPostcomp (LargeScalar k) P (-1) nullhomotopy =
      -((Cochain.ofHom (moduleComponent representation P ≫ (coconeValue cone shift P).hom)).comp
        (CochainComplex.mappingCocone.snd (moduleComponent (yonedaArrow a ha) P)) (zero_add (-1)))
  nullhomotopy_d : dgDifferential (LargeScalar k) (-1) nullhomotopy =
    dgComp (LargeScalar k) inclusion a (add_zero 0)

/-- The actual degree n-1 loop/adjoint composite from these two fixed homotopies. -/
def isotropicArrow {T V L : G.category} {a : DGHom (LargeScalar k) 0 T V}
    {ha : a ∈ dgCycles (LargeScalar k) T V} (F : RelativeTangent a ha) (n : ℤ)
    (b : DGHom (LargeScalar k) n V L) (h : DGHom (LargeScalar k) (n - 1) T L) :
    DGHom (LargeScalar k) (n - 1) F.object L :=
  dgComp (LargeScalar k) F.inclusion h (zero_add _) -
    dgComp (LargeScalar k) F.nullhomotopy b (by omega)

/-- Closure uses the isotropic endpoint equation and the native fibre nullhomotopy. -/
theorem isotropicArrow_closed {T V L : G.category} {a : DGHom (LargeScalar k) 0 T V}
    {ha : a ∈ dgCycles (LargeScalar k) T V} (F : RelativeTangent a ha) (n : ℤ)
    (b : DGHom (LargeScalar k) n V L) (hb : dgDifferential (LargeScalar k) n b = 0)
    (h : DGHom (LargeScalar k) (n - 1) T L)
    (hh : dgDifferential (LargeScalar k) (n - 1) h = dgComp (LargeScalar k) a b (by omega)) :
    dgDifferential (LargeScalar k) (n - 1) (isotropicArrow F n b h) = 0 := by
  rw [isotropicArrow, map_sub, dgDifferential_dgComp, dgDifferential_dgComp,
    (mem_dgCycles (LargeScalar k)).mp F.inclusion_closed, F.nullhomotopy_d, hh, hb]
  simp only [zero_dgComp, dgComp_zero, smul_zero, zero_add, Int.negOnePow_zero, one_smul, add_zero]
  rw [dgComp_assoc _ _ _ _ _ _ (by omega)]
  exact sub_self _

/-- Lagrangian nondegeneracy is the actual shifted-equivalence test for this induced arrow. -/
def IsLagrangianArrow {T V L : G.category} {a : DGHom (LargeScalar k) 0 T V}
    {ha : a ∈ dgCycles (LargeScalar k) T V} (F : RelativeTangent a ha) (n : ℤ)
    (b : DGHom (LargeScalar k) n V L) (hb : dgDifferential (LargeScalar k) n b = 0)
    (h : DGHom (LargeScalar k) (n - 1) T L)
    (hh : dgDifferential (LargeScalar k) (n - 1) h = dgComp (LargeScalar k) a b (by omega)) : Prop :=
  IsShiftedEquivalence L F.object (n - 1) (isotropicArrow F n b h)
    (isotropicArrow_closed F n b hb h hh)

end MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels
