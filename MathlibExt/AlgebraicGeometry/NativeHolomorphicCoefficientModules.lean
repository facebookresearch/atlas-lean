/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.HolomorphicCotangentModuleModels
public import MathlibExt.AlgebraicGeometry.HolomorphicCoefficientRestriction
public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
public import MathlibExt.AlgebraicGeometry.GeometricDModuleFiltrations
public import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Original holomorphic O-module coefficients and top-form regular-D tensor

Scalar restriction and coefficient forgetting are the native functors
along the actual holomorphic constants. The top-form transfer carrier
is the actual native Omega tensor of the scalar-restricted regular D
module, with every pure section given by the native sheafification unit.
Source: DK1311.2374v2 Sections2.5,8.2; Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeHolomorphicCoefficientModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts HarmonicHolomorphicModuleModels
open HolomorphicCotangentModuleModels DifferentialOperatorScalars
open scoped Manifold ContDiff

variable (n : ℕ) (M : Type) [TopologicalSpace M]
  [ChartedSpace (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [IsManifold 𝓘(ℂ, TemperedDistributionSectionModels.ComplexCoordinates n) ∞ M]
  [HolomorphicCoefficientSheaves.SheafCondition
    (TemperedDistributionSectionModels.ComplexCoordinates n) M]
  [CotangentSectionCalculus (n := n) (M := M)] [CotangentSheafCondition (n := n) (M := M)]
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]

abbrev HolomorphicRing := holomorphicStructureRing (n := n) (M := M)

/-- The shared holomorphic coefficient map (`HolomorphicCoefficientRestriction`). -/
abbrev holomorphicCoefficientMap : HolomorphicRing n M ⟶
    coefficientSheaf ℂ M (analyticCoefficients n M) :=
  HolomorphicCoefficientRestriction.holomorphicCoefficientMap n M

/-- The shared restriction of a D-module to the holomorphic functions. -/
abbrev ordinaryHolomorphicCoefficients
    (N : DifferentialOperatorSheaves.DModule ℂ M (analyticCoefficients n M)) :
    SheafOfModules.{0} (HolomorphicRing n M) :=
  HolomorphicCoefficientRestriction.holomorphicRestriction n M N

def fullOpenInitial : IsInitial (op (⊤ : Opens M)) :=
  IsInitial.ofUniqueHom (fun U => (homOfLE (show U.unop ≤ ⊤ from le_top)).op)
    (fun _ _ => Subsingleton.elim _ _)

def holomorphicConstantRingMap : ℂ →+* (HolomorphicRing n M).obj.obj (op ⊤) :=
  algebraMap ℂ (HolomorphicCoefficientSheaves.holomorphicAlgebra
    (TemperedDistributionSectionModels.ComplexCoordinates n) M ⊤)

def rawComplexCoefficients : SheafOfModules.{0} (HolomorphicRing n M) ⥤
    OrdinarySheaf ℂ (TopCat.of M) :=
  SheafOfModules.forgetToSheafModuleCat (HolomorphicRing n M) (op ⊤) (fullOpenInitial M) ⋙
    sheafCompose (Opens.grothendieckTopology M)
      (ModuleCat.restrictScalars (holomorphicConstantRingMap n M))

def omegaRegularTensor : SheafOfModules.{0} (HolomorphicRing n M) :=
  holomorphicTensor (holomorphicOmega (n := n) (M := M) n)
    (ordinaryHolomorphicCoefficients n M (SheafOfModules.unit (analyticDifferentialRing n M)))

def omegaRegularSection (U : Opens M)
    (form : (holomorphicOmega (n := n) (M := M) n).val.obj (op U))
    (P : DifferentialOperatorSheaves.finiteOperatorRing ℂ M (analyticCoefficients n M) U) :
    ((rawComplexCoefficients n M).obj (omegaRegularTensor n M)).presheaf.obj (op U) :=
  holomorphicTensorSection (holomorphicOmega (n := n) (M := M) n)
    (ordinaryHolomorphicCoefficients n M (SheafOfModules.unit (analyticDifferentialRing n M))) U form
      (GeometricDModuleFiltrations.operatorValue
        (TemperedDistributionSectionModels.ComplexCoordinates n) M P)

end MathlibExt.AlgebraicGeometry.NativeHolomorphicCoefficientModules
