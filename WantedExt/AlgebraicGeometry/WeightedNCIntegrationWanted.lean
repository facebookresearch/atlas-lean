/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.WeightedNCIntegration
public import MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
public import MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
public import Batteries.Util.ProofWanted

/-!
# Source pure-tensor and NC integration comparison requests

Every product, differential, closing coefficient, projection and
target-shift component is fixed in the public contract. Finite
perfection/invertibility is a separate theorem for the same actual
comparison. Reference: PTVV arXiv:1111.3209v4, §2.1, pp.31--32.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.WeightedNCIntegration

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.Algebra.Homology.GradedMixedCochainModels
open MathlibExt.Algebra.Homology.PureTensorNegativeCyclic
open MathlibExt.Algebra.Homology.ShiftedTensorUnits
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDeRhamModels
open MathlibExt.AlgebraicGeometry.RelativeSimplicialDeRham
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels

universe u

def_wanted nativePureMixedTensor (R : Type u) [CommRing R]
    (E : GradedMixed R) (C : CochainComplex (ModuleCat.{u} R) ℤ) : PureTensorModel E C

def_wanted nativeNCTensorComparison (R : Type u) [CommRing R]
    (E : GradedMixed R) (C : CochainComplex (ModuleCat.{u} R) ℤ) (P : PureTensorModel E C)
    (p : ℤ) (M : NegativeCyclicModel E p) (N : NegativeCyclicModel P.mixed p) : Comparison P p M N

def_wanted nativeNCMap (R : Type u) [CommRing R] (E F : GradedMixed R)
    (f : MixedMap E F) (p : ℤ) (M : NegativeCyclicModel E p) (N : NegativeCyclicModel F p) :
    CyclicMapModel f p M N

def_wanted nativeShiftedTensorUnit (R : Type u) [CommRing R]
    (C : CochainComplex (ModuleCat.{u} R) ℤ) (t : ℤ) : UnitTensorModel C t

theorem_wanted ncTensorComparisonQuasiIsoOfPerfect (R : Type u) [CommRing R]
    (E : GradedMixed R) (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (U : UnitFunctorModel (R := R) (CochainComplex (ModuleCat.{u} R) ℤ)
      (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)))
    (cofibrant : IsCofibrantModule (cochainModule U C))
    (perfect : IsPerfectModule (scalarCategory R) (cochainModule U C))
    (P : PureTensorModel E C) (p : ℤ) (M : NegativeCyclicModel E p)
    (N : NegativeCyclicModel P.mixed p) (K : Comparison P p M N) : QuasiIso K.map

def_wanted actualRelativeSimplicialProjection (k : Type u) [CommRing k]
    (A B : SAlg k) (M : SimplicialDRModel A) (P : SimplicialDRModel (productAlgebra A B)) :
    RelativeSimplicialDeRham.ProjectionModel A B M P

end MathlibExt.AlgebraicGeometry.WeightedNCIntegration
