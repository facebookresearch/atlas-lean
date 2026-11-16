/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
public import Batteries.Util.ProofWanted

/-!
# Source-normalized DG tensor/coherence construction requests

All joint simplices and all affine/global unit, symmetry and associator
maps are fixed by the public cochain/quotient contracts. Generic
assembly is requested here; no proof of orientation or nondegeneracy
is included. The full module fibration and compatible global realization
are chosen together with their source monoidal data.

References: PTVV arXiv:1111.3209v4, §§1--2; Lurie Higher Algebra
§§1.3 and 7.3; Keller Deriving DG categories §6.
-/

@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.CoherentNerveTransformations
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u v

def_wanted normalizedCoefficientActions (R : Type u) [CommRing R]
    (C : DGCat R) (o : C) [Subsingleton C] :
    ∀ M : RightModule R C, ActionModel C o M

def_wanted normalizedDerivedCoefficientTensor (R : Type u) [CommRing R]
    (C : DGCat R) (o : C) [Subsingleton C]
    (h : IsCommutativeCoefficient C o) : DerivedTensorModel C o

def_wanted normalizedCoefficientOpposite (R : Type u) [CommRing R]
    (C : DGCat R) (o : C) [Subsingleton C]
    (h : IsCommutativeCoefficient C o) : OppositeModel C o

def_wanted normalizedCoefficientCoherence (R : Type u) [CommRing R]
    (C : DGCat R) (o : C) [Subsingleton C] (h : IsCommutativeCoefficient C o)
    (T : DerivedTensorModel C o) (unit : DGDerivedModules R C)
    (unit_eq : unit.obj = regularModule C o) : CoherenceModel C o T unit unit_eq

def_wanted nativeCoherentTensorNerve (R : Type u) [CommRing R]
    (C : Type v) [DGCategory R C]
    (T : EnrichedFunctor (Cochains R) (C × C) C) : NerveTensorModel T

def_wanted nativeDGInterval (R : Type u) [CommRing R] : IntervalModel.{u, v} R

def_wanted nativeCoherentPair (R : Type u) [CommRing R]
    (C D : Type v) [DGCategory R C] [DGCategory R D] : PairNerveModel (R := R) (C := C) (D := D)

def_wanted nativeDGSwap (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] :
    SwapDGFunctorModel (R := R) C

def_wanted nativeDGAssociator (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] :
    AssociatorDGFunctorModel (R := R) C

def_wanted nativeDGFunctorProduct (R : Type u) [CommRing R]
    (C D C' D' : Type v) [DGCategory R C] [DGCategory R D] [DGCategory R C'] [DGCategory R D']
    (F : EnrichedFunctor (Cochains R) C D) (G : EnrichedFunctor (Cochains R) C' D') :
    ProductDGFunctorModel F G

def_wanted nativeCoherentTransformation (R : Type u) [CommRing R]
    (C D : Type v) [DGCategory R C] [DGCategory R D]
    (F G : EnrichedFunctor (Cochains R) C D) (η : ∀ x : C, DGHom R 0 (F.obj x) (G.obj x))
    (closed : ∀ x : C, dgDifferential R 0 (η x) = 0)
    (natural : ∀ (x y : C) (n : ℤ) (f : DGHom R n x y),
      dgComp R (F.dgMap n f) (η y) (add_zero n) = dgComp R (η x) (G.dgMap n f) (zero_add n)) :
    NerveTransformationModel F G η

def_wanted affineCoherentTensorPaths (R : Type u) [CommRing R]
    (C : DGCat R) (o : C) [Subsingleton C] (h : IsCommutativeCoefficient C o)
    (T : DerivedTensorModel C o) (P : NerveTensorModel T.functor)
    (unit : DGDerivedModules R C) (unit_eq : unit.obj = regularModule C o)
    (K : CoherenceModel C o T unit unit_eq) : AffineCoherenceNerves C o T P unit unit_eq K

def_wanted sourceMonoidalModuleFibration (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N) :
    (M : AffineModuleFibration N S) × (U : RegularUnitSystem M) ×
      (T : TensorFibrationModel M) × FibrationCoherenceModel M U T

def_wanted sourceTensorSections (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (T : TensorFibrationModel M) (X : Prestack k) :
    TensorSectionModel M T X

def_wanted sourceCoherenceSections (k : Type u) [CommRing k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (T : TensorFibrationModel M) (B : FibrationCoherenceModel M U T)
    (X : Prestack k) (F : TensorSectionModel M T X) : CoherenceSectionModel M U T B X F

def_wanted compatibleMonoidalCoefficientQCoh (k : Type u) [CommRing k] [Algebra ℚ k]
    (N : ShuffleAlgebraFunctor k) (S : AffineScalarSystem N)
    (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (A : SAlg k) (B : AffineQCohNormalization M U Q A)
    (X : Prestack k) (b : X ⟶ affineMapping k Q A)
    (T : TensorFibrationModel M) (C : FibrationCoherenceModel M U T)
    (F : TensorSectionModel M T X) (K : CoherenceSectionModel M U T C X F) :
    (G : QCohEnhancement M U X) × (H : MonoidalEnhancement G F) ×
      GlobalCoherenceRealization H K × CoefficientRealization G L A Q b V B

end MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
