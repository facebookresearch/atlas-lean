/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels

/-!
# Construction requests for the actual motivic complex sources

The targets retain the published reduced-torus cokernels, actual
simplex/transfer maps, pointwise tensor/sheafification, augmented
K-injective complexes and zero-point Dold--Kan realization. No
representability, Thom or motivic-operation conclusion is an input.

Sources: Mazza--Voevodsky--Weibel, Lectures 2--3 and 13--14;
Voevodsky, arXiv:math/0107109v1, Section 2.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.MotivicComplexSourcesWanted

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.FiniteTransferCycleModels
open MathlibExt.AlgebraicGeometry.FiniteTransferProductModels
open MathlibExt.AlgebraicGeometry.NisnevichTransferModels
open MathlibExt.AlgebraicGeometry.MotivicStandardSchemes
open MathlibExt.AlgebraicGeometry.EffectiveMotivicComplexModels
open MathlibExt.AlgebraicGeometry.PointedMotivicModels
open MathlibExt.AlgebraicGeometry.ReducedMotivicCohomologyModels

def_wanted reduced_torus_source (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (A : StandardSchemes P)
    (R : RepresentableSystem D G) (q : ℕ) :
    ReducedTorusModel (D := D) (G := G) (P := P) (A := A) (R := R) q

def_wanted singular_cycle_source (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (E : ExternalSystem P)
    (C : CorrespondenceProductModel D G P E) (A : StandardSchemes P)
    (F : AdditiveTransferPresheaves D G) :
    SingularModel (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) F

def_wanted tate_cycle_source (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (E : ExternalSystem P)
    (C : CorrespondenceProductModel D G P E) (A : StandardSchemes P)
    (R : RepresentableSystem D G) :
    CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R)

def_wanted nisnevich_tensor_source (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] : NisTensorSystem k

def_wanted coefficient_complex_source (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (E : ExternalSystem P)
    (C : CorrespondenceProductModel D G P E) (A : StandardSchemes P)
    (R : RepresentableSystem D G)
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (S : TransferSheafificationModel D G)
    (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R))
    (N : NisTensorSystem k) :
    CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R) (S := S) T N

def_wanted kinjective_coefficient_resolution (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] :
    KInjectiveResolutionSystem k

def_wanted pointed_doldkan_source (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] :
    PointedSimplicialModuleFunctor k

def_wanted reduced_free_source (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] : ReducedFreeNisSystem k

def_wanted motivic_local_replacement (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (P : SmoothProductSystem k) (A : StandardSchemes P)
    (F : PointedSpaces (k := k)) : MotivicReplacement A F

private def check_reduced_torus (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (A : StandardSchemes P)
    (R : RepresentableSystem D G) (q : ℕ) :
    DefWanted (ReducedTorusModel (D := D) (G := G) (P := P) (A := A) (R := R) q) :=
  reduced_torus_source k D G P A R q

private def check_singular (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (E : ExternalSystem P)
    (C : CorrespondenceProductModel D G P E) (A : StandardSchemes P)
    (F : AdditiveTransferPresheaves D G) :
    DefWanted (SingularModel (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) F) :=
  singular_cycle_source k D G P E C A F

private def check_tate (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (E : ExternalSystem P)
    (C : CorrespondenceProductModel D G P E) (A : StandardSchemes P)
    (R : RepresentableSystem D G) :
    DefWanted (CycleComplexSystem (D := D) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R)) :=
  tate_cycle_source k D G P E C A R

private def check_tensor (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] :
    DefWanted (NisTensorSystem k) := nisnevich_tensor_source k

private def check_coefficients (k : Type) [Field k]
    (D : CompositionSystem k) (G : GraphSystem k)
    [CorrespondenceLaws D G] [CorrespondenceAdditivity D G]
    (P : SmoothProductSystem k) (E : ExternalSystem P)
    (C : CorrespondenceProductModel D G P E) (A : StandardSchemes P)
    (R : RepresentableSystem D G)
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (S : TransferSheafificationModel D G)
    (T : CycleComplexSystem (D := D) (G := G) (P := P) (E := E) (C := C) (A := A) (R := R))
    (N : NisTensorSystem k) :
    DefWanted (CoefficientComplexSystem (D := D) (G := G) (P := P) (E := E)
      (C := C) (A := A) (R := R) (S := S) T N) :=
  coefficient_complex_source k D G P E C A R S T N

private def check_resolution (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] :
    DefWanted (KInjectiveResolutionSystem k) := kinjective_coefficient_resolution k

private def check_pointed (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] :
    DefWanted (PointedSimplicialModuleFunctor k) := pointed_doldkan_source k

private def check_reduced_free (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)] :
    DefWanted (ReducedFreeNisSystem k) := reduced_free_source k

private def check_motivic_replacement (k : Type) [Field k]
    [HasSheafify (nisnevichTopology (k := k)) (ModuleCat.{1} ℤ)]
    (P : SmoothProductSystem k) (A : StandardSchemes P) (F : PointedSpaces (k := k)) :
    DefWanted (MotivicReplacement A F) := motivic_local_replacement k P A F

end WantedExt.AlgebraicGeometry.MotivicComplexSourcesWanted
