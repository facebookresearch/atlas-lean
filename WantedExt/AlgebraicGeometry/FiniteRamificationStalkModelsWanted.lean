/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.FiniteRamificationStalkModels

/-!
# Source constructions and independence for geometric ramification sums

The integral and quotient actions are fixed on every element of the
actual integral closure and its actual maximal-ideal quotients. Finite
descent is requested for genuine finite discrete constructible field
complexes of finite Tor amplitude. Independence compares the exact Swan
and alternating total-dimension definitions, including different bounds
and finite Galois layers. Hasse--Arf integrality is a conclusion under
strictly local DVR and coefficient-invertibility hypotheses.

References: Serre, Local Fields, Chapter IV, Sections 1--2 and Chapter VI,
Section 2; Saito, arXiv:1510.03018v4, Section 1.3, printed pages 13--16.
Completed source material remains explicitly deferred through Batteries
requests, with no axiom or proof asserted here.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.FiniteRamificationStalkModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open AdicDerivedContracts FiniteEtaleConstructibleModels IntegralRamificationModels
open FiniteRamificationStalkModels
open _root_.MathlibExt.RingTheory.DerivedModuleScalarOperations

variable (R K L : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Field L] [Algebra R K] [IsFractionRing R K]
  [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [FiniteDimensional K L] [IsGalois K L]

def_wanted nativeIntegralAction : IntegralAction R K L

variable [IsDiscreteValuationRing (Integers R L)] (A : IntegralAction R K L)

def_wanted nativeRamificationQuotientActions : QuotientActions R K L A

variable (Q : QuotientActions R K L A)

def_wanted nativeRamificationFiniteCut : FiniteCut R K L Q

variable (κ V : Type*) [Field κ] [AddCommGroup V] [Module κ V] [Module.Finite κ V]
  (ρ : Gal(L/K) →* Module.End κ V)

theorem_wanted swan_cut_independent (N N' : FiniteCut R K L Q) :
  swan R K L ρ Q N = swan R K L ρ Q N'

private def check_nativeIntegralAction : DefWanted (IntegralAction R K L) :=
  nativeIntegralAction R K L

private def check_nativeRamificationQuotientActions : DefWanted (QuotientActions R K L A) :=
  nativeRamificationQuotientActions R K L A

private def check_nativeRamificationFiniteCut : DefWanted (FiniteCut R K L Q) :=
  nativeRamificationFiniteCut R K L A Q

private def check_swan_cut_independent (N N' : FiniteCut R K L Q) :
    ProofWanted (swan R K L ρ Q N = swan R K L ρ Q N') :=
  swan_cut_independent R K L A Q κ V ρ N N'

section FieldComplex

variable (Λ κ K : Type) [CommRing Λ] [finiteLambda : Finite Λ] [Field κ] [Finite κ] [Field K]
  (r : Λ →+* κ) [HasExtension r] [DerivedFunctorTheory Λ]
  (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Algebra R K] [IsFractionRing R K] [henselianR : HenselianLocalRing R]
  [residueClosedR : IsAlgClosed (IsLocalRing.ResidueField R)]
  (F : Derived Λ (Spec (.of K)))

def_wanted nativeReducedFieldGaloisAction (q : ℤ) :
  EtaleReducedGaloisStalks.SourceAction Λ κ r K F q

include finiteLambda henselianR residueClosedR in
def_wanted nativeBoundedRamification
    (constructible : IsBoundedConstructible Λ K (Over.mk (𝟙 (Spec (.of K)))) F)
    (tor : HasFiniteTorAmplitude Λ (X := Over.mk (𝟙 (Spec (.of K)))) F)
    (invertible : IsUnit ((ringChar κ : ℕ) : R)) :
    BoundedRamification K Λ κ r R F

include henselianR residueClosedR in
theorem_wanted finite_layer_independent (q : ℤ) (B B' : Layer K Λ κ r R F q) :
  B.totalDimension = B'.totalDimension

include henselianR residueClosedR in
theorem_wanted total_dimension_independent (B B' : BoundedRamification K Λ κ r R F) :
  FiniteRamificationStalkModels.totalDimension K Λ κ r R F B =
    FiniteRamificationStalkModels.totalDimension K Λ κ r R F B'

include henselianR residueClosedR in
theorem_wanted total_dimension_integral (invertible : IsUnit ((ringChar κ : ℕ) : R))
    (B : BoundedRamification K Λ κ r R F) :
  ∃ m : ℤ, FiniteRamificationStalkModels.totalDimension K Λ κ r R F B = (m : ℚ)

private def check_nativeReducedFieldGaloisAction (q : ℤ) :
    DefWanted (EtaleReducedGaloisStalks.SourceAction Λ κ r K F q) :=
  nativeReducedFieldGaloisAction Λ κ K r F q

private def check_nativeBoundedRamification
    (constructible : IsBoundedConstructible Λ K (Over.mk (𝟙 (Spec (.of K)))) F)
    (tor : HasFiniteTorAmplitude Λ (X := Over.mk (𝟙 (Spec (.of K)))) F)
    (invertible : IsUnit ((ringChar κ : ℕ) : R)) :
    DefWanted (BoundedRamification K Λ κ r R F) :=
  nativeBoundedRamification Λ κ K r R F constructible tor invertible

private def check_finite_layer_independent (q : ℤ) (B B' : Layer K Λ κ r R F q) :
    ProofWanted (B.totalDimension = B'.totalDimension) :=
  finite_layer_independent Λ κ K r R F q B B'

private def check_total_dimension_independent (B B' : BoundedRamification K Λ κ r R F) :
    ProofWanted (FiniteRamificationStalkModels.totalDimension K Λ κ r R F B =
      FiniteRamificationStalkModels.totalDimension K Λ κ r R F B') :=
  total_dimension_independent Λ κ K r R F B B'

private def check_total_dimension_integral (invertible : IsUnit ((ringChar κ : ℕ) : R))
    (B : BoundedRamification K Λ κ r R F) :
    ProofWanted (∃ m : ℤ, FiniteRamificationStalkModels.totalDimension K Λ κ r R F B = (m : ℚ)) :=
  total_dimension_integral Λ κ K r R F invertible B

end FieldComplex

end WantedExt.AlgebraicGeometry.FiniteRamificationStalkModelsWanted
