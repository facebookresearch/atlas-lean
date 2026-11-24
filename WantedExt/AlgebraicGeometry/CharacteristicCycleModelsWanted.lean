/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CharacteristicCycleModels

/-!
# Geometric characteristic-cycle source requests

The background constructors target actual native cotangent schemes,
strict local curve rings, graph ideals, Tor modules, base-sheaf cones and
their spectrum-induced Galois operators. The principal requests preserve
all hypotheses of Saito's Theorem 4.9 and quantify all actual local tests.
Theorem 4.18 integrality and the (-1)^n constant zero-section normalization
are separate conclusions. No initial integral coefficient assumption or
Milnor-identity constructor is supplied as background data.

References: Saito, arXiv:1510.03018v4, Section 1.3, Definition 4.3,
Theorem 4.9, formula (4.15), Definition 4.10 and Theorem 4.18; Beilinson,
arXiv:1505.06768v8, Sections 1.1--1.3. The interface definitions retain
the source revisions and native-operation license notices.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CharacteristicCycleModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open AdicDerivedContracts CotangentBundleTestModels CotangentLocalIntersectionModels
open EtaleStrictLocalizationModels EtaleCurveTraitModels EtaleLocalAcyclicityModels
open CharacteristicCycleModels
open _root_.MathlibExt.RingTheory.DerivedModuleScalarOperations

section CurveTrait

def_wanted nativeSmoothCurveTrait (k : Type) [Field k] (perfect : PerfectField k)
    (Y : Over (Spec (.of k))) (curve : SmoothOfRelativeDimension 1 Y.hom)
    (Ω : GeometricField) (y : Spec (.of Ω.carrier) ⟶ Y.left) (u : Y.left)
    (closed : IsClosed ({u} : Set Y.left)) (point : Set.range y = {u})
    (L : StrictLocalization Ω y) : Trait Ω y L

private def check_nativeSmoothCurveTrait (k : Type) [Field k] (perfect : PerfectField k)
    (Y : Over (Spec (.of k))) (curve : SmoothOfRelativeDimension 1 Y.hom)
    (Ω : GeometricField) (y : Spec (.of Ω.carrier) ⟶ Y.left) (u : Y.left)
    (closed : IsClosed ({u} : Set Y.left)) (point : Set.range y = {u})
    (L : StrictLocalization Ω y) : DefWanted (Trait Ω y L) :=
  nativeSmoothCurveTrait k perfect Y curve Ω y u closed point L

end CurveTrait

section LocalIntersection

variable {k : Type} [Field k] (X : Over (Spec (.of k)))
  [finiteX : LocallyOfFiniteType X.hom] [compactX : QuasiCompact X.hom]
  (BX : CotangentBundle X) (C : ClosedCone X BX)

include finiteX compactX in
def_wanted nativeCotangentNoetherian (smooth : Smooth X.hom) : IsNoetherian BX.total

include finiteX compactX in
def_wanted nativeZeroSectionClosed (smooth : Smooth X.hom) : IsClosedImmersion BX.zero

def_wanted nativeCurveFrame (P : CurveTest (X := X)) (u : P.U.left) : CurveFrame P u

include finiteX compactX in
def_wanted nativeLocalIntersection (smooth : Smooth X.hom) (n : ℕ)
    (dimension : PureDimension X.left n) (coneDimension : PureConeDimension C n)
    (P : CurveTest (X := X)) (BU : CotangentBundle P.U) (u : P.U.left)
    (isolated : AtMostIsolated C P u) (ω : CurveFrame P u) : LocalIntersection C P BU u ω n

include finiteX compactX in
theorem_wanted local_pairing_frame_independent (smooth : Smooth X.hom) (n : ℕ)
    (dimension : PureDimension X.left n) (coneDimension : PureConeDimension C n)
    (P : CurveTest (X := X)) (BU : CotangentBundle P.U) (u : P.U.left)
    (isolated : AtMostIsolated C P u) (ω ω' : CurveFrame P u)
    (I : LocalIntersection C P BU u ω n) (I' : LocalIntersection C P BU u ω' n)
    (A : AlgebraicCycle BX.total ℚ) (cycle : IsCycleOnCone C A) :
    localPairing C P BU u ω I A = localPairing C P BU u ω' I' A

private def check_nativeCotangentNoetherian (smooth : Smooth X.hom) :
    DefWanted (IsNoetherian BX.total) := nativeCotangentNoetherian X BX smooth

private def check_nativeZeroSectionClosed (smooth : Smooth X.hom) :
    DefWanted (IsClosedImmersion BX.zero) := nativeZeroSectionClosed X BX smooth

private def check_nativeCurveFrame (P : CurveTest (X := X)) (u : P.U.left) :
    DefWanted (CurveFrame P u) := nativeCurveFrame X P u

private def check_nativeLocalIntersection (smooth : Smooth X.hom) (n : ℕ)
    (dimension : PureDimension X.left n) (coneDimension : PureConeDimension C n)
    (P : CurveTest (X := X)) (BU : CotangentBundle P.U) (u : P.U.left)
    (isolated : AtMostIsolated C P u) (ω : CurveFrame P u) :
    DefWanted (LocalIntersection C P BU u ω n) :=
  nativeLocalIntersection X BX C smooth n dimension coneDimension P BU u isolated ω

private def check_local_pairing_frame_independent (smooth : Smooth X.hom) (n : ℕ)
    (dimension : PureDimension X.left n) (coneDimension : PureConeDimension C n)
    (P : CurveTest (X := X)) (BU : CotangentBundle P.U) (u : P.U.left)
    (isolated : AtMostIsolated C P u) (ω ω' : CurveFrame P u)
    (I : LocalIntersection C P BU u ω n) (I' : LocalIntersection C P BU u ω' n)
    (A : AlgebraicCycle BX.total ℚ) (cycle : IsCycleOnCone C A) :
    ProofWanted (localPairing C P BU u ω I A = localPairing C P BU u ω' I' A) :=
  local_pairing_frame_independent X BX C smooth n dimension coneDimension
    P BU u isolated ω ω' I I' A cycle

end LocalIntersection

section CharacteristicCycle

variable (k Λ : Type) [Field k] [CommRing Λ] [Finite Λ] [IsLocalRing Λ]
  [DerivedFunctorTheory Λ] [HasExtension (IsLocalRing.residue Λ)]
  (X : Over (Spec (.of k))) [LocallyOfFiniteType X.hom] [QuasiCompact X.hom]
  (BX : CotangentBundle X) (C : ClosedCone X BX) (F : Derived Λ X.left)
  (G : StrictLocalizationSystem) (T : ConstructibleTheory Λ k) (n : ℕ)

def_wanted nativeMilnorData (H : Hypotheses C F G T n)
    (P : CurveTest (X := X)) (u : P.U.left) (isolated : AtMostIsolated C P u)
    (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ P.U.left) (point : Set.range x = {u}) :
    MilnorData F P Ω x

theorem_wanted milnor_total_dimension_independent (H : Hypotheses C F G T n)
    (P : CurveTest (X := X)) (u : P.U.left) (isolated : AtMostIsolated C P u)
    (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ P.U.left) (point : Set.range x = {u})
    (D D' : MilnorData F P Ω x) : D.totalDimension F P Ω x = D'.totalDimension F P Ω x

theorem_wanted characteristic_cycle_exists_unique (H : Hypotheses C F G T n) :
  ∃! A : AlgebraicCycle BX.total ℚ, IsCharacteristicCycle C F n A

theorem_wanted characteristic_cycle_independent (C' : ClosedCone X BX)
    (H : Hypotheses C F G T n) (H' : Hypotheses C' F G T n)
    (A A' : AlgebraicCycle BX.total ℚ) (candidate : IsCharacteristicCycle C F n A)
    (candidate' : IsCharacteristicCycle C' F n A') : A = A'

theorem_wanted characteristic_cycle_integral (H : Hypotheses C F G T n)
    (A : AlgebraicCycle BX.total ℚ) (candidate : IsCharacteristicCycle C F n A) :
    IsIntegralCycle A

theorem_wanted constant_characteristic_cycle [IsNoetherian X.left] [IsClosedImmersion BX.zero]
    (H : Hypotheses C (constantComplex (Λ := Λ) X.left) G T n)
    (A : AlgebraicCycle BX.total ℚ)
    (candidate : IsCharacteristicCycle C (constantComplex (Λ := Λ) X.left) n A) :
    A = normalizedConstantCycle n BX

private def check_nativeMilnorData (H : Hypotheses C F G T n)
    (P : CurveTest (X := X)) (u : P.U.left) (isolated : AtMostIsolated C P u)
    (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ P.U.left) (point : Set.range x = {u}) :
    DefWanted (MilnorData F P Ω x) := nativeMilnorData k Λ X BX C F G T n H P u isolated Ω x point

private def check_milnor_total_dimension_independent (H : Hypotheses C F G T n)
    (P : CurveTest (X := X)) (u : P.U.left) (isolated : AtMostIsolated C P u)
    (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ P.U.left) (point : Set.range x = {u})
    (D D' : MilnorData F P Ω x) :
    ProofWanted (D.totalDimension F P Ω x = D'.totalDimension F P Ω x) :=
  milnor_total_dimension_independent k Λ X BX C F G T n H P u isolated Ω x point D D'

private def check_characteristic_cycle_exists_unique (H : Hypotheses C F G T n) :
    ProofWanted (∃! A : AlgebraicCycle BX.total ℚ, IsCharacteristicCycle C F n A) :=
  characteristic_cycle_exists_unique k Λ X BX C F G T n H

private def check_characteristic_cycle_independent (C' : ClosedCone X BX)
    (H : Hypotheses C F G T n) (H' : Hypotheses C' F G T n)
    (A A' : AlgebraicCycle BX.total ℚ) (candidate : IsCharacteristicCycle C F n A)
    (candidate' : IsCharacteristicCycle C' F n A') : ProofWanted (A = A') :=
  characteristic_cycle_independent k Λ X BX C F G T n C' H H' A A' candidate candidate'

private def check_characteristic_cycle_integral (H : Hypotheses C F G T n)
    (A : AlgebraicCycle BX.total ℚ) (candidate : IsCharacteristicCycle C F n A) :
    ProofWanted (IsIntegralCycle A) :=
  characteristic_cycle_integral k Λ X BX C F G T n H A candidate

private def check_constant_characteristic_cycle [IsNoetherian X.left] [IsClosedImmersion BX.zero]
    (H : Hypotheses C (constantComplex (Λ := Λ) X.left) G T n)
    (A : AlgebraicCycle BX.total ℚ)
    (candidate : IsCharacteristicCycle C (constantComplex (Λ := Λ) X.left) n A) :
    ProofWanted (A = normalizedConstantCycle n BX) :=
  constant_characteristic_cycle k Λ X BX C G T n H A candidate

end CharacteristicCycle

end WantedExt.AlgebraicGeometry.CharacteristicCycleModelsWanted
