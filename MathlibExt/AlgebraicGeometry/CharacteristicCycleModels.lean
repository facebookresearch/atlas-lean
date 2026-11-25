/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CotangentLocalIntersectionModels
public import MathlibExt.AlgebraicGeometry.EtaleMilnorConductorModels

/-!
# The geometric Milnor characteristic-cycle predicate

Cycles use the native scheme `AlgebraicCycle` with rational coefficients.
The coefficient condition is the concrete subring Z[1/p] inside Q, with
denominator 1 in characteristic zero. Support is at the actual generic
points of the actual cone components. Integrality is a separate predicate.

The Milnor condition quantifies every actual étale chart and smooth curve
map, every at-most isolated characteristic closed point, every local
one-form frame, and every source-fixed local intersection and vanishing
model. Its pairing is the computed native Tor-length sum; total dimension
is the actual residue-reduced alternating rank-plus-Swan sum. The formula
has the source minus sign. There is no characteristic cycle constructor,
Milnor theorem, uniqueness or integrality in the input data.

Reference: Saito, arXiv:1510.03018v4, Definition 4.3, Theorem 4.9,
formula (4.15), Definition 4.10 and Theorem 4.18, printed pages 39--49.
The constant coefficient normalization is (-1)^n times the native
zero-section cycle. Source and native-operation notices are retained in
the imported component modules.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CharacteristicCycleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open AdicDerivedContracts EtaleConstantDerivedModels EtaleLocalAcyclicityModels
open CotangentBundleTestModels CotangentLocalIntersectionModels
open EtaleStrictLocalizationModels EtaleCurveTraitModels EtaleMilnorConductorModels
open _root_.MathlibExt.RingTheory.DerivedModuleScalarOperations

attribute [local instance] HasDerivedCategory.standard

variable (k Λ : Type) [Field k] [CommRing Λ] [Finite Λ] [IsLocalRing Λ]

/-- The source residue characteristic is invertible in the actual base field. -/
def CoefficientsInvertible : Prop := IsUnit ((ringChar (IsLocalRing.ResidueField Λ) : ℕ) : k)

/-- Characteristic zero uses denominator 1; positive characteristic uses p. -/
def coefficientDenominator : ℕ := if ringChar k = 0 then 1 else ringChar k

/-- The concrete coefficient subring Z[1/p] inside Q. -/
def IsLocalizedInteger (a : ℚ) : Prop :=
  ∃ (m : ℤ) (r : ℕ), a * (coefficientDenominator k : ℚ) ^ r = (m : ℚ)

variable {k Λ} {X : Over (Spec (.of k))} {BX : CotangentBundle X}
  (C : ClosedCone X BX)

def IsCycleOnCone (A : AlgebraicCycle BX.total ℚ) : Prop :=
  (∀ q : BX.total, IsLocalizedInteger k (A q)) ∧
    A.support ⊆ {q | ∃ Z : Component C, componentPoint C Z = q}

/-- Integrality is not folded into `IsCycleOnCone`. -/
def IsIntegralCycle (A : AlgebraicCycle BX.total ℚ) : Prop :=
  ∀ q : BX.total, ∃ m : ℤ, A q = (m : ℚ)

variable [DerivedFunctorTheory Λ] [HasExtension (IsLocalRing.residue Λ)]
  (F : Derived Λ X.left) (P : CurveTest (X := X))
  (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ P.U.left)

abbrev chartCoefficient := (derivedPullback Λ P.h.left).obj F

/-- All stored data concerns actual strict localizations, native arrows,
entire cochain cone triangles, and finite layers of the same Galois stalk.
No characteristic-cycle identity is a field. -/
structure MilnorData where
  LX : StrictLocalization Ω x
  LY : StrictLocalization Ω (x ≫ P.f.left)
  localMap : LocalMorphism Ω x P.f.left LX LY
  [trait : Trait Ω (x ≫ P.f.left) LY]
  [sourceAdjunction : DerivedConstantAdjunction Λ LX.scheme]
  [baseAdjunction : DerivedConstantAdjunction Λ LY.scheme]
  [genericAdjunction : DerivedConstantAdjunction Λ
    (Spec (.of (EtaleMilnorConductorModels.geometricGeneric Ω x P.f.left LY).field.carrier))]
  [closedStalkIso : IsIso (closedStalkArrow Λ Ω x LX (chartCoefficient F P))]
  [constantStalkIso : IsIso
    (constantStalkUnit Λ Ω x (chartCoefficient F P) P.f.left LX LY)]
  baseModel : BaseVanishingModel Λ localMap.map
    (EtaleMilnorConductorModels.localCoefficient Λ Ω x (chartCoefficient F P) LX)
  milnorModel : VanishingModel Λ Ω x (chartCoefficient F P) P.f.left LX LY localMap
    (EtaleMilnorConductorModels.geometricGeneric Ω x P.f.left LY)
  comparison : MilnorComparison Λ Ω x (chartCoefficient F P) P.f.left LX LY localMap
    baseModel milnorModel
  ramification : FiniteRamificationStalkModels.BoundedRamification
    (EtaleMilnorConductorModels.genericField Ω x P.f.left LY) Λ
    (IsLocalRing.ResidueField Λ) (IsLocalRing.residue Λ) (localRing Ω (x ≫ P.f.left) LY)
    (genericVanishing Λ Ω x (chartCoefficient F P) P.f.left LX LY localMap baseModel)

attribute [instance] MilnorData.trait MilnorData.sourceAdjunction MilnorData.baseAdjunction
  MilnorData.genericAdjunction MilnorData.closedStalkIso MilnorData.constantStalkIso

def MilnorData.totalDimension (D : MilnorData F P Ω x) : ℚ :=
  FiniteRamificationStalkModels.totalDimension _ _ _ _ _ _ D.ramification

/-- Exactly the independent geometric and coefficient hypotheses of
Theorem 4.9. The record contains no cycle or Milnor conclusion. -/
structure Hypotheses (G : StrictLocalizationSystem) (T : ConstructibleTheory Λ k)
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] (n : ℕ) : Prop where
  perfectBase : PerfectField k
  finiteCoefficient : Finite Λ
  smooth : Smooth X.hom
  coefficientInvertible : CoefficientsInvertible k Λ
  sourceDimension : PureDimension X.left n
  coneDimension : PureConeDimension C n
  constructible : FiniteEtaleConstructibleModels.IsBoundedConstructible Λ k X F
  finiteTor : FiniteEtaleConstructibleModels.HasFiniteTorAmplitude Λ (X := X) F
  microsupport : MicroSupported Λ k G T X C F constructible

/-- The full source Milnor formula, including every local frame and every
source model, with the minus sign and initial localized coefficients. -/
def IsCharacteristicCycle (n : ℕ) (A : AlgebraicCycle BX.total ℚ) : Prop :=
  IsCycleOnCone C A ∧ ∀ (P : CurveTest (X := X)) (BU : CotangentBundle P.U)
    (u : P.U.left), AtMostIsolated C P u →
      ∀ (ω : CurveFrame P u) (I : LocalIntersection C P BU u ω n)
        (Ω : GeometricField) (x : Spec (.of Ω.carrier) ⟶ P.U.left),
        Set.range x = {u} → ∀ D : MilnorData F P Ω x,
          localPairing C P BU u ω I A = -D.totalDimension F P Ω x

/-- The native finite local constant coefficient complex. -/
def constantComplex (V : Scheme.{0}) : Derived Λ V :=
  single Λ ((constantFunctor Λ V).obj (ModuleCat.of Λ (ULift.{1} Λ)))

/-- The native integral fundamental cycle, pushed along the actual zero
section and then included in rational scheme cycles. -/
def zeroSectionCycle (B : CotangentBundle X) [IsNoetherian X.left]
    [IsClosedImmersion B.zero] : AlgebraicCycle B.total ℚ :=
  (AlgebraicCycle.map B.zero Order.height Order.height
    (_root_.AlgebraicGeometry.StackCycleGeometry.integralFundamentalCycle X.left)).mapRange
      (fun a : ℤ ↦ (a : ℚ)) (by simp)

def normalizedConstantCycle (n : ℕ) (B : CotangentBundle X) [IsNoetherian X.left]
    [IsClosedImmersion B.zero] : AlgebraicCycle B.total ℚ :=
  (-1 : ℚ) ^ n • zeroSectionCycle B

end MathlibExt.AlgebraicGeometry.CharacteristicCycleModels
