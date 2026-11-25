/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EquivariantPerfectObstructionTheoryModels
public import MathlibExt.AlgebraicGeometry.EquivariantDualBundleSourceModels
public import MathlibExt.AlgebraicGeometry.RationalSchemeChowComparisonModels
public import MathlibExt.AlgebraicGeometry.AlgebraicMovingEulerModels

/-!
# Ordinary and equivariant virtual classes from the same original cone

The ordinary class uses the native cone and zero-section recipe of a
cochain presentation equal to the original derived phi. The equivariant
class quotients that same cone and negative-dual total bundle and uses
native projective push and bundle homotopy inverse. Its quotient degree
is virtual dimension minus one. There is no absolute two-term POT on
BGm and no DM assumption on the quotient coefficient stack.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EquivariantVirtualClassModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open IntegralChowChernModels AlgebraicWeightBundleModels DerivedTwoTermObstructionModels
open EquivariantPerfectObstructionTheoryModels EquivariantDualBundleSourceModels
open AlgebraicEquivariantChowModels AlgebraicFixedChowModels RationalSchemeChowComparisonModels
open GlobalPOTVirtualClass FieldChowOperators StackCycleGeometry StackCycleRelations StackChowGroups
open scoped DirectSum TensorProduct

def virtualDimension {X : Over base} (P : DerivedPOT X) : ℤ :=
  (P.model.zeroRank : ℤ) - P.model.negativeRank

/-- Native ordinary geometry retains the original derived presentation and Rees cone. -/
structure OrdinaryVirtualGeometry (X : SchemeData) (P : DerivedPOT X.scheme) where
  presentation : CochainPresentation P
  bundle : DualBundleModel X.scheme P.model.negative P.model.negativeRank
  cone : GlobalPOTVirtualClass.IntrinsicConeModel presentation.native bundle
  [finiteType : LocallyOfFiniteType bundle.total.hom]
  [noetherian : IsNoetherian bundle.total.left]
  pull : ChowPullbackEquivalence X.scheme bundle.total bundle.projection P.model.negativeRank
  push : ClosedCycleDescent bundle.total cone.inclusion

attribute [instance] OrdinaryVirtualGeometry.finiteType OrdinaryVirtualGeometry.noetherian

def OrdinaryVirtualGeometry.nativeClass {X : SchemeData} {P : DerivedPOT X.scheme}
    (O : OrdinaryVirtualGeometry X P) : gradedChow X.scheme (virtualDimension P) :=
  GlobalPOTVirtualClass.virtualClass O.presentation.native O.bundle O.cone O.pull O.push

/-- The rational coefficient conversion uses the actual cycle comparison and its inverse. -/
def OrdinaryVirtualGeometry.rationalClass {X : SchemeData} {P : DerivedPOT X.scheme}
    (O : OrdinaryVirtualGeometry X P) (C : NativeChowComparison X) :
    OrdinaryChow X (virtualDimension P) :=
  gradedFieldToRational X C (virtualDimension P) O.nativeClass

def OrdinaryVirtualGeometry.gradedClass {X : SchemeData} {P : DerivedPOT X.scheme}
    (O : OrdinaryVirtualGeometry X P) (C : NativeChowComparison X) : GradedOrdinary X :=
  DirectSum.lof ℚ ℤ (OrdinaryChow X) (virtualDimension P) (O.rationalClass C)

/-- This is the native Laurent tensor of that same ordinary virtual cycle. -/
def OrdinaryVirtualGeometry.formalClass {X : SchemeData} {P : DerivedPOT X.scheme}
    (O : OrdinaryVirtualGeometry X P) (C : NativeChowComparison X) : FormalChow X :=
  (1 : AlgebraicEquivariantCoefficientModels.Coefficients) ⊗ₜ[ℚ] O.gradedClass C

variable (X : SchemeData) [ModObj Gm X.scheme] (E : EquivariantPOT X.scheme)
  (Q : EquivariantSource X.scheme)
  (D : CycleConstructionData base (FiniteTypeArtin ℂ)) (K : KreschPresentation D)
  (O : OrdinaryVirtualGeometry X E.terms.obstruction)

/-- Both quotient total spaces are the original ordinary geometry, with their actual actions. -/
structure EquivariantVirtualGeometry where
  [bundleAction : ModObj Gm O.bundle.total]
  [coneAction : ModObj Gm O.cone.cone]
  bundleEquivariant : γ[Gm,O.bundle.total] ≫ O.bundle.projection =
    (Gm ◁ O.bundle.projection) ≫ γ[Gm,X.scheme]
  coneEquivariant : γ[Gm,O.cone.cone] ≫ O.cone.inclusion =
    (Gm ◁ O.cone.inclusion) ≫ γ[Gm,O.bundle.total]
  bundleQuotient : EquivariantSource O.bundle.total
  coneQuotient : EquivariantSource O.cone.cone
  bundleMap : EquivariantMap bundleQuotient Q O.bundle.projection bundleEquivariant
  coneMap : EquivariantMap coneQuotient bundleQuotient O.cone.inclusion coneEquivariant
  dual : QuotientDualBundle E.terms.negative O.bundle bundleEquivariant Q bundleQuotient bundleMap
  classes : CycleClassData D K coneQuotient.quotient.stack coneQuotient.inScope
  fundamental : FundamentalCycleData D coneQuotient.quotient.stack coneQuotient.inScope
    ((E.terms.obstruction.model.zeroRank : ℤ)-1)
  push : ProjectiveChowPushData D K coneQuotient.inScope bundleQuotient.inScope coneMap.map
  pull : FlatChowPullData D K bundleQuotient.inScope Q.inScope bundleMap.map
    E.terms.obstruction.model.negativeRank
  homotopy : StackBundleCones.BundleHomotopyData D K Q.inScope
    (QuotientDualBundle.native E.terms.negative O.bundle bundleEquivariant Q bundleQuotient
      bundleMap dual)
    bundleQuotient.inScope pull

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The quotient cone retains its native generic-length fundamental cycle. -/
def equivariantConeClass (G : EquivariantVirtualGeometry X E Q D K O) :
    letI := G.coneAction
    RationalChowGroup D K G.coneQuotient.quotient.stack G.coneQuotient.inScope
      ((E.terms.obstruction.model.zeroRank : ℤ)-1) := by
  letI := G.coneAction
  exact rationalCycleClass D K G.classes ((E.terms.obstruction.model.zeroRank : ℤ)-1)
    G.fundamental.cycle

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- Its bundle class uses the actual closed projective quotient-cone push. -/
def equivariantBundleClass (G : EquivariantVirtualGeometry X E Q D K O) :
    letI := G.bundleAction
    RationalChowGroup D K G.bundleQuotient.quotient.stack G.bundleQuotient.inScope
      ((E.terms.obstruction.model.zeroRank : ℤ)-1) := by
  letI := G.bundleAction
  letI := G.coneAction
  exact rationalMap (G.push.map ((E.terms.obstruction.model.zeroRank : ℤ)-1))
    (equivariantConeClass X E Q D K O G)

set_option maxHeartbeats 8000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The class after the native zero-section inverse has the actual quotient grading. -/
def equivariantZeroClass (G : EquivariantVirtualGeometry X E Q D K O) :
    RationalChowGroup D K Q.quotient.stack Q.inScope
      (((E.terms.obstruction.model.zeroRank : ℤ)-1)-E.terms.obstruction.model.negativeRank) := by
  letI := G.bundleAction
  letI := G.coneAction
  exact rationalMap (StackBundleCones.zeroSectionGysin G.homotopy
    ((E.terms.obstruction.model.zeroRank : ℤ)-1)) (equivariantBundleClass X E Q D K O G)

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 100000 in
/-- The equivariant class is that same native cone/zero-section class in A_d^Gm(X). -/
def equivariantVirtualClass (G : EquivariantVirtualGeometry X E Q D K O) :
    EquivariantChow D K Q (virtualDimension E.terms.obstruction) := by
  letI := G.bundleAction
  letI := G.coneAction
  exact rationalMap (chowRegrade D K Q.quotient.stack Q.inScope
    (show ((E.terms.obstruction.model.zeroRank : ℤ)-1)-E.terms.obstruction.model.negativeRank =
      virtualDimension E.terms.obstruction-1 by unfold virtualDimension; omega))
    (equivariantZeroClass X E Q D K O G)

end MathlibExt.AlgebraicGeometry.EquivariantVirtualClassModels
