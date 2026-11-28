/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.BirationalDualityReferences
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Fixed finite-duality module trace

The trace is obtained from the actual prescribed Rf_* adjunction counit.
The lowest-H0 embedding is explicit normalized integration data on the
actual nonnegative complex. Higher Ext is permitted; no concentration or
finite trace homomorphism is freely supplied.

Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
AlgebraicGeometry/Duality/FiniteTwistedTrace.lean and
FiniteTraceDerivedInternalHomIso.lean, Apache 2.0.
The source-complete finite-duality producer is not requested again.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

attribute [local instance] HasDerivedCategory.standard
variable [HasDerivedPushforwards.{0}]

def singleHomologyIso (X : Scheme.{0}) (M : X.Modules) :
    (DerivedCategory.homologyFunctor X.Modules 0).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) ≅ M :=
  (DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app M

/-- The exact native single-complex/right-derived pushforward unit. -/
def sheafPushforwardUnit {X Y : Scheme.{0}} (f : X ⟶ Y) (M : X.Modules) :
    (DerivedCategory.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (derivedPushforward f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj M) :=
  DerivedCategory.Q.map
    ((HomologicalComplex.singleMapHomologicalComplex
      (Scheme.Modules.pushforward f) (.up ℤ) 0).inv.app M) ≫
        (derivedPushforwardUnit f).app ((CochainComplex.singleFunctor X.Modules 0).obj M)

variable {X Y : Scheme.{0}} (f : X ⟶ Y) [(derivedPushforward f).IsLeftAdjoint]

/-- Canonical lowest-H0 embedding; no false Gorenstein/concentration assumption. -/
structure FiniteDualityEmbedding where
  [bounded : (relativeDuality f).IsGE 0]
  map : (DerivedCategory.singleFunctor X.Modules 0).obj
    (relativeCanonicalModule f 0) ⟶ relativeDuality f
  normalized : (singleHomologyIso X (relativeCanonicalModule f 0)).inv ≫
    (DerivedCategory.homologyFunctor X.Modules 0).map map =
      𝟙 (relativeCanonicalModule f 0)

/-- Literal degree-zero finite trace induced by the fixed adjunction counit. -/
def moduleTrace (C : FiniteDualityEmbedding f) :
    (Scheme.Modules.pushforward f).obj (relativeCanonicalModule f 0) ⟶ structureModule Y :=
  (singleHomologyIso Y ((Scheme.Modules.pushforward f).obj
    (relativeCanonicalModule f 0))).inv ≫
  (DerivedCategory.homologyFunctor Y.Modules 0).map
    (sheafPushforwardUnit f (relativeCanonicalModule f 0) ≫
      (derivedPushforward f).map C.map ≫ trace f) ≫
        (singleHomologyIso Y (structureModule Y)).hom

end MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
