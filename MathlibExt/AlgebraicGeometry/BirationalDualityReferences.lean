/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.FourierMukai
public import MathlibExt.AlgebraicGeometry.BundleTrace
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

/-!
# Fixed derived duality and reflexive-power references

The relative duality object is the actual chosen right adjoint of the fixed
native Rf_* functor applied to O_Y. Its trace is that adjunction's counit.
The module reference is H^(-n) of this object, and its reflexive powers are
literal double duals of the native tensor powers. No canonical sheaf, trace
function or reflexive power is freely supplied.

Existence and source-to-native identification of the genuine adjoints are
explicit source-integration inputs; no new generic duality existence is Wanted.
Source: AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b,
StacksFrontier/AlgebraicGeometry/Duality/FiniteTwistedTrace.lean and
FiniteTraceDerivedInternalHomIso.lean (Apache 2.0). Normalization with a
Cartier log-boundary or an slc family is additional data/proof work.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.BirationalDualityReferences

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.FourierMukai

attribute [local instance] HasDerivedCategory.standard

abbrev derivedUnit (X : Scheme.{0}) :=
  (DerivedCategory.singleFunctor X.Modules 0).obj (structureModule X)

/-- The actual dual module over the same structure sheaf. -/
abbrev dual {X : Scheme.{0}} (M : X.Modules) := BundleTrace.homSheaf X M (structureModule X)

/-- Literal reflexive tensor-power reference; identification with canonical data is separate. -/
def reflexivePower {X : Scheme.{0}} (M : X.Modules) (m : ℕ) : X.Modules :=
  dual (dual (power M m))

variable [HasDerivedPushforwards.{0}] {X Y : Scheme.{0}} (f : X ⟶ Y)
  [(derivedPushforward f).IsLeftAdjoint]

/-- The fixed relative duality object `f^× O_Y`: the right adjoint of the fixed
ambient `Rf_*` (on the derived category of all module sheaves) applied to `O_Y`.
Identifying it with Grothendieck's `f^! O_Y` needs `f` proper and the comparison with
the right adjoint on quasi-coherent complexes (`QuasicoherentDualityReferences`); for a
nonproper `f` the two differ. -/
def relativeDuality : D X := (derivedPushforward f).rightAdjoint.obj (derivedUnit Y)

/-- The actual trace/counit of the prescribed Rf_* adjunction. -/
def trace : (derivedPushforward f).obj (relativeDuality f) ⟶ derivedUnit Y :=
  (Adjunction.ofIsLeftAdjoint (derivedPushforward f)).counit.app (derivedUnit Y)

/-- `H^(-n)(f^× O_Y)`, as an actual module reference, not an assumed canonical line.
Reading it as `H^(-n)(f^! O_Y)` needs the proper quasi-coherent comparison, and the
canonical-module interpretation the appropriate pure-dimensional/CM scope. -/
def relativeCanonicalModule (n : ℕ) : X.Modules :=
  (DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).obj (relativeDuality f)

/-- Actual relative reflexive pluricanonical powers. -/
def relativeCanonicalPower (n m : ℕ) : X.Modules :=
  reflexivePower (relativeCanonicalModule f n) m

end MathlibExt.AlgebraicGeometry.BirationalDualityReferences
