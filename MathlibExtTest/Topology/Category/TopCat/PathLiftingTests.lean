/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.PathLifting

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Topology

universe u

namespace TopCat.PathLiftingTests

variable {E B Z : TopCat.{u}} (p : E ⟶ B)

example : TopCat.{u} := pathLiftInput p

example : pathLiftInput p ⟶ E := pathLiftStart p

example : pathLiftInput p ⟶ pathObject B := pathLiftBasePath p

example : pathLiftStart p ≫ p = pathLiftBasePath p ≫ pathEvalZero B :=
  pullback.condition

example (L : PathLiftingData p) : pathLiftInput p ⟶ pathObject E :=
  L.lift

example (L : PathLiftingData p) :
    L.lift ≫ pathEvalZero E = pathLiftStart p :=
  L.lift_zero

example (L : PathLiftingData p) :
    L.lift ≫ pathObjectMap p = pathLiftBasePath p :=
  L.lift_proj

/-- Destructing and rebuilding uses exactly the three frozen fields. -/
def exactThreeFields (L : PathLiftingData p) : PathLiftingData p :=
  match L with
  | ⟨lift, lift_zero, lift_proj⟩ =>
      { lift := lift
        lift_zero := lift_zero
        lift_proj := lift_proj }

section ArbitraryFamily

variable (L : PathLiftingData p)
variable (start : Z ⟶ E) (basePath : Z ⟶ pathObject B)
variable (h : start ≫ p = basePath ≫ pathEvalZero B)

example : Z ⟶ pathObject E :=
  L.liftFamily start basePath h

example :
    L.liftFamily start basePath h ≫ pathEvalZero E = start :=
  L.liftFamily_zero start basePath h

example :
    L.liftFamily start basePath h ≫ pathObjectMap p = basePath :=
  L.liftFamily_proj start basePath h

end ArbitraryFamily

example (L : PathLiftingData p) : pathLiftInput p ⟶ E :=
  L.liftEndpoint

example (L : PathLiftingData p) :
    L.liftEndpoint ≫ p = pathLiftBasePath p ≫ pathEvalOne B :=
  L.liftEndpoint_proj

example : E ⟶ pathObject B := constantBasePathFamily p

example : constantBasePathFamily p ≫ pathEvalZero B = p :=
  constantBasePathFamily_zero p

example : constantBasePathFamily p ≫ pathEvalOne B = p :=
  constantBasePathFamily_one p

example (L : PathLiftingData p) : E ⟶ pathObject E :=
  L.constantLift

example (L : PathLiftingData p) :
    L.constantLift ≫ pathEvalZero E = 𝟙 E :=
  L.constantLift_zero

example (L : PathLiftingData p) :
    L.constantLift ≫ pathObjectMap p = constantBasePathFamily p :=
  L.constantLift_proj

example (L : PathLiftingData p) : E ⟶ E :=
  L.constantTransport

example (L : PathLiftingData p) : L.constantTransport ≫ p = p :=
  L.constantTransport_proj

-- The matching initial endpoint is a genuine input to the pullback lift.
example (_start : Z ⟶ E) (_basePath : Z ⟶ pathObject B) : True := by
  fail_if_success
    have _ : Z ⟶ pathLiftInput p := pullback.lift _start _basePath
  trivial

-- A raw function family cannot replace a continuous TopCat morphism.
example (_raw : pathLiftInput p → C(TopCat.I.{u}, E)) : True := by
  fail_if_success
    have _ : pathLiftInput p ⟶ pathObject E := _raw
  trivial

-- Projection alone cannot construct data without the start law.
example (lift : pathLiftInput p ⟶ pathObject E)
    (_hproj : lift ≫ pathObjectMap p = pathLiftBasePath p) : True := by
  fail_if_success
    have _ : PathLiftingData p :=
      { lift := lift
        lift_proj := _hproj }
  trivial

-- The start law alone cannot construct data without full-path projection.
example (lift : pathLiftInput p ⟶ pathObject E)
    (_hzero : lift ≫ pathEvalZero E = pathLiftStart p) : True := by
  fail_if_success
    have _ : PathLiftingData p :=
      { lift := lift
        lift_zero := _hzero }
  trivial

-- The data are supplied explicitly, not installed as a typeclass instance.
example : True := by
  fail_if_success
    let _ : PathLiftingData p := inferInstance
  trivial

-- Later Item-8 adapters are intentionally absent from this provider.
example (_L : PathLiftingData p) : True := by
  fail_if_success
    have _ := _L.universalReversedLoopLift
  fail_if_success
    have _ := _L.constantLiftFiberSquare
  trivial

section UniverseOne

variable {E₁ B₁ Z₁ : TopCat.{1}} (p₁ : E₁ ⟶ B₁)

example (L : PathLiftingData p₁) : pathLiftInput p₁ ⟶ pathObject E₁ :=
  L.lift

example (L : PathLiftingData p₁) (start : Z₁ ⟶ E₁)
    (basePath : Z₁ ⟶ pathObject B₁)
    (h : start ≫ p₁ = basePath ≫ pathEvalZero B₁) :
    L.liftFamily start basePath h ≫ pathObjectMap p₁ = basePath :=
  L.liftFamily_proj start basePath h

example (L : PathLiftingData p₁) : L.constantTransport ≫ p₁ = p₁ :=
  L.constantTransport_proj

end UniverseOne

section UniverseZero

variable {E₀ B₀ Z₀ : TopCat.{0}} (p₀ : E₀ ⟶ B₀)

example (L : PathLiftingData p₀) : pathLiftInput p₀ ⟶ pathObject E₀ :=
  L.lift

example (L : PathLiftingData p₀) (start : Z₀ ⟶ E₀)
    (basePath : Z₀ ⟶ pathObject B₀)
    (h : start ≫ p₀ = basePath ≫ pathEvalZero B₀) :
    L.liftFamily start basePath h ≫ pathEvalZero E₀ = start :=
  L.liftFamily_zero start basePath h

example (L : PathLiftingData p₀) : L.constantTransport ≫ p₀ = p₀ :=
  L.constantTransport_proj

end UniverseZero

end TopCat.PathLiftingTests

#check TopCat.pathLiftInput
#check TopCat.pathLiftStart
#check TopCat.pathLiftBasePath
#check TopCat.PathLiftingData
#check TopCat.PathLiftingData.lift
#check TopCat.PathLiftingData.lift_zero
#check TopCat.PathLiftingData.lift_proj
#check TopCat.PathLiftingData.liftFamily
#check TopCat.PathLiftingData.liftFamily_zero
#check TopCat.PathLiftingData.liftFamily_proj
#check TopCat.PathLiftingData.liftEndpoint
#check TopCat.PathLiftingData.liftEndpoint_proj
#check TopCat.constantBasePathFamily
#check TopCat.constantBasePathFamily_zero
#check TopCat.constantBasePathFamily_one
#check TopCat.PathLiftingData.constantLift
#check TopCat.PathLiftingData.constantLift_zero
#check TopCat.PathLiftingData.constantLift_proj
#check TopCat.PathLiftingData.constantTransport
#check TopCat.PathLiftingData.constantTransport_proj

#print axioms TopCat.PathLiftingData
#print axioms TopCat.PathLiftingData.liftFamily
#print axioms TopCat.PathLiftingData.liftFamily_zero
#print axioms TopCat.PathLiftingData.liftEndpoint_proj
#print axioms TopCat.constantBasePathFamily
#print axioms TopCat.PathLiftingData.constantLift_proj
#print axioms TopCat.PathLiftingData.constantTransport_proj

end
