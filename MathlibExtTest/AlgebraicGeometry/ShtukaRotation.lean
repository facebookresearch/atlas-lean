/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.ShtukaPartialFrobenius

/-!
Tests of the pole rotation of a right shtuka: the old second bundle becomes the first, the new
modifications are the two pushout legs, the pole moves by the curve Frobenius and the zero is
unchanged. A construction that swapped the legs instead would fail these.
-/

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ShtukaPartialFrobenius
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.CurveVectorBundles

variable {p : ℕ} [Fact p.Prime] {X S : PrimeFieldScheme p} {r : ℕ}
  (A : Shtuka p X S r) (h : A.RotationConditions)

/-- The old second bundle is the first bundle of the rotation. -/
example : (A.rotate h).E = A.E' := rfl

/-- The new second bundle is the pushout of the two original modifications. -/
example : (A.rotate h).E' =
    pushout A.t ((Scheme.Modules.pullback (twist p X S)).map A.j) := rfl

/-- The new pole modification is the first pushout leg, out of the old second bundle. -/
example : (A.rotate h).j = pushout.inl _ _ := rfl

/-- The new zero modification is the second pushout leg, out of the Frobenius pullback. -/
example : (A.rotate h).t = pushout.inr _ _ := rfl

/-- The pole moves by the curve Frobenius. -/
example : (A.rotate h).pole = A.pole ≫ primeFieldFrobenius p X := rfl

/-- The zero is unchanged. -/
example : (A.rotate h).zero = A.zero := rfl

/-- The new zero modification has the original zero-graph cokernel, with no extra input. -/
example : IsGraphLineBundle (cokernel (A.rotate h).t) A.zero := A.rotationT_cokernel

/-- The base-change prerequisites and the rank give the rotation conditions. -/
example (bundle : IsVectorBundle A.rotationModule r) (P : A.PullbackConditions) :
    (A.rotate (A.rotationConditionsOfBundle bundle P)).pole = A.rotationPole := rfl

#print axioms MathlibExt.AlgebraicGeometry.ShtukaPartialFrobenius.Shtuka.rotate
