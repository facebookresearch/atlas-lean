/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.GeometricallyConnected

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyIrreducible f] :
    GeometricallyConnected f :=
  AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected f

/-- The exact composite-descent statement, with no added hypothesis. -/
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyConnected (f ≫ g)] [Surjective f] :
    GeometricallyConnected g :=
  AlgebraicGeometry.GeometricallyConnected.of_comp_of_surjective f g

-- Pin the default heartbeat budgets: the geometric-fiber instance must
-- resolve within them, so a looping or slow search fails this test.
set_option maxHeartbeats 200000 in
set_option synthInstance.maxHeartbeats 20000 in
/-- Typeclass search finds the connectedness of a geometric fiber. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [GeometricallyConnected f]
    (K : Type u) [Field K] (k : Spec (.of K) ⟶ Y) :
    ConnectedSpace ↥(Limits.pullback f k) :=
  inferInstance

set_option maxHeartbeats 200000 in
set_option synthInstance.maxHeartbeats 20000 in
/-- The same search on the composite fiber that the descent proof uses. -/
example {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [GeometricallyConnected (f ≫ g)] (K : Type u) [Field K]
    (k : Spec (.of K) ⟶ Z) :
    ConnectedSpace ↥(Limits.pullback (f ≫ g) k) :=
  inferInstance
