/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicThickening

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

/-- The transition morphisms are compatible with the inclusions into `X`. -/
example {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (n : ℕ) :
    adicThickeningTransition f I n ≫ adicThickeningTransition f I (n + 1) ≫
      adicThickeningι f I (n + 2) = adicThickeningι f I n := by
  simp

/-- Each adic thickening is a closed subscheme of `X`. -/
example {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (n : ℕ) : IsClosedImmersion (adicThickeningι f I n) :=
  inferInstance

/-- The defining square is the Mathlib pullback square. -/
example {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) (I : Ideal R)
    (n : ℕ) :
    adicThickeningι f I n ≫ f = adicThickeningToBase f I n ≫ adicThickeningBase I n :=
  (isPullback_adicThickening f I n).w
