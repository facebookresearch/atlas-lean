/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.ChowDatum

@[expose] public section

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

private theorem exactSource {R : Type u} [CommRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (.of R)) :
    Nonempty (ChowDatum π) → Nonempty (ChowDatumProj π) :=
  ChowDatumProj.nonempty_of π

-- A higher-universe consumer.
example {R : Type 1} [CommRing R] {V : Scheme.{1}} (π : V ⟶ Spec (.of R))
    (D : ChowDatum π) : Nonempty (ChowDatumProj π) :=
  ChowDatumProj.nonempty_of π ⟨D⟩

-- The Segre embedding of a product of two projective lines over `ℤ`
-- is a closed immersion into projective `3`-space.
example : IsClosedImmersion (ProjSpace.Segre.segre2 (ULift.{u} ℤ) 1 1) :=
  ProjSpace.Segre.segre2_closedImm _ _ _
