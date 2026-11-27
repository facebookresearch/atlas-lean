/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.Data.ZMod.Basic

/-!
# Actual perfect prime-field schemes and universal perfection maps

Perfectness is the bijectivity of Frobenius on every actual affine-open
section ring. A perfection model is an actual perfect scheme with the
universal map on all perfect scheme-valued tests. An ordinary deperfection
is kept separate; its Picard/finite-presentation geometry is not silently
assigned to the actual perfect scheme.

These are original native model adapters to the completed generic source:
TauCetiProject/TauCeti, revision62bbc0596dc3539d488232e4e924a338548ea0a9,
`TauCeti/AlgebraicGeometry/Frobenius/Perfection.lean` (Apache2.0),
which constructs scheme perfection and its adjunction. No duplicate
perfection-constructor theorem is requested here.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PerfectSchemeModels

open CategoryTheory _root_.AlgebraicGeometry

variable (p : ℕ) [Fact p.Prime]

abbrev PrimeFieldScheme := Over (Spec (.of (ZMod p)))

/-- Actual affine Frobenius bijectivity; the prime-field base fixes characteristic. -/
def IsPerfect (X : PrimeFieldScheme p) : Prop :=
  ∀ U : X.left.Opens, IsAffineOpen U →
    Function.Bijective (fun x : Γ(X.left, U) ↦ x ^ p)

/-- The actual universal perfection of a fixed ordinary prime-field scheme. -/
structure PerfectionModel (X : PrimeFieldScheme p) where
  scheme : PrimeFieldScheme p
  perfect : IsPerfect p scheme
  projection : scheme ⟶ X
  universal : ∀ Z : PrimeFieldScheme p, IsPerfect p Z →
    Function.Bijective (fun f : Z ⟶ scheme ↦ f ≫ projection)

end MathlibExt.AlgebraicGeometry.PerfectSchemeModels
