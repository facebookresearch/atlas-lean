/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.BoundedCoherent

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.BoundedCoherent

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

-- A coherent module sheaf has finitely presented sections on every affine open; finite
-- generation alone would not give this over a non-noetherian ring.
example {X : Scheme.{u}} (F : X.Modules) (hF : coherentModule F) (U : X.Opens)
    (hU : IsAffineOpen U) : Module.FinitePresentation Γ(X, U) Γ(F, U) := by
  obtain ⟨hfin, hfp⟩ := hF.2 U hU
  have := hfp ⊤ Module.Finite.fg_top
  exact Module.FinitePresentation.of_equiv (Submodule.topEquiv (R := Γ(X, U)))

-- Bounded coherent objects have finitely many nonzero cohomology sheaves.
example {X : Scheme.{u}} (M : DerivedCategory X.Modules) (hM : boundedCoherent X M) :
    {n : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj M)}.Finite :=
  hM.2

end MathlibExt.AlgebraicGeometry.BoundedCoherent
