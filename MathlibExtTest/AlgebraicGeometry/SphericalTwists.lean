/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.SphericalTwists

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.SphericalTwists

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open FourierMukai

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
example {X : Scheme.{u}} (M : D X) (hM : boundedCoherent X M) :
    {n : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor X.Modules n).obj M)}.Finite :=
  hM.2

-- The kernel is the cone of the restriction `𝒪_{X×X} → Δ_* 𝒪_X`, in `D(X×X)`.
noncomputable example (k : Type u) [Field k] (X : Over (Spec (.of k))) :
    D (pullback X.hom X.hom) :=
  kernel X

-- The diagonal is a section of both projections.
example (k : Type u) [Field k] (X : Over (Spec (.of k))) :
    diagonal X.hom ≫ pullback.fst X.hom X.hom = 𝟙 X.left := by
  simp [diagonal]

end MathlibExt.AlgebraicGeometry.SphericalTwists
