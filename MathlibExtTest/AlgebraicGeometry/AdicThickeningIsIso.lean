/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicThickeningIsIso

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem exactSource
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {Γ X : Scheme.{u}} (γ : Γ ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιΓ : Γ ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (hιΓ : IsClosedImmersion ιΓ)
    (hιΓγ : ιΓ ≫ ProjSpace.π R N = γ)
    (N' : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R))
    (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N' = f)
    (ψ : Γ ⟶ X) (hψ : ψ ≫ f = γ)
    (ψn : ∀ n : ℕ, adicThickening γ I n ⟶ adicThickening f I n)
    (hψn : ∀ n : ℕ, ψn n ≫ adicThickeningι f I n = adicThickeningι γ I n ≫ ψ)
    (hψn' : ∀ n : ℕ, ψn n ≫ adicThickeningToBase f I n = adicThickeningToBase γ I n)
    (hiso : ∀ n : ℕ, IsIso (ψn n)) :
    IsIso ψ :=
  AlgebraicGeometry.isIso_of_forall_isIso_adicThickening_of_isAdicComplete_of_isClosedImmersion_proj
    I γ f N ιΓ hιΓ hιΓγ N' ιX hιX hιXf ψ hψ ψn hψn hψn' hiso
