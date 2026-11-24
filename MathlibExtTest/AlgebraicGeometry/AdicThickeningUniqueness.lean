/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.AdicThickeningUniqueness

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem exactSource
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (g : Y ⟶ Spec (CommRingCat.of R))
    (N : ℕ) (ιX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
    (hιX : IsClosedImmersion ιX)
    (hιXf : ιX ≫ ProjSpace.π R N = f)
    (N' : ℕ) (ιY : Y ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N' + 1)) R))
    (hιY : IsClosedImmersion ιY)
    (hιYg : ιY ≫ ProjSpace.π R N' = g)
    (ψ ψ' : X ⟶ Y) (hψ : ψ ≫ g = f) (hψ' : ψ' ≫ g = f)
    (h : ∀ n : ℕ, adicThickeningι f I n ≫ ψ = adicThickeningι f I n ≫ ψ') :
    ψ = ψ' :=
  AlgebraicGeometry.eq_of_forall_adicThickening_comp_eq_of_isAdicComplete_of_isClosedImmersion_proj
    I f g N ιX hιX hιXf N' ιY hιY hιYg ψ ψ' hψ hψ' h

theorem exactSource_separated
    {H S T : Scheme.{u}} (q : H ⟶ S) [IsSeparated q] (t : T ⟶ S) (u v : T ⟶ H)
    (hu : u ≫ q = t) (hv : v ≫ q = t) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ T), IsClosedImmersion j ∧
      ∀ {T' : Scheme.{u}} (ψ : T' ⟶ T), ψ ≫ u = ψ ≫ v ↔ ∃ ψ' : T' ⟶ Z, ψ' ≫ j = ψ :=
  AlgebraicGeometry.exists_isClosedImmersion_iff_comp_eq_of_isSeparated q t u v hu hv
