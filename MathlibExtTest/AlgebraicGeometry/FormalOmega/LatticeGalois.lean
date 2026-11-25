/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.LatticeGalois

@[expose] public section

open scoped Matrix
open LT.LatticeTree

universe u

/-- Consumer with the original binders: the twisted action of an order-two automorphism iterates
to the norm. -/
private theorem exactSource {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    (δ : Matrix.GeneralLinearGroup (Fin 2) K) {σ : IntegralAut R K}
    (hσ : σ.comp σ = IntegralAut.refl R K) (L : Submodule R (Fin 2 → K)) :
    twistedLatticeMap δ σ (twistedLatticeMap δ σ L) = latticeMap (normTwo δ σ) L :=
  twistedLatticeMap_two_of_orderTwo δ hσ L

/-- Higher-universe consumer: integral automorphisms preserve full lattices. -/
example {R : Type (u + 1)} [CommRing R] {K : Type (u + 1)} [Field K] [Algebra R K]
    {L : Submodule R (Fin 2 → K)} (hL : Submodule.IsFullLattice K L) (σ : IntegralAut R K) :
    Submodule.IsFullLattice K (latticeGal σ L) :=
  IsFullLattice.gal hL σ

example (δ : Matrix.GeneralLinearGroup (Fin 2) ℂ) (L : Submodule ℂ (Fin 2 → ℂ)) :
    twistedLatticeMap δ conjAut (twistedLatticeMap δ conjAut L) =
      latticeMap (normTwo δ conjAut) L :=
  twistedLatticeMap_two_of_orderTwo δ conjAut_comp_conjAut L

/-- Boundary: the identity automorphism fixes every lattice, while complex conjugation moves the
line through `(1, i)`. -/
example : latticeGal (IntegralAut.refl ℂ ℂ) (Submodule.span ℂ {![1, Complex.I]}) =
      Submodule.span ℂ {![1, Complex.I]} ∧
    latticeGal conjAut (Submodule.span ℂ {![1, Complex.I]}) ≠
      Submodule.span ℂ {![1, Complex.I]} :=
  ⟨latticeGal_refl _, latticeGal_conj_line_ne⟩
