/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum

@[expose] public section

open scoped TensorProduct
open LT.LatticeTree

/-- Source-faithful consumer for the even-translate relation, with the
original binders. -/
theorem exactSource_isTranslateEven_iff
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (g : GL (Fin 2) K) (c : Kˣ)
    (Q Q' : CerednikDrinfeld.FormalOmega.DrinfeldDatum (K := K) π B) :
    CerednikDrinfeld.FormalOmega.DrinfeldDatum.IsTranslateEven g c Q Q' ↔
      Nonempty (CerednikDrinfeld.FormalOmega.DrinfeldDatum.TranslateEven
        g c Q Q') :=
  CerednikDrinfeld.FormalOmega.DrinfeldDatum.isTranslateEven_iff g c Q Q'

/-- The standard lattice is a full lattice, and homothety is reflexive;
these are the boundary cases for the lattice carriers. -/
example {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] :
    LT.LatticeTree.IsFullLattice (LT.LatticeTree.stdLattice R K) :=
  LT.LatticeTree.isFullLattice_stdLattice

example {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
    (L : Submodule R (Fin 2 → K)) : LT.LatticeTree.Homothetic L L :=
  LT.LatticeTree.Homothetic.refl L
