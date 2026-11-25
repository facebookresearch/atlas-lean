/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.FormalOmega.DrinfeldDatum
public import MathlibExt.AlgebraicGeometry.FormalOmega.QuadrupleExists

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
    Submodule.IsFullLattice K (LT.LatticeTree.stdLattice R K) :=
  LT.LatticeTree.isFullLattice_stdLattice

example {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K]
    (L : Submodule R (Fin 2 → K)) : LT.LatticeTree.Homothetic L L :=
  LT.LatticeTree.Homothetic.refl L

/-- Source-faithful consumer for the existence of Drinfeld quadruples, with the original
binders. -/
theorem exactSource_exists_drinfeldDatum_isQuadrupleOf
    {𝒪 : Type} [CommRing 𝒪] [IsDomain 𝒪] [IsDiscreteValuationRing 𝒪] {K : Type} [Field K]
    [Algebra 𝒪 K] [IsFractionRing 𝒪 K] {π : 𝒪} (hπ : Irreducible π)
    (hfin : Finite (𝒪 ⧸ Ideal.span {π}))
    {B : Type} [CommRing B] [Algebra 𝒪 B] (hB : IsNilpotent (algebraMap 𝒪 B π))
    (d : CerednikDrinfeld.FormalOmega.DeligneDatum (K := K) π B) :
    ∃ Q : CerednikDrinfeld.FormalOmega.DrinfeldDatum (K := K) π B, Q.IsQuadrupleOf d :=
  CerednikDrinfeld.FormalOmega.DeligneDatum.exists_drinfeldDatum_isQuadrupleOf hπ hfin hB d

/-- Base change of a Deligne datum along the identity is the identity, and along a composite it
is the iterated base change: the functor laws behind `IsQuadrupleOf`. -/
example {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B : Type} [CommRing B] [Algebra 𝒪 B]
    (d : CerednikDrinfeld.FormalOmega.DeligneDatum (K := K) π B) :
    d.map π (AlgHom.id 𝒪 B) = d :=
  CerednikDrinfeld.FormalOmega.DeligneDatum.map_id π d

example {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π : 𝒪}
    {B B' C : Type} [CommRing B] [Algebra 𝒪 B] [CommRing B'] [Algebra 𝒪 B'] [CommRing C]
    [Algebra 𝒪 C] (f : B →ₐ[𝒪] B') (g : B' →ₐ[𝒪] C)
    (d : CerednikDrinfeld.FormalOmega.DeligneDatum (K := K) π B) :
    d.map π (g.comp f) = (d.map π f).map π g :=
  CerednikDrinfeld.FormalOmega.DeligneDatum.map_comp π f g d
