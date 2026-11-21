/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.HopfAlgebra.HopfKer

@[expose] public section

open scoped TensorProduct

namespace HopfAlgebra

universe u v w

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [Bialgebra R A]
  {B : Type w} [CommRing B] [Bialgebra R B]

/-- Consumer with the original binders: membership in the Hopf kernel is the
coaction fixed-point condition. -/
theorem exactSource_hopfKer (π : A →ₐc[R] B) (a : A) :
    a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R] 1 :=
  mem_hopfKer_iff π a

example (π : A →ₐc[R] B) : (1 : A) ∈ hopfKer π := one_mem _

example (π : A →ₐc[R] B) (a a' : A) :
    canMap π (a ⊗ₜ[R] a') = (a ⊗ₜ[R] (1 : B)) * coaction π a' :=
  canMap_tmul π a a'

example (π : A →ₐc[R] B) : canMap π (1 ⊗ₜ[R] (1 : A)) = 1 ⊗ₜ[R] (1 : B) :=
  canMap_tmul_one π 1

noncomputable example {R' : Type u} [CommRing R'] {A' : Type v} [CommRing A'] [HopfAlgebra R' A']
    {B' : Type w} [CommRing B'] [HopfAlgebra R' B'] (π : A' →ₐc[R'] B')
    [Coalgebra.IsCocomm R' A'] [Module.Flat R' A'] [Module.Flat R' B']
    [Module.Flat R' ↥(hopfKer π)] : HopfAlgebra R' ↥(hopfKer π) := inferInstance

example {R' : Type u} [CommRing R'] {A' : Type v} [CommRing A'] [HopfAlgebra R' A']
    {B' : Type w} [CommRing B'] [HopfAlgebra R' B'] (π : A' →ₐc[R'] B')
    [Coalgebra.IsCocomm R' A'] [Module.Flat R' A'] [Module.Flat R' B']
    [Module.Flat R' ↥(hopfKer π)] : Coalgebra.IsCocomm R' ↥(hopfKer π) := by infer_instance

example {R' : Type u} [CommRing R'] {A' : Type v} [CommRing A'] [HopfAlgebra R' A']
    {B' : Type w} [CommRing B'] [HopfAlgebra R' B'] (π : A' →ₐc[R'] B')
    [Coalgebra.IsCocomm R' A'] [Module.Flat R' A'] [Module.Flat R' B']
    [Module.Flat R' ↥(hopfKer π)] (s : ↥(hopfKer π)) :
    ((antipode R' s : ↥(hopfKer π)) : A') = antipode R' (s : A') :=
  HopfKerHopf.coe_antipode π s

/-- Higher-universe consumer: the same statement in a larger universe. -/
example {R' : Type (u + 1)} [CommRing R'] {A' : Type (v + 1)} [CommRing A']
    [Bialgebra R' A'] {B' : Type (w + 1)} [CommRing B'] [Bialgebra R' B']
    (π : A' →ₐc[R'] B') (a : A') :
    a ∈ hopfKer π ↔ coaction π a = a ⊗ₜ[R'] 1 :=
  mem_hopfKer_iff π a

example {H : Type v} [CommRing H] [HopfAlgebra R H] (I : Ideal H) [I.IsHopfIdeal R] :
    Function.Surjective (Bialgebra.Quotient.mkBialgHom (R := R) I) :=
  Ideal.Quotient.mk_surjective

example {H : Type v} [CommRing H] [HopfAlgebra R H] {I J : Ideal H}
    [I.IsHopfIdeal R] [J.IsHopfIdeal R] (h : I ≤ J) :
    Function.Surjective (quotientFactorBialgHom (R := R) h) :=
  quotientFactorBialgHom_surjective h

end HopfAlgebra
