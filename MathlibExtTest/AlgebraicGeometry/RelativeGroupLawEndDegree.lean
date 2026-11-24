/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegree

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace RelativeGroupLawEndDegreeTest

/-- Source-shaped consumer: the degree of multiplication by `n`, stated
with the original binders for a commutative relative group law over a
field. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) (n : ℕ) :
    L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) = L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) :=
  rfl

/-- The degree of the identity endomorphism is `1`, in two universes. -/
example {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) : L.endDegree (RelativeGroupLaw.idEnd (f := f)) = 1 :=
  L.endDegree_idEnd

example {K : Type v} [Field K] {A : Scheme.{v}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) : L.endDegree (RelativeGroupLaw.idEnd (f := f)) = 1 :=
  L.endDegree_idEnd

/-- Boundary example: multiplication by `0` sends every point to the
identity, so the `0`-fold sum differs from the point in general only
through the group law; the kernel description still applies. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ Over.mk f) : L.nsmul t 0 x = L.one t :=
  L.nsmul_zero t x

example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ Over.mk f) : L.nsmul t 1 x = x :=
  L.nsmul_one t x

end RelativeGroupLawEndDegreeTest
