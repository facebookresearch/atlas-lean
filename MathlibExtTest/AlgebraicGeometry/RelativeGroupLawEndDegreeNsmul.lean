/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEndDegreeNsmul

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace RelativeGroupLawEndDegreeNsmulTest

/-- Source-shaped consumer with the original binders, at `n = 1`, on a
commutative law. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) (g : ℕ) :
    L.endDegree (L.nsmulEnd hc 1) = 1 ^ (2 * g) :=
  L.endDegree_nsmulEnd_one_eq_pow hc g

/-- Higher-universe consumer. -/
example {K : Type v} [Field K] {A : Scheme.{v}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) (g : ℕ) :
    L.endDegree (L.nsmulEnd hc 1) = 1 ^ (2 * g) :=
  L.endDegree_nsmulEnd_one_eq_pow hc g

/-- Boundary example: at `g = 0` the formula gives `1`, the degree of
multiplication by one. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) :
    L.endDegree (L.nsmulEnd hc 1) = 1 := by
  rw [L.endDegree_nsmulEnd_one_eq_pow hc 0, pow_zero]

example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) :
    L.endDegree (L.nsmulEnd hc 1) = 1 :=
  L.endDegree_nsmulEnd_one hc

/-- Over any commutative base ring, multiplication by one is the identity
endomorphism, so its underlying scheme map is the identity of `A`. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) : L.nsmulEnd hc 1 = L.idEnd :=
  L.nsmulEnd_one hc

example {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) : (L.nsmulEnd hc 1).hom.left = 𝟙 A := by
  rw [L.nsmulEnd_one hc]
  exact L.idEnd_left

/-- The one-fold sum of the identity point is the identity point. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f) :
    L.nsmul f 1 RelativeGroupLaw.idPoint = RelativeGroupLaw.idPoint :=
  L.nsmul_one_idPoint

end RelativeGroupLawEndDegreeNsmulTest
