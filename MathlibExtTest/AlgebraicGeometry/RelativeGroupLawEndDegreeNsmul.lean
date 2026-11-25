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

/-- Over any commutative base ring, multiplication by one on a commutative law
is the identity endomorphism, so its underlying scheme map is the identity of
`A`. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) : L.nsmulEnd hc 1 = L.idEnd :=
  L.nsmulEnd_one hc

example {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) : (L.nsmulEnd hc 1).hom.left = 𝟙 A := by
  rw [L.nsmulEnd_one hc]
  exact L.idEnd_left

/-- The point-level form is the general `nsmul_one` at the identity point. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) (L : RelativeGroupLaw R f)
    (hc : L.IsCommutative) : (L.nsmulEnd hc 1).hom = RelativeGroupLaw.idPoint := by
  rw [RelativeGroupLaw.nsmulEnd_hom]
  exact L.nsmul_one f RelativeGroupLaw.idPoint

/-- Over a field, multiplication by one on a commutative law has degree `1`,
in two universes. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) :
    L.endDegree (L.nsmulEnd hc 1) = 1 :=
  L.endDegree_nsmulEnd_one hc

example {K : Type v} [Field K] {A : Scheme.{v}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) :
    L.endDegree (L.nsmulEnd hc 1) = 1 :=
  L.endDegree_nsmulEnd_one hc

end RelativeGroupLawEndDegreeNsmulTest
