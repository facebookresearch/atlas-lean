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

/-- Source-shaped consumer with the original binders for a commutative
relative group law over a field, plus finiteness of the kernel: the degree of
multiplication by `n` is the rank of its kernel at the closed point. -/
example {K : Type u} [Field K] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of K)) (L : RelativeGroupLaw K f)
    (hc : L.IsCommutative) (n : ℕ) [IsFinite (L.schemeKerStr hc n)] :
    L.endDegree (L.nsmulEnd hc n) =
      (L.schemeKerStr hc n).finrank (IsLocalRing.closedPoint K) :=
  L.endDegree_nsmulEnd hc n

/-- Multiplication by `n` on a commutative law is a group homomorphism on
points: composing with it multiplies by `n` and preserves the group law. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : Over.mk t ⟶ Over.mk f) :
    L.nsmul t n (L.mul t x y) = L.mul t (L.nsmul t n x) (L.nsmul t n y) := by
  have h := (L.nsmulEnd hc n).map_mul t x y
  simp only [RelativeGroupLaw.nsmulEnd_hom, RelativeGroupLaw.comp_nsmul_idPoint] at h
  exact h

example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : Over.mk t ⟶ Over.mk f) :
    x ≫ (L.nsmulEnd hc n).hom = L.nsmul t n x := by
  rw [RelativeGroupLaw.nsmulEnd_hom, RelativeGroupLaw.comp_nsmul_idPoint]

/-- An endomorphism of the law fixes the identity point, so the identity
section lies in its kernel. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (β : L.End) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) : L.one t ≫ β.hom = L.one t :=
  β.map_one t

/-- Kernel identification over any commutative base ring: the kernel of
multiplication by `n`, as an endomorphism, is `schemeKer`, and its underlying
scheme map is `schemeNsmul`. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ) :
    L.endKer (L.nsmulEnd hc n) = L.schemeKer hc n :=
  L.endKer_nsmulEnd hc n

example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (hc : L.IsCommutative) (n : ℕ) :
    (L.nsmulEnd hc n).hom.left = L.schemeNsmul n :=
  L.nsmulEnd_hom_left hc n

/-- Over any commutative base ring, the kernel inclusion followed by the
endomorphism factors through the identity section, and the kernel of the
identity endomorphism maps isomorphically to the base. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) (β : L.End) :
    L.endKerι β ≫ β.hom.left =
      L.endKerStr β ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).left :=
  L.endKerι_comp β

example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) : IsIso (L.endKerStr L.idEnd) :=
  inferInstance

/-- The degree is the rank of a finite kernel, and `0` for a kernel that is
not finite over the base. -/
example {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (β : L.End) [IsFinite (L.endKerStr β)] :
    L.endDegree β = (L.endKerStr β).finrank (IsLocalRing.closedPoint K) :=
  L.endDegree_of_isFinite β

example {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (β : L.End) (h : ¬ IsFinite (L.endKerStr β)) :
    L.endDegree β = 0 :=
  L.endDegree_of_not_isFinite β h

/-- The degree of the identity endomorphism is `1`, in two universes. -/
example {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) : L.endDegree L.idEnd = 1 :=
  L.endDegree_idEnd

example {K : Type v} [Field K] {A : Scheme.{v}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) : L.endDegree L.idEnd = 1 :=
  L.endDegree_idEnd

/-- Boundary examples: the `0`-fold sum of a point is the identity and the
`1`-fold sum is the point itself. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ Over.mk f) : L.nsmul t 0 x = L.one t :=
  L.nsmul_zero t x

example {R : Type u} [CommRing R] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of R))
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ Over.mk f) : L.nsmul t 1 x = x :=
  L.nsmul_one t x

end RelativeGroupLawEndDegreeTest
