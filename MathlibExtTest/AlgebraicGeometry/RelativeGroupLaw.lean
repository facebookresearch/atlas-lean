/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeGroupLaw

@[expose] public section

open CategoryTheory CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry

universe u

namespace RelativeGroupLawTest

/-- Consumer with the original binders. -/
theorem exactSource {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (a b : Over.mk t ⟶ Over.mk f),
        lift a b ≫ g.mul = G.mul t a b) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
        toUnit (Over.mk t) ≫ g.one = G.one t) ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (a : Over.mk t ⟶ Over.mk f),
        a ≫ g.inv = G.inv t a) :=
  G.exists_grpObj_eq

/-- The same consumer in a higher universe. -/
theorem exactSource_univ1 {R : Type 1} [CommRing R] {A : Scheme.{1}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    ∃ g : GrpObj (Over.mk f),
      (∀ {T : Scheme.{1}} (t : T ⟶ Spec (CommRingCat.of R))
        (a b : Over.mk t ⟶ Over.mk f),
        lift a b ≫ g.mul = G.mul t a b) ∧
      (∀ {T : Scheme.{1}} (t : T ⟶ Spec (CommRingCat.of R)),
        toUnit (Over.mk t) ≫ g.one = G.one t) ∧
      (∀ {T : Scheme.{1}} (t : T ⟶ Spec (CommRingCat.of R))
        (a : Over.mk t ⟶ Over.mk f),
        a ≫ g.inv = G.inv t a) :=
  G.exists_grpObj_eq

/-- The point-group instance is usable through generic group notation:
with `G.pointGroup t` installed, the usual group laws hold for points over
a test scheme. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : Over.mk t ⟶ Over.mk f) :
    G.mul t x (G.inv t x) = G.one t ∧ G.mul t x (G.one t) = x := by
  letI := G.pointGroup t
  have h₁ : x * x⁻¹ = 1 := mul_inv_cancel x
  have h₂ : x * 1 = x := mul_one x
  exact ⟨h₁, h₂⟩

/-- Reindexing along a morphism of test schemes preserves the group
operations of the point groups. -/
example {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : Over.mk t ⟶ Over.mk f) :
    Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ G.mul t x y =
      G.mul t' (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ x) (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ y) := by
  letI := G.pointGroup t
  letI := G.pointGroup t'
  have h : Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ (x * y) =
      (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ x) * (Over.homMk (U := Over.mk t') (V := Over.mk t) ψ hψ ≫ y) :=
    G.mul_natural t t' ψ hψ x y
  exact h

section BaseChange

variable {R : Type u} [CommRing R] {R' : Type u} [CommRing R']
  (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) {A : Scheme.{u}}
  {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {T : Scheme.{u}}
  {t' : T ⟶ Spec (CommRingCat.of R')}

/-- Base change consumer with the original binders: a relative group law over
`Spec R` gives one on the base change along `ι : Spec R' ⟶ Spec R`. -/
example : Nonempty (RelativeGroupLaw R' (RelativeGroupLaw.baseChangeStr ι f)) :=
  ⟨G.baseChange ι⟩

/-- The image of a point of the base change over the original base is its
composite with the first projection. -/
example (x : Over.mk t' ⟶ Over.mk (RelativeGroupLaw.baseChangeStr ι f)) :
    (RelativeGroupLaw.baseChangePointToBase ι x).left = x.left ≫ Limits.pullback.fst f ι :=
  rfl

/-- Points of the base change are determined by their images over the
original base. -/
example (x y : Over.mk t' ⟶ Over.mk (RelativeGroupLaw.baseChangeStr ι f))
    (h : RelativeGroupLaw.baseChangePointToBase ι x =
      RelativeGroupLaw.baseChangePointToBase ι y) : x = y := by
  rw [← RelativeGroupLaw.baseChangePointOfBase_toBase ι x, h,
    RelativeGroupLaw.baseChangePointOfBase_toBase]

/-- The base-changed law multiplies points by multiplying their images over
the original base. -/
example (x y : Over.mk t' ⟶ Over.mk (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).mul t' x y) =
      G.mul (t' ≫ ι) (RelativeGroupLaw.baseChangePointToBase ι x)
        (RelativeGroupLaw.baseChangePointToBase ι y) :=
  RelativeGroupLaw.baseChangePointToBase_ofBase ι _

/-- The identity of the base-changed law maps to the identity of the original
law. -/
example : RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).one t') =
    G.one (t' ≫ ι) :=
  RelativeGroupLaw.baseChangePointToBase_ofBase ι _

/-- The inverse of the base-changed law maps to the inverse of the original
law. -/
example (x : Over.mk t' ⟶ Over.mk (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).inv t' x) =
      G.inv (t' ≫ ι) (RelativeGroupLaw.baseChangePointToBase ι x) :=
  RelativeGroupLaw.baseChangePointToBase_ofBase ι _

/-- The base-changed law gives a group object over the new base. -/
example : Nonempty (GrpObj (Over.mk (RelativeGroupLaw.baseChangeStr ι f))) :=
  ⟨(G.baseChange ι).grpObjOverMk⟩

end BaseChange

/-- The base change consumer in a higher universe. -/
example {R : Type 1} [CommRing R] {R' : Type 1} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) {A : Scheme.{1}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) :
    Nonempty (RelativeGroupLaw R' (RelativeGroupLaw.baseChangeStr ι f)) :=
  ⟨G.baseChange ι⟩

end RelativeGroupLawTest
