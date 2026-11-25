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

end RelativeGroupLawTest
