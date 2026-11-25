/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeGroupLawEtale

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace RelativeGroupLawEtaleTest

/-- Source-shaped consumer with the original binders: commutativity as a hypothesis on the
multiplication of points, smoothness of relative dimension `d`, and `n` a unit in the local
base ring give an étale multiplication by `n`. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) :=
  G.etale_schemeNsmul_of_isUnit (fun t x y => hcomm t x y) d n hn

/-- Source-shaped consumer of the formally unramified step, which needs no smoothness. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ) (hn : IsUnit (n : R)) :
    FormallyUnramified (G.schemeNsmul n) :=
  G.formallyUnramified_schemeNsmul_of_isUnit (fun t x y => hcomm t x y) n hn

/-- The statement is universe polymorphic: a consumer in a higher universe. -/
example {R : Type (u + 1)} [CommRing R] [IsLocalRing R] {A : Scheme.{u + 1}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (hc : G.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : IsUnit (n : R)) :
    Etale (G.schemeNsmul n) :=
  G.etale_schemeNsmul_of_isUnit hc d n hn

/-- Over a field of characteristic zero every positive `n` is a unit, so multiplication by
`n` on a smooth commutative group law over the field is étale. -/
example {K : Type u} [Field K] [CharZero K] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of K)} (G : RelativeGroupLaw K f) (hc : G.IsCommutative)
    (d : ℕ) [SmoothOfRelativeDimension d f] (n : ℕ) (hn : n ≠ 0) :
    Etale (G.schemeNsmul n) :=
  G.etale_schemeNsmul_of_isUnit hc d n (by simpa using hn)

/-- Infinitesimal `n`-torsion points reducing to the identity are trivial when `n` is a unit. -/
example {R : Type u} [CommRing R] [IsLocalRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) {n : ℕ}
    (hn : IsUnit (n : R)) {R' S' : CommRingCat.{u}} (φ : R' ⟶ S')
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ.hom ^ 2 = ⊥)
    (t : Spec R' ⟶ Spec (CommRingCat.of R)) (k : SchemeHomOver t f)
    (hk : Over.homMk (U := Over.mk (Spec.map φ ≫ t)) (V := Over.mk t) (Spec.map φ) rfl ≫ k =
      G.one (Spec.map φ ≫ t))
    (hnk : G.nsmul t n k = G.one t) :
    k = G.one t :=
  G.eq_one_of_sqZero_of_nsmul_eq_one_of_isUnit hn φ hφ hker t k hk hnk

end RelativeGroupLawEtaleTest
