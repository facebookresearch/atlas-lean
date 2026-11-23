/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QMCoarseModuli

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped Quaternion

universe u

namespace QMCoarseModuliTest

/-- Consumer with the original binders for coarse moduli. -/
theorem exactSource {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ)
    {B : Type} [CommRing B] (X : Scheme.{0})
    (πX : X ⟶ Spec (CommRingCat.of B))
    (pt : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      CerednikDrinfeld.QM.FakeEllipticCurve Λ N S →
      SchemeHomOver s πX) :
    CerednikDrinfeld.QM.IsCoarseModuli Λ N X πX pt →
    ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
      (E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S),
      CerednikDrinfeld.QM.FakeEllipticCurve.Iso E E' →
      pt S s E = pt S s E' :=
  fun h => (CerednikDrinfeld.QM.isCoarseModuli_iff Λ N X πX pt).mp h |>.1

/-- Full-level isomorphisms are characterized by a named isomorphism. -/
theorem exactSourceFullLevel {a b : ℚ}
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
    {m : ℕ}
    (u v : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N m S) :
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.Iso u v ↔
      ∃ (e : u.1.A ≅ v.1.A) (he : e.hom ≫ v.1.f = u.1.f),
        CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.IsoVia u v
          e he :=
  CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.iso_iff_exists_via
    u v

/-- Boundary: a twist action is exactly its six-field characterization;
no label conclusion is asserted from the other fields alone. -/
theorem exactSourceTwist {a b : ℚ} (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (N m : ℕ) {B : Type} [CommRing B] (M : Scheme.{0})
    (πM : M ⟶ Spec (CommRingCat.of B))
    (ptF : ∀ (S : Type) [CommRing S]
      (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
      CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N m S →
      SchemeHomOver s πM) (G : Type) [Group G] (ρ : G →* Aut M)
    (χ : G → ↥Λ) :
    CerednikDrinfeld.QM.IsLevelTwistAction Λ N m M πM ptF G ρ χ →
    ∀ g : G, (ρ g).asIso.hom ≫ πM = πM :=
  fun h =>
    (CerednikDrinfeld.QM.isLevelTwistAction_iff Λ N m M πM ptF G ρ χ).mp
      h |>.1

end QMCoarseModuliTest
