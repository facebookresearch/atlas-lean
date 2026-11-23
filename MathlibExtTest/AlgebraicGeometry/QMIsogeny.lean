/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QMIsogeny

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

open scoped Quaternion

universe u

namespace QMIsogenyTest

/-- Consumer with the original binders for isogeny pairs. -/
theorem exactSource {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S] (d : ℕ)
    (E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S)
    (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A) :
    CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPair d E E' φ ψ ↔
      ∃ (hφ : φ ≫ E'.f = E.f) (hψ : ψ ≫ E.f = E'.f),
        CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogenyPairVia d E E'
          φ hφ ψ hψ :=
  CerednikDrinfeld.QM.FakeEllipticCurve.isIsogenyPair_iff_exists_via d E E'
    φ ψ

/-- The identity is a `1`-isogeny, and isogeny is symmetric. -/
example {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S]
    (E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S)
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogeny 3 E E') :
    CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogeny 1 E E ∧
      CerednikDrinfeld.QM.FakeEllipticCurve.IsIsogeny 3 E' E :=
  ⟨CerednikDrinfeld.QM.FakeEllipticCurve.isIsogeny_one_refl E, h.symm⟩

/-- The lattice action of a fake elliptic curve is characterized by its
underlying action map. -/
example {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    {S : Type u} [CommRing S]
    (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) :
    (CerednikDrinfeld.QM.LatticeAction.ofFakeEllipticCurve E).act = E.act :=
  CerednikDrinfeld.QM.LatticeAction.ofFakeEllipticCurve_act E

/-- Boundary: without the group-law compatibility and level preservation,
no representability conclusion is asserted; the predicate is exactly the
four-part characterization in `representsOn_iff`. -/
theorem exactSourceRepresents {a b : ℚ}
    {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (r d : ℕ) (E A : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S)
    {X : Scheme.{0}} (ξ : X ⟶ Spec (CommRingCat.of S))
    (pt : CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.PtFamily r d
      E A ξ) :
    CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.RepresentsOn r d E A
        ξ pt ↔
      (CerednikDrinfeld.QM.FakeEllipticCurve.IsogenyPair.RepresentsOn r d
        E A ξ pt) :=
  Iff.rfl

end QMIsogenyTest
