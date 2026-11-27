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
theorem exactSource {a b : ℚ} (Λ : Subring ℍ[ℚ, a, b]) (N : ℕ)
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
    {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]
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
theorem exactSourceTwist {a b : ℚ} (Λ : Subring ℍ[ℚ, a, b])
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

section TwistAction

variable {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N m : ℕ} {B : Type} [CommRing B]
  {M : Scheme.{0}} {πM : M ⟶ Spec (CommRingCat.of B)}
  {ptF : ∀ (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B)),
    CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N m S →
    SchemeHomOver s πM} {G : Type} [Group G] {ρ : G →* Aut M} {χ : G → ↥Λ}

/-- The twist equation, applied twice: twisting by the label of `g` and
then by the label of `g'` moves points by `ρ g` and then by `ρ g'`. -/
theorem twist_twist
    (h : CerednikDrinfeld.QM.IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (g g' : G) (S : Type) [CommRing S]
    (s : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of B))
    (u v w : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel Λ N m S)
    (huv : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.IsTwist (χ g) u v)
    (hvw : CerednikDrinfeld.QM.FakeEllipticCurve.WithFullLevel.IsTwist (χ g') v w) :
    (ptF S s w).left = (ptF S s u).left ≫ (ρ g).asIso.hom ≫ (ρ g').asIso.hom := by
  rw [h.twist g' S s v w hvw, h.twist g S s u v huv, Category.assoc]

/-- Label multiplication modulo `mΛ`: if `χ g * χ g'` is congruent to the
label of `g''` modulo `mΛ`, then `g * g' = g''`. -/
theorem mul_eq_of_label_mul_sub_mem
    (h : CerednikDrinfeld.QM.IsLevelTwistAction Λ N m M πM ptF G ρ χ)
    (g g' g'' : G)
    (hc : ∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) * (χ g' : ℍ[ℚ, a, b]) -
      (χ g'' : ℍ[ℚ, a, b]) = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    g * g' = g'' := by
  obtain ⟨y₁, hy₁⟩ := h.label_mul g g'
  obtain ⟨y₂, hy₂⟩ := hc
  refine h.label_injective (g * g') g'' ⟨y₁ + y₂, ?_⟩
  rw [Subring.coe_add, smul_add, ← hy₁, ← hy₂]
  exact (sub_add_sub_cancel _ _ _).symm

/-- The label of the identity is `1` modulo `mΛ`, so an element whose label
is `1` modulo `mΛ` is the identity. -/
theorem eq_one_of_label_sub_one_mem
    (h : CerednikDrinfeld.QM.IsLevelTwistAction Λ N m M πM ptF G ρ χ) (g : G)
    (hg : ∃ y : ↥Λ, (χ g : ℍ[ℚ, a, b]) - 1 = (m : ℚ) • (y : ℍ[ℚ, a, b])) :
    g = 1 := by
  obtain ⟨y₁, hy₁⟩ := hg
  obtain ⟨y₂, hy₂⟩ := h.label_one
  refine h.label_injective g 1 ⟨y₁ - y₂, ?_⟩
  rw [AddSubgroupClass.coe_sub, smul_sub, ← hy₁, ← hy₂]
  exact (sub_sub_sub_cancel_right _ _ _).symm

end TwistAction

section Scalar

variable {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {S : Type u} [CommRing S]

/-- At `ℓ = 1` the two maps of a level isogeny are mutually inverse: their
composites are the action of `1 ∈ Λ`, which is the identity. -/
theorem isLevelIsogenyVia_one
    {u : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel Λ N 1 S}
    {d : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S} {φ : u.1.A ⟶ d.A}
    {hφ : φ ≫ d.f = u.1.f} {ψ : d.A ⟶ u.1.A} {hψ : ψ ≫ u.1.f = d.f}
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.IsLevelIsogenyVia 1 u d φ hφ ψ hψ) :
    φ ≫ ψ = 𝟙 u.1.A ∧ ψ ≫ φ = 𝟙 d.A := by
  obtain ⟨-, -, -, -, ⟨h₁, h₂⟩, -, -⟩ := h
  rw [h₁, h₂, Nat.cast_one, u.1.act_one, d.act_one]
  exact ⟨rfl, rfl⟩

/-- A level isogeny at `ℓ = 1` gives mutually inverse maps. -/
theorem isLevelIsogeny_one
    {u : CerednikDrinfeld.QM.FakeEllipticCurve.WithExtraLevel Λ N 1 S}
    {d : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S}
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.IsLevelIsogeny 1 u d) :
    ∃ (φ : u.1.A ⟶ d.A) (ψ : d.A ⟶ u.1.A), φ ≫ ψ = 𝟙 u.1.A ∧ ψ ≫ φ = 𝟙 d.A := by
  obtain ⟨φ, hφ, ψ, hψ, hv⟩ :=
    (CerednikDrinfeld.QM.FakeEllipticCurve.isLevelIsogeny_iff_exists_via 1 u d).mp h
  exact ⟨φ, ψ, isLevelIsogenyVia_one hv⟩

/-- At `r = 1` the two maps of an Atkin--Lehner quotient are mutually
inverse: their composites are the action of `1 ∈ Λ`. -/
theorem isAtkinLehnerQuotientVia_one
    {E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S} {φ : E.A ⟶ E'.A}
    {hφ : φ ≫ E'.f = E.f} {ψ : E'.A ⟶ E.A} {hψ : ψ ≫ E.f = E'.f}
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.IsAtkinLehnerQuotientVia 1 E E'
      φ hφ ψ hψ) :
    φ ≫ ψ = 𝟙 E.A ∧ ψ ≫ φ = 𝟙 E'.A := by
  obtain ⟨-, -, -, -, ⟨h₁, h₂⟩, -, -⟩ := h
  rw [h₁, h₂, Nat.cast_one, E.act_one, E'.act_one]
  exact ⟨rfl, rfl⟩

/-- An Atkin--Lehner quotient at `r = 1` gives mutually inverse maps. -/
theorem isAtkinLehnerQuotient_one
    {E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S}
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.IsAtkinLehnerQuotient 1 E E') :
    ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A), φ ≫ ψ = 𝟙 E.A ∧ ψ ≫ φ = 𝟙 E'.A := by
  obtain ⟨φ, hφ, ψ, hψ, hv⟩ :=
    (CerednikDrinfeld.QM.FakeEllipticCurve.isAtkinLehnerQuotient_iff_exists_via
      1 E E').mp h
  exact ⟨φ, ψ, isAtkinLehnerQuotientVia_one hv⟩

end Scalar

end QMCoarseModuliTest
