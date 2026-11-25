/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.QMFormalModule

/-!
# Tests for formal `O_D`-modules and QM formal completion
-/

@[expose] public section

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal

open scoped Quaternion

universe u

/-- A formal module over a fake elliptic curve unpacks to formal
coordinates. -/
private theorem exactSource {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ}
    {q : ℕ} [Fact q.Prime] {B : Type} [CommRing B]
    (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N B)
    (coord : ↥Λ → Zp2 q × Zp2 q) (X : FormalODModule q B)
    (h : E.IsFormalModuleOf coord X) :
    ∃ θ : AlgebraicGeometry.RelativeGroupLaw.FormalCoordinates E.f 2,
      E.IsFormalModuleVia coord X θ :=
  (CerednikDrinfeld.QM.FakeEllipticCurve.isFormalModuleOf_iff E coord X).mp h

/-- The identity series is a law homomorphism for every formal group. -/
example {B : Type u} [CommRing B] (F : MvFormalGroup 2 B) :
    IsLawHom F F (Series.id B) :=
  IsLawHom.id F

/-- Kernel degree of the action of `p` is the height predicate. -/
example {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
    (X : FormalODModule p B) (h : ℕ) :
    X.HasHeight h ↔ FormalODModule.HasKernelOfDegree (X.act (p : Zp2 p)) (p ^ h) :=
  Iff.rfl

open CategoryTheory AlgebraicGeometry in
/-- Formal coordinates are injective on points infinitesimal along a
square-zero ideal, so the constant family at the identity point is not a
system of formal coordinates over a nontrivial ring. -/
example {B : Type} [CommRing B] [Nontrivial B] {A : Scheme.{0}}
    {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
    (F : MvFormalGroup 1 B) :
    ¬ L.IsFormalCoordinates F (fun _ _ _ _ => L.one _) := by
  rintro ⟨-, h⟩
  have hJ : Ideal.span {(DualNumber.eps : DualNumber B)} ^ (1 + 1) = ⊥ := by
    rw [Ideal.span_singleton_pow, pow_two, DualNumber.eps_mul_eps,
      Ideal.span_singleton_eq_bot]
  have hst := (h (DualNumber B) _ 1 hJ).2.1 0 (fun _ => DualNumber.eps)
    (fun _ => Ideal.zero_mem _) (fun _ => Ideal.mem_span_singleton_self _) rfl
  simpa using congrArg (fun s => TrivSqZeroExt.snd (s 0)) hst

/-- The order acts on a fake elliptic curve as a unital monoid action by
endomorphisms, with no membership side conditions. -/
example {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) :
    ↥Λ →* CategoryTheory.End E.A where
  toFun x := .of (E.act x)
  map_one' := CategoryTheory.End.ext (by simp [E.act_one])
  map_mul' x y := CategoryTheory.End.ext (by simp [E.act_mul])

open CategoryTheory in
/-- Hecke neighbours are taken at a prime, and both composites are the
action of that prime. -/
example {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N ℓ : ℕ} {S : Type} [CommRing S]
    {E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S}
    (h : CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour ℓ E E') :
    ℓ.Prime ∧ ∃ (φ : E.A ⟶ E'.A) (ψ : E'.A ⟶ E.A),
      φ ≫ ψ = E.act (ℓ : ↥Λ) ∧ ψ ≫ φ = E'.act (ℓ : ↥Λ) := by
  obtain ⟨hℓ, φ, -, ψ, -, -, -, -, -, -, -, hc, -, -⟩ := h
  exact ⟨hℓ, φ, ψ, hc⟩

/-- `0`, `1` and the composite `4` give no Hecke neighbours. -/
example {a b : ℚ} {Λ : Subring ℍ[ℚ, a, b]} {N : ℕ} {S : Type} [CommRing S]
    (E E' : CerednikDrinfeld.QM.FakeEllipticCurve Λ N S) :
    ¬ CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour 0 E E' ∧
      ¬ CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour 1 E E' ∧
      ¬ CerednikDrinfeld.QM.FakeEllipticCurve.HeckeNeighbour 4 E E' :=
  ⟨fun h => Nat.not_prime_zero h.1, fun h => Nat.not_prime_one h.1, fun h => by
    have := h.1.eq_one_or_self_of_dvd 2 ⟨2, rfl⟩
    omega⟩

/-- An isogeny of formal modules is an `O_D`-homomorphism: it commutes
with the action and with `varpi`. -/
example {p : ℕ} [Fact p.Prime] {B : Type u} [CommRing B]
    {X Y : FormalODModule p B} {φ : Series B} {h : ℕ}
    (hφ : FormalODModule.IsIsogenyOfHeight X Y φ h) :
    (∀ a, φ.comp (X.act a) = (Y.act a).comp φ) ∧
      φ.comp X.varpi = Y.varpi.comp φ :=
  hφ.1.2
