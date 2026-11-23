/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.DedekindDomain.UnramifiedIdealDescent
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

public section

namespace UnramifiedIdealDescentTest

variable (R K L S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Field K] [Field L] [IsDedekindDomain R]
  [Algebra R K] [IsFractionRing R K] [Algebra S L]
  [Algebra K L] [Algebra R L] [IsScalarTower R S L]
  [IsScalarTower R K L] [IsIntegralClosure S R L]
  [FiniteDimensional K L] [IsGalois K L] [Algebra.Unramified R S]

/-- Exact R2437–2439 consumer, with the source's arbitrary four type universes. -/
theorem source_contract (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I :=
  Ideal.map_comap_eq_of_unramified_of_galois_invariant R K L S I hI

/-- The invariant-principal-ideal interface used at R2644–2646. -/
theorem principal_contraction (β : S)
    (hβ : ∀ σ : L ≃ₐ[K] L,
      (Ideal.span {β}).comap (galRestrict R K L S σ) = Ideal.span {β}) :
    ∃ J : Ideal R, J.map (algebraMap R S) = Ideal.span {β} := by
  exact ⟨(Ideal.span {β}).comap (algebraMap R S),
    source_contract R K L S _ hβ⟩

include K L

/-- Zero exercises the separate empty-factor branch in the public theorem. -/
theorem zero_boundary :
    ((⊥ : Ideal S).comap (algebraMap R S)).map (algebraMap R S) = ⊥ := by
  apply source_contract R K L S
  intro σ
  exact Ideal.comap_bot_of_injective _ (galRestrict R K L S σ).injective

/-- The unit ideal has empty factor support without being zero. -/
theorem unit_boundary :
    ((⊤ : Ideal S).comap (algebraMap R S)).map (algebraMap R S) = ⊤ := by
  apply source_contract R K L S
  intro σ
  exact Ideal.comap_top

/-- A map-comap tautology cannot discharge the source's stronger direction. -/
theorem wrong_direction_control (I : Ideal S)
    (hI : ∀ σ : L ≃ₐ[K] L, I.comap (galRestrict R K L S σ) = I) :
    (I.comap (algebraMap R S)).map (algebraMap R S) = I := by
  fail_if_success
    exact Ideal.map_comap_map (algebraMap R S) (I.comap (algebraMap R S))
  exact source_contract R K L S I hI

end UnramifiedIdealDescentTest

noncomputable section

namespace UnramifiedIdealDescentTest.FiniteFieldFixture

open Polynomial UniqueFactorizationMonoid

attribute [local instance] Polynomial.algebra FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

abbrev k := ZMod 2
abbrev F := GaloisField 2 2
abbrev R := k[X]
abbrev S := F[X]
abbrev K := FractionRing R
abbrev L := FractionRing S

instance : Algebra.Unramified k F where
  formallyUnramified := Algebra.FormallyUnramified.of_isSeparable k F

instance : Algebra.Unramified R S :=
  Algebra.Unramified.of_equiv (Algebra.IsPushout.equiv k R F S)

instance : Module.Finite R S :=
  Module.Finite.equiv (Algebra.IsPushout.equiv k R F S).toLinearEquiv

instance : IsIntegralClosure S R L :=
  IsIntegralClosure.of_isIntegrallyClosed S R L

/-- The coefficient action has exactly the binary polynomials as fixed ring. -/
instance polyGalois : IsGaloisGroup (F ≃ₐ[k] F) R S where
  faithful := ⟨by
    intro g h eq
    ext a
    have he := congrArg (fun p : S ↦ p.coeff 0) (eq (C a))
    simpa using he⟩
  commutes := ⟨by
    intro g p q
    simp only [Algebra.smul_def, Polynomial.smul_eq_map,
      Polynomial.algebraMap_def, Polynomial.coe_mapRingHom,
      Polynomial.map_mul, Polynomial.map_map]
    congr 2
    exact g.toAlgHom.comp_algebraMap⟩
  isInvariant := ⟨by
    intro p hp
    apply (p.lifts_iff_coeff_lifts (f := algebraMap k F)).mpr
    intro n
    apply (IsGaloisGroup.isInvariant
      (G := F ≃ₐ[k] F) (A := k) (B := F)).isInvariant
    intro g
    have he := congrArg (fun p : S ↦ p.coeff n) (hp g)
    simpa using he⟩

local instance : MulSemiringAction (F ≃ₐ[k] F) L :=
  IsFractionRing.mulSemiringAction (F ≃ₐ[k] F) S L

instance : IsGaloisGroup (F ≃ₐ[k] F) K L :=
  IsGaloisGroup.to_isFractionRing (F ≃ₐ[k] F) R S K L

instance : FiniteDimensional K L :=
  IsGaloisGroup.finiteDimensional (F ≃ₐ[k] F) K L

instance : IsGalois K L := IsGaloisGroup.isGalois (F ≃ₐ[k] F) K L

local instance : Fintype F := Fintype.ofFinite F

/-- A genuine nonbinary root, chosen without assuming any descent conclusion. -/
lemma exists_quadratic_root :
    ∃ a : F, a ≠ 0 ∧ a ≠ 1 ∧ a ^ 2 + a + 1 = 0 := by
  classical
  have hcard : Fintype.card F = 4 := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card 2 2 (by decide)
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({0, 1} : Finset F)) (t := Finset.univ) (by simp [hcard])
  have ha0 : a ≠ 0 := by simpa using (fun h ↦ ha (by simp [h]))
  have ha1 : a ≠ 1 := by simpa using (fun h ↦ ha (by simp [h]))
  have h3 : a ^ 3 = 1 := by
    simpa [hcard] using FiniteField.pow_card_sub_one_eq_one a ha0
  refine ⟨a, ha0, ha1, ?_⟩
  apply (mul_eq_zero.mp
    (show (a - 1) * (a ^ 2 + a + 1) = 0 from ?_)).resolve_left
      (sub_ne_zero.mpr ha1)
  calc
    (a - 1) * (a ^ 2 + a + 1) = a ^ 3 - 1 := by ring
    _ = 0 := by rw [h3, sub_self]

@[expose] def a : F := exists_quadratic_root.choose
lemma a_ne_zero : a ≠ 0 := exists_quadratic_root.choose_spec.1
lemma a_ne_one : a ≠ 1 := exists_quadratic_root.choose_spec.2.1
lemma a_relation : a ^ 2 + a + 1 = 0 := exists_quadratic_root.choose_spec.2.2

/-- Two distinct conjugate linear factors of the binary quadratic. -/
lemma conjugate_pair :
    (X - C a : S) * (X - C (a ^ 2)) = X ^ 2 + X + 1 := by
  have hsum : a + a ^ 2 = -1 := by linear_combination a_relation
  have hprod : a * a ^ 2 = 1 := by
    have hcard : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 2 (by decide)
    simpa [hcard, pow_succ, mul_comm] using
      FiniteField.pow_card_sub_one_eq_one a a_ne_zero
  calc
    (X - C a : S) * (X - C (a ^ 2)) =
        X ^ 2 - C (a + a ^ 2) * X + C (a * a ^ 2) := by
      simp only [map_add, map_mul]
      ring
    _ = X ^ 2 + X + 1 := by simp [hsum, hprod]

/-- The prime of the affine line at a supplied coefficient. -/
@[expose] def linearIdeal (r : F) : Ideal S := Ideal.span {X - C r}

/-- Supplied on S as three prime powers, not as an extended base ideal. -/
@[expose] def invariantIdeal : Ideal S :=
  linearIdeal 0 ^ 3 * linearIdeal a ^ 2 * linearIdeal (a ^ 2) ^ 2

lemma invariantIdeal_eq_span :
    invariantIdeal = Ideal.span {(X : S) ^ 3 * (X ^ 2 + X + 1) ^ 2} := by
  simp only [invariantIdeal, linearIdeal, Ideal.span_singleton_pow,
    Ideal.span_singleton_mul_span_singleton, map_zero, sub_zero]
  rw [mul_assoc, ← mul_pow, conjugate_pair]

/-- Invariance is proved from the polynomial identity, before calling descent. -/
lemma invariantIdeal_comap (φ : S ≃ₐ[R] S) :
    invariantIdeal.comap φ = invariantIdeal := by
  have hX : φ.symm (X : S) = X := by
    simpa using φ.symm.commutes (X : R)
  change invariantIdeal.comap φ.toRingEquiv = invariantIdeal
  rw [← Ideal.map_symm φ.toRingEquiv, invariantIdeal_eq_span,
    Ideal.map_span, Set.image_singleton]
  simp [hX]

/-- The nonradical, multiple-orbit ideal uses the exact public descent theorem. -/
theorem nonradical_multiorbit_descent :
    (invariantIdeal.comap (algebraMap R S)).map (algebraMap R S) =
      invariantIdeal :=
  Ideal.map_comap_eq_of_unramified_of_galois_invariant R K L S
    invariantIdeal (fun σ ↦ invariantIdeal_comap (galRestrict R K L S σ))

lemma linearIdeal_prime (r : F) : Prime (linearIdeal r) := by
  apply Ideal.prime_of_isPrime
  · simpa [linearIdeal, Ideal.span_singleton_eq_bot] using
      (Polynomial.X_sub_C_ne_zero r)
  · exact Ideal.isPrime_span_singleton_of_prime (Polynomial.prime_X_sub_C r)

lemma linearIdeal_injective : Function.Injective linearIdeal := by
  intro r s h
  have hmem : X - C r ∈ linearIdeal s :=
    h ▸ (Ideal.subset_span (Set.mem_singleton (X - C r)))
  rw [linearIdeal, Ideal.mem_span_singleton, Polynomial.dvd_iff_isRoot] at hmem
  simpa [Polynomial.IsRoot, sub_eq_zero, eq_comm] using hmem

lemma a_sq_ne_a : a ^ 2 ≠ a := by
  intro h
  have he : a * (a - 1) = 0 := by rw [mul_sub, mul_one, ← pow_two, h, sub_self]
  exact (mul_ne_zero a_ne_zero (sub_ne_zero.mpr a_ne_one)) he

lemma invariantIdeal_ne_bot : invariantIdeal ≠ ⊥ :=
  mul_ne_zero
    (mul_ne_zero (pow_ne_zero 3 (linearIdeal_prime 0).ne_zero)
      (pow_ne_zero 2 (linearIdeal_prime a).ne_zero))
    (pow_ne_zero 2 (linearIdeal_prime (a ^ 2)).ne_zero)

/-- Canonical integral-ideal factors retain the unequal orbit exponents. -/
lemma invariantIdeal_factors :
    normalizedFactors invariantIdeal =
      3 • {linearIdeal 0} + 2 • {linearIdeal a} + 2 • {linearIdeal (a ^ 2)} := by
  classical
  have hn (r : F) (n : ℕ) : linearIdeal r ^ n ≠ 0 :=
    pow_ne_zero n (linearIdeal_prime r).ne_zero
  have hf (r : F) : normalizedFactors (linearIdeal r) = {linearIdeal r} := by
    simpa using normalizedFactors_irreducible (linearIdeal_prime r).irreducible
  rw [invariantIdeal,
    normalizedFactors_mul (mul_ne_zero (hn 0 3) (hn a 2)) (hn (a ^ 2) 2),
    normalizedFactors_mul (hn 0 3) (hn a 2)]
  simp only [normalizedFactors_pow, hf]

lemma invariantIdeal_counts :
    (normalizedFactors invariantIdeal).count (linearIdeal 0) = 3 ∧
    (normalizedFactors invariantIdeal).count (linearIdeal a) = 2 ∧
    (normalizedFactors invariantIdeal).count (linearIdeal (a ^ 2)) = 2 := by
  classical
  simp [invariantIdeal_factors, linearIdeal_injective.eq_iff,
    a_ne_zero, a_ne_zero.symm, a_sq_ne_a, a_sq_ne_a.symm,
    (pow_ne_zero 2 a_ne_zero).symm]

lemma invariantIdeal_ne_top : invariantIdeal ≠ ⊤ := by
  intro h
  have hc := invariantIdeal_counts.1
  simp [h, ← Ideal.one_eq_top] at hc

/-- Dropping multiplicities fails: the product with exponents one is absent,
although its cube belongs to the ideal. -/
lemma radical_only_counterexample :
    (X * (X ^ 2 + X + 1) : S) ∉ invariantIdeal ∧
    (X * (X ^ 2 + X + 1) : S) ^ 3 ∈ invariantIdeal := by
  rw [invariantIdeal_eq_span]
  constructor
  · intro h
    have hd : (X : S) ^ 3 ∣ X * (X ^ 2 + X + 1) :=
      dvd_trans (dvd_mul_right _ _) (Ideal.mem_span_singleton.mp h)
    have hc := Polynomial.X_pow_dvd_iff.mp hd 1 (by decide)
    norm_num [Polynomial.coeff_X_mul] at hc
  · rw [Ideal.mem_span_singleton]
    exact ⟨X ^ 2 + X + 1, by ring⟩

lemma invariantIdeal_not_isRadical : ¬ invariantIdeal.IsRadical := by
  intro h
  exact radical_only_counterexample.1 (h ⟨3, radical_only_counterexample.2⟩)

/-- Nontrivial coefficient Frobenius, fixing the polynomial variable. -/
@[expose] def coefficientFrobenius : S ≃ₐ[R] S :=
  MulSemiringAction.toAlgAut (F ≃ₐ[k] F) R S
    (FiniteField.frobeniusAlgEquivOfAlgebraic k F)

lemma frobenius_linearIdeal (r : F) :
    (linearIdeal r).map coefficientFrobenius = linearIdeal (r ^ 2) := by
  rw [linearIdeal, Ideal.map_span, Set.image_singleton, linearIdeal]
  congr 1
  simp [coefficientFrobenius, smul_sub, Polynomial.smul_X, Polynomial.smul_C,
    AlgEquiv.smul_def, k]

lemma linearIdeal_zero_fixed (φ : S ≃ₐ[R] S) :
    (linearIdeal 0).map φ = linearIdeal 0 := by
  have hX : φ (X : S) = X := by simpa using φ.commutes (X : R)
  simp [linearIdeal, Ideal.map_span, hX]

/-- A fixed orbit and a distinct two-element orbit occur in the support. -/
lemma two_prime_orbits :
    (∀ φ : S ≃ₐ[R] S, (linearIdeal 0).map φ = linearIdeal 0) ∧
    (linearIdeal a).map coefficientFrobenius = linearIdeal (a ^ 2) ∧
    (linearIdeal (a ^ 2)).map coefficientFrobenius = linearIdeal a ∧
    linearIdeal 0 ≠ linearIdeal a ∧
    linearIdeal 0 ≠ linearIdeal (a ^ 2) ∧
    linearIdeal a ≠ linearIdeal (a ^ 2) := by
  have hfour : a ^ 4 = a := by
    have hcard : Fintype.card F = 4 := by
      rw [← Nat.card_eq_fintype_card]
      exact GaloisField.card 2 2 (by decide)
    simpa [hcard] using FiniteField.pow_card a
  refine ⟨linearIdeal_zero_fixed, frobenius_linearIdeal a, ?_, ?_, ?_, ?_⟩
  · rw [frobenius_linearIdeal, ← pow_mul, show (2 * 2 : ℕ) = 4 from rfl, hfour]
  · exact fun h ↦ a_ne_zero (linearIdeal_injective h).symm
  · exact fun h ↦ (pow_ne_zero 2 a_ne_zero) (linearIdeal_injective h).symm
  · exact fun h ↦ a_sq_ne_a (linearIdeal_injective h).symm

/-- Without invariance, a lone conjugate prime is not extended from its contraction.
The proof uses its moved conjugate, not failure to synthesize a hypothesis. -/
lemma lone_conjugate_counterexample :
    ((linearIdeal a).comap (algebraMap R S)).map (algebraMap R S) ≠
      linearIdeal a := by
  intro h
  let J := (linearIdeal a).comap (algebraMap R S)
  have he : (J.map (algebraMap R S)).map coefficientFrobenius =
      J.map (algebraMap R S) := by
    change (J.map (algebraMap R S)).map coefficientFrobenius.toRingHom = _
    rw [Ideal.map_map]
    exact congrArg (fun f : R →+* S ↦ J.map f)
      coefficientFrobenius.toAlgHom.comp_algebraMap
  change (Ideal.map coefficientFrobenius
    ((linearIdeal a).comap (algebraMap R S) |>.map (algebraMap R S))) = _ at he
  rw [h, frobenius_linearIdeal] at he
  exact a_sq_ne_a (linearIdeal_injective he)

/-- The nontrivial ideal permutation is induced by an actual field automorphism. -/
lemma nontrivial_galois_action :
    ∃ σ : L ≃ₐ[K] L,
      (linearIdeal a).map (galRestrict R K L S σ) = linearIdeal (a ^ 2) ∧
      (linearIdeal a).map (galRestrict R K L S σ) ≠ linearIdeal a := by
  refine ⟨(galRestrict R K L S).symm coefficientFrobenius, ?_⟩
  rw [MulEquiv.apply_symm_apply, frobenius_linearIdeal]
  exact ⟨rfl, fun h ↦ a_sq_ne_a (linearIdeal_injective h)⟩

/-- Group order two really occurs in characteristic two, so averaging is unavailable. -/
lemma characteristic_and_group_order :
    ringChar R = 2 ∧ Nat.card (L ≃ₐ[K] L) = 2 := by
  constructor
  · exact ringChar.eq R 2
  · rw [IsGalois.card_aut_eq_finrank,
      ← IsGaloisGroup.card_eq_finrank (F ≃ₐ[k] F) K L,
      IsGalois.card_aut_eq_finrank]
    exact GaloisField.finrank 2 (by decide)

/-- The nonzero guard on the prime-fiber product cannot be dropped. -/
lemma zero_prime_product_counterexample :
    (∏ P ∈ IsDedekindDomain.primesOverFinset (⊥ : Ideal R) S, P) ≠
      (⊥ : Ideal R).map (algebraMap R S) := by
  simp only [IsDedekindDomain.primesOverFinset, Ideal.map_bot]
  change (∏ P ∈ (factors (0 : Ideal S)).toFinset, P) ≠ 0
  rw [factors_eq_normalizedFactors, normalizedFactors_zero,
    Multiset.toFinset_zero, Finset.prod_empty]
  exact one_ne_zero

/-- Identify the contraction independently by coefficient-field divisibility. -/
lemma contraction_identified :
    invariantIdeal.comap (algebraMap R S) =
      Ideal.span {(X : R) ^ 3 * (X ^ 2 + X + 1) ^ 2} := by
  rw [invariantIdeal_eq_span]
  ext p
  simp only [Ideal.mem_comap, Ideal.mem_span_singleton]
  have hf : Polynomial.map (algebraMap k F)
      ((X : R) ^ 3 * (X ^ 2 + X + 1) ^ 2) =
      (X : S) ^ 3 * (X ^ 2 + X + 1) ^ 2 := by simp
  rw [← hf]
  exact Polynomial.map_dvd_map' (algebraMap k F)

end UnramifiedIdealDescentTest.FiniteFieldFixture

namespace UnramifiedIdealDescentTest.GaussianCounterexample

@[expose] def z : GaussianInt := ⟨1, 1⟩
@[expose] def ramifiedIdeal : Ideal GaussianInt := Ideal.span {z}

lemma contraction :
    ramifiedIdeal.comap (algebraMap ℤ GaussianInt) = Ideal.span {(2 : ℤ)} := by
  ext n
  simp only [ramifiedIdeal, Ideal.mem_comap, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨w, hw⟩
    have hr := congrArg Zsqrtd.re hw
    have hi := congrArg Zsqrtd.im hw
    simp [z] at hr hi
    exact ⟨w.re, by omega⟩
  · rintro ⟨m, rfl⟩
    refine ⟨⟨m, -m⟩, ?_⟩
    ext <;> simp [z]
    ring

/-- Conjugation fixes (1+i); invariance alone does not imply descent. -/
lemma conjugation_stable :
    ramifiedIdeal.map (starRingEnd GaussianInt) = ramifiedIdeal := by
  rw [ramifiedIdeal, Ideal.map_span, Set.image_singleton,
    Ideal.span_singleton_eq_span_singleton]
  change Associated (star z) z
  apply associated_of_dvd_dvd
  · refine ⟨(⟨0, 1⟩ : GaussianInt), ?_⟩
    ext <;> norm_num [z]
  · refine ⟨(⟨0, -1⟩ : GaussianInt), ?_⟩
    ext <;> norm_num [z]

lemma ramified_counterexample :
    (ramifiedIdeal.comap (algebraMap ℤ GaussianInt)).map
      (algebraMap ℤ GaussianInt) ≠ ramifiedIdeal := by
  intro h
  have hz : z ∈ (ramifiedIdeal.comap (algebraMap ℤ GaussianInt)).map
      (algebraMap ℤ GaussianInt) := by
    rw [h]
    exact Ideal.subset_span (Set.mem_singleton z)
  rw [contraction, Ideal.map_span, Set.image_singleton] at hz
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hz
  have hr := congrArg Zsqrtd.re hw
  norm_num [z] at hr
  omega

end UnramifiedIdealDescentTest.GaussianCounterexample
