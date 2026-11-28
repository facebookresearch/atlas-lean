/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.HeegnerIsogeny

import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

open NumberField NumberField.RingOfIntegers NumberField.FractionalIdeal nonZeroDivisors

local notation "ℚ(i)" => CyclotomicField 4 ℚ

/-- The Gaussian field `ℚ(i) = CyclotomicField 4 ℚ` is an imaginary quadratic field. -/
theorem gaussianField_imaginaryQuadratic :
    IsTotallyComplex (CyclotomicField 4 ℚ) ∧ Module.finrank ℚ (CyclotomicField 4 ℚ) = 2 := by
  -- the cyclotomic structure for the `ℚ`-algebra structure coming from characteristic zero
  have : @IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) _ _ DivisionRing.toRatAlgebra := by
    convert CyclotomicField.isCyclotomicExtension 4 ℚ
    exact Subsingleton.elim _ _
  exact ⟨IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) (CyclotomicField 4 ℚ) (by norm_num),
    by rw [IsCyclotomicExtension.Rat.finrank 4]; rfl⟩

-- The hypotheses of the Heegner-hypothesis theorem hold for `K = ℚ(i)` and `N = 1`.
example : ∃ 𝒩 : Ideal (𝓞 (CyclotomicField 4 ℚ)),
    IsAddCyclic (𝓞 (CyclotomicField 4 ℚ) ⧸ 𝒩) ∧ Nat.card (𝓞 (CyclotomicField 4 ℚ) ⧸ 𝒩) = 1 :=
  have := gaussianField_imaginaryQuadratic.1
  exists_ideal_isAddCyclic_quotient_of_heegnerHypothesis gaussianField_imaginaryQuadratic.2
    le_rfl fun _ hp hdvd => absurd (Nat.le_of_dvd one_pos hdvd) (by simpa using hp.one_lt)

-- The hypotheses of the Heegner isogeny theorem hold for `K = ℚ(i)`, `𝒩 = 𝓞 K` and `N = 1`, for
-- every complex embedding `σ`.
example (σ : CyclotomicField 4 ℚ →+* ℂ) :
    ∃ h : complexLattice σ 1 ≤ complexLattice σ
        ((⊤ : Ideal (𝓞 ℚ(i))) : FractionalIdeal (𝓞 ℚ(i))⁰ ℚ(i))⁻¹,
      Nat.card (LinearMap.ker ((complexLattice σ 1).mapQ (complexLattice σ
        ((⊤ : Ideal (𝓞 ℚ(i))) : FractionalIdeal (𝓞 ℚ(i))⁰ ℚ(i))⁻¹)
          LinearMap.id h)) = 1 := by
  have := gaussianField_imaginaryQuadratic.1
  obtain ⟨-, -, h, -, -, -, -, hcard⟩ := heegner_isogeny_isAddCyclic_ker
    gaussianField_imaginaryQuadratic.2 σ (𝒩 := ⊤) top_ne_bot (N := 1) inferInstance
    (by simp)
  exact ⟨h, hcard⟩

-- The two results chain: under the Heegner hypothesis the ideal `𝒩` of the first theorem gives a
-- cyclic `N`-isogeny `ℂ / σ(𝓞 K) → ℂ / σ(𝒩⁻¹)`.
example {K : Type*} [Field K] [NumberField K] [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) (σ : K →+* ℂ) {N : ℕ} (hN : 1 ≤ N)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ N → ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) :
    ∃ 𝒩 : Ideal (𝓞 K), ∃ h : complexLattice σ 1 ≤ complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      IsAddCyclic (LinearMap.ker ((complexLattice σ 1).mapQ
        (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) LinearMap.id h)) ∧
      Nat.card (LinearMap.ker ((complexLattice σ 1).mapQ
        (complexLattice σ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) LinearMap.id h)) = N := by
  obtain ⟨𝒩, hcyc, hcard⟩ := exists_ideal_isAddCyclic_quotient_of_heegnerHypothesis hK hN hsplit
  have h𝒩 : 𝒩 ≠ ⊥ := by
    rintro rfl
    have : Infinite (𝓞 K ⧸ (⊥ : Ideal (𝓞 K))) :=
      Infinite.of_injective _ (RingHom.quotientKerEquivOfRightInverse (f := RingHom.id (𝓞 K))
        (g := id) fun _ => rfl).symm.injective
    simp [Nat.card_eq_zero_of_infinite] at hcard
    omega
  obtain ⟨-, -, h, -, -, -, hcyc', hcard'⟩ := heegner_isogeny_isAddCyclic_ker hK σ h𝒩 hcyc hcard
  exact ⟨𝒩, h, hcyc', hcard'⟩
