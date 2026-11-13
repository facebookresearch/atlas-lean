/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.UnramifiedMinpoly
public import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
public import Mathlib.Data.ZMod.QuotientRing

/-!
# Source contracts and Gaussian integer tests

The main fixture uses `2i`, which generates the fraction field over `ℚ`
but not `GaussianInt` over `ℤ`. The prime is the kernel of `i ↦ 3` modulo 5.
Controls prove ramification at the kernel of `i ↦ 1` modulo 2, failure of
field generation by zero, and failure of the converse for `3i` at `(3)`.
-/

@[expose] public section

open Polynomial

namespace UnramifiedMinpolyTest

section Source

variable {R K L S : Type*}
  [CommRing R] [CommRing S] [Algebra R S] [Field K] [Field L]
  [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  [Algebra S L] [Algebra K L] [Algebra R L]
  [IsScalarTower R S L] [IsScalarTower R K L]
  [IsIntegralClosure S R L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

-- Exact R2520–2524 contract, without Galois or ring-generation assumptions.
theorem ringElementSource (P : Ideal S) [P.IsPrime] (hP : P ≠ ⊥)
    (x : S) (hx : Algebra.adjoin K {algebraMap S L x} = ⊤)
    (hs : ((minpoly R x).map (Ideal.Quotient.mk (P.under R))).Separable) :
    Algebra.IsUnramifiedAt R P :=
  Algebra.isUnramifiedAt_of_separable_minpoly K L P hP x hx hs

-- Exact R2572–2580 integral field-element contract.
theorem fieldElementSource (P : Ideal S) [P.IsPrime] (hP : P ≠ ⊥)
    (x : L) (hi : IsIntegral R x) (hx : Algebra.adjoin K {x} = ⊤)
    (hs : ((minpoly R x).map (Ideal.Quotient.mk (P.under R))).Separable) :
    Algebra.IsUnramifiedAt R P :=
  Algebra.isUnramifiedAt_of_separable_minpoly_of_isIntegral K L P hP x hi hx hs

-- R3074–3079's polynomial-identification interface, with a ramification-index
-- consequence. This does not assert or implement any Kummer result.
theorem polynomialGeneratorClient (P : Ideal S) [P.IsPrime] (hP : P ≠ ⊥)
    (x : L) (hi : IsIntegral R x) (hx : Algebra.adjoin K {x} = ⊤)
    (f : R[X]) (hf : minpoly R x = f)
    (hs : (f.map (Ideal.Quotient.mk (P.under R))).Separable) :
    Ideal.ramificationIdx P R = 1 := by
  have : Module.Finite R S := IsIntegralClosure.finite R K L S
  have : Algebra.IsUnramifiedAt R P :=
    Algebra.isUnramifiedAt_of_separable_minpoly_of_isIntegral K L P hP x hi hx
      (hf.symm ▸ hs)
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

end Source

namespace Gaussian

local notation "G" => GaussianInt
local notation "L" => FractionRing GaussianInt
local notation "i" => (Zsqrtd.sqrtd : G)

-- The actual minimal polynomial of n*i, not an arbitrary annihilator.
theorem minpoly_imaginary (n : ℤ) (hn : n ≠ 0) :
    minpoly ℤ (⟨0, n⟩ : G) = X ^ 2 + C (n ^ 2) := by
  have hm : (X ^ 2 + C (n ^ 2) : ℤ[X]).Monic :=
    monic_X_pow_add_C _ (by decide)
  have he : aeval (⟨0, n⟩ : G) (X ^ 2 + C (n ^ 2) : ℤ[X]) = 0 := by
    simp only [map_add, map_pow, aeval_X, aeval_C]
    ext <;> simp [pow_two]
  have hi : IsIntegral ℤ (⟨0, n⟩ : G) := ⟨_, hm, he⟩
  symm
  apply eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hi) hm
    (minpoly.isIntegrallyClosed_dvd hi he)
  rw [natDegree_X_pow_add_C]
  apply (minpoly.two_le_natDegree_iff hi).mpr
  rintro ⟨a, ha⟩
  have := congrArg Zsqrtd.im ha
  exact hn (by simpa using this.symm)

private def coordinates : (ℤ × ℤ) ≃ₗ[ℤ] G where
  toFun z := ⟨z.1, z.2⟩
  invFun z := (z.re, z.im)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a z := by
    ext <;> simp [Algebra.smul_def]

local instance : Module.Finite ℤ G := Module.Finite.equiv coordinates

local instance : IsIntegralClosure G ℤ L :=
  IsIntegralClosure.of_isIntegrallyClosed G ℤ L

local instance ratTower : @IsScalarTower ℤ ℚ L
    (inferInstance : Algebra ℤ ℚ).toSMul
    (inferInstance : Algebra ℚ L).toSMul
    (inferInstance : Algebra ℤ L).toSMul :=
  IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := L)
    (Subsingleton.elim _ _)

local instance : Algebra.IsAlgebraic ℚ L :=
  isAlgebraic_of_isFractionRing ℤ G ℚ L

local instance : IsLocalization
    (Algebra.algebraMapSubmonoid G (nonZeroDivisors ℤ)) L :=
  IsIntegralClosure.isLocalization ℤ ℚ L G

local instance : FiniteDimensional ℚ L :=
  Module.Finite.of_isLocalization ℤ G (nonZeroDivisors ℤ)

theorem field_generation (n : ℤ) (hn : n ≠ 0) :
    Algebra.adjoin ℚ {algebraMap G L (⟨0, n⟩ : G)} = ⊤ := by
  let F := IntermediateField.adjoin ℚ {algebraMap G L (⟨0, n⟩ : G)}
  have hnL : (n : L) ≠ 0 := by exact_mod_cast hn
  have hni : algebraMap G L (⟨0, n⟩ : G) =
      (n : L) * algebraMap G L i := by
    rw [← map_intCast (algebraMap G L), ← map_mul]
    congr 1
    ext <;> simp
  have hi : algebraMap G L i ∈ F := by
    have hx : algebraMap G L (⟨0, n⟩ : G) ∈ F := by
      apply IntermediateField.subset_adjoin
      rfl
    have h := F.div_mem hx (F.intCast_mem n)
    simpa [hni, mul_div_cancel_left₀ _ hnL] using h
  have hall (z : G) : algebraMap G L z ∈ F := by
    obtain ⟨a, b⟩ := z
    rw [Zsqrtd.decompose, map_add, map_mul, map_intCast, map_intCast]
    exact F.add_mem (F.intCast_mem a) (F.mul_mem hi (F.intCast_mem b))
  apply IntermediateField.adjoin_eq_top_iff.mp
  change F = ⊤
  apply top_unique
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective G z
  exact F.div_mem (hall a) (hall b)

theorem even_imaginary_of_mem_adjoin {z : G}
    (hz : z ∈ Algebra.adjoin ℤ {(⟨0, 2⟩ : G)}) : 2 ∣ z.im := by
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
    obtain rfl := Set.mem_singleton_iff.mp hz
    exact dvd_rfl
  | algebraMap r => simp
  | add a b _ _ ha hb => exact dvd_add ha hb
  | mul a b _ _ ha hb =>
    exact dvd_add (dvd_mul_of_dvd_right hb _) (dvd_mul_of_dvd_left ha _)

theorem not_ring_generation : Algebra.adjoin ℤ {(⟨0, 2⟩ : G)} ≠ ⊤ := by
  intro h
  have hi : i ∈ Algebra.adjoin ℤ {(⟨0, 2⟩ : G)} := h ▸ Algebra.mem_top
  have := even_imaginary_of_mem_adjoin hi
  norm_num at this

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def residueFive : G →+* ZMod 5 := Zsqrtd.lift ⟨3, by decide⟩

def primeFive : Ideal G := RingHom.ker residueFive

instance : primeFive.IsPrime :=
  RingHom.ker_isPrime residueFive

theorem primeFive_ne_bot : primeFive ≠ ⊥ := by
  intro h
  have hm : (5 : G) ∈ primeFive := by
    change residueFive 5 = 0
    decide
  rw [h, Ideal.mem_bot] at hm
  have := congrArg Zsqrtd.re hm
  norm_num at this

theorem under_primeFive : primeFive.under ℤ = Ideal.span {(5 : ℤ)} := by
  change RingHom.ker (residueFive.comp (algebraMap ℤ G)) = _
  rw [Subsingleton.elim (residueFive.comp (algebraMap ℤ G))
    (Int.castRingHom (ZMod 5))]
  exact ZMod.ker_intCastRingHom 5

theorem separable_at_five :
    ((minpoly ℤ (⟨0, 2⟩ : G)).map
      (Ideal.Quotient.mk (primeFive.under ℤ))).Separable := by
  have hs : (X ^ 2 + C 4 : (ZMod 5)[X]).Separable := by
    simpa only [map_neg, sub_neg_eq_add] using
      (separable_X_pow_sub_C (n := 2) (-4 : ZMod 5) (by decide) (by decide))
  rw [minpoly_imaginary 2 (by decide), under_primeFive]
  simpa [map_ofNat, C_ofNat] using
    hs.map (f := (Int.quotientSpanNatEquivZMod 5).symm.toRingHom)

theorem derivative_residue_five :
    residueFive (aeval (⟨0, 2⟩ : G)
      (minpoly ℤ (⟨0, 2⟩ : G)).derivative) = 2 := by
  rw [minpoly_imaginary 2 (by decide)]
  norm_num [derivative_add, derivative_pow, derivative_X, derivative_C,
    residueFive, Zsqrtd.lift, map_ofNat]
  decide

-- A full importing application where the SAME x is only a field generator.
theorem unramified_five : Algebra.IsUnramifiedAt ℤ primeFive :=
  Algebra.isUnramifiedAt_of_separable_minpoly ℚ L primeFive primeFive_ne_bot
    ⟨0, 2⟩ (field_generation 2 (by decide)) separable_at_five

theorem unramified_five_field_element : Algebra.IsUnramifiedAt ℤ primeFive := by
  apply Algebra.isUnramifiedAt_of_separable_minpoly_of_isIntegral ℚ L
    primeFive primeFive_ne_bot (algebraMap G L (⟨0, 2⟩ : G))
    ((IsIntegral.of_finite ℤ (⟨0, 2⟩ : G)).algebraMap)
    (field_generation 2 (by decide))
  simpa only [minpoly.algebraMap_eq (IsFractionRing.injective G L)]
    using separable_at_five

theorem ring_generation_i : Algebra.adjoin ℤ {i} = ⊤ := by
  apply top_unique
  rintro ⟨a, b⟩ _
  rw [Zsqrtd.decompose]
  exact add_mem (algebraMap_mem _ a)
    (mul_mem (Algebra.self_mem_adjoin_singleton ℤ i) (algebraMap_mem _ b))

theorem different_gaussian :
    differentIdeal ℤ G = Ideal.span {(⟨0, 2⟩ : G)} := by
  have h := conductor_mul_differentIdeal ℤ ℚ L i
    (field_generation 1 (by decide))
  rw [conductor_eq_top_of_adjoin_eq_top ring_generation_i, Ideal.top_mul] at h
  have hd : aeval i (minpoly ℤ i).derivative = (⟨0, 2⟩ : G) := by
    change aeval (⟨0, 1⟩ : G) (minpoly ℤ (⟨0, 1⟩ : G)).derivative = _
    rw [minpoly_imaginary 1 (by decide)]
    norm_num [derivative_add, derivative_pow, derivative_X, derivative_C,
      map_ofNat]
    rfl
  exact h.trans (congrArg (fun z : G => Ideal.span {z}) hd)

def residueTwo : G →+* ZMod 2 := Zsqrtd.lift ⟨1, by decide⟩

def primeTwo : Ideal G := RingHom.ker residueTwo

instance : primeTwo.IsPrime := RingHom.ker_isPrime residueTwo

theorem primeTwo_ne_bot : primeTwo ≠ ⊥ := by
  intro h
  have hm : (2 : G) ∈ primeTwo := by
    change residueTwo 2 = 0
    decide
  rw [h, Ideal.mem_bot] at hm
  have := congrArg Zsqrtd.re hm
  norm_num at this

theorem under_primeTwo : primeTwo.under ℤ = Ideal.span {(2 : ℤ)} := by
  change RingHom.ker (residueTwo.comp (algebraMap ℤ G)) = _
  rw [Subsingleton.elim (residueTwo.comp (algebraMap ℤ G))
    (Int.castRingHom (ZMod 2))]
  exact ZMod.ker_intCastRingHom 2

attribute [local instance] FractionRing.liftAlgebra

theorem ramified_two : ¬ Algebra.IsUnramifiedAt ℤ primeTwo := by
  apply (dvd_differentIdeal_iff (A := ℤ) (B := G) (P := primeTwo)).mp
  rw [different_gaussian, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  change residueTwo (⟨0, 2⟩ : G) = 0
  decide

private theorem repeated_reduction (p : ℕ) [Fact p.Prime] :
    ¬ ((X ^ 2 + C ((p : ℤ) ^ 2) : ℤ[X]).map
      (Ideal.Quotient.mk (Ideal.span {(p : ℤ)}))).Separable := by
  intro h
  have hs := h.map (f := (Int.quotientSpanNatEquivZMod p).toRingHom)
  have hs' : (X ^ 2 : (ZMod p)[X]).Separable := by
    simpa [Polynomial.map_map, map_ofNat] using hs
  exact hs'.eval₂_derivative_ne_zero (RingHom.id _) (x := 0)
    (by simp) (by simp)

theorem inseparable_at_two :
    ¬ ((minpoly ℤ (⟨0, 2⟩ : G)).map
      (Ideal.Quotient.mk (primeTwo.under ℤ))).Separable := by
  rw [minpoly_imaginary 2 (by decide), under_primeTwo]
  exact repeated_reduction 2

theorem zero_minpoly : minpoly ℤ (0 : G) = X := by
  simpa using minpoly.eq_X_sub_C_of_algebraMap_inj (A := ℤ) (B := G) 0
    Int.cast_injective

theorem zero_separable_at_two :
    ((minpoly ℤ (0 : G)).map
      (Ideal.Quotient.mk (primeTwo.under ℤ))).Separable := by
  rw [zero_minpoly, Polynomial.map_X]
  exact separable_X

theorem zero_not_field_generator : Algebra.adjoin ℚ {(0 : L)} ≠ ⊤ := by
  have hd : (minpoly ℚ (algebraMap G L (⟨0, 1⟩ : G))).natDegree = 2 := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions ℚ L
      (IsIntegral.of_finite ℤ (⟨0, 1⟩ : G)), minpoly_imaginary 1 (by decide)]
    simp
  intro h
  have hm : algebraMap G L (⟨0, 1⟩ : G) ∈ Algebra.adjoin ℚ {(0 : L)} :=
    h ▸ Algebra.mem_top
  have hlow := (minpoly.two_le_natDegree_iff
    (Algebra.IsIntegral.isIntegral (R := ℚ) (algebraMap G L (⟨0, 1⟩ : G)))).mp
    (by omega)
  exact hlow (by simpa [Algebra.mem_bot] using hm)

def primeThree : Ideal G := Ideal.span {(3 : G)}

instance : primeThree.IsPrime :=
  Ideal.isPrime_span_singleton_of_prime
    (GaussianInt.prime_of_nat_prime_of_mod_four_eq_three 3 (by decide))

theorem primeThree_ne_bot : primeThree ≠ ⊥ := by
  rw [primeThree, ne_eq, Ideal.span_singleton_eq_bot]
  decide

theorem under_primeThree : primeThree.under ℤ = Ideal.span {(3 : ℤ)} := by
  ext n
  change (algebraMap ℤ G n ∈ Ideal.span {(3 : G)}) ↔ _
  simp only [Ideal.mem_span_singleton, algebraMap_int_eq]
  exact Zsqrtd.intCast_dvd_intCast 3 n

theorem unramified_three : Algebra.IsUnramifiedAt ℤ primeThree := by
  apply (not_dvd_differentIdeal_iff (A := ℤ) (B := G) (P := primeThree)).mp
  rw [different_gaussian, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem,
    primeThree, Ideal.mem_span_singleton]
  change ¬ ((3 : ℤ) : G) ∣ (⟨0, 2⟩ : G)
  rw [Zsqrtd.intCast_dvd]
  norm_num

-- Unramifiedness does not imply separable reduction for this chosen generator.
theorem no_converse_at_three :
    Algebra.IsUnramifiedAt ℤ primeThree ∧
    Algebra.adjoin ℚ {algebraMap G L (⟨0, 3⟩ : G)} = ⊤ ∧
    ¬ ((minpoly ℤ (⟨0, 3⟩ : G)).map
      (Ideal.Quotient.mk (primeThree.under ℤ))).Separable := by
  refine ⟨unramified_three, field_generation 3 (by decide), ?_⟩
  rw [minpoly_imaginary 3 (by decide), under_primeThree]
  exact repeated_reduction 3

theorem top_is_not_prime : ¬ (⊤ : Ideal G).IsPrime := by
  intro h
  exact h.ne_top rfl

end Gaussian
end UnramifiedMinpolyTest
