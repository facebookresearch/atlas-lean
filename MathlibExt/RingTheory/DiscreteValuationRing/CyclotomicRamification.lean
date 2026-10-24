/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.RamificationInertia.Ramification
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.RootsOfUnity.Lemmas

@[expose] public section

/-!
# Ramification of cyclotomic extensions of complete DVRs

This is the ramified half of Corollary 10.18 of ATLAS `NumberTheoryI`
(Section 10.2): if `p ∣ m` then the cyclotomic extension obtained by adjoining
a primitive `m`-th root of unity to the fraction field of a complete discrete
valuation ring is ramified, under the hypotheses that `(p)` is the maximal
ideal of the ring and that the fraction field contains no nontrivial `p`-th
root of unity.

The converse half of Corollary 10.18 (that `p ∤ m` implies the extension is
unramified) is not ported here: the v1 formalization proves it through
`cyclotomic_monogenicity_hensel`, whose proof in
`v1/Atlas/NumberTheoryI/code/CyclotomicRamification.lean` is incomplete
(it ends with an unproved goal), so that direction is treated as unproved.
Every theorem below is proved in full; the chain is
`pth_root_unity_eq_one_of_no_prim_root` →
`no_prim_root_in_unramified_ext_of_base` →
`no_prim_pth_root_in_unramified_ext` →
`unramified_pth_root_in_base` → `dvr_pth_root_ramified`.

The ramification index is written `Ideal.ramificationIdx'`, the two-ideal form
in `Mathlib/NumberTheory/RamificationInertia/Ramification.lean` (the largest
`n` with `𝔭.map ≤ 𝔮 ^ n`); it is related to the newer
`Ideal.ramificationIdx 𝔮 A` by `Ideal.ramificationIdx'_eq_ramificationIdx`.
-/

open scoped Classical

/-- A `p`-th root of unity in a field with no primitive `p`-th root is `1`:
its order divides the prime `p`, so it is `1` or `p`, and `p` is excluded. -/
theorem pth_root_unity_eq_one_of_no_prim_root
    (L : Type*) [Field L] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hno : ∀ ω : L, ¬IsPrimitiveRoot ω p)
    (η : L) (hη : η ^ p = 1) : η = 1 := by
  have h1 : orderOf η ∣ p := orderOf_dvd_of_pow_eq_one hη
  rcases hp.out.eq_one_or_self_of_dvd (orderOf η) h1 with h | h
  · rwa [orderOf_eq_one_iff] at h
  · exact absurd (h ▸ IsPrimitiveRoot.orderOf η) (hno η)

/-- In an unramified extension of complete DVRs, a primitive `p`-th root of
unity cannot appear out of nowhere: if the residue characteristic is `p`,
`(p)` is the maximal ideal, the ramification index is `1`, and the base field
has no primitive `p`-th root, then neither does the extension.

The proof is the valuation argument: a primitive root `b ∈ B` reduces to `1`
in the residue field (characteristic `p`), so each factor `1 - b ^ (k + 1)`
lies in the maximal ideal, while their product is exactly `p`; hence
`p ∈ 𝔪_B ^ (p - 1)`, which forces `p ∈ 𝔪_B ^ 2`, contradicting
ramification index `1` (for `p = 2` the argument is replaced by the
observation that `-1` would be a primitive square root in the base field). -/
theorem no_prim_root_in_unramified_ext_of_base
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) = 1)
    (hnoroot : ∀ ω : K, ¬IsPrimitiveRoot ω p)
    (ω : L) : ¬IsPrimitiveRoot ω p := by
  intro hprim
  have hmap_le : Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤
      IsLocalRing.maximalIdeal B := by
    have h := Ideal.le_pow_of_le_ramificationIdx'
      (show 1 ≤ Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
        (IsLocalRing.maximalIdeal B) from he.symm ▸ le_refl 1)
    simpa [pow_one] using h
  have hp_mem_B : (↑p : B) ∈ IsLocalRing.maximalIdeal B := by
    have hp_mem_A : (↑p : A) ∈ IsLocalRing.maximalIdeal A :=
      habsunram ▸ Ideal.subset_span (Set.mem_singleton _)
    have := hmap_le (Ideal.mem_map_of_mem _ hp_mem_A)
    rwa [map_natCast] at this
  have hp_not_sq : (↑p : B) ∉ (IsLocalRing.maximalIdeal B) ^ 2 := by
    intro h
    have hnotmap : ¬(Ideal.map (algebraMap A B) (IsLocalRing.maximalIdeal A) ≤
        (IsLocalRing.maximalIdeal B) ^ 2) := by
      rw [← Ideal.ramificationIdx'_ne_one_iff hmap_le]
      omega
    apply hnotmap
    rw [← habsunram, Ideal.map_span, Ideal.span_le]
    rintro x ⟨a, rfl, rfl⟩
    rwa [map_natCast]
  have hcharB : CharP (IsLocalRing.ResidueField B) p := by
    rw [CharP.charP_iff_prime_eq_zero hp.out]
    rw [show (↑p : IsLocalRing.ResidueField B) =
      (IsLocalRing.residue B) (↑p : B) from
      (map_natCast (IsLocalRing.residue B) p).symm]
    exact (IsLocalRing.residue_eq_zero_iff (↑p : B)).mpr hp_mem_B
  have hp_ne_zero_A : (↑p : A) ≠ 0 := by
    intro h
    have : IsLocalRing.maximalIdeal A = ⊥ := by
      rw [← habsunram, h, Ideal.span_singleton_eq_bot]
    exact IsDiscreteValuationRing.not_isField A
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)
  have hp_ne_zero_K : (↑p : K) ≠ 0 := by
    intro h
    apply hp_ne_zero_A
    have : algebraMap A K (↑p : A) = 0 := by rwa [map_natCast]
    exact (IsFractionRing.injective A K) (this.trans (map_zero _).symm)
  by_cases hp2 : p = 2
  · apply hnoroot (-1 : K)
    subst hp2
    have hne : (-1 : K) ≠ 1 := by
      intro h
      apply hp_ne_zero_K
      have h1 : (1 : K) + 1 = 0 := by
        have := neg_add_cancel (1 : K); rwa [h] at this
      have : (2 : K) = 0 := by
        have : (2 : K) = 1 + 1 := by norm_num
        rw [this]; exact h1
      exact_mod_cast this
    constructor
    · norm_num
    · intro l hl
      rw [neg_one_pow_eq_one_iff_even hne] at hl
      exact hl.two_dvd
  · have hp_ge_3 : 3 ≤ p := by have := hp.out.two_le; omega
    obtain ⟨b, hb_eq, hb_prim⟩ :
        ∃ b : B, algebraMap B L b = ω ∧ IsPrimitiveRoot b p := by
      have hint : IsIntegral B ω := (hprim.isIntegral hp.out.pos).tower_top
      obtain ⟨b, hb⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
      exact ⟨b, hb, (hb ▸ hprim).of_map_of_injective
        (IsFractionRing.injective B L)⟩
    have hres_one : IsLocalRing.residue B b = 1 := by
      have hbp : b ^ p = 1 := hb_prim.pow_eq_one
      have hres_pow : (IsLocalRing.residue B b) ^ p = 1 := by
        rw [← map_pow, hbp, map_one]
      have h1 : ((IsLocalRing.residue B b) - 1) ^ p = 0 := by
        rw [sub_pow_char _ 1, one_pow, hres_pow, sub_self]
      have h2 : (IsLocalRing.residue B b) - 1 = 0 := by
        rwa [pow_eq_zero_iff (Nat.Prime.ne_zero hp.out)] at h1
      exact sub_eq_zero.mp h2
    have hmem_max : ∀ k ∈ Finset.range (p - 1),
        1 - b ^ (k + 1) ∈ IsLocalRing.maximalIdeal B := by
      intro k _
      rw [← IsLocalRing.residue_eq_zero_iff]
      simp only [map_sub, map_one, map_pow, hres_one, one_pow, sub_self]
    have hprod : ∏ k ∈ Finset.range (p - 1), (1 - b ^ (k + 1)) = (↑p : B) := by
      have hp1 : 1 ≤ p := hp.out.one_le
      have hb' : IsPrimitiveRoot b ((p - 1) + 1) :=
        (show p = (p - 1) + 1 by omega) ▸ hb_prim
      rw [IsPrimitiveRoot.prod_one_sub_pow_eq_order hb']
      push_cast [Nat.cast_sub hp1]
      ring
    have hp_in_pow : (↑p : B) ∈ (IsLocalRing.maximalIdeal B) ^ (p - 1) := by
      rw [← hprod]
      have h := Ideal.prod_mem_prod (s := Finset.range (p - 1))
        (I := fun _ => IsLocalRing.maximalIdeal B)
        (x := fun i => 1 - b ^ (i + 1)) hmem_max
      rwa [Finset.prod_const, Finset.card_range] at h
    exact hp_not_sq (Ideal.pow_le_pow_right (by omega : 2 ≤ p - 1) hp_in_pow)

/-- In an unramified extension of complete DVRs with `(p)` the maximal ideal,
every `p`-th root of unity is `1`, provided the base field has no primitive
`p`-th root. -/
theorem no_prim_pth_root_in_unramified_ext
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) = 1)
    (hnoroot : ∀ ω : K, ¬IsPrimitiveRoot ω p)
    (η : L) (hη : η ^ p = 1) : η = 1 := by
  have hnoL : ∀ ω : L, ¬IsPrimitiveRoot ω p :=
    no_prim_root_in_unramified_ext_of_base A K p L B habsunram he hnoroot
  exact pth_root_unity_eq_one_of_no_prim_root L p hnoL η hη

/-- A `p`-th root of unity in an unramified extension of complete DVRs (with
`(p)` the maximal ideal) already lies in the base field. -/
theorem unramified_pth_root_in_base
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    [Fintype (IsLocalRing.ResidueField A)]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [CharP (IsLocalRing.ResidueField A) p]
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A)
    (he : Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) = 1)
    (η : L) (hη : η ^ p = 1) :
    ∃ ζ : K, algebraMap K L ζ = η := by
  by_cases hprim : ∃ ω : K, IsPrimitiveRoot ω p
  · obtain ⟨ω, hω⟩ := hprim
    have hωL : IsPrimitiveRoot (algebraMap K L ω) p :=
      hω.map_of_injective (algebraMap K L).injective
    have : NeZero p := ⟨Nat.Prime.ne_zero hp.out⟩
    obtain ⟨i, _, hi⟩ := hωL.eq_pow_of_pow_eq_one hη
    exact ⟨ω ^ i, by rw [map_pow, hi]⟩
  · rw [not_exists] at hprim
    have h1 := no_prim_pth_root_in_unramified_ext A K p L B habsunram he
      hprim η hη
    exact ⟨1, by rw [map_one, h1]⟩

/-- The ramified direction of Corollary 10.18: if `p ∣ m` and the fraction
field `K` of a complete DVR contains no nontrivial `p`-th root of unity, then
the cyclotomic extension obtained by adjoining a primitive `m`-th root of
unity is ramified (its ramification index over the maximal ideal is not `1`),
when `(p)` is the maximal ideal of the ring and the residue field has
characteristic `p`. -/
theorem dvr_pth_root_ramified
    (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (p : ℕ) [hp : Fact (Nat.Prime p)]
    [Fintype (IsLocalRing.ResidueField A)]
    [CharP (IsLocalRing.ResidueField A) p]
    (hno_prim : ∀ ζ : K, ζ ^ p = 1 → ζ = 1)
    (m : ℕ) (hm : 0 < m) (hdvd : p ∣ m)
    (L : Type*) [Field L] [Algebra K L]
    [IsCyclotomicExtension {m} K L]
    [FiniteDimensional K L]
    (B : Type*) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsFractionRing B L]
    [IsScalarTower A B L] [IsScalarTower A K L]
    (habsunram : Ideal.span {(↑p : A)} = IsLocalRing.maximalIdeal A) :
    Ideal.ramificationIdx' (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) ≠ 1 := by
  intro he
  have hm_ne : m ≠ 0 := Nat.pos_iff_ne_zero.mp hm
  have hpp : Nat.Prime p := hp.out
  obtain ⟨ζ_m, hζ_m⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) hm_ne
  obtain ⟨j, hj⟩ := hdvd
  have hj_pos : 0 < j := Nat.pos_of_ne_zero (by intro h; simp [h] at hj; omega)
  have η_prim : IsPrimitiveRoot (ζ_m ^ j) p := by
    rw [hj] at hζ_m
    have hj_ne : j ≠ 0 := Nat.pos_iff_ne_zero.mp hj_pos
    have hj_dvd : j ∣ p * j := dvd_mul_left j p
    have h := hζ_m.pow_of_dvd hj_ne hj_dvd
    rwa [Nat.mul_div_cancel _ hj_pos] at h
  set η := ζ_m ^ j with hη_def
  obtain ⟨ζ, hζ⟩ := unramified_pth_root_in_base A K p L B habsunram he η
    η_prim.pow_eq_one
  have hζ_pow : ζ ^ p = 1 := by
    have h1 : algebraMap K L (ζ ^ p) = η ^ p := by rw [map_pow, hζ]
    rw [η_prim.pow_eq_one] at h1
    exact (algebraMap K L).injective (h1.trans (map_one _).symm)
  have hζ_eq : ζ = 1 := hno_prim ζ hζ_pow
  have hη_eq : η = 1 := by rw [← hζ, hζ_eq, map_one]
  exact η_prim.ne_one hpp.one_lt hη_eq

end
