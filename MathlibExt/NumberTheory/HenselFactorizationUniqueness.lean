/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from the following files in
https://github.com/TianyiPeng/fermats-last-theorem at commit
6e837e75355538c7f80bab5b956861e86c4eacc2:
* P2M/Sol/S_Polynomial_existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot.lean
* P2M/Sol/S_Polynomial_exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete.lean
and their paired Theorems/Thm_ wrappers.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The source NOTICE also credits Mathlib, copyright its respective authors,
released under the Apache License, Version 2.0. Neither source file has a
separate third-party entry in that revision's ATTRIBUTION.md.
The square-zero correction, nilpotent induction and resultant argument are
adapted here without the source's proof-extraction framework. Complete-ring
existence uses the existing public Hensel factorization theorem instead.
-/

module

public import MathlibExt.NumberTheory.HenselFactorization
import Mathlib.RingTheory.Henselian

/-!
# Coprimality and uniqueness of Hensel factors

Coprimality of polynomials, one of them monic, is reflected by local ring
homomorphisms. This gives uniqueness of a monic divisor with a specified
coprime reduction. We apply this to factor lifting over complete rings and
nilpotent thickenings. In the nilpotent case, the original polynomial and
the complementary reduced factor need not be monic.
-/

@[expose] public section

namespace Polynomial

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A local ring homomorphism reflects coprimality of polynomials when the
first polynomial is monic. Neither ring needs to be local. -/
theorem Monic.isCoprime_of_isCoprime_map {g h : R[X]} (hg : g.Monic)
    (π : R →+* S) [IsLocalHom π]
    (hcop : IsCoprime (g.map π) (h.map π)) : IsCoprime g h := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact ⟨0, 0, Subsingleton.elim _ _⟩
  have : Nontrivial S := ⟨⟨0, 1, fun h01 => not_isUnit_zero
    (isUnit_of_map_unit π 0 (by simpa only [map_zero, h01] using (isUnit_one : IsUnit (1 : S))))⟩⟩
  apply (isUnit_resultant_iff_isCoprime hg).mp
  apply IsUnit.of_map π
  rw [← resultant_map_map]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (natDegree_map_le (p := h) (f := π))
  rw [hg.natDegree_map π |>.symm, hk, resultant_add_right_deg _ _ _ _ _ le_rfl,
    (hg.map π).coeff_natDegree, one_pow, one_mul]
  exact (isUnit_resultant_iff_isCoprime (hg.map π)).mpr hcop

private theorem monic_eq_of_map_eq_of_dvd (π : R →+* S) [IsLocalHom π]
    {g h q : R[X]} (hg : g.Monic) (hq : q.Monic)
    (hcop : IsCoprime (g.map π) (h.map π))
    (hmap : q.map π = g.map π) (hdvd : q ∣ g * h) : q = g := by
  nontriviality R
  have : Nontrivial S := ⟨⟨0, 1, fun h01 => not_isUnit_zero
    (isUnit_of_map_unit π 0 (by simpa only [map_zero, h01] using (isUnit_one : IsUnit (1 : S))))⟩⟩
  have hc : IsCoprime q h := hq.isCoprime_of_isCoprime_map π (hmap ▸ hcop)
  have hd : g.natDegree = q.natDegree := by
    rw [← hg.natDegree_map π, ← hq.natDegree_map π, hmap]
  exact (eq_of_monic_of_dvd_of_natDegree_le hq hg
    (hc.dvd_of_dvd_mul_right hdvd) hd.le).symm

private theorem isLocalHom_of_nilpotent_ker (π : R →+* S)
    (hπ : Function.Surjective π) (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥) :
    IsLocalHom π := by
  constructor
  intro x hx
  obtain ⟨y, hy⟩ := hx.exists_left_inv
  obtain ⟨y, rfl⟩ := hπ y
  have hn : IsNilpotent (y * x - 1) := by
    obtain ⟨n, hn⟩ := hnil
    refine ⟨n, ?_⟩
    have hm : y * x - 1 ∈ RingHom.ker π := by
      simp only [RingHom.mem_ker, map_sub, map_mul, map_one, hy, sub_self]
    have hp := Ideal.pow_mem_pow hm n
    simpa only [hn, Ideal.mem_bot] using hp
  have hu : IsUnit (y * x) := by simpa only [sub_add_cancel] using hn.isUnit_add_one
  exact (IsUnit.mul_iff.mp hu).2

private theorem mul_eq_zero_of_map_eq_zero (π : R →+* S)
    (hsq : RingHom.ker π * RingHom.ker π = ⊥)
    {p q : R[X]} (hp : p.map π = 0) (hq : q.map π = 0) : p * q = 0 := by
  have mem (r : R[X]) (hr : r.map π = 0) : r ∈ (RingHom.ker π).map C := by
    rw [← ker_mapRingHom, RingHom.mem_ker, coe_mapRingHom]
    exact hr
  have h := Ideal.mul_mem_mul (mem p hp) (mem q hq)
  simpa only [← Ideal.map_mul, hsq, Ideal.map_bot, Ideal.mem_bot] using h

private theorem exists_monic_factor_of_sq_zero (π : R →+* S)
    (hπ : Function.Surjective π) (hsq : RingHom.ker π * RingHom.ker π = ⊥)
    (f : R[X]) (g' k' : S[X]) (hg' : g'.Monic) (hcop : IsCoprime g' k')
    (hfac : f.map π = g' * k') :
    ∃ g k : R[X], g.Monic ∧ g.map π = g' ∧ k.map π = k' ∧ f = g * k := by
  obtain ⟨g, hgmap, -, hg⟩ :=
    lifts_and_natDegree_eq_and_monic (mem_lifts_of_surjective hπ g') hg'
  obtain ⟨k, hk⟩ := map_surjective π hπ k'
  obtain ⟨u', v', huv⟩ := hcop
  obtain ⟨u, hu⟩ := map_surjective π hπ u'
  obtain ⟨v, hv⟩ := map_surjective π hπ v'
  let e := f - g * k
  let r := (v * e) %ₘ g
  let s := u * e + (v * e) /ₘ g * k
  have he : e.map π = 0 := by simp only [e, Polynomial.map_sub,
    Polynomial.map_mul, hgmap, hk, hfac, sub_self]
  have hr : r.map π = 0 := by
    simp only [r, map_modByMonic π hg, Polynomial.map_mul, he, mul_zero, zero_modByMonic]
  have hs : s.map π = 0 := by
    simp only [s, Polynomial.map_add, Polynomial.map_mul, map_divByMonic π hg,
      he, mul_zero, zero_divByMonic, zero_mul, add_zero]
  have hη : (u * g + v * k - 1).map π = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      hu, hv, hgmap, hk, huv, Polynomial.map_one, sub_self]
  have h₁ := modByMonic_add_div (v * e) g
  have h₂ := mul_eq_zero_of_map_eq_zero π hsq he hη
  have h₃ := mul_eq_zero_of_map_eq_zero π hsq hr hs
  refine ⟨g + r, k + s, ?_, ?_, ?_, ?_⟩
  · nontriviality R
    exact hg.add_of_left (degree_modByMonic_lt _ hg)
  · simp only [Polynomial.map_add, hgmap, hr, add_zero]
  · simp only [Polynomial.map_add, hk, hs, add_zero]
  · dsimp [e, r, s] at *
    linear_combination (-k) * h₁ - h₂ - h₃

private theorem exists_monic_factor_of_ker_pow (n : ℕ) :
    ∀ {R S : Type*} [CommRing R] [CommRing S] (π : R →+* S),
      Function.Surjective π → RingHom.ker π ^ n = ⊥ →
      ∀ (f : R[X]) (g' k' : S[X]), g'.Monic → IsCoprime g' k' →
        f.map π = g' * k' →
        ∃ g k : R[X], g.Monic ∧ g.map π = g' ∧ k.map π = k' ∧ f = g * k := by
  induction n with
  | zero =>
    intro R S _ _ π hπ hn f g' k' hg' hcop hfac
    have h1 : (1 : R) ∈ RingHom.ker π ^ 0 := by simp
    rw [hn, Ideal.mem_bot] at h1
    have : Subsingleton R := subsingleton_of_zero_eq_one h1.symm
    have : Subsingleton S := hπ.subsingleton
    exact ⟨0, 0, monic_of_subsingleton _, Subsingleton.elim _ _,
      Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  | succ n ih =>
    intro R S _ _ π hπ hn f g' k' hg' hcop hfac
    rcases Nat.eq_zero_or_pos n with rfl | hnpos
    · have hinj : Function.Injective π := by
        rwa [pow_one, ← RingHom.injective_iff_ker_eq_bot] at hn
      obtain ⟨g, hg⟩ := map_surjective π hπ g'
      obtain ⟨k, hk⟩ := map_surjective π hπ k'
      exact ⟨g, k, monic_of_injective hinj (hg.symm ▸ hg'), hg, hk,
        map_injective π hinj (by rw [Polynomial.map_mul, hg, hk, hfac])⟩
    · let J := RingHom.ker π ^ n
      let q := Ideal.Quotient.mk J
      let π₁ : R ⧸ J →+* S := Ideal.Quotient.lift J π
        (fun _ ha => Ideal.pow_le_self (Nat.ne_of_gt hnpos) ha)
      have hcomp : π₁.comp q = π := rfl
      have hπ₁ : Function.Surjective π₁ := by
        have h : Function.Surjective (π₁ ∘ q) := hπ
        exact h.of_comp
      have hker : RingHom.ker π₁ = (RingHom.ker π).map q := by
        conv_rhs => rw [← hcomp, ← RingHom.comap_ker]
        exact (Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective _).symm
      have hn₁ : RingHom.ker π₁ ^ n = ⊥ := by
        rw [hker, ← Ideal.map_pow]
        exact Ideal.map_quotient_self J
      have hsq : RingHom.ker q * RingHom.ker q = ⊥ := by
        rw [Ideal.mk_ker, ← pow_two, ← pow_mul]
        exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
      obtain ⟨g₁, k₁, hg₁, hgmap, hkmap, hfk⟩ :=
        ih π₁ hπ₁ hn₁ (f.map q) g' k' hg' hcop (by rw [Polynomial.map_map, hcomp, hfac])
      let := isLocalHom_of_nilpotent_ker π₁ hπ₁ ⟨n, hn₁⟩
      have hcop₁ : IsCoprime g₁ k₁ := hg₁.isCoprime_of_isCoprime_map π₁
        (by rw [hgmap, hkmap]; exact hcop)
      obtain ⟨g, k, hg, hgm, hkm, hprod⟩ :=
        exists_monic_factor_of_sq_zero q Ideal.Quotient.mk_surjective hsq f g₁ k₁ hg₁ hcop₁ hfk
      exact ⟨g, k, hg, by rw [← hcomp, ← Polynomial.map_map, hgm, hgmap],
        by rw [← hcomp, ← Polynomial.map_map, hkm, hkmap], hprod⟩

/-- A monic factor of a coprime factorization lifts uniquely through a
surjective homomorphism with nilpotent kernel. The original polynomial
and the complementary reduced factor are not required to be monic. -/
theorem existsUnique_monic_map_eq_dvd_of_isCoprime_of_ker_pow_eq_bot
    (π : R →+* S) (hπ : Function.Surjective π)
    (hnil : ∃ n : ℕ, RingHom.ker π ^ n = ⊥)
    (f : R[X]) (g' k' : S[X]) (hg' : g'.Monic) (hcop : IsCoprime g' k')
    (hfac : f.map π = g' * k') :
    ∃! g : R[X], g.Monic ∧ g.map π = g' ∧ g ∣ f := by
  obtain ⟨n, hn⟩ := hnil
  obtain ⟨g, k, hg, hgm, hkm, hprod⟩ :=
    exists_monic_factor_of_ker_pow n π hπ hn f g' k' hg' hcop hfac
  let := isLocalHom_of_nilpotent_ker π hπ ⟨n, hn⟩
  refine ⟨g, ⟨hg, hgm, ⟨k, hprod⟩⟩, ?_⟩
  rintro q ⟨hq, hqm, hqd⟩
  exact monic_eq_of_map_eq_of_dvd π hg hq (by rw [hgm, hkm]; exact hcop)
    (hqm.trans hgm.symm) (hprod ▸ hqd)

/-- Coprime monic factors lift over a ring complete at the kernel of a
surjective homomorphism. The lifts are coprime, and the first is the unique
monic divisor of the original polynomial with its specified reduction. -/
theorem exists_monic_mul_eq_and_map_eq_of_isCoprime_of_isAdicComplete
    (π : R →+* S) (hπ : Function.Surjective π)
    [IsAdicComplete (RingHom.ker π) R]
    {F : R[X]} (hF : F.Monic) {g₀ h₀ : S[X]} (hg₀ : g₀.Monic) (hh₀ : h₀.Monic)
    (hcop : IsCoprime g₀ h₀) (hF₀ : F.map π = g₀ * h₀) :
    ∃ g h : R[X], g.Monic ∧ h.Monic ∧ g * h = F ∧
      g.map π = g₀ ∧ h.map π = h₀ ∧ IsCoprime g h ∧
      ∀ g' : R[X], g'.Monic → g'.map π = g₀ → g' ∣ F → g' = g := by
  let I := RingHom.ker π
  let e : R ⧸ I ≃+* S := RingHom.quotientKerEquivOfSurjective hπ
  have he : e.toRingHom.comp (Ideal.Quotient.mk I) = π := rfl
  have he' : e.symm.toRingHom.comp π = Ideal.Quotient.mk I := by
    rw [← he]
    ext x
    exact e.symm_apply_apply _
  obtain ⟨g, h, hg, hh, hgh, hgm, hhm⟩ :=
    exists_monic_coprime_factorization_of_isAdicComplete I F hF
      (g₀.map e.symm.toRingHom) (h₀.map e.symm.toRingHom)
      (hg₀.map _) (hh₀.map _)
      (by rw [← he', ← Polynomial.map_map, hF₀, Polynomial.map_mul])
      (hcop.map (mapRingHom e.symm.toRingHom))
  have back {p : R[X]} {q : S[X]}
      (hpq : p.map (Ideal.Quotient.mk I) = q.map e.symm.toRingHom) : p.map π = q := by
    apply map_injective e.symm.toRingHom e.symm.injective
    rwa [Polynomial.map_map, he']
  have hgm' := back hgm
  have hhm' := back hhm
  let := isLocalHom_of_le_jacobson_bot I (IsAdicComplete.le_jacobson_bot I)
  have : IsLocalHom e.toRingHom :=
    ⟨fun x hx => by simpa using hx.map e.symm.toMonoidHom⟩
  have : IsLocalHom π := he ▸ RingHom.isLocalHom_comp e.toRingHom (Ideal.Quotient.mk I)
  refine ⟨g, h, hg, hh, hgh.symm, hgm', hhm',
    hg.isCoprime_of_isCoprime_map π (by rw [hgm', hhm']; exact hcop), ?_⟩
  intro q hq hqm hqd
  exact monic_eq_of_map_eq_of_dvd π hg hq (by rw [hgm', hhm']; exact hcop)
    (hqm.trans hgm'.symm) (hgh ▸ hqd)

end Polynomial
