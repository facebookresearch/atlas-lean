/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow.lean`
and
`P2M/Sol/S_MvPolynomial_finite_and_flat_and_finrank_expand_eq_pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Expand
public import Mathlib.RingTheory.Flat.Rank

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Flat.Basic

@[expose] public section

open MvPolynomial

universe u v

namespace MvPolynomial.ExpandRank

private theorem finite_flat_finrank_of_unique_decomposition
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    {ι : Type*} [Fintype ι] (b : ι → S)
    (hex : ∀ s : S, ∃ c : ι → R, ∑ i, f (c i) * b i = s)
    (huniq : ∀ c : ι → R, ∑ i, f (c i) * b i = 0 → ∀ i, c i = 0) :
    f.Finite ∧ f.Flat ∧ ∀ q, f.finrank q = Fintype.card ι := by
  letI : Algebra R S := f.toAlgebra
  have hsmul : ∀ (r : R) (s : S), r • s = f r * s := fun r s => Algebra.smul_def r s
  have hli : LinearIndependent R b := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    apply huniq
    simpa [hsmul] using hg
  have hsp : ⊤ ≤ Submodule.span R (Set.range b) := by
    rintro s -
    rw [Submodule.mem_span_range_iff_exists_fun]
    obtain ⟨c, hc⟩ := hex s
    exact ⟨c, by simpa [hsmul] using hc⟩
  let B : Module.Basis ι R S := Module.Basis.mk hli hsp
  haveI : Module.Free R S := Module.Free.of_basis B
  haveI : Module.Finite R S := Module.Finite.of_basis B
  refine ⟨‹Module.Finite R S›, (inferInstance : Module.Flat R S), fun q => ?_⟩
  haveI : Nontrivial R := q.nontrivial
  change Module.rankAtStalk S q = _
  rw [Module.rankAtStalk_eq_finrank_of_free, Pi.natCast_apply,
    Module.finrank_eq_card_basis B, Nat.cast_id]

section

variable {σ : Type*} (p : ℕ)

private noncomputable def divP (e : σ →₀ ℕ) : σ →₀ ℕ := e.mapRange (· / p) (by simp)

private lemma divP_apply (e : σ →₀ ℕ) (i : σ) : divP p e i = e i / p := by
  simp [divP]

variable [Finite σ]

private noncomputable def ofRes (r : σ → Fin p) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => (r i : ℕ))

private lemma ofRes_apply (r : σ → Fin p) (i : σ) : ofRes p r i = (r i : ℕ) := by
  simp [ofRes]

variable {p} (hp : 0 < p)
include hp

private def modP (e : σ →₀ ℕ) : σ → Fin p := fun i => ⟨e i % p, Nat.mod_lt _ hp⟩

private lemma modP_apply (e : σ →₀ ℕ) (i : σ) : (modP hp e i : ℕ) = e i % p := rfl

private lemma decomp (e : σ →₀ ℕ) : p • divP p e + ofRes p (modP hp e) = e := by
  ext i
  simp only [Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, divP_apply, ofRes_apply, modP_apply]
  have h := Nat.div_add_mod (e i) p
  omega

private lemma divP_add (d : σ →₀ ℕ) (r : σ → Fin p) :
    divP p (p • d + ofRes p r) = d := by
  ext i
  simp only [divP_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ofRes_apply]
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (r i).isLt,
    Nat.zero_add]

private lemma modP_add (d : σ →₀ ℕ) (r : σ → Fin p) :
    modP hp (p • d + ofRes p r) = r := by
  funext i
  apply Fin.ext
  simp only [modP_apply, Finsupp.coe_add, Finsupp.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, ofRes_apply]
  rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r i).isLt]

private lemma le_and_dvd_iff (e : σ →₀ ℕ) (r : σ → Fin p) :
    (ofRes p r ≤ e ∧ ∀ i, p ∣ (e - ofRes p r) i) ↔ modP hp e = r := by
  constructor
  · rintro ⟨hle, hdvd⟩
    funext i
    apply Fin.ext
    simp only [modP_apply]
    have h1 : (r i : ℕ) ≤ e i := by
      have hh := hle i
      rwa [ofRes_apply] at hh
    have h2 : p ∣ e i - r i := by
      have hh := hdvd i
      simp only [Finsupp.coe_tsub, Pi.sub_apply, ofRes_apply] at hh
      exact hh
    obtain ⟨k, hk⟩ := h2
    have hthis : e i = r i + p * k := by omega
    rw [hthis, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (r i).isLt]
  · rintro rfl
    refine ⟨fun i => ?_, fun i => ?_⟩
    · rw [ofRes_apply]
      simpa [modP_apply] using Nat.mod_le (e i) p
    · refine ⟨e i / p, ?_⟩
      simp only [Finsupp.coe_tsub, Pi.sub_apply, ofRes_apply, modP_apply]
      have h := Nat.div_add_mod (e i) p
      omega

private lemma sub_ofRes_modP (e : σ →₀ ℕ) :
    e - ofRes p (modP hp e) = p • divP p e := by
  ext i
  simp only [Finsupp.coe_tsub, Pi.sub_apply, ofRes_apply, modP_apply,
    Finsupp.coe_smul, Pi.smul_apply, divP_apply, smul_eq_mul]
  have h := Nat.div_add_mod (e i) p
  omega

end

section

variable {R : Type*} [CommRing R] {σ : Type*} [Finite σ] {p : ℕ} (hp : 0 < p)
include hp

private noncomputable def bvec (r : σ → Fin p) : MvPolynomial σ R :=
  monomial (ofRes p r) 1

private lemma coeff_expand_mul_bvec [DecidableEq (σ → Fin p)]
    (c : MvPolynomial σ R) (r : σ → Fin p) (e : σ →₀ ℕ) :
    (expand p c * bvec r).coeff e =
      if modP hp e = r then c.coeff (divP p e) else 0 := by
  classical
  rw [show (bvec (R := R) r : MvPolynomial σ R) = monomial (ofRes p r) 1 from rfl,
    coeff_mul_monomial', mul_one]
  by_cases hr : modP hp e = r
  · rw [ite_eq_left hr]
    have hle : ofRes p r ≤ e := ((le_and_dvd_iff hp e r).mpr hr).1
    rw [ite_eq_left hle]
    subst hr
    rw [sub_ofRes_modP hp e, coeff_expand_smul _ hp.ne']
  · rw [ite_eq_right hr]
    split_ifs with hle
    · have hnot : ¬ ∀ i, p ∣ (e - ofRes p r) i :=
        fun h => hr ((le_and_dvd_iff hp e r).mp ⟨hle, h⟩)
      push Not at hnot
      obtain ⟨i, hi⟩ := hnot
      exact coeff_expand_of_not_dvd _ hi
    · rfl

end

section

variable {R : Type*} [CommRing R] {σ : Type*} [Fintype σ] [DecidableEq σ]
  {p : ℕ} (hp : 0 < p)
include hp

private noncomputable def Ψ (c : (σ → Fin p) → MvPolynomial σ R) :
    MvPolynomial σ R :=
  ∑ r, expand p (c r) * bvec r

private lemma coeff_Ψ (c : (σ → Fin p) → MvPolynomial σ R) (e : σ →₀ ℕ) :
    (Ψ c).coeff e = (c (modP hp e)).coeff (divP p e) := by
  classical
  rw [show Ψ c = ∑ r, expand p (c r) * bvec r from rfl, coeff_sum]
  simp_rw [coeff_expand_mul_bvec hp]
  rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]

private lemma Ψ_eq_zero (c : (σ → Fin p) → MvPolynomial σ R) (h : Ψ c = 0) :
    ∀ r, c r = 0 := by
  intro r
  ext d
  have hcoeff := coeff_Ψ hp c (p • d + ofRes p r)
  rw [h, MvPolynomial.coeff_zero, divP_add hp, modP_add hp] at hcoeff
  simpa using hcoeff.symm

private lemma Ψ_surjective (s : MvPolynomial σ R) :
    ∃ c : (σ → Fin p) → MvPolynomial σ R, Ψ c = s := by
  classical
  refine ⟨fun r => ∑ e ∈ s.support,
    if modP hp e = r then monomial (divP p e) (s.coeff e) else 0, ?_⟩
  ext e
  rw [coeff_Ψ hp, coeff_sum]
  refine (Finset.sum_eq_single e ?_ ?_).trans ?_
  · intro b _ hb
    show ((if modP hp b = modP hp e then monomial (divP p b) (s.coeff b)
      else 0).coeff (divP p e)) = 0
    by_cases hmod : modP hp b = modP hp e
    · have hdiv : divP p b ≠ divP p e := by
        intro hd
        apply hb
        rw [← decomp hp b, ← decomp hp e, hmod, hd]
      rw [ite_eq_left hmod, coeff_monomial, ite_eq_right hdiv]
    · rw [ite_eq_right hmod]
      simp
  · intro hmem
    show ((if modP hp e = modP hp e then monomial (divP p e) (s.coeff e)
      else 0).coeff (divP p e)) = 0
    rw [ite_eq_left rfl, coeff_monomial, ite_eq_left rfl]
    exact notMem_support_iff.mp hmem
  · show ((if modP hp e = modP hp e then monomial (divP p e) (s.coeff e)
      else 0).coeff (divP p e)) = s.coeff e
    rw [ite_eq_left rfl, coeff_monomial, ite_eq_left rfl]

end

end MvPolynomial.ExpandRank

namespace MvPolynomial

/-- The expansion endomorphism `MvPolynomial.expand p` is finite and flat, and
its fibre rank at every prime is `p ^ Nat.card σ` when `σ` is finite and
`0 < p`. The monomials `X ^ r` with `0 ≤ r i < p` form a free basis over the
image of `expand p`. -/
public theorem finite_and_flat_and_finrank_expand_eq_pow
    (R : Type u) [CommRing R] (σ : Type v) [Finite σ] (p : ℕ) (hp : 0 < p) :
    (expand p (σ := σ) (R := R)).toRingHom.Finite ∧
      (expand p (σ := σ) (R := R)).toRingHom.Flat ∧
      ∀ q : PrimeSpectrum (MvPolynomial σ R),
        (expand p (σ := σ) (R := R)).toRingHom.finrank q = p ^ Nat.card σ := by
  classical
  haveI : Fintype σ := Fintype.ofFinite σ
  have h := ExpandRank.finite_flat_finrank_of_unique_decomposition
    (expand p (σ := σ) (R := R)).toRingHom (ι := σ → Fin p)
    (ExpandRank.bvec (R := R))
    (fun s => by
      obtain ⟨c, hc⟩ := ExpandRank.Ψ_surjective hp s
      exact ⟨c, hc⟩)
    (fun c hc => ExpandRank.Ψ_eq_zero hp c hc)
  refine ⟨h.1, h.2.1, fun q => ?_⟩
  rw [h.2.2 q, Fintype.card_fun, Fintype.card_fin, Nat.card_eq_fintype_card]

end MvPolynomial
