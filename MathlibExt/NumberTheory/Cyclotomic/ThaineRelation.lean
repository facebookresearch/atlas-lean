/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ExtCitation_Cyclotomic_thaine_relation_plusField.lean` and
`P2M/Sol/S_ExtCitation_Cyclotomic_thaine_relation_plusField.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import MathlibExt.NumberTheory.Cyclotomic.UnitsModPowersEigenspace
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.RootsOfUnity.Lemmas
import MathlibExt.NumberTheory.Cyclotomic.CyclotomicUnitOmegaTwo
import MathlibExt.NumberTheory.Cyclotomic.UnitsOmegaEigenspaceFinrank

/-!
# A Thaine relation for a degree-one prime of `ℚ(ζ_p)⁺`

For a prime `p ≥ 5`, `Stickelberger.thaine_relation_plusField` takes a totally real field `K⁺`
over which `ℚ(ζ_p)` has degree 2, a unit `δ` of `𝓞 K⁺` in the `ω²` eigenspace modulo `p`-th
powers, and a prime `𝔏` of `K⁺` of absolute norm `ℓ ≠ p` modulo which `δ` is not a `p`-th power.
It produces `α ≠ 0`, `t ≠ 0` in `ZMod p` and an ideal `J` with
`(α) = ∏_d σ_d(𝔏) ^ (t d⁻²) · J ^ p`: the `ω²` component of the class of `𝔏` is trivial in
`Cl(K⁺) / p`.

## References

* F. Thaine, *On the ideal class groups of real abelian number fields*, Ann. of Math. (2) 128
  (1988), 1–18.
* L. C. Washington, *Introduction to Cyclotomic Fields*, 2nd ed., Graduate Texts in Mathematics
  83, Springer, 1997, Chapter 15 (Thaine's theorem).

The statement is the per-prime step of Thaine's argument, specialized to the `ω²` eigenspace of
`ℚ(ζ_p)⁺`. Neither source states it verbatim as a numbered result, so the citation is to the
argument, not to a theorem number.

## Modeling notes

* `Kplus` is any totally real field with `[Algebra Kplus (CyclotomicField p ℚ)]` and
  `Module.finrank Kplus (CyclotomicField p ℚ) = 2`. Its image is the unique index-2 subfield of
  `ℚ(ζ_p)`, the source's `K⁺ = ℚ(ζ_p + ζ_p⁻¹)`. `Kplus` is universe-polymorphic.
* The source's action of `Gal(K⁺ / ℚ)` is `Δact : (ZMod p)ˣ →* (𝓞 Kplus ≃+* 𝓞 Kplus)`, which
  `hΔact` makes compatible with `Stickelberger.clRingAction`, the transport of
  `Gal(ℚ(ζ_p) / ℚ) ≃ (ZMod p)ˣ` to ring automorphisms of `𝓞 (ℚ(ζ_p))`.
  With the pinned Mathlib, `IsCyclotomicExtension {p} ℚ (CyclotomicField p ℚ)` is not
  synthesized under default options, so stating `hΔact` needs
  `attribute [local instance] Stickelberger.instIsCycExt` or
  `set_option backward.isDefEq.respectTransparency false`, as the test file does.
* The Teichmüller character `ω` enters through its reduction `d ↦ (d : ZMod p)`: `hδeig` says
  `σ_d δ = δ ^ (d²) · v ^ p`, the `ω²` eigen-condition on `E⁺ / (E⁺) ^ p`.
* A degree-one prime is a maximal ideal `𝔏` with `Ideal.absNorm 𝔏 = ℓ`. The hypothesis that `δ`
  is not a `p`-th power modulo `𝔏` can only hold when `p ∣ ℓ - 1`, as for the source's auxiliary
  primes.
* The conclusion uses fractional ideals and exponents `(t * (d ^ 2)⁻¹).val ∈ [0, p)` rather than
  `Stickelberger.ClGalModule`. Up to the unit `t`, the exponents are the coefficients of
  `(p - 1) e₂`, where `e₂ = (p - 1)⁻¹ ∑_d (d²)⁻¹ σ_d` is the source's idempotent, here
  `Stickelberger.omegaIdempotent` with `i = 2`.
* The proof uses `Stickelberger.finrank_unitsOmegaEigenspace_two` (the `ω²` eigenspace
  `Stickelberger.unitsOmegaEigenspace p 2` of `E / E ^ p` is a line) and
  `Stickelberger.omegaIdempotent_two_cycloUnitTwo_ne_zero` (the cyclotomic unit `1 + ζ_p` has
  nonzero `ω²` component).
* `p ≥ 5` excludes `p = 3`, where `ω²` is trivial.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open NumberField Stickelberger
open scoped nonZeroDivisors

attribute [local instance] Stickelberger.instIsCycExt

open NumberField IsCyclotomicExtension Polynomial UniqueFactorizationMonoid

namespace ThaineAux

variable (F : Type*) [Field F] [NumberField F]
variable (L : Type*) [Field L] [NumberField L] [Algebra F L]
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime] [IsCyclotomicExtension {ℓ} F L]

private noncomputable def zetaInt : 𝓞 L :=
  haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  (zeta_spec ℓ F L).toInteger

omit [NumberField F] [NumberField L] in
private lemma zetaInt_isPrimitiveRoot : IsPrimitiveRoot (zetaInt F L ℓ) ℓ := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  exact (zeta_spec ℓ F L).toInteger_isPrimitiveRoot

omit [NumberField F] [NumberField L] in
private lemma associated_natCast_pow : Associated ((ℓ : 𝓞 L)) ((zetaInt F L ℓ - 1) ^ (ℓ - 1)) := by
  have hζ := zetaInt_isPrimitiveRoot F L ℓ
  obtain ⟨n, hn⟩ : ∃ n, ℓ = n + 1 := ⟨ℓ - 1, (Nat.succ_pred_eq_of_pos hℓ.out.pos).symm⟩
  have hζ' : IsPrimitiveRoot (zetaInt F L ℓ) (n + 1) := hn ▸ hζ
  have hprod := hζ'.prod_one_sub_pow_eq_order
  have hℓn : (ℓ : 𝓞 L) = ∏ k ∈ Finset.range n, (1 - zetaInt F L ℓ ^ (k + 1)) := by
    rw [hprod, hn, Nat.cast_succ]
  rw [hℓn, show ℓ - 1 = n by omega]
  conv_rhs => rw [← Finset.card_range n, ← Finset.prod_const]
  refine Associated.prod _ _ _ fun k hk => ?_
  have hcop : (k + 1).Coprime ℓ := by
    rw [Finset.mem_range] at hk
    exact Nat.Coprime.symm (Nat.coprime_of_lt_prime (by omega) (by omega) hℓ.out)
  have h1 := hζ.associated_sub_one_pow_sub_one_of_coprime hcop
  refine (h1.trans ?_).symm
  have hneg : (1 : 𝓞 L) - zetaInt F L ℓ ^ (k + 1) = -(zetaInt F L ℓ ^ (k + 1) - 1) := by ring
  rw [hneg]
  exact (Associated.refl _).neg_right

omit [NumberField F] [NumberField L] in
private lemma span_natCast_eq_pow :
    Ideal.span {(ℓ : 𝓞 L)} = Ideal.span {zetaInt F L ℓ - 1} ^ (ℓ - 1) := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_eq_span_singleton]
  exact associated_natCast_pow F L ℓ

omit [NumberField F] in
private lemma finrank_le : Module.finrank F L ≤ ℓ - 1 := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hζ := zeta_spec ℓ F L
  rw [(hζ.powerBasis F).finrank, IsPrimitiveRoot.powerBasis_dim]
  have hdvd : minpoly F (zeta ℓ F L) ∣ cyclotomic ℓ F := by
    refine minpoly.dvd F _ ?_
    have : NeZero ((ℓ : ℕ) : L) := NeZero.charZero
    exact aeval_zeta ℓ F L
  calc (minpoly F (zeta ℓ F L)).natDegree ≤ (cyclotomic ℓ F).natDegree :=
        natDegree_le_of_dvd hdvd (cyclotomic_ne_zero ℓ F)
    _ = ℓ - 1 := by rw [natDegree_cyclotomic, Nat.totient_prime hℓ.out]

section Ramification

variable {F L}
variable (𝔔 : Ideal (𝓞 F)) [𝔔.IsMaximal] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [h𝔓𝔔 : 𝔓.LiesOver 𝔔]

private theorem ram_package (hℓ𝔔 : (ℓ : 𝓞 F) ∈ 𝔔) (hℓ𝔔2 : (ℓ : 𝓞 F) ∉ 𝔔 ^ 2) :
    Module.finrank F L = ℓ - 1 ∧
    Ideal.ramificationIdx' 𝔔 𝔓 = ℓ - 1 ∧
    Ideal.inertiaDeg' 𝔔 𝔓 = 1 ∧
    Ideal.primesOver 𝔔 (𝓞 L) = {𝔓} ∧
    𝔔.map (algebraMap (𝓞 F) (𝓞 L)) = 𝔓 ^ (ℓ - 1) ∧
    (zetaInt F L ℓ - 1) ∈ 𝔓 ∧ (zetaInt F L ℓ - 1) ∉ 𝔓 ^ 2 := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hℓ2 : 2 ≤ ℓ := hℓ.out.two_le
  obtain ⟨u, hu⟩ := associated_natCast_pow F L ℓ
  have hspan := span_natCast_eq_pow F L ℓ
  set lam : 𝓞 L := zetaInt F L ℓ - 1 with hlam

  have h𝔔bot : 𝔔 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at hℓ𝔔
    exact hℓ.out.ne_zero (by exact_mod_cast hℓ𝔔)
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔔bot 𝔓
  have h𝔓max : 𝔓.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔓bot ‹_›
  have hmap0 : 𝔔.map (algebraMap (𝓞 F) (𝓞 L)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot h𝔔bot
  have hunder : Ideal.comap (algebraMap (𝓞 F) (𝓞 L)) 𝔓 = 𝔔 := (h𝔓𝔔.over).symm

  have hℓ𝔓 : (ℓ : 𝓞 L) ∈ 𝔓 := by
    have : algebraMap (𝓞 F) (𝓞 L) ℓ ∈ 𝔓 := by rw [← Ideal.mem_comap, hunder]; exact hℓ𝔔
    simpa using this
  have hlam𝔓 : lam ∈ 𝔓 := by
    refine Ideal.IsPrime.mem_of_pow_mem ‹_› (ℓ - 1) ?_
    rw [← hu]
    exact Ideal.mul_mem_right _ _ hℓ𝔓

  obtain ⟨𝔞, h𝔞⟩ : 𝔔 ∣ Ideal.span {(ℓ : 𝓞 F)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hℓ𝔔)
  have h𝔞le : ¬ 𝔞 ≤ 𝔔 := by
    intro h
    apply hℓ𝔔2
    have : 𝔔 ^ 2 ∣ Ideal.span {(ℓ : 𝓞 F)} := by
      rw [h𝔞, pow_two]
      exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr h)
    exact (Ideal.span_singleton_le_iff_mem _).mp (Ideal.dvd_iff_le.mp this)

  have hmapℓ : 𝔔.map (algebraMap (𝓞 F) (𝓞 L)) * 𝔞.map (algebraMap (𝓞 F) (𝓞 L)) = Ideal.span {lam} ^
      (ℓ - 1) := by
    rw [← Ideal.map_mul, ← h𝔞, Ideal.map_span, Set.image_singleton, map_natCast]
    exact hspan

  have h𝔞𝔓 : ¬ 𝔞.map (algebraMap (𝓞 F) (𝓞 L)) ≤ 𝔓 := by
    intro h
    rw [Ideal.map_le_iff_le_comap, hunder] at h
    exact h𝔞le h
  have hsup : 𝔓 ⊔ 𝔞.map (algebraMap (𝓞 F) (𝓞 L)) = ⊤ := h𝔓max.out.2 _ (left_lt_sup.mpr h𝔞𝔓)
  have hcop : IsCoprime 𝔓 (𝔞.map (algebraMap (𝓞 F) (𝓞 L))) := Ideal.isCoprime_iff_sup_eq.mpr hsup

  have hPirr := (Ideal.prime_of_isPrime h𝔓bot ‹_›).irreducible
  have hcount : ∀ n : ℕ, 𝔓 ^ n ∣ 𝔔.map (algebraMap (𝓞 F) (𝓞 L)) →
      n ≤ Ideal.ramificationIdx' 𝔔 𝔓 := by
    intro n hn
    rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 ‹_› h𝔓bot]
    rwa [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ h𝔓bot) hmap0,
      normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
      Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le] at hn
  have hdvd1 : 𝔓 ^ (ℓ - 1) ∣ 𝔔.map (algebraMap (𝓞 F) (𝓞 L)) := by
    refine (hcop.pow_left).dvd_of_dvd_mul_right ?_
    rw [hmapℓ]
    exact pow_dvd_pow_of_dvd
        (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hlam𝔓)) _
  have he : ℓ - 1 ≤ Ideal.ramificationIdx' 𝔔 𝔓 := hcount _ hdvd1

  have hsum := Ideal.sum_ramification_inertia (R := 𝓞 F) (𝓞 L) F L (p := 𝔔) h𝔔bot
  have h𝔓mem : 𝔓 ∈ IsDedekindDomain.primesOverFinset 𝔔 (𝓞 L) :=
    (IsDedekindDomain.mem_primesOverFinset_iff h𝔔bot _).mpr ⟨‹_›, ‹_›⟩
  have hf : 0 < Ideal.inertiaDeg' 𝔔 𝔓 := Ideal.inertiaDeg'_pos' 𝔔 𝔓
  have hfin := finrank_le F L ℓ
  rw [← Finset.add_sum_erase _ _ h𝔓mem] at hsum
  set T := ∑ P ∈ (IsDedekindDomain.primesOverFinset 𝔔 (𝓞 L)).erase 𝔓,
    Ideal.ramificationIdx' 𝔔 P * Ideal.inertiaDeg' 𝔔 P with hT
  have hef : ℓ - 1 ≤ Ideal.ramificationIdx' 𝔔 𝔓 * Ideal.inertiaDeg' 𝔔 𝔓 :=
    le_mul_of_le_of_one_le he hf
  set ef := Ideal.ramificationIdx' 𝔔 𝔓 * Ideal.inertiaDeg' 𝔔 𝔓 with hef_def
  have hT0 : T = 0 := by omega
  have hfin' : Module.finrank F L = ℓ - 1 := by omega
  have hef' : ef = ℓ - 1 := by omega
  have hf1 : Ideal.inertiaDeg' 𝔔 𝔓 = 1 := by
    by_contra hne
    have hf2 : 2 ≤ Ideal.inertiaDeg' 𝔔 𝔓 := by omega
    have h2ef : (ℓ - 1) * 2 ≤ ef := by
      rw [hef_def]; exact Nat.mul_le_mul he hf2
    omega
  have he' : Ideal.ramificationIdx' 𝔔 𝔓 = ℓ - 1 := by
    rw [hef_def, hf1, mul_one] at hef'; exact hef'
  rw [hT] at hT0

  have herase : (IsDedekindDomain.primesOverFinset 𝔔 (𝓞 L)).erase 𝔓 = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro P hP
    have hP' := Finset.mem_of_mem_erase hP
    obtain ⟨hP1, hP2⟩ := (IsDedekindDomain.mem_primesOverFinset_iff h𝔔bot _).mp hP'
    have := hP1
    have := hP2
    have h1 : Ideal.ramificationIdx' 𝔔 P ≠ 0 :=
      Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver P h𝔔bot
    have h2 : 0 < Ideal.inertiaDeg' 𝔔 P := Ideal.inertiaDeg'_pos' 𝔔 P
    have h3 : Ideal.ramificationIdx' 𝔔 P * Ideal.inertiaDeg' 𝔔 P = 0 :=
      (Finset.sum_eq_zero_iff.mp hT0) P hP
    rcases Nat.mul_eq_zero.mp h3 with h | h <;> omega
  have hsingle : IsDedekindDomain.primesOverFinset 𝔔 (𝓞 L) = {𝔓} := by
    rcases (Finset.erase_eq_empty_iff _ _).mp herase with h | h
    · rw [h] at h𝔓mem; simp at h𝔓mem
    · exact h
  have hprimesOver : Ideal.primesOver 𝔔 (𝓞 L) = {𝔓} := by
    rw [← IsDedekindDomain.coe_primesOverFinset h𝔔bot (𝓞 L), hsingle, Finset.coe_singleton]

  have hnf : normalizedFactors (𝔔.map (algebraMap (𝓞 F) (𝓞 L))) = Multiset.replicate (ℓ - 1) 𝔓 := by
    have hall : ∀ b ∈ normalizedFactors (𝔔.map (algebraMap (𝓞 F) (𝓞 L))), b = 𝔓 := by
      intro b hb
      have : b ∈ IsDedekindDomain.primesOverFinset 𝔔 (𝓞 L) := by
        simpa [IsDedekindDomain.primesOverFinset, factors_eq_normalizedFactors,
          UniqueFactorizationMonoid.mem_primeFactors] using hb
      rw [hsingle, Finset.mem_singleton] at this
      exact this
    rw [Multiset.eq_replicate]
    refine ⟨?_, hall⟩
    rw [← Multiset.count_eq_card.mpr (fun b hb => (hall b hb).symm),
      ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmap0 ‹_› h𝔓bot, he']
  have hmapeq : 𝔔.map (algebraMap (𝓞 F) (𝓞 L)) = 𝔓 ^ (ℓ - 1) := by
    rw [← associated_iff_eq.mp (prod_normalizedFactors hmap0), hnf, Multiset.prod_replicate]

  have hlam2 : lam ∉ 𝔓 ^ 2 := by
    intro h
    have h2 : (𝔓 ^ 2) ^ (ℓ - 1) ∣ 𝔔.map (algebraMap (𝓞 F) (𝓞 L)) := by
      refine (hcop.pow_left.pow_left).dvd_of_dvd_mul_right ?_
      rw [hmapℓ]
      exact pow_dvd_pow_of_dvd (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr h)) _
    rw [← pow_mul] at h2
    have := hcount _ h2
    rw [he'] at this
    omega
  exact ⟨hfin', he', hf1, hprimesOver, hmapeq, hlam𝔓, hlam2⟩

end Ramification

private lemma le_ramificationIdx_of_pow_dvd {R S : Type*} [CommRing R] [CommRing S]
    [IsDedekindDomain S]
    [Algebra R S] {p : Ideal R} {P : Ideal S} [hP : P.IsPrime] (hP0 : P ≠ ⊥)
    (hp0 : p.map (algebraMap R S) ≠ ⊥) {n : ℕ} (h : P ^ n ∣ p.map (algebraMap R S)) :
    n ≤ Ideal.ramificationIdx' p P := by
  classical
  have hPirr := (Ideal.prime_of_isPrime hP0 hP).irreducible
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hp0 hP hP0]
  rwa [dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero _ hP0) hp0,
    normalizedFactors_pow, normalizedFactors_irreducible hPirr, normalize_eq,
    Multiset.nsmul_singleton, ← Multiset.le_count_iff_replicate_le] at h

omit [NumberField F] in
private lemma irreducible_cyclotomic (h : Module.finrank F L = ℓ - 1) [FiniteDimensional F L] :
    Irreducible (cyclotomic ℓ F) := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hζ := zeta_spec ℓ F L
  have hint : IsIntegral F (zeta ℓ F L) := .of_finite F _
  have hdvd : minpoly F (zeta ℓ F L) ∣ cyclotomic ℓ F := by
    refine minpoly.dvd F _ ?_
    have : NeZero ((ℓ : ℕ) : L) := NeZero.charZero
    exact aeval_zeta ℓ F L
  have hdeg : (cyclotomic ℓ F).natDegree ≤ (minpoly F (zeta ℓ F L)).natDegree := by
    rw [natDegree_cyclotomic, Nat.totient_prime hℓ.out, ← IsPrimitiveRoot.powerBasis_dim F hζ,
      ← (hζ.powerBasis F).finrank, h]
  have heq := eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic ℓ F)
    hdvd hdeg
  rw [heq]
  exact minpoly.irreducible hint

section Residue

variable {F L}
variable (𝔔 : Ideal (𝓞 F)) [𝔔.IsMaximal] (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] [h𝔓𝔔 : 𝔓.LiesOver 𝔔]

private theorem algEquiv_sub_self_mem (hℓ𝔔 : (ℓ : 𝓞 F) ∈ 𝔔) (hℓ𝔔2 : (ℓ : 𝓞 F) ∉ 𝔔 ^ 2)
    (τ : (𝓞 L) ≃ₐ[𝓞 F] (𝓞 L)) (x : 𝓞 L) : τ x - x ∈ 𝔓 := by
  classical
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  obtain ⟨-, -, hf1, hprimes, -, -, -⟩ := ram_package ℓ 𝔔 𝔓 hℓ𝔔 hℓ𝔔2
  have h𝔔bot : 𝔔 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mem_bot] at hℓ𝔔
    exact hℓ.out.ne_zero (by exact_mod_cast hℓ𝔔)
  have h𝔓bot : 𝔓 ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔔bot 𝔓
  have h𝔓max : 𝔓.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔓bot ‹_›

  have hmap : 𝔓.map τ = 𝔓 := by
    have h1 : 𝔓.map τ ∈ Ideal.primesOver 𝔔 (𝓞 L) :=
      ⟨Ideal.map_isPrime_of_equiv τ, inferInstance⟩
    rw [hprimes, Set.mem_singleton_iff] at h1
    exact h1

  let : Field (𝓞 F ⧸ 𝔔) := Ideal.Quotient.field 𝔔
  have : Nontrivial (𝓞 L ⧸ 𝔓) := Ideal.Quotient.nontrivial_of_liesOver_of_isPrime 𝔓 𝔔
  have hbot : (⊥ : Subalgebra (𝓞 F ⧸ 𝔔) (𝓞 L ⧸ 𝔓)) = ⊤ :=
    Subalgebra.bot_eq_top_of_finrank_eq_one (by rw [← Ideal.inertiaDeg'_algebraMap]; exact hf1)
  have hx : Ideal.Quotient.mk 𝔓 x ∈ (⊥ : Subalgebra (𝓞 F ⧸ 𝔔) (𝓞 L ⧸ 𝔓)) := by
    rw [hbot]; exact Algebra.mem_top
  rw [Algebra.mem_bot] at hx
  obtain ⟨ybar, hy⟩ := hx
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective ybar
  rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.Quotient.eq] at hy

  have h2 : τ (algebraMap (𝓞 F) (𝓞 L) y - x) ∈ 𝔓 := by
    have := Ideal.mem_map_of_mem τ hy
    rwa [hmap] at this
  rw [map_sub, AlgEquiv.commutes] at h2
  have : τ x - x = (algebraMap (𝓞 F) (𝓞 L) y - x) - (algebraMap (𝓞 F) (𝓞 L) y - τ x) := by
    ring
  rw [this]
  exact Ideal.sub_mem _ hy h2

private theorem galRestrict_sub_self_mem (hℓ𝔔 : (ℓ : 𝓞 F) ∈ 𝔔) (hℓ𝔔2 : (ℓ : 𝓞 F) ∉ 𝔔 ^ 2)
    (σ : L ≃ₐ[F] L) (x : 𝓞 L) : galRestrict (𝓞 F) F L (𝓞 L) σ x - x ∈ 𝔓 :=
  algEquiv_sub_self_mem ℓ 𝔔 𝔓 hℓ𝔔 hℓ𝔔2 _ x

private lemma smul_eq_galRestrict (σ : L ≃ₐ[F] L) (x : 𝓞 L) :
    σ • x = galRestrict (𝓞 F) F L (𝓞 L) σ x := by
  apply RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply]
  rfl

private theorem smul_sub_self_mem (hℓ𝔔 : (ℓ : 𝓞 F) ∈ 𝔔) (hℓ𝔔2 : (ℓ : 𝓞 F) ∉ 𝔔 ^ 2)
    (σ : L ≃ₐ[F] L) (x : 𝓞 L) : σ • x - x ∈ 𝔓 := by
  rw [smul_eq_galRestrict]
  exact galRestrict_sub_self_mem ℓ 𝔔 𝔓 hℓ𝔔 hℓ𝔔2 σ x

private lemma galRestrict_zetaInt (σ : L ≃ₐ[F] L) :
    haveI : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
    galRestrict (𝓞 F) F L (𝓞 L) σ (zetaInt F L ℓ) =
      zetaInt F L ℓ ^ (((zeta_spec ℓ F L).autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ).val := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  apply RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply, map_pow]
  exact ((zeta_spec ℓ F L).autToPow_spec F σ).symm

end Residue

section Inertia

variable {F L}

private theorem inertia_eq_bot (𝔓 : Ideal (𝓞 L)) [𝔓.IsPrime] (hℓ𝔓 : (ℓ : 𝓞 L) ∉ 𝔓) :
    𝔓.inertia (L ≃ₐ[F] L) = ⊥ := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have : Fact (1 < ℓ) := ⟨hℓ.out.one_lt⟩
  have hζ := zetaInt_isPrimitiveRoot F L ℓ
  have hζL := zeta_spec ℓ F L
  rw [eq_bot_iff]
  intro σ hσ
  rw [Subgroup.mem_bot]
  have h1 : σ • zetaInt F L ℓ - zetaInt F L ℓ ∈ 𝔓 :=
    (AddSubgroup.mem_inertia.mp hσ) (zetaInt F L ℓ)
  set k : ℕ := ((hζL.autToPow F σ : (ZMod ℓ)ˣ) : ZMod ℓ).val with hk
  have hσζ : σ • zetaInt F L ℓ = zetaInt F L ℓ ^ k := by
    rw [smul_eq_galRestrict, galRestrict_zetaInt]
  rw [hσζ] at h1
  have hunit : ∀ u : (𝓞 L), IsUnit u → u ∉ 𝔓 := fun u hu h =>
    ‹𝔓.IsPrime›.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  have hk0 : k ≠ 0 := by
    rw [hk, ne_eq, ZMod.val_eq_zero]
    exact Units.ne_zero _
  have hklt : k < ℓ := ZMod.val_lt _
  by_cases hk1 : k = 1
  · have hu : (hζL.autToPow F σ : (ZMod ℓ)ˣ) = 1 := by
      rw [← Units.val_eq_one]
      apply ZMod.val_injective ℓ
      rw [ZMod.val_one]
      exact hk1
    apply hζL.autToPow_injective F
    rw [hu, map_one]
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hm0 : 1 ≤ m := by omega
    have hfac : zetaInt F L ℓ ^ k - zetaInt F L ℓ =
        zetaInt F L ℓ * (zetaInt F L ℓ ^ m - 1) := by
      rw [hm]; ring
    rw [hfac] at h1
    have hζunit : IsUnit (zetaInt F L ℓ) := hζ.isUnit hℓ.out.ne_zero
    have h2 : zetaInt F L ℓ ^ m - 1 ∈ 𝔓 :=
      (‹𝔓.IsPrime›.mem_or_mem h1).resolve_left (hunit _ hζunit)
    have hcop : m.Coprime ℓ := Nat.Coprime.symm
        (Nat.coprime_of_lt_prime (by omega) (by omega) hℓ.out)
    obtain ⟨u, hu⟩ := hζ.associated_sub_one_pow_sub_one_of_coprime hcop
    rw [← hu] at h2
    have h3 : zetaInt F L ℓ - 1 ∈ 𝔓 :=
      (‹𝔓.IsPrime›.mem_or_mem h2).resolve_right (hunit _ u.isUnit)
    have h4 : (zetaInt F L ℓ - 1) ^ (ℓ - 1) ∈ 𝔓 :=
      Ideal.pow_mem_of_mem 𝔓 h3 _ (by have := hℓ.out.two_le; omega)
    obtain ⟨v, hv⟩ := associated_natCast_pow F L ℓ
    rw [← hv] at h4
    exact hℓ𝔓 ((‹𝔓.IsPrime›.mem_or_mem h4).resolve_right (hunit _ v.isUnit))

end Inertia

section Unramified

variable {F L}

private theorem ramificationIdx_eq_one_of_not_mem (𝔔' : Ideal (𝓞 F)) [𝔔'.IsMaximal]
    (hℓ𝔔' : (ℓ : 𝓞 F) ∉ 𝔔') (𝔓' : Ideal (𝓞 L)) [𝔓'.IsPrime] [𝔓'.LiesOver 𝔔'] :
    Ideal.ramificationIdx' 𝔔' 𝔓' = 1 := by
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have : NeZero ((ℓ : ℕ) : F) := NeZero.charZero
  have : IsGalois F L := IsCyclotomicExtension.isGalois {ℓ} F L
  have h𝔔'bot : 𝔔' ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField F)
  have h𝔓'bot : 𝔓' ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot h𝔔'bot 𝔓'
  have : 𝔓'.IsMaximal := Ring.DimensionLEOne.maximalOfPrime h𝔓'bot ‹_›
  have hℓ𝔓' : (ℓ : 𝓞 L) ∉ 𝔓' := fun h =>
    hℓ𝔔' ((Ideal.mem_of_liesOver 𝔓' 𝔔' _).mpr (by simpa using h))
  let : Field (𝓞 F ⧸ 𝔔') := Ideal.Quotient.field 𝔔'
  let : Field (𝓞 L ⧸ 𝔓') := Ideal.Quotient.field 𝔓'
  have : Finite (𝓞 F ⧸ 𝔔') := Ring.HasFiniteQuotients.finiteQuotient h𝔔'bot
  have : Algebra.IsIntegral (𝓞 F ⧸ 𝔔') (𝓞 L ⧸ 𝔓') := Algebra.IsIntegral.tower_top (𝓞 F)
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[F] L) 𝔔' 𝔓'
  rw [inertia_eq_bot ℓ 𝔓' hℓ𝔓', Subgroup.card_bot,
    Ideal.ramificationIdxIn_eq_ramificationIdx 𝔔' 𝔓' (L ≃ₐ[F] L),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := 𝔔') (q := 𝔓') h𝔔'bot] at hcard
  exact hcard.symm

end Unramified

section BaseUnramified

private theorem natCast_not_mem_sq (p : ℕ) [hp : Fact p.Prime] (hne : ℓ ≠ p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (𝔏 : Ideal (𝓞 K)) [𝔏.IsMaximal] (hℓ𝔏 : (ℓ : 𝓞 K) ∈ 𝔏) : (ℓ : 𝓞 K) ∉ 𝔏 ^ 2 := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero ((p : ℕ) : ℚ) := NeZero.charZero
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {p} ℚ K
  have h𝔏bot : 𝔏 ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField ‹_› (RingOfIntegers.not_isField K)
  have hpZbot : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.out.ne_zero
  have hpZprime : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hℓ.out.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hℓ.out
  have hpZmax : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hpZbot hpZprime
  have hle : Ideal.span {(ℓ : ℤ)} ≤ 𝔏.under ℤ := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
    simpa using hℓ𝔏
  have : 𝔏.LiesOver (Ideal.span {(ℓ : ℤ)}) :=
    ⟨hpZmax.eq_of_le (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)) hle⟩
  have hp𝔏 : (p : 𝓞 K) ∉ 𝔏 := by
    intro hp𝔏
    have hcop : Nat.Coprime ℓ p := (Nat.coprime_primes hℓ.out hp.out).mpr hne
    obtain ⟨a, b, hab⟩ := (Nat.Coprime.cast (R := 𝓞 K) hcop : IsCoprime (ℓ : 𝓞 K) (p : 𝓞 K))
    apply (Ideal.IsMaximal.ne_top ‹𝔏.IsMaximal›)
    rw [Ideal.eq_top_iff_one, ← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hℓ𝔏) (Ideal.mul_mem_left _ _ hp𝔏)
  let : Field (ℤ ⧸ Ideal.span {(ℓ : ℤ)}) := Ideal.Quotient.field _
  let : Field (𝓞 K ⧸ 𝔏) := Ideal.Quotient.field 𝔏
  have : Finite (ℤ ⧸ Ideal.span {(ℓ : ℤ)}) := Ring.HasFiniteQuotients.finiteQuotient hpZbot
  have : Algebra.IsIntegral (ℤ ⧸ Ideal.span {(ℓ : ℤ)}) (𝓞 K ⧸ 𝔏) :=
    Algebra.IsIntegral.tower_top ℤ
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := K ≃ₐ[ℚ] K)
    (Ideal.span {(ℓ : ℤ)}) 𝔏
  rw [inertia_eq_bot (F := ℚ) p 𝔏 hp𝔏, Subgroup.card_bot,
    Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(ℓ : ℤ)}) 𝔏 (K ≃ₐ[ℚ] K),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (p := Ideal.span {(ℓ : ℤ)}) (q := 𝔏)
        hpZbot] at hcard
  intro h2
  have hmap0 : (Ideal.span {(ℓ : ℤ)}).map (algebraMap ℤ (𝓞 K)) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hpZbot
  have hdvd : 𝔏 ^ 2 ∣ (Ideal.span {(ℓ : ℤ)}).map (algebraMap ℤ (𝓞 K)) := by
    rw [Ideal.dvd_iff_le, Ideal.map_span, Set.image_singleton, Ideal.span_singleton_le_iff_mem]
    simpa using h2
  have := le_ramificationIdx_of_pow_dvd h𝔏bot hmap0 hdvd
  omega

omit [NumberField F] in
private theorem natCast_not_mem_sq_of_algebra (p : ℕ) [hp : Fact p.Prime] (hne : ℓ ≠ p)
    (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [Algebra F K]
    (𝔏 : Ideal (𝓞 F)) [𝔏.IsMaximal] (hℓ𝔏 : (ℓ : 𝓞 F) ∈ 𝔏) : (ℓ : 𝓞 F) ∉ 𝔏 ^ 2 := by
  intro h2
  have hker : RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔏 := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact bot_le
  obtain ⟨𝔏', h𝔏'max, h𝔏'⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔏 hker
  have := h𝔏'max
  have : 𝔏'.LiesOver 𝔏 := ⟨h𝔏'.symm⟩
  have hℓ' : (ℓ : 𝓞 K) ∈ 𝔏' := by
    simpa using (Ideal.mem_of_liesOver 𝔏' 𝔏 (ℓ : 𝓞 F)).mp hℓ𝔏
  have h2' : (ℓ : 𝓞 K) ∈ 𝔏' ^ 2 := by
    have hmem := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 K)) h2
    rw [Ideal.map_pow, map_natCast] at hmem
    have hle : 𝔏.map (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔏' := by
      rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, h𝔏']
    exact Ideal.pow_right_mono hle 2 hmem
  exact natCast_not_mem_sq ℓ p hne K 𝔏' hℓ' h2'

end BaseUnramified

end ThaineAux

open NumberField

open scoped Pointwise
open UniqueFactorizationMonoid

namespace ThaineAux

section KSide

variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
variable (F : Type*) [Field F] [NumberField F] [Algebra F K]
variable {Δ : Type*} [Group Δ] (Δact : Δ →* ((𝓞 F) ≃+* (𝓞 F))) (σt : Δ →* (K ≃ₐ[ℚ] K))

private lemma smul_eq_galRestrict_int (σ : K ≃ₐ[ℚ] K) (y : 𝓞 K) :
    σ • y = galRestrict ℤ ℚ K (𝓞 K) σ y := by
  apply RingOfIntegers.coe_injective
  rw [algebraMap_galRestrict_apply]
  rfl

omit [NumberField F] in
private lemma map_toRingHom_eq (e : (𝓞 F) ≃+* (𝓞 F)) (𝔔 : Ideal (𝓞 F)) :
    𝔔.map e.toRingHom = 𝔔.map e := rfl

omit [NumberField F] in
private theorem exists_eq_map_of_natCast_mem (hσt : Function.Surjective σt)
    (hcomm : ∀ d x, algebraMap (𝓞 F) (𝓞 K) (Δact d x) =
      galRestrict ℤ ℚ K (𝓞 K) (σt d) (algebraMap (𝓞 F) (𝓞 K) x))
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (𝔔₁ 𝔔₂ : Ideal (𝓞 F)) [𝔔₁.IsMaximal] [𝔔₂.IsMaximal]
    (h₁ : (ℓ : 𝓞 F) ∈ 𝔔₁) (h₂ : (ℓ : 𝓞 F) ∈ 𝔔₂) :
    ∃ d : Δ, 𝔔₂ = 𝔔₁.map (Δact d) := by
  classical
  have hker : ∀ 𝔔 : Ideal (𝓞 F), RingHom.ker (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔔 := fun 𝔔 => by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 K))]
    exact bot_le
  obtain ⟨𝔓₁, h𝔓₁max, h𝔓₁⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔔₁ (hker 𝔔₁)
  obtain ⟨𝔓₂, h𝔓₂max, h𝔓₂⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔔₂ (hker 𝔔₂)
  have := h𝔓₁max
  have := h𝔓₂max
  have : 𝔓₁.LiesOver 𝔔₁ := ⟨h𝔓₁.symm⟩
  have : 𝔓₂.LiesOver 𝔔₂ := ⟨h𝔓₂.symm⟩
  have hpZbot : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.out.ne_zero
  have hpZprime : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hℓ.out.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hℓ.out
  have hpZmax : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hpZbot hpZprime
  have hover : ∀ (𝔓 : Ideal (𝓞 K)) [𝔓.IsMaximal], (ℓ : 𝓞 K) ∈ 𝔓 →
      𝔓.LiesOver (Ideal.span {(ℓ : ℤ)}) := by
    intro 𝔓 _ hℓ𝔓
    have hle : Ideal.span {(ℓ : ℤ)} ≤ 𝔓.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hℓ𝔓
    exact ⟨hpZmax.eq_of_le (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top ‹_›)) hle⟩
  have hℓ₁ : (ℓ : 𝓞 K) ∈ 𝔓₁ := by simpa using (Ideal.mem_of_liesOver 𝔓₁ 𝔔₁ (ℓ : 𝓞 F)).mp h₁
  have hℓ₂ : (ℓ : 𝓞 K) ∈ 𝔓₂ := by simpa using (Ideal.mem_of_liesOver 𝔓₂ 𝔔₂ (ℓ : 𝓞 F)).mp h₂
  have := hover 𝔓₁ hℓ₁
  have := hover 𝔓₂ hℓ₂
  obtain ⟨σ, hσ⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (Ideal.span {(ℓ : ℤ)}) 𝔓₁ 𝔓₂
    (K ≃ₐ[ℚ] K)
  obtain ⟨d, rfl⟩ := hσt σ
  refine ⟨d, ?_⟩
  have hinv : (Δact d).symm = Δact d⁻¹ := by rw [map_inv]; rfl
  ext x
  rw [Ideal.mem_of_liesOver 𝔓₂ 𝔔₂ x, ← hσ, Ideal.mem_pointwise_smul_iff_inv_smul_mem,
    smul_eq_galRestrict_int, ← map_inv, ← hcomm, ← Ideal.mem_of_liesOver 𝔓₁ 𝔔₁,
    ← Ideal.comap_symm, Ideal.mem_comap, hinv]

omit [NumberField F] in
private lemma absNorm_map_equiv (e : (𝓞 F) ≃+* (𝓞 F)) (𝔔 : Ideal (𝓞 F)) [NumberField F] :
    Ideal.absNorm (𝔔.map e) = Ideal.absNorm 𝔔 := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
    Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv 𝔔 (𝔔.map e) e rfl).toEquiv).symm

private theorem span_natCast_eq_prod_primesOver (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hunram : ∀ (𝔔 : Ideal (𝓞 F)) [𝔔.IsMaximal], (ℓ : 𝓞 F) ∈ 𝔔 → (ℓ : 𝓞 F) ∉ 𝔔 ^ 2) :
    Ideal.span {(ℓ : 𝓞 F)} =
      ∏ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)}) (𝓞 F), 𝔔 := by
  classical
  have hmap : (Ideal.span {(ℓ : ℤ)}).map (algebraMap ℤ (𝓞 F)) = Ideal.span {(ℓ : 𝓞 F)} := by
    rw [Ideal.map_span, Set.image_singleton]
    simp
  have hI0 : Ideal.span {(ℓ : 𝓞 F)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.out.ne_zero
  have hcount : ∀ P ∈ normalizedFactors (Ideal.span {(ℓ : 𝓞 F)}),
      (normalizedFactors (Ideal.span {(ℓ : 𝓞 F)})).count P = 1 := by
    intro P hP
    have hPp := prime_of_normalized_factor P hP
    have hP0 : P ≠ ⊥ := hPp.ne_zero
    have hPprime : P.IsPrime := Ideal.isPrime_of_prime hPp
    have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hPprime
    have hdvd : P ∣ Ideal.span {(ℓ : 𝓞 F)} := dvd_of_mem_normalizedFactors hP
    have hℓP : (ℓ : 𝓞 F) ∈ P :=
      (Ideal.span_singleton_le_iff_mem _).mp (Ideal.le_of_dvd hdvd)
    have h2 := hunram P hℓP
    have he : Ideal.ramificationIdx' (Ideal.span {(ℓ : ℤ)}) P = 1 := by
      apply Ideal.ramificationIdx'_spec
      · rw [pow_one, hmap]; exact Ideal.le_of_dvd hdvd
      · rw [hmap]
        intro hle
        exact h2 ((Ideal.span_singleton_le_iff_mem _).mp hle)
    rwa [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count (by rwa [hmap])
      hPprime hP0, hmap] at he
  have hnodup : (normalizedFactors (Ideal.span {(ℓ : 𝓞 F)})).Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro P
    by_cases h : P ∈ normalizedFactors (Ideal.span {(ℓ : 𝓞 F)})
    · rw [hcount P h]
    · rw [Multiset.count_eq_zero.mpr h]; exact zero_le_one
  rw [IsDedekindDomain.primesOverFinset, hmap, factors_eq_normalizedFactors,
    Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup,
    Multiset.map_id']
  exact (associated_iff_eq.mp (prod_normalizedFactors hI0)).symm

private theorem ringEquiv_sub_self_mem_of_map_eq (e : (𝓞 F) ≃+* (𝓞 F)) (𝔏 : Ideal (𝓞 F))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hcard : Ideal.absNorm 𝔏 = ℓ) (he : 𝔏.map e = 𝔏) (x : 𝓞 F) :
    e x - x ∈ 𝔏 := by
  classical
  have hfin : Finite (𝓞 F ⧸ 𝔏) := by
    apply Nat.finite_of_card_ne_zero
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hcard]
    exact hℓ.ne_zero
  let : Fintype (𝓞 F ⧸ 𝔏) := Fintype.ofFinite _
  have hcard' : Fintype.card (𝓞 F ⧸ 𝔏) = ℓ := by
    rw [← Nat.card_eq_fintype_card, ← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hcard]
  let φ : ZMod ℓ ≃+* 𝓞 F ⧸ 𝔏 := ZMod.ringEquivOfPrime (𝓞 F ⧸ 𝔏) hℓ hcard'
  let ebar : 𝓞 F ⧸ 𝔏 ≃+* 𝓞 F ⧸ 𝔏 := Ideal.quotientEquiv 𝔏 𝔏 e he.symm
  have hid : ∀ y : 𝓞 F ⧸ 𝔏, ebar y = y := by
    intro y
    obtain ⟨z, rfl⟩ := φ.surjective y
    have := RingHom.ext_zmod (ebar.toRingHom.comp φ.toRingHom) φ.toRingHom
    exact DFunLike.congr_fun this z
  rw [← Ideal.Quotient.eq]
  have := hid (Ideal.Quotient.mk 𝔏 x)
  rwa [show ebar (Ideal.Quotient.mk 𝔏 x) = Ideal.Quotient.mk 𝔏 (e x) from
    Ideal.quotientEquiv_mk 𝔏 𝔏 e he.symm x] at this

private theorem dvd_pred_of_not_pow (𝔏 : Ideal (𝓞 F)) [𝔏.IsMaximal] {ℓ : ℕ} (_hℓ : ℓ.Prime)
    (hcard : Ideal.absNorm 𝔏 = ℓ) {p : ℕ} (hp : p.Prime)
    (x : 𝓞 F ⧸ 𝔏) (hx : x ∉ {x : 𝓞 F ⧸ 𝔏 | ∃ y, y ^ p = x}) : p ∣ ℓ - 1 := by
  classical
  by_contra hnd
  have hcop : Nat.Coprime (ℓ - 1) p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hnd).symm
  let : Field (𝓞 F ⧸ 𝔏) := Ideal.Quotient.field 𝔏
  have hcardq : Nat.card (𝓞 F ⧸ 𝔏) = ℓ := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, hcard]
  have : Finite (𝓞 F ⧸ 𝔏) := Nat.finite_of_card_ne_zero (by rw [hcardq]; exact _hℓ.ne_zero)
  have hunits : Nat.card (𝓞 F ⧸ 𝔏)ˣ = ℓ - 1 := by
    rw [Nat.card_units, hcardq]
  apply hx
  by_cases hx0 : x = 0
  · exact ⟨0, by rw [hx0]; exact zero_pow hp.ne_zero⟩
  · let e : (𝓞 F ⧸ 𝔏)ˣ ≃ (𝓞 F ⧸ 𝔏)ˣ := powCoprime (hunits ▸ hcop)
    refine ⟨((e.symm (Units.mk0 x hx0) : (𝓞 F ⧸ 𝔏)ˣ) : 𝓞 F ⧸ 𝔏), ?_⟩
    have h1 : e (e.symm (Units.mk0 x hx0)) = Units.mk0 x hx0 := e.apply_symm_apply _
    rw [powCoprime_apply] at h1
    have h2 := congrArg Units.val h1
    rwa [Units.val_pow_eq_pow_val, Units.val_mk0] at h2

private theorem natCast_eq_one_of_not_pow (𝔏 : Ideal (𝓞 F)) [𝔏.IsMaximal] {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hcard : Ideal.absNorm 𝔏 = ℓ) {p : ℕ} (hp : p.Prime)
    (x : 𝓞 F ⧸ 𝔏) (hx : x ∉ {x : 𝓞 F ⧸ 𝔏 | ∃ y, y ^ p = x}) : (ℓ : ZMod p) = 1 := by
  obtain ⟨k, hk⟩ := dvd_pred_of_not_pow F 𝔏 hℓ hcard hp x hx
  have : ℓ = p * k + 1 := by have := hℓ.one_le; omega
  rw [this]
  push_cast
  simp

end KSide

end ThaineAux

open scoped nonZeroDivisors

namespace ThaineAux

private theorem bookkeeping {R : Type*} [CommRing R] [IsDedekindDomain R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    {ι : Type*} [Fintype ι] (S : Finset (Ideal R)) (φ : ι → Ideal R)
    (hφS : ∀ i, φ i ∈ S)
    (n : ℕ) (hn : 0 < n) (a : Ideal R → ℕ) (c : ι → ℕ)
    (hcong : ∀ 𝔔 ∈ S, (a 𝔔 : ZMod n) =
      ∑ i ∈ Finset.univ.filter (fun i => φ i = 𝔔), (c i : ZMod n))
    (π a₀ : R) (hπ0 : π ≠ 0) (ha₀ : a₀ ≠ 0) (hπ : Ideal.span {π} = ∏ 𝔔 ∈ S, 𝔔)
    (W : Ideal R) (hrel : Ideal.span {a₀} = (∏ 𝔔 ∈ S, 𝔔 ^ a 𝔔) * W ^ n) :
    ∃ (α : K) (_ : α ≠ 0) (J : Ideal R),
      FractionalIdeal.spanSingleton R⁰ α =
        (∏ i, (φ i : FractionalIdeal R⁰ K) ^ c i) * (J : FractionalIdeal R⁰ K) ^ n := by
  classical
  have : NeZero n := ⟨hn.ne'⟩
  set s : Ideal R → ℕ := fun 𝔔 => ∑ i ∈ Finset.univ.filter (fun i => φ i = 𝔔), c i with hs
  set M : ℕ := ∑ i, c i with hM
  set a' : Ideal R → ℕ := fun 𝔔 => a 𝔔 + n * M with ha'
  have hsM : ∀ 𝔔, s 𝔔 ≤ M := fun 𝔔 =>
    Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hle : ∀ 𝔔, s 𝔔 ≤ a' 𝔔 := fun 𝔔 =>
    (hsM 𝔔).trans ((Nat.le_mul_of_pos_left M hn).trans (Nat.le_add_left _ _))
  have hdiv : ∀ 𝔔 ∈ S, n ∣ a' 𝔔 - s 𝔔 := by
    intro 𝔔 h𝔔
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub (hle 𝔔), sub_eq_zero]
    simp only [a', s, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
      Nat.cast_sum]
    exact hcong 𝔔 h𝔔
  set q : Ideal R → ℕ := fun 𝔔 => (a' 𝔔 - s 𝔔) / n with hq
  have hq' : ∀ 𝔔 ∈ S, a' 𝔔 = s 𝔔 + n * q 𝔔 := by
    intro 𝔔 h𝔔
    have h1 : n * ((a' 𝔔 - s 𝔔) / n) = a' 𝔔 - s 𝔔 := Nat.mul_div_cancel' (hdiv 𝔔 h𝔔)
    have h2 := hle 𝔔
    simp only [q]
    omega
  have hfiber : ∏ i, φ i ^ c i = ∏ 𝔔 ∈ S, 𝔔 ^ s 𝔔 := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := φ)
      (fun i _ => hφS i)]
    refine Finset.prod_congr rfl (fun 𝔔 _ => ?_)
    rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]),
      Finset.prod_pow_eq_pow_sum]
  have hL : Ideal.span {π ^ (n * M) * a₀} = (∏ 𝔔 ∈ S, 𝔔 ^ a' 𝔔) * W ^ n := by
    rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_pow, hπ, hrel,
      ← mul_assoc, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine congrArg (· * W ^ n) (Finset.prod_congr rfl fun 𝔔 _ => ?_)
    rw [← pow_add]
    congr 1
    simp only [a']
    ring
  have hR : (∏ i, φ i ^ c i) * (W * ∏ 𝔔 ∈ S, 𝔔 ^ q 𝔔) ^ n =
      (∏ 𝔔 ∈ S, 𝔔 ^ a' 𝔔) * W ^ n := by
    rw [hfiber, mul_pow, mul_comm (W ^ n), ← mul_assoc, ← Finset.prod_pow,
      ← Finset.prod_mul_distrib]
    refine congrArg (· * W ^ n) (Finset.prod_congr rfl fun 𝔔 h𝔔 => ?_)
    rw [← pow_mul, ← pow_add, hq' 𝔔 h𝔔, mul_comm]
  have key : Ideal.span {π ^ (n * M) * a₀} = (∏ i, φ i ^ c i) * (W * ∏ 𝔔 ∈ S, 𝔔 ^ q 𝔔) ^ n :=
    hL.trans hR.symm
  refine ⟨algebraMap R K (π ^ (n * M) * a₀), ?_, W * ∏ 𝔔 ∈ S, 𝔔 ^ q 𝔔, ?_⟩
  · exact (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr
      (mul_ne_zero (pow_ne_zero _ hπ0) ha₀)
  · rw [← FractionalIdeal.coeIdeal_span_singleton, key, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.coeIdeal_pow]
    congr 1
    rw [show ((∏ i, φ i ^ c i : Ideal R) : FractionalIdeal R⁰ K) =
        FractionalIdeal.coeIdealHom R⁰ K (∏ i, φ i ^ c i) from rfl, map_prod]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [map_pow]
    rfl

end ThaineAux

open NumberField Stickelberger

namespace ThaineReduce

variable (p : ℕ) [hp : Fact p.Prime]

private lemma p_nsmul_eq_zero {M : Type*} [AddCommGroup M] [Module (ZMod p) M] (x : M) :
    p • x = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_self, zero_smul]

section Stub

variable (Kplus : Type*) [Field Kplus] [NumberField Kplus]
  [Algebra Kplus (CyclotomicField p ℚ)]
  (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
  (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
    (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
      (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
  (δ : (𝓞 Kplus)ˣ)
  (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
    Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)

omit [NumberField Kplus] in
include hΔact in
private lemma mapEquiv_clRingAction_map (d : (ZMod p)ˣ) (u : (𝓞 Kplus)ˣ) :
    Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv
        (Units.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).toMonoidHom u) =
      Units.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).toMonoidHom
        (Units.mapEquiv (Δact d).toMulEquiv u) := by
  apply Units.ext
  simpa using (DFunLike.congr_fun (hΔact d) (u : 𝓞 Kplus)).symm

omit [NumberField Kplus] in
include hΔact hδeig in
private theorem proj_map_mem_unitsOmegaEigenspace :
    ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p
        (Additive.ofMul
          (Units.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).toMonoidHom δ))
      ∈ unitsOmegaEigenspace p 2 := by
  change IsOmegaEigenvector (unitsGalAction p) 2 _
  intro d
  obtain ⟨v, hv⟩ := hδeig d
  rw [show unitsGalAction p d =
      unitsEnd p (𝓞 (CyclotomicField p ℚ)) (clRingAction p (CyclotomicField p ℚ) d) from rfl,
    unitsEnd_proj, mapEquiv_clRingAction_map p Kplus Δact hΔact d δ, hv, map_mul, map_pow,
    map_pow, ofMul_mul, ofMul_pow, ofMul_pow, map_add, map_nsmul, map_nsmul, p_nsmul_eq_zero p,
    add_zero, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]

private theorem omegaIdempotent_proj_eq (c : (𝓞 (CyclotomicField p ℚ))ˣ) :
    omegaIdempotent p (unitsGalAction p) 2
        (ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul c)) =
      ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul
        (∏ d : (ZMod p)ˣ, (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv c) ^
          ((((Nat.card (ZMod p)ˣ : ℕ) : ZMod p)⁻¹ * (((d : ZMod p)) ^ 2)⁻¹).val))) := by
  rw [ofMul_prod, map_sum]
  simp only [omegaIdempotent, LinearMap.smul_apply, LinearMap.coe_sum, Finset.sum_apply,
    Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val,
    show unitsGalAction p d =
      unitsEnd p (𝓞 (CyclotomicField p ℚ)) (clRingAction p (CyclotomicField p ℚ) d) from rfl,
    unitsEnd_proj]

omit [NumberField Kplus] in
include hΔact hδeig in
private theorem reduceK (hDIM : Module.finrank (ZMod p) (unitsOmegaEigenspace p 2) = 1)
    (c₂ : (𝓞 (CyclotomicField p ℚ))ˣ)
    (hB2 : omegaIdempotent p (unitsGalAction p) 2
        (ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul c₂)) ≠ 0) :
    ∃ (m : ℕ) (w : (𝓞 (CyclotomicField p ℚ))ˣ),
      Units.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).toMonoidHom δ =
        (∏ d : (ZMod p)ˣ,
          (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv c₂) ^
            ((((Nat.card (ZMod p)ˣ : ℕ) : ZMod p)⁻¹ * (((d : ZMod p)) ^ 2)⁻¹).val)) ^ m *
        w ^ p := by
  set δK := Units.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).toMonoidHom δ with hδK
  set u₂ := ∏ d : (ZMod p)ˣ,
      (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv c₂) ^
        ((((Nat.card (ZMod p)ˣ : ℕ) : ZMod p)⁻¹ * (((d : ZMod p)) ^ 2)⁻¹).val) with hu₂
  set x := ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul δK) with hx
  set y := omegaIdempotent p (unitsGalAction p) 2
      (ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul c₂)) with hy
  have hxmem : x ∈ unitsOmegaEigenspace p 2 :=
    proj_map_mem_unitsOmegaEigenspace p Kplus Δact hΔact δ hδeig
  have hymem : y ∈ unitsOmegaEigenspace p 2 :=
    Stickelberger.isOmegaEigenvector_omegaIdempotent p (unitsGalAction p) 2 _
  have hy0 : (⟨y, hymem⟩ : unitsOmegaEigenspace p 2) ≠ 0 := fun h =>
    hB2 (congrArg Subtype.val h)
  obtain ⟨mz, hmz⟩ := (finrank_eq_one_iff_of_ne_zero' _ hy0).mp hDIM ⟨x, hxmem⟩
  have hxy : x = mz • y := by
    have := congrArg Subtype.val hmz
    simpa using this.symm
  have hyu : y = ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul u₂) :=
    omegaIdempotent_proj_eq p c₂
  have hx' : x = ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p
      (Additive.ofMul (u₂ ^ mz.val)) := by
    rw [hxy, hyu, ofMul_pow, map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  have hker : ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p
      (Additive.ofMul δK - Additive.ofMul (u₂ ^ mz.val)) = 0 := by
    rw [map_sub, ← hx, hx', sub_self]
  rw [ModN.mkQ_eq_zero_iff] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨mz.val, Additive.toMul z, ?_⟩
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_pow _ (Additive.toMul z), ofMul_toMul, hz]
  abel

end Stub

end ThaineReduce

open NumberField Stickelberger IsCyclotomicExtension

namespace ThaineReduce

variable (p : ℕ) [hp : Fact p.Prime]

private theorem cycloGalEquiv_symm_apply_zeta (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] (t : (ZMod p)ˣ) :
    (IsCyclotomicExtension.Rat.galEquivZMod p K).symm t (zeta p ℚ K) =
      zeta p ℚ K ^ (t : ZMod p).val := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have h1 :=
    (zeta_spec p ℚ K).autToPow_spec ℚ ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm t)
  have h2 :
      ((zeta_spec p ℚ K).autToPow ℚ ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm t) :
        (ZMod p)ˣ) = t :=
    (MulEquiv.apply_symm_apply (IsCyclotomicExtension.Rat.galEquivZMod p K) t : _)
  rw [← h1, h2]

section KplusFrame

variable (Kplus : Type*) [Field Kplus] [NumberField Kplus] [Algebra Kplus (CyclotomicField p ℚ)]
  (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)

private scoped instance isScalarTower_rat : IsScalarTower ℚ Kplus (CyclotomicField p ℚ) :=
  IsScalarTower.of_algebraMap_eq (fun q => by rw [eq_ratCast, eq_ratCast, map_ratCast])

private scoped instance isGalois_Kplus : IsGalois Kplus (CyclotomicField p ℚ) := by
  have : IsGalois ℚ (CyclotomicField p ℚ) := IsCyclotomicExtension.isGalois {p} ℚ _
  exact IsGalois.tower_top_of_isGalois ℚ Kplus (CyclotomicField p ℚ)

include hKplus in
private theorem exists_involution :
    ∃ τ₀ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ), τ₀ ≠ 1 ∧
      (∀ σ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ), σ = 1 ∨ σ = τ₀) ∧
      ∀ x : CyclotomicField p ℚ,
        τ₀ x = (IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm (-1) x := by
  classical
  have hcard : Fintype.card ((CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ)) = 2 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hKplus]
  obtain ⟨τ₀, hτ₀⟩ := Fintype.exists_ne_of_one_lt_card (by rw [hcard]; norm_num)
    (1 : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))
  have huniv : (Finset.univ : Finset ((CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))) =
      {1, τ₀} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ₀), hcard]
  have hsq : τ₀ * τ₀ = 1 := by
    have := pow_card_eq_one (G := (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ)) (x := τ₀)
    rwa [hcard, pow_two] at this
  set τ : (CyclotomicField p ℚ) ≃ₐ[ℚ] (CyclotomicField p ℚ) := AlgEquiv.restrictScalars ℚ τ₀ with hτ
  have hτx : ∀ x, τ x = τ₀ x := fun x => rfl
  have hτsq : τ * τ = 1 := by
    ext x
    rw [AlgEquiv.mul_apply, hτx, hτx, ← AlgEquiv.mul_apply, hsq, AlgEquiv.one_apply,
      AlgEquiv.one_apply]
  have hτne : τ ≠ 1 := by
    intro h
    apply hτ₀
    ext x
    rw [← hτx, h, AlgEquiv.one_apply, AlgEquiv.one_apply]
  set e : (ZMod p)ˣ := IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ) τ with he
  have hesq : e * e = 1 := by rw [he, ← map_mul, hτsq, map_one]
  have hene : e ≠ 1 := fun h =>
    hτne ((IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).injective
      (by rw [← he, h, map_one]))
  have he1 : e = -1 := by
    have h2 : (e : ZMod p) * e = 1 := by rw [← Units.val_mul, hesq, Units.val_one]
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact absurd (Units.val_eq_one.mp h) hene
    · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
  have hall : ∀ σ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ), σ = 1 ∨ σ = τ₀ := by
    intro σ
    have : σ ∈ (Finset.univ : Finset ((CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))) :=
      Finset.mem_univ σ
    rw [huniv, Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  refine ⟨τ₀, hτ₀, hall, fun x => ?_⟩
  have hτeq : τ = (IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm (-1) := by
    rw [← he1, he, MulEquiv.symm_apply_apply]
  rw [← hτx, hτeq]

omit hp in
private lemma univ_eq_pair [DecidableEq ((CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))]
    (τ₀ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))
    (hall : ∀ σ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ), σ = 1 ∨ σ = τ₀) :
    (Finset.univ : Finset ((CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))) = {1, τ₀} := by
  ext σ
  simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
  exact hall σ

omit hp in
private theorem coe_algebraMap_norm_eq (τ₀ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))
    (hτ₀ : τ₀ ≠ 1)
    (hall : ∀ σ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ), σ = 1 ∨ σ = τ₀)
    (x : 𝓞 (CyclotomicField p ℚ)) :
    ((algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) (NumberField.RingOfIntegers.norm Kplus x) :
        𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) =
      (x : CyclotomicField p ℚ) * τ₀ (x : CyclotomicField p ℚ) := by
  classical
  rw [NumberField.RingOfIntegers.coe_algebraMap_norm, Algebra.norm_eq_prod_automorphisms,
    univ_eq_pair p Kplus τ₀ hall, Finset.prod_pair (Ne.symm hτ₀), AlgEquiv.one_apply]

omit hp in
private theorem exists_trace (τ₀ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ))
    (hτ₀ : τ₀ ≠ 1)
    (hall : ∀ σ : (CyclotomicField p ℚ) ≃ₐ[Kplus] (CyclotomicField p ℚ), σ = 1 ∨ σ = τ₀)
    (y : 𝓞 (CyclotomicField p ℚ)) :
    ∃ a : 𝓞 Kplus, ((algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) a :
        𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) =
      (y : CyclotomicField p ℚ) + τ₀ (y : CyclotomicField p ℚ) := by
  classical
  refine ⟨⟨Algebra.trace Kplus (CyclotomicField p ℚ) (y : CyclotomicField p ℚ),
    Algebra.isIntegral_trace y.2⟩, ?_⟩
  rw [show ((algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))
      ⟨Algebra.trace Kplus (CyclotomicField p ℚ) (y : CyclotomicField p ℚ),
        Algebra.isIntegral_trace y.2⟩ : 𝓞 (CyclotomicField p ℚ)) : CyclotomicField p ℚ) =
      algebraMap Kplus (CyclotomicField p ℚ)
        (Algebra.trace Kplus (CyclotomicField p ℚ) (y : CyclotomicField p ℚ)) from rfl,
    trace_eq_sum_automorphisms, univ_eq_pair p Kplus τ₀ hall, Finset.sum_pair (Ne.symm hτ₀),
    AlgEquiv.one_apply]

omit hp [NumberField Kplus] in
include hKplus in
private theorem sq_eq_of_map_eq (δ : (𝓞 Kplus)ˣ) (u w : (𝓞 (CyclotomicField p ℚ))ˣ) (m : ℕ)
    (h : Units.map (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).toMonoidHom δ =
      u ^ m * w ^ p) :
    δ ^ 2 = (Units.map (NumberField.RingOfIntegers.norm Kplus) u) ^ m *
      (Units.map (NumberField.RingOfIntegers.norm Kplus) w) ^ p := by
  have h' := congrArg
    (Units.map (NumberField.RingOfIntegers.norm Kplus (L := CyclotomicField p ℚ))) h
  rw [map_mul, map_pow, map_pow] at h'
  rw [← h']
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.coe_map, Units.coe_map, RingHom.toMonoidHom_eq_coe,
    MonoidHom.coe_ofClass, NumberField.RingOfIntegers.norm_algebraMap, hKplus]

end KplusFrame

end ThaineReduce
open scoped ThaineReduce

namespace ThaineReduce

open NumberField Stickelberger IsCyclotomicExtension

section Pack

variable (p : ℕ) [hp : Fact p.Prime]

private lemma algebraMap_clRingAction (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K]
    (d : (ZMod p)ˣ) (x : 𝓞 K) :
    algebraMap (𝓞 K) K (clRingAction p K d x) =
      (IsCyclotomicExtension.Rat.galEquivZMod p K).symm d (algebraMap (𝓞 K) K x) :=
  algebraMap_galRestrict_apply ℤ ((IsCyclotomicExtension.Rat.galEquivZMod p K).symm d) x

private lemma cycloGalEquiv_symm_neg_one_zeta (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {p} ℚ K] :
    (IsCyclotomicExtension.Rat.galEquivZMod p K).symm (-1) (zeta p ℚ K) = (zeta p ℚ K)⁻¹ := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  rw [cycloGalEquiv_symm_apply_zeta]
  apply eq_inv_of_mul_eq_one_left
  rw [← pow_succ, (zeta_spec p ℚ K).pow_eq_one_iff_dvd, ← ZMod.natCast_eq_zero_iff]
  push_cast
  simp

private theorem reduce_out (hp2 : p ≠ 2)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hDIM : Module.finrank (ZMod p) (unitsOmegaEigenspace p 2) = 1)
    (hB2 : ∀ (ζ : 𝓞 (CyclotomicField p ℚ)) (_ : IsPrimitiveRoot (ζ : CyclotomicField p ℚ) p)
      (c₂ : (𝓞 (CyclotomicField p ℚ))ˣ) (_ : (c₂ : 𝓞 (CyclotomicField p ℚ)) = 1 + ζ),
      omegaIdempotent p (unitsGalAction p) 2
        (ModN.mkQ (G := Additive (𝓞 (CyclotomicField p ℚ))ˣ) p (Additive.ofMul c₂)) ≠ 0) :
    ∃ (m : ℕ) (w : (𝓞 Kplus)ˣ) (δ₀ : (𝓞 Kplus)ˣ) (n : (ZMod p)ˣ → ℕ) (a : (ZMod p)ˣ → 𝓞 Kplus),
      δ ^ 2 = δ₀ ^ m * w ^ p ∧
      (δ₀ : 𝓞 Kplus) = ∏ d, (2 + a d) ^ n d ∧
      ∀ d, algebraMap (𝓞 Kplus) (CyclotomicField p ℚ) (a d) =
        zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val +
          (zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val)⁻¹ := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hζK := zeta_spec p ℚ (CyclotomicField p ℚ)
  set ζI : 𝓞 (CyclotomicField p ℚ) := hζK.toInteger with hζI
  have hζIK : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ) ζI =
      zeta p ℚ (CyclotomicField p ℚ) := rfl
  have hζI : IsPrimitiveRoot ζI p := hζK.toInteger_isPrimitiveRoot
  have hcop : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
  obtain ⟨u, hu⟩ := hζI.associated_sub_one_pow_sub_one_of_coprime hcop
  have hζ1 : ζI - 1 ≠ 0 := sub_ne_zero.mpr (hζI.ne_one hp.out.one_lt)
  have hu' : (u : 𝓞 (CyclotomicField p ℚ)) = 1 + ζI := by
    apply mul_left_cancel₀ hζ1
    rw [hu]
    ring
  obtain ⟨m, w, hmw⟩ := reduceK p Kplus Δact hΔact δ hδeig hDIM u
    (hB2 ζI (by rw [RingOfIntegers.coe_eq_algebraMap, hζIK]; exact hζK) u hu')
  set nn : (ZMod p)ˣ → ℕ := fun d =>
    (((Nat.card (ZMod p)ˣ : ℕ) : ZMod p)⁻¹ * (((d : ZMod p)) ^ 2)⁻¹).val with hnn
  refine ⟨m, Units.map (NumberField.RingOfIntegers.norm Kplus (L := CyclotomicField p ℚ)) w,
    Units.map (NumberField.RingOfIntegers.norm Kplus (L := CyclotomicField p ℚ))
      (∏ d : (ZMod p)ˣ,
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u) ^ nn d), nn, ?_⟩
  obtain ⟨τ₀, hτ₀, hall, hτ₀x⟩ := exists_involution p Kplus hKplus
  have ha := fun d : (ZMod p)ˣ =>
    exists_trace p Kplus τ₀ hτ₀ hall (ζI ^ (d : ZMod p).val)
  choose a ha using ha
  have hτζ : ∀ k : ℕ, τ₀ (zeta p ℚ (CyclotomicField p ℚ) ^ k) =
      (zeta p ℚ (CyclotomicField p ℚ) ^ k)⁻¹ := fun k => by
    rw [map_pow, hτ₀x, cycloGalEquiv_symm_neg_one_zeta, inv_pow]
  have ha' : ∀ d, algebraMap (𝓞 Kplus) (CyclotomicField p ℚ) (a d) =
      zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val +
        (zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val)⁻¹ := fun d => by
    rw [IsScalarTower.algebraMap_apply (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ),
      ← RingOfIntegers.coe_eq_algebraMap, ha d, RingOfIntegers.coe_eq_algebraMap, map_pow, hζIK,
      hτζ]
  refine ⟨a, sq_eq_of_map_eq p Kplus hKplus δ _ w m hmw, ?_, ha'⟩
  apply FaithfulSMul.algebraMap_injective (𝓞 Kplus) (CyclotomicField p ℚ)
  rw [IsScalarTower.algebraMap_apply (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ),
    Units.coe_map, ← RingOfIntegers.coe_eq_algebraMap,
    coe_algebraMap_norm_eq p Kplus τ₀ hτ₀ hall, RingOfIntegers.coe_eq_algebraMap, map_prod]
  have hzne : zeta p ℚ (CyclotomicField p ℚ) ≠ 0 := hζK.ne_zero hp.out.ne_zero
  have hu₂ : algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
      (Units.val (∏ d : (ZMod p)ˣ,
        (Units.mapEquiv (clRingAction p (CyclotomicField p ℚ) d).toMulEquiv u) ^ nn d)) =
      ∏ d : (ZMod p)ˣ, (1 + zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val) ^ nn d := by
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl (fun d _ => ?_)
    rw [Units.val_pow_eq_pow_val, map_pow, Units.coe_mapEquiv]
    change algebraMap (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
      (clRingAction p (CyclotomicField p ℚ) d (u : 𝓞 (CyclotomicField p ℚ))) ^ nn d = _
    rw [algebraMap_clRingAction, hu', map_add, map_one, map_add, map_one, hζIK,
      cycloGalEquiv_symm_apply_zeta]
  rw [hu₂, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun d _ => ?_)
  simp only [map_pow, map_add, map_one, map_ofNat, ha', hτζ]
  rw [← mul_pow]
  congr 1
  have hz : zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val ≠ 0 := pow_ne_zero _ hzne
  field_simp
  ring

end Pack
open scoped ThaineReduce

end ThaineReduce
open scoped ThaineReduce

namespace ThaineReduce

open NumberField Stickelberger IsCyclotomicExtension

private theorem eigen_pow_of_sq_rel {G : Type*} [CommGroup G] (φ : G →* G) (q : ℕ) (δ δ₀ w v : G)
    (m k : ℕ) (hv : φ δ = δ ^ k * v ^ q) (hrel : δ ^ 2 = δ₀ ^ m * w ^ q) :
    ∃ v' : G, φ (δ₀ ^ m) = (δ₀ ^ m) ^ k * v' ^ q := by
  refine ⟨w ^ k * v ^ 2 * (φ w)⁻¹, ?_⟩
  have key : φ (δ₀ ^ m) * φ w ^ q = (δ₀ ^ m) ^ k * (w ^ k * v ^ 2) ^ q := by
    have h1 : φ (δ₀ ^ m) * φ w ^ q = (δ ^ k * v ^ q) ^ 2 := by
      rw [← map_pow, ← map_mul, ← hrel, map_pow, hv]
    have h2 : (δ₀ ^ m) ^ k * (w ^ k * v ^ 2) ^ q = (δ ^ 2) ^ k * (v ^ 2) ^ q := by
      rw [hrel, mul_pow (δ₀ ^ m) (w ^ q) k, mul_pow (w ^ k) (v ^ 2) q, ← pow_mul w k q,
        ← pow_mul w q k, Nat.mul_comm q k, mul_assoc]
    rw [h1, h2, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, ← pow_mul, Nat.mul_comm k 2,
      Nat.mul_comm q 2]
  calc φ (δ₀ ^ m) = φ (δ₀ ^ m) * φ w ^ q * (φ w ^ q)⁻¹ := by rw [mul_inv_cancel_right]
    _ = (δ₀ ^ m) ^ k * (w ^ k * v ^ 2) ^ q * (φ w ^ q)⁻¹ := by rw [key]
    _ = (δ₀ ^ m) ^ k * (w ^ k * v ^ 2 * (φ w)⁻¹) ^ q := by
      rw [mul_pow (w ^ k * v ^ 2) (φ w)⁻¹ q, inv_pow, mul_assoc]

private theorem mapEquiv_pow_eigen (p : ℕ) {R : Type*} [CommRing R]
    (Δact : (ZMod p)ˣ →* R ≃+* R) (δ δ₀ w : Rˣ) (m : ℕ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : Rˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hrel : δ ^ 2 = δ₀ ^ m * w ^ p) (e : (ZMod p)ˣ) :
    ∃ v : Rˣ, Units.mapEquiv (Δact e).toMulEquiv (δ₀ ^ m) =
      (δ₀ ^ m) ^ ((e : ZMod p) ^ 2).val * v ^ p := by
  obtain ⟨v, hv⟩ := hδeig e
  exact eigen_pow_of_sq_rel (Units.mapEquiv (Δact e).toMulEquiv).toMonoidHom p δ δ₀ w v m _ hv hrel

variable (p : ℕ) [hp : Fact p.Prime]

private theorem Δact_neg_one
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)))) :
    Δact (-1) = 1 := by
  obtain ⟨τ₀, -, -, hτ₀x⟩ := exists_involution p Kplus hKplus
  apply DFunLike.ext
  intro x
  change (Δact (-1)) x = x
  have h := DFunLike.congr_fun (hΔact (-1)) x
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe] at h
  apply FaithfulSMul.algebraMap_injective (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))
  apply FaithfulSMul.algebraMap_injective (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ)
  rw [h, algebraMap_clRingAction,
    ← IsScalarTower.algebraMap_apply (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) (CyclotomicField p ℚ),
    IsScalarTower.algebraMap_apply (𝓞 Kplus) Kplus (CyclotomicField p ℚ), ← hτ₀x,
    AlgEquiv.commutes]

end ThaineReduce
open scoped ThaineReduce

open Polynomial

namespace ThaineLift

section R1_geom_sum
variable {K : Type*} [Field K] {ℓ : ℕ}

private lemma eval_cyclotomic_prime_of_pow_eq_self (hℓ : ℓ.Prime) (w : K)
    (hw : w ^ ℓ = w) (hne : w ≠ 1) :
    (cyclotomic ℓ K).eval w = 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  rw [cyclotomic_prime, eval_geom_sum, geom_sum_eq hne, hw]
  exact div_self (sub_ne_zero.mpr hne)

private lemma primRoot_pow_pow_eq_self {p : ℕ} [Fact p.Prime] {ζp : K} (hζp : IsPrimitiveRoot ζp p)
    (hcong : (ℓ : ZMod p) = 1) (d : ℕ) :
    (ζp ^ d) ^ ℓ = ζp ^ d := by
  rw [← pow_mul]
  have hpℓ : p ∣ ℓ - 1 := by
    have : (ℓ : ZMod p) - 1 = 0 := by rw [hcong]; ring
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · simp only [h0, Nat.cast_zero] at hcong
      exact absurd hcong.symm (by simp)
    · rwa [← Nat.cast_one, ← Nat.cast_sub hpos, ZMod.natCast_eq_zero_iff] at this
  obtain ⟨m, hm⟩ := hpℓ
  have harith : d * ℓ = p * (d * m) + d := by
    rcases Nat.eq_zero_or_pos ℓ with h0 | hpos
    · simp only [h0, Nat.cast_zero] at hcong
      exact absurd hcong.symm (by simp)
    have h1 : ℓ = p * m + 1 := by
      have := Nat.sub_add_cancel hpos; rw [hm] at this; omega
    rw [h1]; ring
  rw [harith, pow_add, pow_mul, hζp.pow_eq_one, one_pow, one_mul]

private lemma eval_cyclotomic_prime_at_primRoot {p : ℕ} [Fact p.Prime] {ζp : K}
    (hℓ : ℓ.Prime) (hζp : IsPrimitiveRoot ζp p)
    (hcong : (ℓ : ZMod p) = 1) (d : ℕ) (hd : ¬ (p ∣ d)) :
    (cyclotomic ℓ K).eval (ζp ^ d) = 1 :=
  eval_cyclotomic_prime_of_pow_eq_self hℓ _
    (primRoot_pow_pow_eq_self hζp hcong d)
    (fun h => hd (hζp.pow_eq_one_iff_dvd d |>.mp h))

end R1_geom_sum
open scoped ThaineReduce

section R1b_neg_root_hyps

variable {K : Type*} [Field K] {p ℓ : ℕ} [Fact p.Prime] {ζp : K}

private lemma neg_primRoot_pow_ne_one (hp2 : p ≠ 2) (hζp : IsPrimitiveRoot ζp p)
    (d : ℕ) (hd : ¬ p ∣ d) : -ζp ^ d ≠ 1 := by
  intro h
  have : ζp ^ (2 * d) = 1 := by
    have h2 : (ζp ^ d) ^ 2 = 1 := by rw [← neg_eq_iff_eq_neg.mpr h.symm]; ring
    rwa [← pow_mul, mul_comm] at h2
  have hp2d := hζp.pow_eq_one_iff_dvd (2 * d) |>.mp this
  have hpp : p.Prime := Fact.out
  rcases (hpp.dvd_mul).mp hp2d with h | h
  · exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h)
  · exact hd h

private lemma inv_neg_primRoot_pow_ne_one (hp2 : p ≠ 2) (hζp : IsPrimitiveRoot ζp p)
    (d : ℕ) (hd : ¬ p ∣ d) : (-ζp ^ d)⁻¹ ≠ 1 := by
  rw [ne_eq, inv_eq_one]
  exact neg_primRoot_pow_ne_one hp2 hζp d hd

private lemma neg_primRoot_pow_pow_eq_self (hζp : IsPrimitiveRoot ζp p)
    (hcong : (ℓ : ZMod p) = 1) (hℓodd : Odd ℓ) (d : ℕ) :
    (-ζp ^ d) ^ ℓ = -ζp ^ d := by
  rw [neg_pow, hℓodd.neg_one_pow, neg_one_mul, primRoot_pow_pow_eq_self hζp hcong d]

private lemma odd_of_cong_one (hℓ : ℓ.Prime) (hcong : (ℓ : ZMod p) = 1) : Odd ℓ := by
  refine hℓ.odd_of_ne_two fun h2 => ?_
  subst h2
  have hpd : p ∣ 2 - 1 := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub one_le_two, hcong, Nat.cast_one, sub_self]
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp (by simpa using hpd))

end R1b_neg_root_hyps
open scoped ThaineReduce

section R2_resultant_K
variable {K : Type*} [Field K] {ℓ : ℕ}

private noncomputable def Pd_K (r : K) : K[X] := (X - C r) * (X - C r⁻¹)

private lemma Pd_K_splits (r : K) : (Pd_K r).Splits :=
  (Splits.X_sub_C _).mul (Splits.X_sub_C _)

private lemma Pd_K_natDegree {r : K} (hr : r ≠ 0) : (Pd_K r).natDegree = 2 := by
  have hne : r ≠ 0 := hr
  unfold Pd_K
  rw [natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _),
    natDegree_X_sub_C, natDegree_X_sub_C]

private lemma Pd_K_roots (r : K) : (Pd_K r).roots = {r, r⁻¹} := by
  unfold Pd_K
  rw [roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

private lemma resultant_Pd_cyclotomic_K' (hℓ : ℓ.Prime) {r : K} (hr : r ≠ 0)
    (hrℓ : r ^ ℓ = r) (hrne : r ≠ 1) (hrinvne : r⁻¹ ≠ 1) :
    (Pd_K r).resultant (cyclotomic ℓ K) 2 (ℓ - 1) = 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hdeg := Pd_K_natDegree hr
  have hcycdeg : (cyclotomic ℓ K).natDegree = ℓ - 1 := by
    rw [natDegree_cyclotomic]; exact Nat.totient_prime hℓ
  rw [← hdeg, resultant_eq_prod_eval _ _ _ (hcycdeg.le) (Pd_K_splits r), Pd_K_roots r]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton]
  have hlc : (Pd_K r).leadingCoeff = 1 := by
    unfold Pd_K; exact (monic_X_sub_C _).mul (monic_X_sub_C _)
  rw [hlc, one_pow, one_mul]
  have hrinv : (r⁻¹) ^ ℓ = r⁻¹ := by rw [inv_pow, hrℓ]
  rw [eval_cyclotomic_prime_of_pow_eq_self hℓ r hrℓ hrne,
    eval_cyclotomic_prime_of_pow_eq_self hℓ r⁻¹ hrinv hrinvne, mul_one]

private lemma resultant_Pd_cyclotomic_K {p : ℕ} [Fact p.Prime] {ζp : K}
    (hℓ : ℓ.Prime) (hζp : IsPrimitiveRoot ζp p)
    (hcong : (ℓ : ZMod p) = 1) (d : ℕ) (hd : ¬ p ∣ d) :
    (Pd_K (ζp ^ d)).resultant (cyclotomic ℓ K) 2 (ℓ - 1) = 1 := by
  have hne0 : ζp ≠ 0 := hζp.ne_zero (Fact.out : p.Prime).pos.ne'
  have hpowne : ζp ^ d ≠ 1 := fun h => hd (hζp.pow_eq_one_iff_dvd d |>.mp h)
  have hinv : (ζp ^ d)⁻¹ = ζp ^ (d * (p - 1)) := by
    refine inv_eq_of_mul_eq_one_right ?_
    have hexp : d + d * (p - 1) = p * d := by
      have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_le
      rw [Nat.mul_sub_one, Nat.add_sub_cancel'
        (Nat.le_mul_of_pos_right d hp1), Nat.mul_comm]
    rw [← pow_add, hexp, pow_mul, hζp.pow_eq_one, one_pow]
  have hd' : ¬ p ∣ d * (p - 1) := by
    intro h; have hpp : p.Prime := Fact.out
    rcases hpp.dvd_mul.mp h with h | h
    · exact hd h
    · have : p - 1 < p := Nat.sub_lt hpp.pos one_pos
      have := Nat.le_of_dvd (Nat.sub_pos_of_lt hpp.one_lt) h; omega
  exact resultant_Pd_cyclotomic_K' hℓ (pow_ne_zero d hne0)
    (primRoot_pow_pow_eq_self hζp hcong d) hpowne
    (hinv ▸ fun h => hd' (hζp.pow_eq_one_iff_dvd _ |>.mp h))

end R2_resultant_K
open scoped ThaineReduce

section R3_R5_glue

variable {Kplus K L : Type*} [Field Kplus] [Field K] [Field L]
variable [Algebra Kplus K] [Algebra Kplus L]
variable {p ℓ : ℕ} [Fact p.Prime]
variable {ζp : K} {ζℓ : L}

private noncomputable def Pd (ad : Kplus) : Kplus[X] := X ^ 2 - C ad * X + 1

private lemma Pd_map_eq_factored (ad : Kplus) (r : K)
    (hr : algebraMap Kplus K ad = r + r⁻¹) (hrne : r ≠ 0) :
    (Pd ad).map (algebraMap Kplus K) = (X - C r) * (X - C r⁻¹) := by
  unfold Pd
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_one, map_X, map_C, hr]
  have hCrr : C r * C r⁻¹ = (1 : K[X]) := by
    rw [← map_mul, mul_inv_cancel₀ hrne, map_one]
  rw [show (X - C r) * (X - C r⁻¹)
      = X ^ 2 - (C r + C r⁻¹) * X + C r * C r⁻¹ by ring, hCrr, ← C_add]

private lemma Pd_natDegree (ad : Kplus) : (Pd ad).natDegree = 2 := by
  unfold Pd
  compute_degree!

private lemma prod_primitiveRoots_eval_Pd' (hℓ : ℓ.Prime)
    (hζℓ : IsPrimitiveRoot ζℓ ℓ)
    (ad : Kplus) {r : K} (hr : r ≠ 0) (hrℓ : r ^ ℓ = r) (hrne : r ≠ 1) (hrinvne : r⁻¹ ≠ 1)
    (had : algebraMap Kplus K ad = r + r⁻¹) :
    (((cyclotomic ℓ L).roots).map
      (fun x => ((Pd ad).map (algebraMap Kplus L)).eval x)).prod = 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hsplits : (cyclotomic ℓ L).Splits := by
    have h := cyclotomic_eq_prod_X_sub_primitiveRoots hζℓ
    rw [h]; exact Splits.prod fun _ _ => Splits.X_sub_C _
  have hcycdeg : (cyclotomic ℓ L).natDegree = ℓ - 1 := by
    rw [natDegree_cyclotomic]; exact Nat.totient_prime hℓ
  have hPddeg : ((Pd ad).map (algebraMap Kplus L)).natDegree ≤ 2 := by
    refine le_trans natDegree_map_le ?_; rw [Pd_natDegree]
  have hres_L : (cyclotomic ℓ L).resultant ((Pd ad).map (algebraMap Kplus L)) (ℓ - 1) 2 =
      ((cyclotomic ℓ L).roots.map
        (fun x => ((Pd ad).map (algebraMap Kplus L)).eval x)).prod := by
    rw [← hcycdeg, resultant_eq_prod_eval _ _ _ hPddeg hsplits,
      (cyclotomic.monic ℓ L).leadingCoeff, one_pow, one_mul]
  have hres_Kplus : (cyclotomic ℓ Kplus).resultant (Pd ad) (ℓ - 1) 2 = 1 := by
    apply (algebraMap Kplus K).injective
    rw [← resultant_map_map, map_cyclotomic, map_one, Pd_map_eq_factored ad r had hr]
    have := resultant_Pd_cyclotomic_K' hℓ hr hrℓ hrne hrinvne
    unfold Pd_K at this
    rw [resultant_comm, this, mul_one, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [← hres_L, show (cyclotomic ℓ L) = (cyclotomic ℓ Kplus).map (algebraMap Kplus L) from
    (map_cyclotomic ℓ (algebraMap Kplus L)).symm, resultant_map_map, hres_Kplus, map_one]

private lemma prod_primitiveRoots_eval_Pd (hℓ : ℓ.Prime) (hζp : IsPrimitiveRoot ζp p)
    (hζℓ : IsPrimitiveRoot ζℓ ℓ) (hcong : (ℓ : ZMod p) = 1)
    (ad : Kplus) (d : ℕ) (hd : ¬ p ∣ d)
    (had : algebraMap Kplus K ad = ζp ^ d + (ζp ^ d)⁻¹) :
    (((cyclotomic ℓ L).roots).map
      (fun x => ((Pd ad).map (algebraMap Kplus L)).eval x)).prod = 1 := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hsplits : (cyclotomic ℓ L).Splits := by
    have h := cyclotomic_eq_prod_X_sub_primitiveRoots hζℓ
    rw [h]; exact Splits.prod fun _ _ => Splits.X_sub_C _
  have hcycdeg : (cyclotomic ℓ L).natDegree = ℓ - 1 := by
    rw [natDegree_cyclotomic]; exact Nat.totient_prime hℓ
  have hPddeg : ((Pd ad).map (algebraMap Kplus L)).natDegree ≤ 2 := by
    refine le_trans natDegree_map_le ?_; rw [Pd_natDegree]
  have hres_L : (cyclotomic ℓ L).resultant ((Pd ad).map (algebraMap Kplus L)) (ℓ - 1) 2 =
      ((cyclotomic ℓ L).roots.map
        (fun x => ((Pd ad).map (algebraMap Kplus L)).eval x)).prod := by
    rw [← hcycdeg, resultant_eq_prod_eval _ _ _ hPddeg hsplits,
      (cyclotomic.monic ℓ L).leadingCoeff, one_pow, one_mul]
  have hres_Kplus : (cyclotomic ℓ Kplus).resultant (Pd ad) (ℓ - 1) 2 = 1 := by
    apply (algebraMap Kplus K).injective
    rw [← resultant_map_map, map_cyclotomic, map_one,
      Pd_map_eq_factored ad (ζp ^ d) had (pow_ne_zero d (hζp.ne_zero
        (Fact.out : p.Prime).pos.ne'))]
    have := resultant_Pd_cyclotomic_K hℓ hζp hcong d hd
    unfold Pd_K at this
    rw [resultant_comm, this, mul_one, mul_comm, pow_mul, neg_one_sq, one_pow]
  rw [← hres_L, show (cyclotomic ℓ L) = (cyclotomic ℓ Kplus).map (algebraMap Kplus L) from
    (map_cyclotomic ℓ (algebraMap Kplus L)).symm, resultant_map_map, hres_Kplus, map_one]

end R3_R5_glue
open scoped ThaineReduce

section R6_norm
variable {Kplus L : Type*} [Field Kplus] [Field L] [Algebra Kplus L]
variable {ℓ : ℕ} [Fact ℓ.Prime] [IsCyclotomicExtension {ℓ} Kplus L]
open IsCyclotomicExtension

private lemma prod_gal_aeval_eq_prod_primitiveRoots (hirr : Irreducible (cyclotomic ℓ Kplus))
    {ζℓ : L} (hζℓ : IsPrimitiveRoot ζℓ ℓ) (f : Kplus[X]) :
    haveI : FiniteDimensional Kplus L := IsCyclotomicExtension.finiteDimensional {ℓ} Kplus L
    ∏ σ : Gal(L/Kplus), σ (aeval ζℓ f) =
      ∏ μ ∈ primitiveRoots ℓ L, aeval μ f := by
  have : FiniteDimensional Kplus L := IsCyclotomicExtension.finiteDimensional {ℓ} Kplus L
  simp_rw [show ∀ σ : Gal(L/Kplus), σ (aeval ζℓ f) = aeval (σ ζℓ) f from
    fun σ => (aeval_algHom_apply σ ζℓ f).symm]
  rw [← Finset.prod_attach (primitiveRoots ℓ L), ← Finset.univ_eq_attach]
  have hcard : Fintype.card (L ≃ₐ[Kplus] L) = (primitiveRoots ℓ L).card := by
    have : IsGalois Kplus L := IsCyclotomicExtension.isGalois {ℓ} Kplus L
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank,
      IsCyclotomicExtension.finrank L hirr, hζℓ.card_primitiveRoots]
  refine Fintype.prod_equiv
    (Equiv.ofBijective (fun σ : Gal(L/Kplus) => (⟨σ ζℓ,
      (mem_primitiveRoots (Fact.out : ℓ.Prime).pos).mpr
        (hζℓ.map_of_injective σ.injective)⟩ : primitiveRoots ℓ L))
      ((Fintype.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩)) _ _ ?_
  · intro σ σ' h
    simp only [Subtype.mk.injEq] at h
    exact AlgEquiv.coe_toAlgHom_injective ((hζℓ.powerBasis Kplus).algHom_ext
      (by simpa [IsPrimitiveRoot.powerBasis_gen] using h))
  · simp [hcard]
  · intro σ; rfl

private lemma norm_aeval_Pd' (K : Type*) [Field K] [Algebra Kplus K]
    (hℓ : ℓ.Prime) (hirr : Irreducible (cyclotomic ℓ Kplus))
    {ζℓ : L} (hζℓ : IsPrimitiveRoot ζℓ ℓ)
    (ad : Kplus) {r : K} (hr : r ≠ 0) (hrℓ : r ^ ℓ = r) (hrne : r ≠ 1) (hrinvne : r⁻¹ ≠ 1)
    (had : algebraMap Kplus K ad = r + r⁻¹) :
    Algebra.norm Kplus (aeval ζℓ (Pd ad) : L) = 1 := by
  have : FiniteDimensional Kplus L := IsCyclotomicExtension.finiteDimensional {ℓ} Kplus L
  have : IsGalois Kplus L := IsCyclotomicExtension.isGalois {ℓ} Kplus L
  apply (algebraMap Kplus L).injective
  rw [map_one, Algebra.norm_eq_prod_automorphisms,
    prod_gal_aeval_eq_prod_primitiveRoots hirr hζℓ]
  have hprod := prod_primitiveRoots_eval_Pd' (K := K) hℓ hζℓ ad hr hrℓ hrne hrinvne had
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero (ℓ : L) := IsCyclotomicExtension.neZero (n := ℓ) (A := Kplus) (B := L)
  rw [cyclotomic.roots_eq_primitiveRoots_val, ← Finset.prod_eq_multiset_prod] at hprod
  simp only [eval_map_algebraMap] at hprod
  exact hprod

private lemma norm_aeval_Pd (K : Type*) [Field K] [Algebra Kplus K]
    {p : ℕ} [Fact p.Prime] {ζp : K}
    (hℓ : ℓ.Prime) (hζp : IsPrimitiveRoot ζp p)
    (hirr : Irreducible (cyclotomic ℓ Kplus))
    {ζℓ : L} (hζℓ : IsPrimitiveRoot ζℓ ℓ) (hcong : (ℓ : ZMod p) = 1)
    (ad : Kplus) (d : ℕ) (hd : ¬ p ∣ d)
    (had : algebraMap Kplus K ad = ζp ^ d + (ζp ^ d)⁻¹) :
    Algebra.norm Kplus (aeval ζℓ (Pd ad) : L) = 1 := by
  have : FiniteDimensional Kplus L := IsCyclotomicExtension.finiteDimensional {ℓ} Kplus L
  have : IsGalois Kplus L := IsCyclotomicExtension.isGalois {ℓ} Kplus L
  apply (algebraMap Kplus L).injective
  rw [map_one, Algebra.norm_eq_prod_automorphisms,
    prod_gal_aeval_eq_prod_primitiveRoots hirr hζℓ]
  have hprod := prod_primitiveRoots_eval_Pd (K := K) hℓ hζp hζℓ hcong ad d hd had
  have : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  have : NeZero (ℓ : L) := IsCyclotomicExtension.neZero (n := ℓ) (A := Kplus) (B := L)
  rw [cyclotomic.roots_eq_primitiveRoots_val, ← Finset.prod_eq_multiset_prod] at hprod
  simp only [eval_map_algebraMap] at hprod
  exact hprod

end R6_norm
open scoped ThaineReduce

section R7_residue

variable {Kplus : Type*} [Field Kplus]
variable {B : Type*} [CommRing B] [Algebra Kplus B]

private lemma Pd_aeval_sub_aeval_one (ad : Kplus) (ζℓ : B) :
    aeval ζℓ (Pd ad) - aeval 1 (Pd ad) = (ζℓ - 1) * (ζℓ + 1 - algebraMap Kplus B ad) := by
  simp only [Pd, map_add, map_sub, map_one, map_mul, map_pow, aeval_X, aeval_C,
    one_pow, mul_one]
  ring

private lemma Pd_aeval_one (ad : Kplus) : aeval (1 : B) (Pd ad) = 2 - algebraMap Kplus B ad := by
  simp only [Pd, map_add, map_sub, map_one, map_mul, map_pow, aeval_X, aeval_C,
    one_pow, mul_one]
  ring

private lemma Pd_aeval_sub_mem (ad : Kplus) (ζℓ : B) (𝔓 : Ideal B) (hζℓ𝔓 : ζℓ - 1 ∈ 𝔓) :
    aeval ζℓ (Pd ad) - (2 - algebraMap Kplus B ad) ∈ 𝔓 := by
  rw [← Pd_aeval_one ad, Pd_aeval_sub_aeval_one]
  exact 𝔓.mul_mem_right _ hζℓ𝔓

end R7_residue
open scoped ThaineReduce

end ThaineLift
open scoped ThaineReduce

open Polynomial NumberField

namespace ThaineLift

section copy
variable {Kplus : Type*} [Field Kplus]
private noncomputable def Pd' (ad : Kplus) : Kplus[X] := X ^ 2 - C ad * X + 1
end copy
open scoped ThaineReduce

section assemble
variable {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime]
variable {Kplus : Type*} [Field Kplus]
variable {L : Type*} [Field L] [Algebra Kplus L]

private noncomputable def PdInt (ad : 𝓞 Kplus) (ζℓ : 𝓞 L) : 𝓞 L :=
  ζℓ ^ 2 - algebraMap (𝓞 Kplus) (𝓞 L) ad * ζℓ + 1

private lemma coe_PdInt (ad : 𝓞 Kplus) (ζℓ : 𝓞 L) :
    (PdInt ad ζℓ : L) = aeval (ζℓ : L) (Pd' (ad : Kplus)) := by
  have hsq : (algebraMap (𝓞 L) L) ((algebraMap (𝓞 Kplus) (𝓞 L)) ad) =
      (algebraMap Kplus L) ((ad : Kplus)) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  simp only [PdInt, Pd', map_add, map_sub, map_one, map_mul, map_pow, aeval_X, aeval_C, hsq]

section NF
variable [NumberField Kplus] [NumberField L] [IsCyclotomicExtension {ℓ} Kplus L]

private lemma isUnit_of_norm_one' (x : 𝓞 L) (hx : Algebra.norm Kplus (x : L) = 1) : IsUnit x := by
  rw [← NumberField.RingOfIntegers.isUnit_norm Kplus]
  suffices h : NumberField.RingOfIntegers.norm Kplus x = 1 by rw [h]; exact isUnit_one
  apply RingOfIntegers.coe_injective
  simp only [NumberField.RingOfIntegers.coe_norm, hx, map_one]

private lemma isUnit_PdInt (ad : 𝓞 Kplus) (ζℓ : 𝓞 L)
    (hN : Algebra.norm Kplus (aeval (ζℓ : L) (Pd' (ad : Kplus))) = 1) :
    IsUnit (PdInt ad ζℓ) :=
  isUnit_of_norm_one' _ (by rw [coe_PdInt]; exact hN)

end NF
open scoped ThaineReduce

private lemma PdInt_sub_mem (ad : 𝓞 Kplus) (ζℓ : 𝓞 L) (𝔓 : Ideal (𝓞 L))
    (hζℓ𝔓 : ζℓ - 1 ∈ 𝔓) :
    PdInt ad ζℓ - (2 - algebraMap (𝓞 Kplus) (𝓞 L) ad) ∈ 𝔓 := by
  have : PdInt ad ζℓ - (2 - algebraMap (𝓞 Kplus) (𝓞 L) ad)
      = (ζℓ - 1) * (ζℓ + 1 - algebraMap (𝓞 Kplus) (𝓞 L) ad) := by
    unfold PdInt; ring
  rw [this]; exact 𝔓.mul_mem_right _ hζℓ𝔓

private lemma prod_PdInt_pow_sub_mem (ad : (ZMod p)ˣ → 𝓞 Kplus) (n : (ZMod p)ˣ → ℕ)
    (ζℓ : 𝓞 L) (𝔓 : Ideal (𝓞 L)) (hζℓ𝔓 : ζℓ - 1 ∈ 𝔓) :
    ∏ d, PdInt (ad d) ζℓ ^ n d -
      ∏ d, (2 - algebraMap (𝓞 Kplus) (𝓞 L) (ad d)) ^ n d ∈ 𝔓 := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero, map_prod, map_prod]
  refine Finset.prod_congr rfl fun d _ => ?_
  rw [map_pow, map_pow]
  congr 1
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact PdInt_sub_mem (ad d) ζℓ 𝔓 hζℓ𝔓

private noncomputable def eta_unit (ad : (ZMod p)ˣ → 𝓞 Kplus) (ζℓ : 𝓞 L)
    (hU : ∀ d, IsUnit (PdInt (ad d) ζℓ)) (b : (ZMod p)ˣ → ℕ) : (𝓞 L)ˣ :=
  ∏ d, (hU d).unit ^ b d

private lemma eta_unit_coe (ad : (ZMod p)ˣ → 𝓞 Kplus) (ζℓ : 𝓞 L)
    (hU : ∀ d, IsUnit (PdInt (ad d) ζℓ)) (b : (ZMod p)ˣ → ℕ) :
    (eta_unit ad ζℓ hU b : 𝓞 L) = ∏ d, PdInt (ad d) ζℓ ^ b d := by
  unfold eta_unit
  push_cast
  exact Finset.prod_congr rfl fun d _ => by rw [IsUnit.unit_spec]

private lemma norm_eta_unit [NumberField Kplus] [NumberField L]
    (ad : (ZMod p)ˣ → 𝓞 Kplus) (ζℓ : 𝓞 L)
    (hU : ∀ d, IsUnit (PdInt (ad d) ζℓ)) (b : (ZMod p)ˣ → ℕ)
    (hNd : ∀ d, Algebra.norm Kplus (algebraMap (𝓞 L) L (PdInt (ad d) ζℓ)) = 1) :
    Algebra.norm Kplus (algebraMap (𝓞 L) L (eta_unit ad ζℓ hU b : 𝓞 L)) = 1 := by
  rw [eta_unit_coe, map_prod, map_prod]
  refine Finset.prod_eq_one fun d _ => ?_
  rw [map_pow, map_pow, hNd d, one_pow]

private lemma eta_unit_sub_mem (ad : (ZMod p)ˣ → 𝓞 Kplus) (ζℓ : 𝓞 L)
    (hU : ∀ d, IsUnit (PdInt (ad d) ζℓ)) (b : (ZMod p)ˣ → ℕ)
    (𝔓 : Ideal (𝓞 L)) (hζℓ𝔓 : ζℓ - 1 ∈ 𝔓) :
    (eta_unit ad ζℓ hU b : 𝓞 L) -
      ∏ d, (2 - algebraMap (𝓞 Kplus) (𝓞 L) (ad d)) ^ b d ∈ 𝔓 := by
  rw [eta_unit_coe]
  exact prod_PdInt_pow_sub_mem ad b ζℓ 𝔓 hζℓ𝔓

omit [Fact ℓ.Prime] in
private theorem lift_block [NumberField Kplus] [NumberField L]
    (ζℓ : 𝓞 L)
    (hζℓ𝔓 : ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
      ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsMaximal], 𝔓.LiesOver 𝔔 → ζℓ - 1 ∈ 𝔓)
    (ad : (ZMod p)ˣ → 𝓞 Kplus)
    (hNd : ∀ d, Algebra.norm Kplus (aeval (ζℓ : L) (Pd' ((ad d : Kplus)))) = 1)
    (b : (ZMod p)ˣ → ℕ)
    (δ₀ : (𝓞 Kplus)ˣ)
    (hδ₀ : ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
      ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsMaximal], 𝔓.LiesOver 𝔔 →
      algebraMap (𝓞 Kplus) (𝓞 L) (δ₀ : 𝓞 Kplus) -
        ∏ d, (2 - algebraMap (𝓞 Kplus) (𝓞 L) (ad d)) ^ b d ∈ 𝔓) :
    ∃ (η : (𝓞 L)ˣ),
      Algebra.norm Kplus (algebraMap (𝓞 L) L (η : 𝓞 L)) = 1 ∧
      ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
        ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsMaximal], 𝔓.LiesOver 𝔔 →
          (η : 𝓞 L) - algebraMap (𝓞 Kplus) (𝓞 L) (δ₀ : 𝓞 Kplus) ∈ 𝔓 := by
  have hU : ∀ d, IsUnit (PdInt (ad d) ζℓ) := fun d =>
    isUnit_PdInt (ad d) ζℓ (hNd d)
  refine ⟨eta_unit ad ζℓ hU b, ?_, ?_⟩
  · refine norm_eta_unit ad ζℓ hU b (fun d => ?_)
    have := coe_PdInt (L := L) (ad d) ζℓ
    rw [show (algebraMap (𝓞 L) L) (PdInt (ad d) ζℓ) = (PdInt (ad d) ζℓ : L) from rfl, this]
    exact hNd d
  · intro 𝔔 _ hℓ𝔔 𝔓 _ h𝔓
    have h1 := eta_unit_sub_mem ad ζℓ hU b 𝔓 (hζℓ𝔓 𝔔 hℓ𝔔 𝔓 h𝔓)
    have h2 := hδ₀ 𝔔 hℓ𝔔 𝔓 h𝔓
    have := 𝔓.sub_mem h1 h2
    convert this using 1; ring

end assemble
open scoped ThaineReduce

end ThaineLift
open scoped ThaineReduce

open scoped Pointwise

namespace ThaineDesk

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsDomain B]
  [FiniteDimensional K L] [IsGalois K L]

omit [IsFractionRing B L] [IsIntegrallyClosed A] [IsDomain B] [FiniteDimensional K L] in
private theorem smul_eq_map_galRestrict (σ : L ≃ₐ[K] L) (I : Ideal B) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    σ • I = I.map (galRestrict A K L B σ) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  rw [Ideal.pointwise_smul_def]
  rfl

omit [IsFractionRing B L] [IsIntegrallyClosed A] [FiniteDimensional K L] in
private theorem map_galRestrict_span_eq (g : L ≃ₐ[K] L)
    (hg : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers g)
    (η : Bˣ) (β : B) (hrel : (η : B) * galRestrict A K L B g β = β) (σ : L ≃ₐ[K] L) :
    (Ideal.span {β}).map (galRestrict A K L B σ) = Ideal.span {β} := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  rw [← smul_eq_map_galRestrict]
  have hgβ : galRestrict A K L B g β = (η⁻¹ : Bˣ) * β :=
    (Units.mul_right_inj η).mp (by rw [hrel, ← mul_assoc, Units.mul_inv, one_mul])
  have hgmem : g ∈ MulAction.stabilizer (L ≃ₐ[K] L) (Ideal.span {β} : Ideal B) := by
    change g • (Ideal.span {β} : Ideal B) = Ideal.span {β}
    rw [smul_eq_map_galRestrict, Ideal.map_span, Set.image_singleton, hgβ,
      Ideal.span_singleton_eq_span_singleton]
    exact ⟨η, by rw [mul_comm ((η⁻¹ : Bˣ) : B) β, mul_assoc, Units.inv_mul, mul_one]⟩
  exact Subgroup.zpowers_le.mpr hgmem (hg σ)

section Dedekind

variable [IsDedekindDomain B]

omit [IsDedekindDomain B] [IsFractionRing B L] [IsIntegrallyClosed A] [IsDomain B]
    [FiniteDimensional K L] in
private theorem span_le_map_pow_iff (β : B) (σ : L ≃ₐ[K] L)
    (hinv : (Ideal.span {β}).map (galRestrict A K L B σ⁻¹) = Ideal.span {β})
    (Q : Ideal B) (n : ℕ) :
    Ideal.span {β} ≤ (Q.map (galRestrict A K L B σ)) ^ n ↔ Ideal.span {β} ≤ Q ^ n := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  rw [← smul_eq_map_galRestrict, ← smul_pow']
  rw [show ((Ideal.span {β} : Ideal B) ≤ σ • Q ^ n) ↔
        (σ⁻¹ • (Ideal.span {β} : Ideal B) ≤ σ⁻¹ • (σ • Q ^ n)) from
      Ideal.pointwise_smul_le_pointwise_smul_iff.symm,
    inv_smul_smul, smul_eq_map_galRestrict, hinv]

omit [IsFractionRing B L] [IsIntegrallyClosed A] [IsDomain B] [FiniteDimensional K L] in
private theorem count_factors_map_eq (β : B) (hβ : β ≠ 0) (σ : L ≃ₐ[K] L)
    (hinv : (Ideal.span {β}).map (galRestrict A K L B σ⁻¹) = Ideal.span {β})
    (Q : Ideal B) (hQ : Q.IsPrime) (hQ0 : Q ≠ ⊥) :
    (Associates.mk (Q.map (galRestrict A K L B σ))).count
        (Associates.mk (Ideal.span {β})).factors
      = (Associates.mk Q).count (Associates.mk (Ideal.span {β})).factors := by
  have hspan0 : (Ideal.span {β} : Ideal B) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hβ
  have hQmap : (Q.map (galRestrict A K L B σ)).IsPrime :=
    Ideal.map_isPrime_of_equiv (galRestrict A K L B σ) (I := Q)
  have hQmap0 : Q.map (galRestrict A K L B σ) ≠ ⊥ := fun h =>
    hQ0 (by rwa [Ideal.map_eq_bot_iff_of_injective (galRestrict A K L B σ).injective] at h)
  have char : ∀ (J : Ideal B), J.IsPrime → J ≠ ⊥ → ∀ m : ℕ,
      (m ≤ (Associates.mk J).count (Associates.mk (Ideal.span {β})).factors ↔
        Ideal.span {β} ≤ J ^ m) := by
    intro J hJ hJ0 m
    rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hspan0)
        (Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime hJ0 hJ).irreducible),
      ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]
  refine le_antisymm ?_ ?_
  · rw [char _ hQ hQ0]
    rw [← span_le_map_pow_iff A K L B β σ hinv]
    rw [← char _ hQmap hQmap0]
  · rw [char _ hQmap hQmap0]
    rw [span_le_map_pow_iff A K L B β σ hinv]
    rw [← char _ hQ hQ0]

omit [IsDomain B] in
private theorem count_factors_eq_of_liesOver (g : L ≃ₐ[K] L)
    (hg : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers g)
    (η : Bˣ) (β : B) (hβ : β ≠ 0) (hrel : (η : B) * galRestrict A K L B g β = β)
    (P : Ideal A) (Q Q' : Ideal B) [hQp : Q.IsPrime] [hQ'p : Q'.IsPrime]
    [hQP : Q.LiesOver P] [hQ'P : Q'.LiesOver P] (hQ0 : Q ≠ ⊥) :
    (Associates.mk Q').count (Associates.mk (Ideal.span {β})).factors
      = (Associates.mk Q).count (Associates.mk (Ideal.span {β})).factors := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  have : SMulCommClass (L ≃ₐ[K] L) A B :=
    ⟨fun σ a b => map_smul (galRestrict A K L B σ) a b⟩
  have : Algebra.IsInvariant A B (L ≃ₐ[K] L) := Algebra.isInvariant_of_isGalois A K L B
  have hmem : Q' ∈ MulAction.orbit (L ≃ₐ[K] L) Q := by
    rw [Algebra.IsInvariant.orbit_eq_primesOver A B (L ≃ₐ[K] L) P Q]
    exact ⟨hQ'p, hQ'P⟩
  obtain ⟨σ, hσ⟩ := hmem
  have hσ' : σ • Q = Q' := hσ
  rw [← hσ', smul_eq_map_galRestrict]
  exact count_factors_map_eq A K L B β hβ σ
    (map_galRestrict_span_eq A K L B g hg η β hrel σ⁻¹) Q hQp hQ0

end Dedekind
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

open UniqueFactorizationMonoid

section Count

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

private theorem le_count_iff_le_pow {J I : Ideal B} (hI : I ≠ 0) (hJp : J.IsPrime) (hJ0 : J ≠ ⊥)
    (m : ℕ) :
    m ≤ Multiset.count J (normalizedFactors I) ↔ I ≤ J ^ m := by
  rw [← Ideal.count_associates_factors_eq hI hJp hJ0,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
      (Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime hJ0 hJp).irreducible),
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

private theorem count_span_eq_zero {𝔓 : Ideal B} (h𝔓p : 𝔓.IsPrime) (h𝔓0 : 𝔓 ≠ ⊥)
    {d : B} (hd0 : d ≠ 0) (hd : d ∉ 𝔓) :
    Multiset.count 𝔓 (normalizedFactors (Ideal.span {d})) = 0 := by
  by_contra h
  have h1 : 1 ≤ Multiset.count 𝔓 (normalizedFactors (Ideal.span {d})) :=
    Nat.one_le_iff_ne_zero.mpr h
  rw [le_count_iff_le_pow (by simpa [Ideal.span_singleton_eq_bot] using hd0) h𝔓p h𝔓0,
    pow_one, Ideal.span_le, Set.singleton_subset_iff] at h1
  exact hd h1

private theorem count_span_mul (𝔓 : Ideal B)
    (x y : B) (hx : x ≠ 0) (hy : y ≠ 0) :
    Multiset.count 𝔓 (normalizedFactors (Ideal.span {x * y}))
      = Multiset.count 𝔓 (normalizedFactors (Ideal.span {x}))
        + Multiset.count 𝔓 (normalizedFactors (Ideal.span {y})) := by
  rw [← Ideal.span_singleton_mul_span_singleton,
    normalizedFactors_mul (by simpa [Ideal.span_singleton_eq_bot] using hx)
      (by simpa [Ideal.span_singleton_eq_bot] using hy),
    Multiset.count_add]

private theorem exists_mul_eq_pow_mul (𝔓 : Ideal B) [h𝔓p : 𝔓.IsPrime] (h𝔓0 : 𝔓 ≠ ⊥)
    (π : B) (hπ1 : π ∈ 𝔓) (hπ2 : π ∉ 𝔓 ^ 2)
    (β : B) (hβ0 : β ≠ 0) (a : ℕ)
    (ha : Ideal.span {β} ≤ 𝔓 ^ a) (ha' : ¬ Ideal.span {β} ≤ 𝔓 ^ (a + 1)) :
    ∃ d e : B, d ∉ 𝔓 ∧ e ∉ 𝔓 ∧ β * d = π ^ a * e := by
  classical
  have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ Ideal.zero_mem _)
  have h𝔓pr : Prime (𝔓 : Ideal B) := Ideal.prime_of_isPrime h𝔓0 h𝔓p
  have hspanβ0 : (Ideal.span {β} : Ideal B) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hβ0
  have hspanπ0 : (Ideal.span {π} : Ideal B) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hπ0
  have hπcount : Multiset.count 𝔓 (normalizedFactors (Ideal.span {π})) = 1 :=
    Ideal.count_normalizedFactors_eq (n := 1)
      (by simpa [pow_one, Ideal.span_le, Set.singleton_subset_iff] using hπ1)
      (by simpa [Ideal.span_le, Set.singleton_subset_iff] using hπ2)
  obtain ⟨D, hD⟩ : 𝔓 ∣ Ideal.span {π} :=
    Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ1))
  have hD0 : D ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hD
    exact hspanπ0 hD
  have hDcount : Multiset.count 𝔓 (normalizedFactors D) = 0 := by
    have h1 : Multiset.count 𝔓 (normalizedFactors (Ideal.span {π}))
        = Multiset.count 𝔓 (normalizedFactors (𝔓 : Ideal B))
          + Multiset.count 𝔓 (normalizedFactors D) := by
      rw [hD, normalizedFactors_mul h𝔓pr.ne_zero hD0, Multiset.count_add]
    have h2 : normalizedFactors (𝔓 : Ideal B) = {𝔓} := by
      rw [normalizedFactors_irreducible h𝔓pr.irreducible, normalize_eq]
    rw [hπcount, h2, Multiset.count_singleton, ite_eq_left rfl] at h1
    omega
  have hDnle : ¬ D ≤ 𝔓 := by
    intro hle
    have := (le_count_iff_le_pow hD0 h𝔓p h𝔓0 1).mpr (by simpa [pow_one] using hle)
    omega
  obtain ⟨d₁, hd₁D, hd₁𝔓⟩ := IsConcreteLE.not_le_iff_exists.mp hDnle
  obtain ⟨C, hC⟩ : 𝔓 ^ a ∣ Ideal.span {β} := Ideal.dvd_iff_le.mpr ha
  have hd₁0 : d₁ ≠ 0 := fun h => hd₁𝔓 (h ▸ Ideal.zero_mem _)
  have hd₁a𝔓 : d₁ ^ a ∉ 𝔓 := fun h => hd₁𝔓 (h𝔓p.mem_of_pow_mem a h)
  have hmem : β * d₁ ^ a ∈ Ideal.span {π ^ a} * C := by
    have h1 : β * d₁ ^ a ∈ Ideal.span {β} * D ^ a :=
      Ideal.mul_mem_mul (Ideal.mem_span_singleton_self β) (Ideal.pow_mem_pow hd₁D a)
    have h2 : Ideal.span {β} * D ^ a = Ideal.span {π ^ a} * C := by
      rw [hC, ← Ideal.span_singleton_pow, hD, mul_pow]
      ring
    rwa [h2] at h1
  obtain ⟨e, heC, hee⟩ := Ideal.mem_span_singleton_mul.mp hmem
  have hβd0 : β * d₁ ^ a ≠ 0 := mul_ne_zero hβ0 (pow_ne_zero _ hd₁0)
  have he0 : e ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hee
    exact hβd0 hee.symm
  have hβc : Multiset.count 𝔓 (normalizedFactors (Ideal.span {β})) = a :=
    Ideal.count_normalizedFactors_eq ha ha'
  have hπac : Multiset.count 𝔓 (normalizedFactors (Ideal.span {π ^ a})) = a := by
    rw [← Ideal.span_singleton_pow, normalizedFactors_pow, Multiset.count_nsmul, hπcount,
      mul_one]
  have hdc : Multiset.count 𝔓 (normalizedFactors (Ideal.span {d₁ ^ a})) = 0 :=
    count_span_eq_zero h𝔓p h𝔓0 (pow_ne_zero _ hd₁0) hd₁a𝔓
  have hcounts : Multiset.count 𝔓 (normalizedFactors (Ideal.span {e})) = 0 := by
    have h1 := count_span_mul 𝔓 β (d₁ ^ a) hβ0 (pow_ne_zero _ hd₁0)
    have h2 := count_span_mul 𝔓 (π ^ a) e (pow_ne_zero _ hπ0) he0
    rw [hβc, hdc] at h1
    rw [hπac] at h2
    rw [← hee, h2] at h1
    omega
  have he𝔓 : e ∉ 𝔓 := by
    intro hmem'
    have h1 : (1 : ℕ) ≤ Multiset.count 𝔓 (normalizedFactors (Ideal.span {e})) := by
      rw [le_count_iff_le_pow (by simpa [Ideal.span_singleton_eq_bot] using he0) h𝔓p h𝔓0,
        pow_one, Ideal.span_le, Set.singleton_subset_iff]
      exact hmem'
    omega
  exact ⟨d₁ ^ a, e, hd₁a𝔓, he𝔓, hee.symm⟩

end Count
open scoped ThaineReduce

section Residue

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsDedekindDomain B]
  [FiniteDimensional K L] [IsGalois K L]

omit [IsFractionRing B L] [IsIntegrallyClosed A] [FiniteDimensional K L] in
private theorem eta_mul_pow_sub_one_mem (𝔓 : Ideal B) [h𝔓p : 𝔓.IsPrime] (h𝔓0 : 𝔓 ≠ ⊥)
    (π : B) (hπ1 : π ∈ 𝔓) (hπ2 : π ∉ 𝔓 ^ 2)
    (g : L ≃ₐ[K] L) (hgtriv : ∀ x : B, galRestrict A K L B g x - x ∈ 𝔓)
    (u : B) (hu : galRestrict A K L B g π = π * u)
    (s : ℕ) (hs : u - (s : B) ∈ 𝔓)
    (η : Bˣ) (β : B) (hβ0 : β ≠ 0) (hrel : (η : B) * galRestrict A K L B g β = β)
    (a : ℕ) (ha : Ideal.span {β} ≤ 𝔓 ^ a) (ha' : ¬ Ideal.span {β} ≤ 𝔓 ^ (a + 1)) :
    (η : B) * (s : B) ^ a - 1 ∈ 𝔓 := by
  obtain ⟨d, e, hd𝔓, he𝔓, hde⟩ := exists_mul_eq_pow_mul 𝔓 h𝔓0 π hπ1 hπ2 β hβ0 a ha ha'
  have hπ0 : π ≠ 0 := fun h => hπ2 (h ▸ Ideal.zero_mem _)
  set σ := galRestrict A K L B g with hσdef
  have hE4 : e * σ d = (η : B) * u ^ a * σ e * d := by
    have h3 : σ β * σ d = (π * u) ^ a * σ e := by
      rw [← map_mul σ β d, hde, map_mul, map_pow, hu]
    have h6 : (η : B) * (σ β * σ d) * d = π ^ a * (e * σ d) := by
      rw [show (η : B) * (σ β * σ d) * d = (η : B) * σ β * d * σ d by ring, hrel, hde]
      ring
    have h7 : (η : B) * ((π * u) ^ a * σ e) * d
        = π ^ a * ((η : B) * u ^ a * σ e * d) := by
      rw [mul_pow]
      ring
    have h8 : π ^ a * (e * σ d) = π ^ a * ((η : B) * u ^ a * σ e * d) := by
      rw [← h6, h3, h7]
    exact mul_left_cancel₀ (pow_ne_zero _ hπ0) h8
  have hfd : Ideal.Quotient.mk 𝔓 (σ d) = Ideal.Quotient.mk 𝔓 d :=
    Ideal.Quotient.eq.mpr (hgtriv d)
  have hfe : Ideal.Quotient.mk 𝔓 (σ e) = Ideal.Quotient.mk 𝔓 e :=
    Ideal.Quotient.eq.mpr (hgtriv e)
  have hfu : Ideal.Quotient.mk 𝔓 u = Ideal.Quotient.mk 𝔓 (s : B) :=
    Ideal.Quotient.eq.mpr hs
  have hmain := congrArg (Ideal.Quotient.mk 𝔓) hE4
  simp only [map_mul, map_pow, hfd, hfe, hfu] at hmain
  have hfe0 : Ideal.Quotient.mk 𝔓 e ≠ 0 := fun h =>
    he𝔓 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hfd0 : Ideal.Quotient.mk 𝔓 d ≠ 0 := fun h =>
    hd𝔓 (Ideal.Quotient.eq_zero_iff_mem.mp h)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul, map_pow, sub_eq_zero]
  have hcancel : (Ideal.Quotient.mk 𝔓 e * Ideal.Quotient.mk 𝔓 d)
      * (Ideal.Quotient.mk 𝔓 (η : B) * Ideal.Quotient.mk 𝔓 (s : B) ^ a - 1) = 0 := by
    linear_combination -hmain
  rcases mul_eq_zero.mp hcancel with h | h
  · exact absurd h (mul_ne_zero hfe0 hfd0)
  · rw [sub_eq_zero] at h
    exact h

end Residue
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

variable {ℓ p : ℕ} [Fact ℓ.Prime]

private theorem pow_cast_eq_of_pow_eq (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) {m m' : ℕ} (h : s ^ m = s ^ m') :
    (m : ZMod p) = (m' : ZMod p) := by
  have hord : orderOf s = ℓ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]
  have hmod : m ≡ m' [MOD ℓ - 1] := by
    rwa [pow_eq_pow_iff_modEq, hord] at h
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.of_dvd hpℓ hmod

private theorem exists_pow_eq_gen (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (x : (ZMod ℓ)ˣ) : ∃ m : ℕ, s ^ m = x := by
  have hx := hs x
  rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx

private theorem cast_eq_zero_iff_exists_pow (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (x : (ZMod ℓ)ˣ) {m : ℕ} (hm : s ^ m = x) :
    (m : ZMod p) = 0 ↔ ∃ y : (ZMod ℓ)ˣ, y ^ p = x := by
  constructor
  · intro h0
    obtain ⟨k, rfl⟩ : p ∣ m := by
      rwa [ZMod.natCast_eq_zero_iff] at h0
    exact ⟨s ^ k, by rw [← pow_mul, mul_comm, hm]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨j, hj⟩ := exists_pow_eq_gen s hs y
    have hmj : s ^ m = s ^ (j * p) := by rw [pow_mul, hj]; exact hm
    have := pow_cast_eq_of_pow_eq s hs hpℓ hmj
    rw [this]
    push_cast
    simp

private theorem exists_t_of_not_pow (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (x : (ZMod ℓ)ˣ)
    (hx : ¬ ∃ y : (ZMod ℓ)ˣ, y ^ p = x) :
    ∃ t : ZMod p, t ≠ 0 ∧ ∀ m : ℕ, s ^ m = x → (m : ZMod p) = t := by
  obtain ⟨m₀, hm₀⟩ := exists_pow_eq_gen s hs x
  refine ⟨(m₀ : ZMod p), ?_, ?_⟩
  · intro h0
    exact hx ((cast_eq_zero_iff_exists_pow s hs hpℓ x hm₀).mp h0)
  · intro m hm
    exact pow_cast_eq_of_pow_eq s hs hpℓ (hm.trans hm₀.symm)

private theorem exists_units_pow_iff_exists_pow [Fact p.Prime] (x : (ZMod ℓ)ˣ) :
    (∃ y : (ZMod ℓ)ˣ, y ^ p = x) ↔ ∃ y : ZMod ℓ, y ^ p = (x : ZMod ℓ) := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨(y : ZMod ℓ), by push_cast; rfl⟩
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [zero_pow (Fact.out : p.Prime).ne_zero] at hy
      exact x.ne_zero hy.symm
    have hp1 : p - 1 + 1 = p := Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos
    have hinv1 : y * (y ^ (p - 1) * ((x⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ)) = 1 := by
      rw [← mul_assoc, mul_comm y (y ^ (p - 1)), ← pow_succ, hp1, hy]
      exact Units.mul_inv x
    refine ⟨⟨y, y ^ (p - 1) * ((x⁻¹ : (ZMod ℓ)ˣ) : ZMod ℓ), hinv1,
      by rw [mul_comm]; exact hinv1⟩, Units.ext ?_⟩
    change y ^ p = (x : ZMod ℓ)
    exact hy

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

open UniqueFactorizationMonoid

variable {A : Type*} [CommRing A] [IsDedekindDomain A]

private theorem count_nF_finsetProd_pow (T : Finset (Ideal A))
    (hT : ∀ P ∈ T, Prime P) (m : Ideal A → ℕ) (𝔓 : Ideal A) :
    Multiset.count 𝔓 (normalizedFactors (∏ P ∈ T, P ^ m P))
      = if 𝔓 ∈ T then m 𝔓 else 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [normalizedFactors_one, -Ideal.one_eq_top]
  | insert P₀ T hP₀T ih =>
    have hP₀ : Prime P₀ := hT P₀ (Finset.mem_insert_self _ _)
    have hT' : ∀ P ∈ T, Prime P := fun P hP => hT P (Finset.mem_insert_of_mem hP)
    have hprod0 : (∏ P ∈ T, P ^ m P) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun P hP => pow_ne_zero _ (hT' P hP).ne_zero
    rw [Finset.prod_insert hP₀T,
      normalizedFactors_mul (pow_ne_zero _ hP₀.ne_zero) hprod0, Multiset.count_add,
      hP₀.irreducible.normalizedFactors_pow, normalize_eq, Multiset.count_replicate,
      ih hT']
    by_cases h1 : 𝔓 = P₀
    · subst h1
      simp [hP₀T]
    · by_cases h2 : 𝔓 ∈ T <;> simp [Finset.mem_insert, h1, h2, Ne.symm h1]

private theorem eq_of_count_normalizedFactors_eq {I J : Ideal A} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ Q : Ideal A, Prime Q →
      Multiset.count Q (normalizedFactors I) = Multiset.count Q (normalizedFactors J)) :
    I = J := by
  have hmul : normalizedFactors I = normalizedFactors J := by
    ext Q
    by_cases hQ : Prime Q
    · exact h Q hQ
    · rw [Multiset.count_eq_zero_of_notMem
        (fun hmem => hQ (prime_of_normalized_factor Q hmem)),
        Multiset.count_eq_zero_of_notMem
        (fun hmem => hQ (prime_of_normalized_factor Q hmem))]
  have h1 : (normalizedFactors I).prod = I := associated_iff_eq.mp (prod_normalizedFactors hI)
  have h2 : (normalizedFactors J).prod = J := associated_iff_eq.mp (prod_normalizedFactors hJ)
  rw [← h1, ← h2, hmul]

private theorem exists_eq_finsetProd_mul_pow (p : ℕ) (I : Ideal A) (hI0 : I ≠ 0)
    (S : Finset (Ideal A)) (hS : ∀ 𝔔 ∈ S, Prime 𝔔) (av : Ideal A → ℕ)
    (hin : ∀ 𝔔 ∈ S, Multiset.count 𝔔 (normalizedFactors I) = av 𝔔)
    (hout : ∀ 𝔔 : Ideal A, Prime 𝔔 → 𝔔 ∉ S →
      p ∣ Multiset.count 𝔔 (normalizedFactors I)) :
    ∃ W : Ideal A, W ≠ 0 ∧ I = (∏ 𝔔 ∈ S, 𝔔 ^ av 𝔔) * W ^ p := by
  classical
  set T : Finset (Ideal A) := (normalizedFactors I).toFinset \ S with hT
  have hTprime : ∀ 𝔔 ∈ T, Prime 𝔔 := fun 𝔔 h𝔔 =>
    prime_of_normalized_factor 𝔔 (Multiset.mem_toFinset.mp (Finset.mem_sdiff.mp h𝔔).1)
  refine ⟨∏ 𝔔 ∈ T, 𝔔 ^ (Multiset.count 𝔔 (normalizedFactors I) / p), ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun 𝔔 h𝔔 => pow_ne_zero _ (hTprime 𝔔 h𝔔).ne_zero
  have hW0 : (∏ 𝔔 ∈ T, 𝔔 ^ (Multiset.count 𝔔 (normalizedFactors I) / p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun 𝔔 h𝔔 => pow_ne_zero _ (hTprime 𝔔 h𝔔).ne_zero
  have hS0 : (∏ 𝔔 ∈ S, 𝔔 ^ av 𝔔) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun 𝔔 h𝔔 => pow_ne_zero _ (hS 𝔔 h𝔔).ne_zero
  refine eq_of_count_normalizedFactors_eq hI0
    (mul_ne_zero hS0 (pow_ne_zero _ hW0)) fun Q hQ => ?_
  rw [normalizedFactors_mul hS0 (pow_ne_zero _ hW0), Multiset.count_add,
    normalizedFactors_pow, Multiset.count_nsmul,
    count_nF_finsetProd_pow S hS av Q, count_nF_finsetProd_pow T hTprime _ Q]
  by_cases hQS : Q ∈ S
  · have hQT : Q ∉ T := fun h => (Finset.mem_sdiff.mp h).2 hQS
    rw [ite_eq_left hQS, ite_eq_right hQT, mul_zero, add_zero]
    exact hin Q hQS
  · rw [ite_eq_right hQS, zero_add]
    by_cases hQT : Q ∈ T
    · rw [ite_eq_left hQT]
      exact (Nat.mul_div_cancel' (hout Q hQ hQS)).symm
    · rw [ite_eq_right hQT, mul_zero]
      have hQnf : Q ∉ (normalizedFactors I).toFinset := by
        intro hmem
        exact hQT (Finset.mem_sdiff.mpr ⟨hmem, hQS⟩)
      rw [Multiset.count_eq_zero_of_notMem (fun h => hQnf (Multiset.mem_toFinset.mpr h))]

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

open UniqueFactorizationMonoid

open scoped Pointwise

section Descent

variable (A K L B : Type*) [CommRing A] [CommRing B] [Field K] [Field L]
  [Algebra A K] [Algebra B L] [IsFractionRing A K] [IsFractionRing B L]
  [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsScalarTower A B L]
  [IsIntegrallyClosed A] [IsIntegralClosure B A L] [IsDomain B]
  [FiniteDimensional K L] [IsGalois K L]

omit [IsFractionRing B L] [IsIntegrallyClosed A] [FiniteDimensional K L] in
private theorem map_galRestrict_span_eq' (g : L ≃ₐ[K] L)
    (hg : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers g)
    (η : Bˣ) (β : B) (hrel : (η : B) * galRestrict A K L B g β = β) (σ : L ≃ₐ[K] L) :
    (Ideal.span {β}).map (galRestrict A K L B σ) = Ideal.span {β} := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  have hgβ : galRestrict A K L B g β = (η⁻¹ : Bˣ) * β :=
    (Units.mul_right_inj η).mp (by rw [hrel, ← mul_assoc, Units.mul_inv, one_mul])
  have hstab : ∀ τ : L ≃ₐ[K] L, τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) (Ideal.span {β}) := by
    have hgmem : g ∈ MulAction.stabilizer (L ≃ₐ[K] L) (Ideal.span {β}) := by
      rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_def]
      change (Ideal.span {β}).map (galRestrict A K L B g) = Ideal.span {β}
      rw [Ideal.map_span, Set.image_singleton, hgβ,
        Ideal.span_singleton_eq_span_singleton]
      exact associated_unit_mul_left β (η⁻¹ : Bˣ) (Units.isUnit _)
    intro τ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg τ)
    exact Subgroup.zpow_mem _ hgmem n
  have := hstab σ
  rw [MulAction.mem_stabilizer_iff, Ideal.pointwise_smul_def] at this
  exact this

omit [IsDomain B] in
private theorem exists_algebraMap_eq_prod_galRestrict (β : B) :
    ∃ α : A, algebraMap A B α = ∏ σ : L ≃ₐ[K] L, galRestrict A K L B σ β := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  have : SMulCommClass (L ≃ₐ[K] L) A B :=
    ⟨fun σ a b => map_smul (galRestrict A K L B σ) a b⟩
  have : Algebra.IsInvariant A B (L ≃ₐ[K] L) := Algebra.isInvariant_of_isGalois A K L B
  apply Algebra.IsInvariant.isInvariant (G := L ≃ₐ[K] L)
  intro τ
  change galRestrict A K L B τ (∏ σ : L ≃ₐ[K] L, galRestrict A K L B σ β) = _
  rw [map_prod]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun σ => by
    simp [map_mul, AlgEquiv.mul_apply]

omit [IsFractionRing B L] [IsIntegrallyClosed A] in
private theorem span_prod_galRestrict_eq (g : L ≃ₐ[K] L)
    (hg : ∀ x : L ≃ₐ[K] L, x ∈ Subgroup.zpowers g)
    (η : Bˣ) (β : B) (hrel : (η : B) * galRestrict A K L B g β = β) :
    Ideal.span {∏ σ : L ≃ₐ[K] L, galRestrict A K L B σ β}
      = Ideal.span {β} ^ Fintype.card (L ≃ₐ[K] L) := by
  rw [← Ideal.prod_span_singleton]
  have h : ∀ σ : L ≃ₐ[K] L,
      Ideal.span {galRestrict A K L B σ β} = Ideal.span {β} := by
    intro σ
    rw [← Set.image_singleton, ← Ideal.map_span]
    exact map_galRestrict_span_eq' A K L B g hg η β hrel σ
  rw [Finset.prod_congr rfl fun σ _ => h σ, Finset.prod_const, Finset.card_univ]

end Descent
open scoped ThaineReduce

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] [IsDedekindDomain A] [IsDedekindDomain B]
  [Algebra A B] [Algebra.IsIntegral A B] [Module.IsTorsionFree A B]

omit [Algebra.IsIntegral A B] in
private theorem count_nF_map_algebraMap'
    (𝔔 : Ideal A) (h𝔔0 : 𝔔 ≠ ⊥) [h𝔔p : 𝔔.IsPrime] (𝔓 : Ideal B) [h𝔓p : 𝔓.IsPrime]
    [h𝔓Q : 𝔓.LiesOver 𝔔] (I : Ideal A) (hI : I ≠ 0) :
    Multiset.count 𝔓 (normalizedFactors (I.map (algebraMap A B)))
      = 𝔔.ramificationIdx' 𝔓 * Multiset.count 𝔔 (normalizedFactors I) := by
  have hinj : Function.Injective (algebraMap A B) :=
    Module.isTorsionFree_iff_algebraMap_injective.mp inferInstance
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hinj
  have h𝔓0 : 𝔓 ≠ ⊥ := fun h =>
    h𝔔0 (by rw [h𝔓Q.over, h]; exact Ideal.comap_bot_of_injective _ hinj)
  have hv : Irreducible 𝔔 := (Ideal.prime_of_isPrime h𝔔0 h𝔔p).irreducible
  have hw : Irreducible 𝔓 := (Ideal.prime_of_isPrime h𝔓0 h𝔓p).irreducible
  have hmap : I.map (algebraMap A B) ≠ 0 := by
    rwa [Ne, Ideal.zero_eq_bot, Ideal.map_eq_bot_iff_of_injective hinj]
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hI hv hw h𝔓0
  rw [emultiplicity_eq_count_normalizedFactors hw hmap,
    emultiplicity_eq_count_normalizedFactors hv hI, normalize_eq, normalize_eq] at h
  exact_mod_cast h

omit [Algebra.IsIntegral A B] in
private theorem count_descended (α : A) (β : B) (hβ0 : β ≠ 0) (n : ℕ)
    (hα : Ideal.span {algebraMap A B α} = Ideal.span {β} ^ n)
    (𝔔 : Ideal A) (h𝔔0 : 𝔔 ≠ ⊥) [𝔔.IsPrime] (𝔓 : Ideal B) [𝔓.IsPrime] [𝔓.LiesOver 𝔔]
    (hα0 : α ≠ 0) :
    𝔔.ramificationIdx' 𝔓 * Multiset.count 𝔔 (normalizedFactors (Ideal.span {α}))
      = n * Multiset.count 𝔓 (normalizedFactors (Ideal.span {β})) := by
  have hspan : (Ideal.span {α}).map (algebraMap A B) = Ideal.span {β} ^ n := by
    rw [Ideal.map_span, Set.image_singleton, hα]
  have hspanα0 : (Ideal.span {α} : Ideal A) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hα0
  have hspanβ0 : (Ideal.span {β} : Ideal B) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hβ0
  rw [← count_nF_map_algebraMap' 𝔔 h𝔔0 𝔓 _ hspanα0, hspan, normalizedFactors_pow,
    Multiset.count_nsmul]

end Transport
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

section ZSide

variable {ℓ p : ℕ} [Fact ℓ.Prime]

private theorem exists_pow_eq_gen' (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (x : (ZMod ℓ)ˣ) : ∃ m : ℕ, s ^ m = x := by
  have hx := hs x
  rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx

private theorem orderOf_gen (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s) :
    orderOf s = ℓ - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]

private theorem cast_eq_neg_of_mul_pow_eq_one (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (xQ : (ZMod ℓ)ˣ) (tQ : ZMod p)
    (htQ : ∀ m : ℕ, s ^ m = xQ → (m : ZMod p) = tQ)
    (a : ℕ) (ha : xQ * s ^ a = 1) :
    (a : ZMod p) = -tQ := by
  obtain ⟨m, hm⟩ := exists_pow_eq_gen' s hs xQ
  have h1 : s ^ (m + a) = s ^ 0 := by
    rw [pow_add, hm, pow_zero, ha]
  have hmod : m + a ≡ 0 [MOD ℓ - 1] := by
    rwa [pow_eq_pow_iff_modEq, orderOf_gen s hs] at h1
  have hcast : ((m + a : ℕ) : ZMod p) = ((0 : ℕ) : ZMod p) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.ModEq.of_dvd hpℓ hmod
  have h2 := htQ m hm
  push_cast at hcast
  linear_combination hcast - h2

private theorem spec_of_eq_pow_mul_pow (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (x₀ : (ZMod ℓ)ˣ) (t₀ : ZMod p)
    (ht₀ : ∀ m : ℕ, s ^ m = x₀ → (m : ZMod p) = t₀)
    (n : ℕ) (w : (ZMod ℓ)ˣ) (xQ : (ZMod ℓ)ˣ) (hxQ : xQ = x₀ ^ n * w ^ p) :
    ∀ m : ℕ, s ^ m = xQ → (m : ZMod p) = (n : ZMod p) * t₀ := by
  intro m hm
  obtain ⟨m₀, hm₀⟩ := exists_pow_eq_gen' s hs x₀
  obtain ⟨j, hj⟩ := exists_pow_eq_gen' s hs w
  have h1 : s ^ m = s ^ (n * m₀ + p * j) := by
    rw [hm, hxQ, pow_add, pow_mul' s n m₀, pow_mul' s p j, hm₀, hj]
  have hmod : m ≡ n * m₀ + p * j [MOD ℓ - 1] := by
    rwa [pow_eq_pow_iff_modEq, orderOf_gen s hs] at h1
  have hcast : (m : ZMod p) = ((n * m₀ + p * j : ℕ) : ZMod p) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.ModEq.of_dvd hpℓ hmod
  have h₀ := ht₀ m₀ hm₀
  push_cast at hcast
  rw [hcast, h₀]
  simp

private theorem eq_one_or_neg_one_of_fix [Fact p.Prime] (s : (ZMod ℓ)ˣ)
    (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (x₀ : (ZMod ℓ)ˣ) (t₀ : ZMod p) (ht₀0 : t₀ ≠ 0)
    (ht₀ : ∀ m : ℕ, s ^ m = x₀ → (m : ZMod p) = t₀)
    (e : (ZMod p)ˣ) (v : (ZMod ℓ)ˣ)
    (hfix : x₀ = x₀ ^ (((e : ZMod p) ^ 2).val) * v ^ p) :
    e = 1 ∨ e = -1 := by
  have hspec := spec_of_eq_pow_mul_pow s hs hpℓ x₀ t₀ ht₀
    (((e : ZMod p) ^ 2).val) v x₀ hfix
  obtain ⟨m₀, hm₀⟩ := exists_pow_eq_gen' s hs x₀
  have h1 := ht₀ m₀ hm₀
  have h2 := hspec m₀ hm₀
  rw [h1, ZMod.natCast_val, ZMod.cast_id] at h2
  have hsq : ((e : ZMod p)) ^ 2 = 1 := by
    have h3 : (((e : ZMod p) ^ 2) - 1) * t₀ = 0 := by linear_combination -h2
    rcases mul_eq_zero.mp h3 with h | h
    · linear_combination h
    · exact absurd h ht₀0
  rcases mul_self_eq_one_iff.mp (by linear_combination hsq) with h | h
  · left
    exact Units.ext (by simpa using h)
  · right
    exact Units.ext (by simpa using h)

end ZSide
open scoped ThaineReduce

section Fiber

variable {p : ℕ} {A : Type*} [CommRing A]

private theorem mem_under_of_algebraMap_mem {B : Type*} [CommRing B] [Algebra A B]
    (𝔔 : Ideal A) (𝔓 : Ideal B) [h : 𝔓.LiesOver 𝔔] (x : A)
    (hx : algebraMap A B x ∈ 𝔓) : x ∈ 𝔔 := by
  rw [h.over]
  exact Ideal.mem_comap.mpr hx

end Fiber
open scoped ThaineReduce

section Fiber2

variable {p : ℕ} [Fact p.Prime] {A : Type*} [CommRing A]

private theorem comp_eq_mul (Δact : (ZMod p)ˣ →* (A ≃+* A)) (e f : (ZMod p)ˣ) :
    ((Δact e : A ≃+* A) : A →+* A).comp ((Δact f : A ≃+* A) : A →+* A)
      = ((Δact (e * f) : A ≃+* A) : A →+* A) := by
  ext x
  rw [map_mul Δact]
  rfl

private theorem filter_map_eq_pair (Δact : (ZMod p)ˣ →* (A ≃+* A)) (𝔏 : Ideal A)
    (hstab : ∀ e : (ZMod p)ˣ, 𝔏.map ((Δact e : A ≃+* A) : A →+* A) = 𝔏 → e = 1 ∨ e = -1)
    (hminus : Δact (-1) = 1) (d₀ : (ZMod p)ˣ) :
    Finset.univ.filter
        (fun d : (ZMod p)ˣ =>
          𝔏.map ((Δact d : A ≃+* A) : A →+* A) = 𝔏.map ((Δact d₀ : A ≃+* A) : A →+* A))
      = {d₀, -d₀} := by
  have hid : ∀ I : Ideal A, I.map ((Δact 1 : A ≃+* A) : A →+* A) = I := by
    intro I
    rw [map_one Δact]
    change I.map ((RingEquiv.refl A : A ≃+* A) : A →+* A) = I
    simp [Ideal.map_id]
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hmap
    have h3 : (𝔏.map ((Δact d : A ≃+* A) : A →+* A)).map ((Δact d⁻¹ : A ≃+* A) : A →+* A)
        = (𝔏.map ((Δact d₀ : A ≃+* A) : A →+* A)).map ((Δact d⁻¹ : A ≃+* A) : A →+* A) := by
      rw [hmap]
    rw [Ideal.map_map, Ideal.map_map, comp_eq_mul, comp_eq_mul, inv_mul_cancel, hid] at h3
    rcases hstab _ h3.symm with h | h
    · left
      have := inv_mul_eq_one.mp h
      exact this.symm ▸ rfl
    · right
      have h5 : d * (d⁻¹ * d₀) = d * (-1) := by rw [h]
      rw [← mul_assoc, mul_inv_cancel, one_mul, mul_neg, mul_one] at h5
      rw [h5, neg_neg]
  · rintro (rfl | rfl)
    · rfl
    · have heq : (Δact (-d₀) : A ≃+* A) = (Δact d₀ : A ≃+* A) := by
        have h5 : -d₀ = -1 * d₀ := by rw [neg_one_mul]
        rw [h5, map_mul, hminus, one_mul]
      rw [heq]

end Fiber2
open scoped ThaineReduce

section PairSum

variable {p : ℕ} [Fact p.Prime]

private theorem sum_pair_eq (hp2 : p ≠ 2) (t : ZMod p) (d₀ : (ZMod p)ˣ) :
    ∑ d ∈ ({d₀, -d₀} : Finset (ZMod p)ˣ), t * (((d : ZMod p)) ^ 2)⁻¹
      = 2 * t * (((d₀ : ZMod p)) ^ 2)⁻¹ := by
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h3
    have h4 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h4)
  have hne : d₀ ≠ -d₀ := by
    intro h
    have h1 : (d₀ : ZMod p) = -(d₀ : ZMod p) := by
      have h6 := congrArg Units.val h
      rwa [Units.val_neg] at h6
    have h2 : (2 : ZMod p) * (d₀ : ZMod p) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact h20 h
    · exact d₀.ne_zero h
  rw [Finset.sum_pair hne]
  have hsq : ((-d₀ : (ZMod p)ˣ) : ZMod p) ^ 2 = ((d₀ : ZMod p)) ^ 2 := by
    rw [Units.val_neg]
    ring
  rw [hsq]
  ring

end PairSum
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

open UniqueFactorizationMonoid

section GeomSum

variable {B : Type*} [CommRing B]

private theorem sub_one_mul_geom_sum (ζ : B) (n : ℕ) :
    (ζ - 1) * ∑ i ∈ Finset.range n, ζ ^ i = ζ ^ n - 1 := by
  rw [mul_comm]
  exact geom_sum_mul ζ n

private theorem geom_sum_sub_natCast_mem (𝔓 : Ideal B) (ζ : B) (hζ : ζ - 1 ∈ 𝔓) (n : ℕ) :
    (∑ i ∈ Finset.range n, ζ ^ i) - (n : B) ∈ 𝔓 := by
  have hterm : ∀ i : ℕ, ζ ^ i - 1 ∈ 𝔓 := by
    intro i
    obtain ⟨c, hc⟩ : (ζ - 1) ∣ (ζ ^ i - 1) := by
      have := sub_one_mul_geom_sum ζ i
      exact ⟨_, this.symm⟩
    rw [hc]
    exact Ideal.mul_mem_right _ _ hζ
  have hsplit : (∑ i ∈ Finset.range n, ζ ^ i) - (n : B)
      = ∑ i ∈ Finset.range n, (ζ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one]
  rw [hsplit]
  exact Ideal.sum_mem _ fun i _ => hterm i

private theorem pow_sub_one_mem (𝔓 : Ideal B) (ζ : B) (hζ : ζ - 1 ∈ 𝔓) (n : ℕ) :
    ζ ^ n - 1 ∈ 𝔓 := by
  rw [← sub_one_mul_geom_sum]
  exact Ideal.mul_mem_right _ _ hζ

end GeomSum
open scoped ThaineReduce

section CountChar

variable {B : Type*} [CommRing B] [IsDedekindDomain B]

private theorem le_count_iff_le_pow' {J I : Ideal B} (hI : I ≠ 0) (hJp : J.IsPrime) (hJ0 : J ≠ ⊥)
    (m : ℕ) :
    m ≤ Multiset.count J (normalizedFactors I) ↔ I ≤ J ^ m := by
  rw [← Ideal.count_associates_factors_eq hI hJp hJ0,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hI)
      (Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime hJ0 hJp).irreducible),
    ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le]

private theorem span_le_pow_count (𝔓 : Ideal B) [h𝔓p : 𝔓.IsPrime] (h𝔓0 : 𝔓 ≠ ⊥)
    (β : B) (hβ0 : β ≠ 0) :
    Ideal.span {β} ≤ 𝔓 ^ (Multiset.count 𝔓 (normalizedFactors (Ideal.span {β})))
      ∧ ¬ Ideal.span {β}
          ≤ 𝔓 ^ (Multiset.count 𝔓 (normalizedFactors (Ideal.span {β})) + 1) := by
  have hspan0 : (Ideal.span {β} : Ideal B) ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hβ0
  constructor
  · exact (le_count_iff_le_pow' hspan0 h𝔓p h𝔓0 _).mp le_rfl
  · intro h
    have := (le_count_iff_le_pow' hspan0 h𝔓p h𝔓0 _).mpr h
    omega

end CountChar
open scoped ThaineReduce

section UnitsLift

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type*} [CommRing A]

private theorem exists_units_mul_pow_eq_one (ψ : A →+* ZMod ℓ) (𝔔 : Ideal A)
    (hker : ∀ x ∈ 𝔔, ψ x = 0)
    (δ₀ : Aˣ) (s : (ZMod ℓ)ˣ) (a : ℕ)
    (hmem : (δ₀ : A) * (((s : ZMod ℓ).val : A)) ^ a - 1 ∈ 𝔔) :
    ∃ u : (ZMod ℓ)ˣ, (u : ZMod ℓ) = ψ (δ₀ : A) ∧ u * s ^ a = 1 := by
  have h0 := hker _ hmem
  rw [map_sub, map_mul, map_pow, map_one, map_natCast, sub_eq_zero,
    ZMod.natCast_val, ZMod.cast_id] at h0
  have hunit : IsUnit (ψ (δ₀ : A)) := δ₀.isUnit.map ψ
  refine ⟨hunit.unit, hunit.unit_spec, Units.ext ?_⟩
  push_cast
  rw [hunit.unit_spec]
  exact h0

end UnitsLift
open scoped ThaineReduce

section Tglobal

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]

private theorem cast_eq_zero_iff_exists_pow' (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (x : (ZMod ℓ)ˣ) {m : ℕ} (hm : s ^ m = x) :
    (m : ZMod p) = 0 ↔ ∃ y : (ZMod ℓ)ˣ, y ^ p = x := by
  constructor
  · intro h0
    obtain ⟨k, rfl⟩ : p ∣ m := by
      rwa [ZMod.natCast_eq_zero_iff] at h0
    exact ⟨s ^ k, by rw [← pow_mul, mul_comm, hm]⟩
  · rintro ⟨y, rfl⟩
    obtain ⟨j, hj⟩ : ∃ j : ℕ, s ^ j = y := by
      have hx := hs y
      rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx
    have hmj : s ^ m = s ^ (j * p) := by rw [pow_mul, hj]; exact hm
    have hord : orderOf s = ℓ - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]
    have hmod : m ≡ j * p [MOD ℓ - 1] := by
      rwa [pow_eq_pow_iff_modEq, hord] at hmj
    have hcast : (m : ZMod p) = ((j * p : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact Nat.ModEq.of_dvd hpℓ hmod
    rw [hcast]
    push_cast
    simp

private theorem exists_t0_spec (hp2 : p ≠ 2) (hpℓ : p ∣ ℓ - 1)
    (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (x₀ xδ w₂ : (ZMod ℓ)ˣ) (m : ℕ) (hrel : xδ ^ 2 = x₀ ^ m * w₂ ^ p)
    (hxδ : ¬ ∃ y : (ZMod ℓ)ˣ, y ^ p = xδ) :
    ∃ t₀ : ZMod p, t₀ ≠ 0 ∧ ∀ k : ℕ, s ^ k = x₀ → (k : ZMod p) = t₀ := by
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℕ, s ^ m₀ = x₀ := by
    have hx := hs x₀
    rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx
  refine ⟨(m₀ : ZMod p), ?_, ?_⟩
  · intro h0
    obtain ⟨y, hy⟩ := (cast_eq_zero_iff_exists_pow' s hs hpℓ x₀ hm₀).mp h0
    have hsq : xδ ^ 2 = (y ^ m * w₂) ^ p := by
      rw [mul_pow, ← pow_mul, pow_mul', hy]
      exact hrel
    obtain ⟨k, hk⟩ : ∃ k : ℕ, s ^ k = xδ := by
      have hx := hs xδ
      rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx
    obtain ⟨j, hj⟩ : ∃ j : ℕ, s ^ j = y ^ m * w₂ := by
      have hx := hs (y ^ m * w₂)
      rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx
    have h1 : s ^ (k * 2) = s ^ (j * p) := by
      rw [pow_mul, pow_mul, hk, hj]
      exact hsq
    have hord : orderOf s = ℓ - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]
    have hmod : k * 2 ≡ j * p [MOD ℓ - 1] := by
      rwa [pow_eq_pow_iff_modEq, hord] at h1
    have hcast : ((k * 2 : ℕ) : ZMod p) = ((j * p : ℕ) : ZMod p) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact Nat.ModEq.of_dvd hpℓ hmod
    have h20 : (2 : ZMod p) ≠ 0 := by
      intro h3
      have h4 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h3
      rw [ZMod.natCast_eq_zero_iff] at h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h4)
    have hk0 : (k : ZMod p) = 0 := by
      push_cast at hcast
      simp only [ZMod.natCast_self, mul_zero] at hcast
      rcases mul_eq_zero.mp hcast with h | h
      · exact h
      · exact absurd h h20
    exact hxδ ((cast_eq_zero_iff_exists_pow' s hs hpℓ xδ hk).mp hk0)
  · intro k hk
    have h1 : s ^ k = s ^ m₀ := by rw [hk, hm₀]
    have hord : orderOf s = ℓ - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
        ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]
    have hmod : k ≡ m₀ [MOD ℓ - 1] := by
      rwa [pow_eq_pow_iff_modEq, hord] at h1
    rw [ZMod.natCast_eq_natCast_iff]
    exact Nat.ModEq.of_dvd hpℓ hmod

end Tglobal
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

section E5

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {A : Type*} [CommRing A]

private theorem exists_pow_eq_gen'' (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (x : (ZMod ℓ)ˣ) : ∃ m : ℕ, s ^ m = x := by
  have hx := hs x
  rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx

private theorem orderOf_gen' (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s) :
    orderOf s = ℓ - 1 := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]

private theorem cast_eq_of_pow_eq_pow (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) {m m' : ℕ} (h : s ^ m = s ^ m') :
    (m : ZMod p) = (m' : ZMod p) := by
  have hmod : m ≡ m' [MOD ℓ - 1] := by
    rwa [pow_eq_pow_iff_modEq, orderOf_gen' s hs] at h
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.of_dvd hpℓ hmod

private theorem cast_eq_neg_inv_sq_mul (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (x₀ : (ZMod ℓ)ˣ) (t₀ : ZMod p)
    (ht₀ : ∀ k : ℕ, s ^ k = x₀ → (k : ZMod p) = t₀)
    (d₀ : (ZMod p)ˣ) (w₃ xQ : (ZMod ℓ)ˣ)
    (hxQ : xQ = x₀ ^ ((((d₀⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ 2).val * w₃ ^ p)
    (a : ℕ) (ha : xQ * s ^ a = 1) :
    (a : ZMod p) = -(((d₀ : ZMod p)) ^ 2)⁻¹ * t₀ := by
  set n₀ : ℕ := ((((d₀⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ 2).val with hn₀
  obtain ⟨m₀, hm₀⟩ := exists_pow_eq_gen'' s hs x₀
  obtain ⟨j, hj⟩ := exists_pow_eq_gen'' s hs w₃
  have hxQ' : s ^ (n₀ * m₀ + p * j) = xQ := by
    rw [hxQ, pow_add, pow_mul' s n₀ m₀, pow_mul' s p j, hm₀, hj]
  have h1 : s ^ (n₀ * m₀ + p * j + a) = s ^ 0 := by
    rw [pow_add, hxQ', pow_zero, ha]
  have hcast := cast_eq_of_pow_eq_pow s hs hpℓ h1
  have h₀ := ht₀ m₀ hm₀
  push_cast at hcast
  rw [ZMod.natCast_self] at hcast
  have hn₀cast : ((n₀ : ℕ) : ZMod p) = (((d₀ : ZMod p)) ^ 2)⁻¹ := by
    rw [hn₀, ZMod.natCast_val, ZMod.cast_id, ← inv_pow, Units.val_inv_eq_inv_val]
  rw [hn₀cast, h₀] at hcast
  linear_combination hcast

private theorem cast_eq_sum_pair_of_rep (hp2 : p ≠ 2)
    (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) (x₀ : (ZMod ℓ)ˣ) (t₀ : ZMod p)
    (ht₀ : ∀ k : ℕ, s ^ k = x₀ → (k : ZMod p) = t₀)
    (d₀ : (ZMod p)ˣ) (w₃ xQ : (ZMod ℓ)ˣ)
    (hxQ : xQ = x₀ ^ ((((d₀⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ 2).val * w₃ ^ p)
    (a : ℕ) (ha : xQ * s ^ a = 1) :
    (a : ZMod p) = ∑ d ∈ ({d₀, -d₀} : Finset (ZMod p)ˣ),
      (-(2 : ZMod p)⁻¹ * t₀) * (((d : ZMod p)) ^ 2)⁻¹ := by
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h3
    have h4 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h3
    rw [ZMod.natCast_eq_zero_iff] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h4)
  have hne : d₀ ≠ -d₀ := by
    intro h
    have h1 : (d₀ : ZMod p) = -(d₀ : ZMod p) := by
      have h6 := congrArg Units.val h
      rwa [Units.val_neg] at h6
    have h2 : (2 : ZMod p) * (d₀ : ZMod p) = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact h20 h
    · exact d₀.ne_zero h
  rw [Finset.sum_pair hne]
  have hsq : ((-d₀ : (ZMod p)ˣ) : ZMod p) ^ 2 = ((d₀ : ZMod p)) ^ 2 := by
    rw [Units.val_neg]
    ring
  rw [hsq, cast_eq_neg_inv_sq_mul s hs hpℓ x₀ t₀ ht₀ d₀ w₃ xQ hxQ a ha]
  linear_combination (t₀ * (((d₀ : ZMod p)) ^ 2)⁻¹) * inv_mul_cancel₀ h20

end E5
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

section G1

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]

private theorem delta_mul_pow_sub_one_mem (𝔔 : Ideal A) (𝔓 : Ideal B) [h𝔓Q : 𝔓.LiesOver 𝔔]
    (η : B) (δ₁ : A) (sval a : ℕ)
    (h1 : η * (sval : B) ^ a - 1 ∈ 𝔓)
    (h2 : η - algebraMap A B δ₁ ∈ 𝔓) :
    δ₁ * (sval : A) ^ a - 1 ∈ 𝔔 := by
  have hpush : algebraMap A B (δ₁ * (sval : A) ^ a - 1)
      = (η * (sval : B) ^ a - 1) - (η - algebraMap A B δ₁) * (sval : B) ^ a := by
    push_cast
    ring
  have hmem : algebraMap A B (δ₁ * (sval : A) ^ a - 1) ∈ 𝔓 := by
    rw [hpush]
    exact Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ h2)
  rw [h𝔓Q.over]
  exact Ideal.mem_comap.mpr hmem

end G1
open scoped ThaineReduce

section G2

variable {ℓ : ℕ} [Fact ℓ.Prime]
variable {A : Type*} [CommRing A] [IsDedekindDomain A] [Infinite A]
  [Module.Free ℤ A] [Module.Finite ℤ A]

omit [Module.Free ℤ A] [Module.Finite ℤ A] in
private theorem exists_residue_equiv (𝔏 : Ideal A) (hcard : Ideal.absNorm 𝔏 = ℓ) :
    Nonempty ((A ⧸ 𝔏) ≃+* ZMod ℓ) := by
  have hnat : Nat.card (A ⧸ 𝔏) = ℓ := by
    rw [← hcard, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfin : Finite (A ⧸ 𝔏) := by
    refine Nat.finite_of_card_ne_zero ?_
    rw [hnat]
    exact (Fact.out : ℓ.Prime).ne_zero
  have : Fintype (A ⧸ 𝔏) := Fintype.ofFinite _
  have hcard' : Fintype.card (A ⧸ 𝔏) = ℓ := by
    rw [← Nat.card_eq_fintype_card, hnat]
  exact ⟨(ZMod.ringEquivOfPrime _ (Fact.out : ℓ.Prime) hcard').symm⟩

end G2
open scoped ThaineReduce

section G3

variable {ℓ p : ℕ} [Fact ℓ.Prime] [Fact p.Prime]
variable {A : Type*} [CommRing A]

private theorem exists_pow_eq_gen₃ (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (x : (ZMod ℓ)ˣ) : ∃ m : ℕ, s ^ m = x := by
  have hx := hs x
  rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hx

private theorem cast_eq_of_pow_eq_pow₃ (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1) {m m' : ℕ} (h : s ^ m = s ^ m') :
    (m : ZMod p) = (m' : ZMod p) := by
  have hord : orderOf s = ℓ - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, Nat.card_eq_fintype_card,
      ZMod.card_units_eq_totient, Nat.totient_prime (Fact.out : ℓ.Prime)]
  have hmod : m ≡ m' [MOD ℓ - 1] := by
    rwa [pow_eq_pow_iff_modEq, hord] at h
  rw [ZMod.natCast_eq_natCast_iff]
  exact Nat.ModEq.of_dvd hpℓ hmod

private theorem fix_eq_pm_one (s : (ZMod ℓ)ˣ) (hs : ∀ x, x ∈ Subgroup.zpowers s)
    (hpℓ : p ∣ ℓ - 1)
    (ψ : A →+* ZMod ℓ) (𝔏 : Ideal A) (hker : ∀ x ∈ 𝔏, ψ x = 0)
    (δ₁ : Aˣ) (x₀ : (ZMod ℓ)ˣ) (hx₀ : (x₀ : ZMod ℓ) = ψ (δ₁ : A))
    (t₀ : ZMod p) (ht₀0 : t₀ ≠ 0)
    (ht₀ : ∀ k : ℕ, s ^ k = x₀ → (k : ZMod p) = t₀)
    (e : (ZMod p)ˣ) (E : A ≃+* A)
    (hE : ∀ x : A, E x - x ∈ 𝔏)
    (v : Aˣ) (heig : E (δ₁ : A) = (δ₁ : A) ^ (((e : ZMod p) ^ 2).val) * (v : A) ^ p) :
    e = 1 ∨ e = -1 := by
  have h1 : ψ (E (δ₁ : A)) = ψ (δ₁ : A) := by
    have := hker _ (hE (δ₁ : A))
    rw [map_sub, sub_eq_zero] at this
    exact this
  have h2 : ψ (δ₁ : A) = ψ (δ₁ : A) ^ (((e : ZMod p) ^ 2).val) * ψ (v : A) ^ p := by
    conv_lhs => rw [← h1]
    rw [heig, map_mul, map_pow, map_pow]
  have hvunit : IsUnit (ψ (v : A)) := v.isUnit.map ψ
  have hfix : x₀ = x₀ ^ (((e : ZMod p) ^ 2).val) * hvunit.unit ^ p := by
    refine Units.ext ?_
    push_cast
    rw [hx₀, hvunit.unit_spec]
    exact h2
  have hspec : ∀ m : ℕ, s ^ m = x₀ →
      (m : ZMod p) = ((((e : ZMod p) ^ 2).val : ℕ) : ZMod p) * t₀ := by
    intro m hm
    obtain ⟨m₀, hm₀⟩ := exists_pow_eq_gen₃ s hs x₀
    obtain ⟨j, hj⟩ := exists_pow_eq_gen₃ s hs hvunit.unit
    have h3 : s ^ m = s ^ ((((e : ZMod p) ^ 2).val) * m₀ + p * j) := by
      rw [hm, hfix, pow_add, pow_mul' s _ m₀, pow_mul' s p j, hm₀, hj]
    have hcast := cast_eq_of_pow_eq_pow₃ s hs hpℓ h3
    have h₀ := ht₀ m₀ hm₀
    push_cast at hcast
    rw [ZMod.natCast_self] at hcast
    rw [hcast, h₀]
    ring
  obtain ⟨m₀, hm₀⟩ := exists_pow_eq_gen₃ s hs x₀
  have h4 := ht₀ m₀ hm₀
  have h5 := hspec m₀ hm₀
  rw [h4, ZMod.natCast_val, ZMod.cast_id] at h5
  have hsq : ((e : ZMod p)) ^ 2 = 1 := by
    have h6 : (((e : ZMod p) ^ 2) - 1) * t₀ = 0 := by linear_combination -h5
    rcases mul_eq_zero.mp h6 with h | h
    · linear_combination h
    · exact absurd h ht₀0
  rcases mul_self_eq_one_iff.mp (by linear_combination hsq) with h | h
  · left
    exact Units.ext (by simpa using h)
  · right
    exact Units.ext (by simpa using h)

end G3
open scoped ThaineReduce

section G4

variable {ℓ p : ℕ} [Fact ℓ.Prime]
variable {A : Type*} [CommRing A]

private theorem not_exists_units_pow (𝔏 : Ideal A) (ψiso : (A ⧸ 𝔏) ≃+* ZMod ℓ) (δ : A)
    (hδ : Ideal.Quotient.mk 𝔏 δ ∉ {x : A ⧸ 𝔏 | ∃ y, y ^ p = x})
    (xδ : (ZMod ℓ)ˣ) (hxδval : (xδ : ZMod ℓ) = ψiso (Ideal.Quotient.mk 𝔏 δ)) :
    ¬ ∃ y : (ZMod ℓ)ˣ, y ^ p = xδ := by
  rintro ⟨y, hy⟩
  apply hδ
  refine ⟨ψiso.symm (y : ZMod ℓ), ?_⟩
  have hyval : ((y : ZMod ℓ)) ^ p = (xδ : ZMod ℓ) := by
    have := congrArg Units.val hy
    push_cast at this
    exact this
  rw [← map_pow, hyval, hxδval, RingEquiv.symm_apply_apply]

end G4
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineDesk

section H90poly

open Finset groupCohomology

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

private noncomputable def hchain (g : L ≃ₐ[K] L) (x : Lˣ) (k : ℕ) : Lˣ :=
  ∏ i ∈ Finset.range k, Units.map ((g ^ i : L ≃ₐ[K] L) : L →* L) x

omit [FiniteDimensional K L] in
private lemma hchain_add (g : L ≃ₐ[K] L) (x : Lˣ) (a b : ℕ) :
    hchain g x (a + b)
      = hchain g x a * Units.map ((g ^ a : L ≃ₐ[K] L) : L →* L) (hchain g x b) := by
  rw [hchain, hchain, hchain, Finset.prod_range_add, map_prod]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  have hcomp : ((g ^ (a + i) : L ≃ₐ[K] L) : L →* L)
      = ((g ^ a : L ≃ₐ[K] L) : L →* L).comp ((g ^ i : L ≃ₐ[K] L) : L →* L) := by
    ext z
    simp [pow_add, AlgEquiv.mul_apply]
  rw [hcomp]
  rfl

omit [FiniteDimensional K L] in
private lemma hchain_one (g : L ≃ₐ[K] L) (x : Lˣ) : hchain g x 1 = x := by
  rw [hchain, Finset.prod_range_one]
  refine Units.ext ?_
  simp

private lemma hchain_orderOf [IsGalois K L] (g : L ≃ₐ[K] L)
    (hg : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers g) (x : Lˣ)
    (hx : Algebra.norm K (x : L) = 1) :
    hchain g x (orderOf g) = 1 := by
  have hord : orderOf g = Fintype.card (L ≃ₐ[K] L) :=
    (orderOf_eq_card_of_forall_mem_zpowers hg).trans Nat.card_eq_fintype_card
  refine Units.ext ?_
  have hval : ((hchain g x (orderOf g) : Lˣ) : L)
      = ∏ i ∈ Finset.range (orderOf g), (g ^ i) (x : L) := by
    rw [hchain]
    push_cast
    rfl
  rw [hval]
  have hre : ∏ i ∈ Finset.range (orderOf g), (g ^ i) (x : L)
      = ∏ σ : L ≃ₐ[K] L, σ (x : L) := by
    refine Finset.prod_nbij (fun i => g ^ i) (fun i _ => Finset.mem_univ _) ?_ ?_
      (fun i _ => rfl)
    · intro i hi j hj hij
      exact pow_injOn_Iio_orderOf (by simpa using Finset.mem_range.mp hi)
        (by simpa using Finset.mem_range.mp hj) hij
    · intro τ _
      obtain ⟨j, hj⟩ : ∃ j : ℕ, g ^ j = τ := by
        have hτ := hg τ
        rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hτ
      refine ⟨j % orderOf g, ?_, ?_⟩
      · simp only [Finset.coe_range, Set.mem_Iio]
        exact Nat.mod_lt _ (by rw [hord]; exact Fintype.card_pos)
      · change g ^ (j % orderOf g) = τ
        rw [pow_mod_orderOf, hj]
  rw [hre, ← Algebra.norm_eq_prod_automorphisms, hx, map_one]
  exact Units.val_one.symm

private lemma hchain_orderOf_mul [IsGalois K L] (g : L ≃ₐ[K] L)
    (hg : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers g) (x : Lˣ)
    (hx : Algebra.norm K (x : L) = 1) (q : ℕ) :
    hchain g x (orderOf g * q) = 1 := by
  induction q with
  | zero => rw [mul_zero, hchain, Finset.range_zero, Finset.prod_empty]
  | succ q ih =>
    rw [mul_add, mul_one, hchain_add, ih, one_mul, pow_mul, pow_orderOf_eq_one,
      one_pow, hchain_orderOf g hg x hx]
    refine Units.ext ?_
    simp

private lemma hchain_eq_of_pow_eq [IsGalois K L] (g : L ≃ₐ[K] L)
    (hg : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers g) (x : Lˣ)
    (hx : Algebra.norm K (x : L) = 1) {j k : ℕ} (h : g ^ j = g ^ k) :
    hchain g x j = hchain g x k := by
  have hmod : j % orderOf g = k % orderOf g := pow_eq_pow_iff_modEq.mp h
  have hred : ∀ m : ℕ, hchain g x m = hchain g x (m % orderOf g) := by
    intro m
    conv_lhs => rw [← Nat.div_add_mod m (orderOf g)]
    rw [hchain_add, hchain_orderOf_mul g hg x hx, one_mul, pow_mul,
      pow_orderOf_eq_one, one_pow]
    refine Units.ext ?_
    simp
  rw [hred j, hred k, hmod]

open scoped Classical in
private theorem exists_div_of_norm_eq_one' [IsGalois K L] (g : L ≃ₐ[K] L)
    (hg : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers g) (x : Lˣ)
    (hx : Algebra.norm K (x : L) = 1) :
    ∃ y : Lˣ, (y : L) / (g (y : L)) = (x : L) := by
  have hex : ∀ τ : L ≃ₐ[K] L, ∃ j : ℕ, g ^ j = τ := by
    intro τ
    have hτ := hg τ
    rwa [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hτ
  set f : (L ≃ₐ[K] L) → Lˣ := fun τ => hchain g x (Nat.find (hex τ)) with hfdef
  have hfval : ∀ (τ : L ≃ₐ[K] L) (j : ℕ), g ^ j = τ → f τ = hchain g x j := by
    intro τ j hj
    exact hchain_eq_of_pow_eq g hg x hx (by rw [Nat.find_spec (hex τ), hj])
  have hcoc : IsMulCocycle₁ f := by
    intro σ τ
    obtain ⟨a, ha⟩ := hex σ
    obtain ⟨b, hb⟩ := hex τ
    have hστ : g ^ (a + b) = σ * τ := by rw [pow_add, ha, hb]
    rw [hfval (σ * τ) (a + b) hστ, hfval σ a ha, hfval τ b hb, hchain_add]
    rw [mul_comm]
    congr 1
    rw [← ha]
    rfl
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcoc
  have hβg := hβ g
  have hfg : f g = x := by
    rw [hfval g 1 (pow_one g), hchain_one]
  rw [hfg] at hβg
  refine ⟨β⁻¹, ?_⟩
  have h1 : (Units.map (g : L →* L) β : Lˣ) / β = x := by
    rwa [AlgEquiv.smul_units_def] at hβg
  have h2 : (g ((β : Lˣ) : L)) / ((β : Lˣ) : L) = (x : L) := by
    have h3 := congrArg Units.val h1
    push_cast at h3
    exact h3
  rw [Units.val_inv_eq_inv_val, map_inv₀, inv_div_inv]
  exact h2

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra A L] [Algebra A K]
variable [Algebra B L] [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing A K]
variable [IsDomain A] [IsIntegralClosure B A L]

open scoped nonZeroDivisors

private theorem exists_mul_galRestrict_of_norm_eq_one' [IsGalois K L] (g : L ≃ₐ[K] L)
    (hg : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers g) {η : B}
    (hη : Algebra.norm K (algebraMap B L η) = 1) :
    ∃ ε : B, ε ≠ 0 ∧ η * galRestrict A K L B g ε = ε := by
  have : Module.IsTorsionFree A L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq A K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective A K)
  have : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L :=
    IsIntegralClosure.isLocalization A K L B
  let η' : Lˣ := Units.mk0 (algebraMap B L η) (fun h => by simp [h] at hη)
  obtain ⟨ε, hε0⟩ := exists_div_of_norm_eq_one' g hg η' hη
  have hε : (ε : L) / g (ε : L) = algebraMap B L η := hε0
  obtain ⟨a, b, h⟩ := IsLocalization.exists_mk'_eq (Algebra.algebraMapSubmonoid B A⁰) ε.1
  obtain ⟨t, ht, ht'⟩ := b.prop
  have hsm : t • IsLocalization.mk' L a b = algebraMap _ _ a := by
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A B L, ht', IsLocalization.mk'_spec']
  refine ⟨a, ?_, ?_⟩
  · rintro rfl
    simp only [IsLocalization.mk'_zero, _root_.map_zero, div_zero, ← h] at hε
    rw [← hε, Algebra.norm_zero] at hη
    exact zero_ne_one hη
  · replace hε := hε.symm
    rw [← h, eq_div_iff_mul_eq] at hε
    · replace hε := congr_arg (t • ·) hε
      beta_reduce at hε
      rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def t, ← g.toAlgHom_apply,
        ← AlgHom.map_smul_of_tower, hsm] at hε
      apply IsIntegralClosure.algebraMap_injective B A L
      rw [map_mul, ← hε]
      congr 1
      exact algebraMap_galRestrictHom_apply A K L B g a
    · intro e
      rw [(_root_.map_eq_zero _).mp e, zero_div] at hε
      rw [hε, Algebra.norm_zero] at hη
      exact zero_ne_one hη

end H90poly
open scoped ThaineReduce

end ThaineDesk
open scoped ThaineReduce

namespace ThaineAssembly

open Polynomial in
private theorem reduce_lift (p : ℕ) [hp : Fact p.Prime] (hp5 : 5 ≤ p) (ℓ : ℕ) [hℓ : Fact ℓ.Prime]
    (hℓp : ℓ ≠ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus ≃+* 𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hpl : p ∣ ℓ - 1)
    (L : Type*) [Field L] [NumberField L] [Algebra Kplus L] [IsCyclotomicExtension {ℓ} Kplus L]
    (hirr : Irreducible (cyclotomic ℓ Kplus)) :
    ∃ (δ₁ w : (𝓞 Kplus)ˣ) (η : (𝓞 L)ˣ),
      δ ^ 2 = δ₁ * w ^ p ∧
      (∀ e : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
        Units.mapEquiv (Δact e).toMulEquiv δ₁ = δ₁ ^ ((e : ZMod p) ^ 2).val * v ^ p) ∧
      Algebra.norm Kplus (algebraMap (𝓞 L) L (η : 𝓞 L)) = 1 ∧
      ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
        ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsMaximal], 𝔓.LiesOver 𝔔 →
          (η : 𝓞 L) - algebraMap (𝓞 Kplus) (𝓞 L) (δ₁ : 𝓞 Kplus) ∈ 𝔓 := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero ℓ := ⟨hℓ.out.ne_zero⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨m, w, δ₀, n, a, hrel, hδ₀, ha⟩ := ThaineReduce.reduce_out p hp2 Kplus hKplus Δact hΔact δ
    hδeig (Stickelberger.finrank_unitsOmegaEigenspace_two p hp5)
    (fun ζ hζ c₂ hc =>
      Stickelberger.omegaIdempotent_two_cycloUnitTwo_ne_zero p hp5 ζ hζ c₂ hc)
  have hz := IsCyclotomicExtension.zeta_spec p ℚ (CyclotomicField p ℚ)
  have hzne : IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ≠ 0 :=
    hz.ne_zero hp.out.ne_zero
  obtain ⟨c, hc⟩ := hpl
  have hℓ1 : ℓ = p * c + 1 := by have := hℓ.out.one_le; omega
  have hℓodd : Odd ℓ := by
    refine hℓ.out.odd_of_ne_two ?_
    rintro rfl
    have h1 : p * c = 1 := by omega
    have := Nat.eq_one_of_mul_eq_one_right h1
    omega
  have hzℓ : ∀ k : ℕ, (IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k) ^ ℓ =
      IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k := fun k => by
    rw [← pow_mul, hℓ1, Nat.mul_add, mul_one, pow_add, Nat.mul_left_comm, pow_mul,
      hz.pow_eq_one, one_pow, one_mul]
  have hr : ∀ k : ℕ, -(IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k) ≠ 0 :=
    fun k => neg_ne_zero.mpr (pow_ne_zero _ hzne)
  have hrℓ : ∀ k : ℕ, (-(IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k)) ^ ℓ =
      -(IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k) := fun k => by
    rw [neg_pow, hℓodd.neg_one_pow, hzℓ, neg_one_mul]
  have hrne : ∀ k : ℕ, -(IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k) ≠ 1 := by
    intro k h
    have h1 : IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k = -1 :=
      neg_eq_iff_eq_neg.mp h
    have h2 : IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ (k * 2) = 1 := by
      rw [pow_mul, h1, neg_one_sq]
    have h3 : p ∣ k := by
      have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
      exact hcop.dvd_of_dvd_mul_right ((hz.pow_eq_one_iff_dvd _).mp h2)
    have h4 : IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k = 1 :=
      (hz.pow_eq_one_iff_dvd _).mpr h3
    rw [h4] at h1
    have h5 : (2 : CyclotomicField p ℚ) = 0 := by linear_combination h1
    exact two_ne_zero h5
  have hrinvne : ∀ k : ℕ, (-(IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ k))⁻¹ ≠ 1 :=
    fun k h => hrne k (inv_eq_one.mp h)
  have had : ∀ d : (ZMod p)ˣ, algebraMap Kplus (CyclotomicField p ℚ) ((-a d : 𝓞 Kplus) : Kplus) =
      -(IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val) +
        (-(IsCyclotomicExtension.zeta p ℚ (CyclotomicField p ℚ) ^ (d : ZMod p).val))⁻¹ := by
    intro d
    rw [RingOfIntegers.coe_eq_algebraMap, map_neg, map_neg,
      ← IsScalarTower.algebraMap_apply (𝓞 Kplus) Kplus (CyclotomicField p ℚ), ha d, neg_add,
      inv_neg]
  have hNd : ∀ d : (ZMod p)ˣ, Algebra.norm Kplus (aeval (ThaineAux.zetaInt Kplus L ℓ : L)
      (ThaineLift.Pd' ((-a d : 𝓞 Kplus) : Kplus))) = 1 := fun d =>
    ThaineLift.norm_aeval_Pd' (L := L) (CyclotomicField p ℚ) hℓ.out hirr
      (IsCyclotomicExtension.zeta_spec ℓ Kplus L) ((-a d : 𝓞 Kplus) : Kplus)
      (hr _) (hrℓ _) (hrne _) (hrinvne _) (had d)
  have hζℓ𝔓 : ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
      ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsMaximal], 𝔓.LiesOver 𝔔 →
        ThaineAux.zetaInt Kplus L ℓ - 1 ∈ 𝔓 := by
    intro 𝔔 _ hℓ𝔔 𝔓 _ h𝔓
    have := h𝔓
    exact (ThaineAux.ram_package ℓ 𝔔 𝔓 hℓ𝔔
      (ThaineAux.natCast_not_mem_sq_of_algebra (F := Kplus) ℓ p hℓp (CyclotomicField p ℚ) 𝔔
        hℓ𝔔)).2.2.2.2.2.1
  have hδ₁ : algebraMap (𝓞 Kplus) (𝓞 L) ((δ₀ ^ m : (𝓞 Kplus)ˣ) : 𝓞 Kplus) =
      ∏ d, (2 - algebraMap (𝓞 Kplus) (𝓞 L) (-a d)) ^ (n d * m) := by
    rw [Units.val_pow_eq_pow_val, hδ₀, ← Finset.prod_pow, map_prod]
    refine Finset.prod_congr rfl (fun d _ => ?_)
    rw [← pow_mul, map_pow, map_add, map_ofNat (algebraMap (𝓞 Kplus) (𝓞 L)) 2, map_neg,
      sub_neg_eq_add]
  have hδ₁' : ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
      ∀ (𝔓 : Ideal (𝓞 L)) [𝔓.IsMaximal], 𝔓.LiesOver 𝔔 →
        algebraMap (𝓞 Kplus) (𝓞 L) ((δ₀ ^ m : (𝓞 Kplus)ˣ) : 𝓞 Kplus) -
          ∏ d, (2 - algebraMap (𝓞 Kplus) (𝓞 L) (-a d)) ^ (n d * m) ∈ 𝔓 := by
    intro 𝔔 _ _ 𝔓 _ _
    rw [hδ₁, sub_self]
    exact zero_mem 𝔓
  obtain ⟨η, hN, hres⟩ := ThaineLift.lift_block (p := p) (ℓ := ℓ) (ThaineAux.zetaInt Kplus L ℓ)
    hζℓ𝔓 (fun d => -a d) hNd (fun d => n d * m) (δ₀ ^ m) hδ₁'
  exact ⟨δ₀ ^ m, w, η, hrel, fun e => ThaineReduce.mapEquiv_pow_eigen p Δact δ δ₀ w m hδeig hrel e,
    hN, hres⟩

private theorem engine_out (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [IsTotallyReal Kplus]
    [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (𝔏 : Ideal (𝓞 Kplus)) (h𝔏max : 𝔏.IsMaximal)
    (h𝔏deg : Ideal.absNorm 𝔏 = ℓ)
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hδ𝔏 : (Ideal.Quotient.mk 𝔏 (δ : 𝓞 Kplus))
      ∉ {x : 𝓞 Kplus ⧸ 𝔏 | ∃ y, y ^ p = x}) :
    ∃ (a₀ : 𝓞 Kplus) (W : Ideal (𝓞 Kplus)) (av : Ideal (𝓞 Kplus) → ℕ) (t : ZMod p),
      a₀ ≠ 0 ∧ t ≠ 0 ∧
      Ideal.span {a₀} =
        (∏ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)}) (𝓞 Kplus), 𝔔 ^ av 𝔔) *
          W ^ p ∧
      ∀ 𝔔 ∈ IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)}) (𝓞 Kplus),
        (av 𝔔 : ZMod p) =
          ∑ d ∈ Finset.univ.filter (fun d : (ZMod p)ˣ => 𝔏.map (Δact d) = 𝔔),
            t * ((d : ZMod p) ^ 2)⁻¹ := by
  classical
  have := h𝔏max
  have hℓF : Fact ℓ.Prime := ⟨hℓ⟩
  have hpp := (Fact.out : p.Prime)
  have hp2 : p ≠ 2 := by omega
  have hℓ𝔏 : (ℓ : 𝓞 Kplus) ∈ 𝔏 := by
    have := Ideal.absNorm_mem 𝔏
    rw [h𝔏deg] at this
    exact_mod_cast this
  have hpℓ : p ∣ ℓ - 1 :=
    ThaineAux.dvd_pred_of_not_pow Kplus 𝔏 hℓ h𝔏deg (Fact.out : p.Prime) _ hδ𝔏
  have hunram : ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
      (ℓ : 𝓞 Kplus) ∉ 𝔔 ^ 2 :=
    fun 𝔔 _ h =>
      ThaineAux.natCast_not_mem_sq_of_algebra (F := Kplus) ℓ p hℓp (CyclotomicField p ℚ) 𝔔 h
  have hℓ𝔏2 : (ℓ : 𝓞 Kplus) ∉ 𝔏 ^ 2 := hunram 𝔏 hℓ𝔏
  have hgal0 : IsGalois Kplus (CyclotomicField ℓ Kplus) :=
    IsCyclotomicExtension.isGalois {ℓ} Kplus _
  obtain ⟨𝔓₁, h𝔓₁max, h𝔓₁Q⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (CyclotomicField ℓ Kplus)) 𝔏
  have := h𝔓₁max
  have := h𝔓₁Q
  obtain ⟨hfinrank, he𝔏, hf𝔏, hprimes𝔏, hmap𝔏, hζ𝔓₁, hζ𝔓₁2⟩ :=
    ThaineAux.ram_package (F := Kplus) (L := (CyclotomicField ℓ Kplus)) (ℓ := ℓ) 𝔏 𝔓₁ hℓ𝔏 hℓ𝔏2
  have hirr : Irreducible (Polynomial.cyclotomic ℓ Kplus) :=
    ThaineAux.irreducible_cyclotomic Kplus (CyclotomicField ℓ Kplus) ℓ hfinrank
  have hζspec : IsPrimitiveRoot (IsCyclotomicExtension.zeta ℓ Kplus (CyclotomicField ℓ Kplus)) ℓ :=
    IsCyclotomicExtension.zeta_spec ℓ Kplus (CyclotomicField ℓ Kplus)
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hinj := hζspec.autToPow_injective Kplus
  have hcards : Fintype.card ((CyclotomicField ℓ Kplus) ≃ₐ[Kplus] (CyclotomicField ℓ Kplus)) =
      Fintype.card (ZMod ℓ)ˣ := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hℓ, ← hfinrank,
      ← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank Kplus (CyclotomicField ℓ Kplus)
  have hbij : Function.Bijective (hζspec.autToPow Kplus) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcards⟩
  have : IsCyclic ((CyclotomicField ℓ Kplus) ≃ₐ[Kplus] (CyclotomicField ℓ Kplus)) :=
      isCyclic_of_injective _ hinj
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
      (α := (CyclotomicField ℓ Kplus) ≃ₐ[Kplus] (CyclotomicField ℓ Kplus))
  set s : (ZMod ℓ)ˣ := hζspec.autToPow Kplus g with hsdef
  have hs : ∀ x : (ZMod ℓ)ˣ, x ∈ Subgroup.zpowers s := by
    intro x
    obtain ⟨τ, hτ⟩ := hbij.surjective x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg τ)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [hsdef, ← map_zpow, hk, hτ]⟩
  obtain ⟨δ₁, wR, η, hδ₁sq, hδ₁eig, hηN, hηres⟩ :=
    reduce_lift p hp5 ℓ hℓp Kplus hKplus Δact hΔact δ hδeig hpℓ (CyclotomicField ℓ Kplus) hirr
  obtain ⟨β, hβ0, hβrel⟩ :=
    ThaineDesk.exists_mul_galRestrict_of_norm_eq_one'
      (A := 𝓞 Kplus) (K := Kplus) (L := (CyclotomicField ℓ Kplus))
          (B := 𝓞 (CyclotomicField ℓ Kplus)) g (fun x => hg x) hηN
  obtain ⟨α, hα⟩ :=
    ThaineDesk.exists_algebraMap_eq_prod_galRestrict (𝓞 Kplus) Kplus (CyclotomicField ℓ Kplus)
        (𝓞 (CyclotomicField ℓ Kplus)) (β : 𝓞 (CyclotomicField ℓ Kplus))
  have hspanB : Ideal.span {algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField ℓ Kplus)) α}
      = Ideal.span {(β : 𝓞 (CyclotomicField ℓ Kplus))} ^ Fintype.card
          ((CyclotomicField ℓ Kplus) ≃ₐ[Kplus] (CyclotomicField ℓ Kplus)) := by
    rw [hα]
    exact ThaineDesk.span_prod_galRestrict_eq (𝓞 Kplus) Kplus (CyclotomicField ℓ Kplus)
        (𝓞 (CyclotomicField ℓ Kplus)) g
      (fun x => hg x) η (β : 𝓞 (CyclotomicField ℓ Kplus)) hβrel
  have hcardGal : Fintype.card ((CyclotomicField ℓ Kplus) ≃ₐ[Kplus] (CyclotomicField ℓ Kplus))
      = ℓ - 1 := by
    rw [← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, hfinrank]
  have hα0 : α ≠ 0 := by
    intro h0
    apply hβ0
    have h1 : algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField ℓ Kplus)) α = 0 := by rw [h0, map_zero]
    rw [hα] at h1
    obtain ⟨σ, -, hσ0⟩ := Finset.prod_eq_zero_iff.mp h1
    exact (galRestrict (𝓞 Kplus) Kplus (CyclotomicField ℓ Kplus) (𝓞 (CyclotomicField ℓ Kplus))
        σ).injective
      (a₁ := (β : 𝓞 (CyclotomicField ℓ Kplus))) (a₂ := 0) (by rw [hσ0, map_zero])
  set S : Finset (Ideal (𝓞 Kplus)) :=
    IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)}) (𝓞 Kplus) with hSdef
  have hpZbot : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.ne_zero
  have hpZmax : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsMaximal := by
    refine Ring.DimensionLEOne.maximalOfPrime hpZbot ?_
    rw [Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hℓ
  have hSmem : ∀ 𝔔 : Ideal (𝓞 Kplus), 𝔔 ∈ S ↔
      (𝔔.IsPrime ∧ (ℓ : 𝓞 Kplus) ∈ 𝔔) := by
    intro 𝔔
    rw [hSdef, IsDedekindDomain.mem_primesOverFinset_iff hpZbot]
    constructor
    · rintro ⟨hp', hover⟩
      refine ⟨hp', ?_⟩
      have h1 := hover.over
      have hmem : (ℓ : ℤ) ∈ 𝔔.under ℤ := by
        rw [← h1]
        exact Ideal.mem_span_singleton_self _
      rw [Ideal.under_def, Ideal.mem_comap] at hmem
      simpa using hmem
    · rintro ⟨hp', hℓmem⟩
      refine ⟨hp', ⟨?_⟩⟩
      have hle : Ideal.span {(ℓ : ℤ)} ≤ 𝔔.under ℤ := by
        rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
        simpa using hℓmem
      exact hpZmax.eq_of_le (Ideal.comap_ne_top _ hp'.ne_top) hle
  have hSbot : ∀ 𝔔 ∈ S, 𝔔 ≠ ⊥ := by
    intro 𝔔 h𝔔 h0
    have h1 := (hSmem 𝔔).mp h𝔔
    rw [h0] at h1
    exact hℓ.ne_zero (by exact_mod_cast (Ideal.mem_bot.mp h1.2))
  have hSmax : ∀ 𝔔 ∈ S, 𝔔.IsMaximal := by
    intro 𝔔 h𝔔
    exact ((hSmem 𝔔).mp h𝔔).1.isMaximal (hSbot 𝔔 h𝔔)
  have hSprime : ∀ 𝔔 ∈ S, Prime 𝔔 :=
    fun 𝔔 h𝔔 => Ideal.prime_of_isPrime (hSbot 𝔔 h𝔔) ((hSmem 𝔔).mp h𝔔).1
  have hcount : ∀ (𝔔 : Ideal (𝓞 Kplus)), 𝔔 ≠ ⊥ → 𝔔.IsPrime →
      ∀ (𝔓 : Ideal (𝓞 (CyclotomicField ℓ Kplus))), 𝔓.IsPrime → 𝔓.LiesOver 𝔔 →
      Ideal.ramificationIdx' 𝔔 𝔓 *
        Multiset.count 𝔔 (normalizedFactors (Ideal.span {α}))
        = (ℓ - 1) * Multiset.count 𝔓
            (normalizedFactors (Ideal.span {(β : 𝓞 (CyclotomicField ℓ Kplus))})) := by
    intro 𝔔 h𝔔0 h𝔔p 𝔓 h𝔓p h𝔓Q
    have := h𝔔p
    have := h𝔓p
    have := h𝔓Q
    rw [← hcardGal]
    exact ThaineDesk.count_descended (A := 𝓞 Kplus) (B := 𝓞 (CyclotomicField ℓ Kplus)) α
        (β : 𝓞 (CyclotomicField ℓ Kplus))
      (by exact_mod_cast hβ0) _ hspanB 𝔔 h𝔔0 𝔓 hα0
  obtain ⟨W, hW0, hWrel⟩ :=
    ThaineDesk.exists_eq_finsetProd_mul_pow (A := 𝓞 Kplus) p (Ideal.span {α})
      (by simpa [Ideal.span_singleton_eq_bot] using hα0) S hSprime
      (fun 𝔔 => Multiset.count 𝔔 (normalizedFactors (Ideal.span {α})))
      (fun 𝔔 _ => rfl)
      (by
        intro 𝔔 h𝔔pr h𝔔S
        have h𝔔p : 𝔔.IsPrime := Ideal.isPrime_of_prime h𝔔pr
        have h𝔔max : 𝔔.IsMaximal := h𝔔p.isMaximal h𝔔pr.ne_zero
        have := h𝔔max
        obtain ⟨𝔓, h𝔓max, h𝔓Q⟩ :=
          Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (CyclotomicField ℓ Kplus)) 𝔔
        have := h𝔓max
        have := h𝔓Q
        have hℓ𝔔 : (ℓ : 𝓞 Kplus) ∉ 𝔔 := by
          intro hmem
          exact h𝔔S ((hSmem 𝔔).mpr ⟨h𝔔p, hmem⟩)
        have he1 : Ideal.ramificationIdx' 𝔔 𝔓 = 1 :=
          ThaineAux.ramificationIdx_eq_one_of_not_mem (F := Kplus) (L := (CyclotomicField ℓ Kplus))
              (ℓ := ℓ) 𝔔 hℓ𝔔 𝔓
        have h2 := hcount 𝔔 h𝔔pr.ne_zero h𝔔p 𝔓 h𝔓max.isPrime h𝔓Q
        rw [he1, one_mul] at h2
        rw [h2]
        exact Dvd.dvd.mul_right hpℓ _)
  obtain ⟨ρ⟩ := ThaineDesk.exists_residue_equiv (A := 𝓞 Kplus) 𝔏 h𝔏deg
  set ψL : 𝓞 Kplus →+* ZMod ℓ := ρ.toRingHom.comp (Ideal.Quotient.mk 𝔏) with hψLdef
  have hψLker : ∀ x : 𝓞 Kplus, ψL x = 0 ↔ x ∈ 𝔏 := by
    intro x
    rw [hψLdef, RingHom.comp_apply]
    constructor
    · intro h
      have h0 : Ideal.Quotient.mk 𝔏 x = 0 := by
        apply ρ.injective
        simpa using h
      exact Ideal.Quotient.eq_zero_iff_mem.mp h0
    · intro h
      simp [Ideal.Quotient.eq_zero_iff_mem.mpr h]
  have hx₀u : IsUnit (ψL (δ₁ : 𝓞 Kplus)) := δ₁.isUnit.map ψL
  have hxδu : IsUnit (ψL (δ : 𝓞 Kplus)) := δ.isUnit.map ψL
  have hxδrel : hxδu.unit ^ 2 = hx₀u.unit ^ 1 * (wR.isUnit.map ψL).unit ^ p := by
    refine Units.ext ?_
    push_cast
    rw [hxδu.unit_spec, hx₀u.unit_spec, (wR.isUnit.map ψL).unit_spec, pow_one]
    have h1 := congrArg Units.val hδ₁sq
    push_cast at h1
    rw [← map_pow, h1, map_mul, map_pow]
  have hxδnp : ¬ ∃ y : (ZMod ℓ)ˣ, y ^ p = hxδu.unit := by
    refine ThaineDesk.not_exists_units_pow (p := p) 𝔏 ρ (δ : 𝓞 Kplus) hδ𝔏 hxδu.unit ?_
    rw [hxδu.unit_spec, hψLdef, RingHom.comp_apply]
    rfl
  obtain ⟨t₀, ht₀0, ht₀⟩ :=
    ThaineDesk.exists_t0_spec hp2 hpℓ s hs hx₀u.unit hxδu.unit (wR.isUnit.map ψL).unit
      1 hxδrel hxδnp
  refine ⟨α, W, fun 𝔔 => Multiset.count 𝔔 (normalizedFactors (Ideal.span {α})),
    -(2 : ZMod p)⁻¹ * t₀, hα0, ?_, hWrel, ?_⟩
  · have h20 : (2 : ZMod p) ≠ 0 := by
      intro h3
      have h4 : ((2 : ℕ) : ZMod p) = 0 := by push_cast; exact h3
      rw [ZMod.natCast_eq_zero_iff] at h4
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp h4)
    intro h0
    rcases mul_eq_zero.mp h0 with h | h
    · rw [neg_eq_zero] at h
      exact h20 (by simpa using (inv_eq_zero.mp h))
    · exact ht₀0 h
  · have hσtK : Function.Surjective
        ((IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm.toMonoidHom :
          (ZMod p)ˣ →* (CyclotomicField p ℚ ≃ₐ[ℚ] CyclotomicField p ℚ)) :=
      (IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm.surjective
    have hcommK : ∀ (d : (ZMod p)ˣ) (x : 𝓞 Kplus),
        algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) (Δact d x)
          = galRestrict ℤ ℚ (CyclotomicField p ℚ) (𝓞 (CyclotomicField p ℚ))
              ((IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm.toMonoidHom d)
              (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ)) x) := by
      intro d x
      have h1 := DFunLike.congr_fun (hΔact d) x
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingHom.coe_coe] at h1
      rw [h1]
      rfl
    have hminus : Δact (-1) = 1 :=
      ThaineReduce.Δact_neg_one p Kplus hKplus Δact hΔact
    intro 𝔔 h𝔔S
    have h𝔔max : 𝔔.IsMaximal := hSmax 𝔔 h𝔔S
    have := h𝔔max
    have hℓ𝔔 : (ℓ : 𝓞 Kplus) ∈ 𝔔 := ((hSmem 𝔔).mp h𝔔S).2
    have hℓ𝔔2 : (ℓ : 𝓞 Kplus) ∉ 𝔔 ^ 2 := hunram 𝔔 hℓ𝔔
    obtain ⟨𝔓, h𝔓max, h𝔓Q⟩ :=
      Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 (CyclotomicField ℓ Kplus)) 𝔔
    have := h𝔓max
    have := h𝔓Q
    obtain ⟨-, he𝔔, -, -, -, hζ𝔓, hζ𝔓2⟩ :=
      ThaineAux.ram_package (F := Kplus) (L := (CyclotomicField ℓ Kplus)) (ℓ := ℓ) 𝔔 𝔓 hℓ𝔔 hℓ𝔔2
    have hℓ𝔓 : ((ℓ : ℕ) : 𝓞 (CyclotomicField ℓ Kplus)) ∈ 𝔓 := by
      have h2 := hℓ𝔔
      rw [h𝔓Q.over] at h2
      have h3 := Ideal.mem_comap.mp h2
      rwa [map_natCast] at h3
    have h𝔓0 : 𝔓 ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.mem_bot] at hℓ𝔓
      exact hℓ.ne_zero (by exact_mod_cast hℓ𝔓)
    have haQP : Multiset.count 𝔔 (normalizedFactors (Ideal.span {α}))
        = Multiset.count 𝔓
            (normalizedFactors (Ideal.span {(β : 𝓞 (CyclotomicField ℓ Kplus))})) := by
      have h1 := hcount 𝔔 (hSbot 𝔔 h𝔔S) h𝔔max.isPrime 𝔓 h𝔓max.isPrime h𝔓Q
      rw [he𝔔] at h1
      have hℓ2 := hℓ.two_le
      exact Nat.eq_of_mul_eq_mul_left (by omega) h1
    have hgζ : galRestrict (𝓞 Kplus) Kplus (CyclotomicField ℓ Kplus) (𝓞 (CyclotomicField ℓ Kplus)) g
        (ThaineAux.zetaInt Kplus (CyclotomicField ℓ Kplus) ℓ)
        = ThaineAux.zetaInt Kplus (CyclotomicField ℓ Kplus) ℓ ^ ((s : ZMod ℓ)).val :=
      ThaineAux.galRestrict_zetaInt (F := Kplus) (L := CyclotomicField ℓ Kplus) (ℓ := ℓ) g
    have hu : galRestrict (𝓞 Kplus) Kplus (CyclotomicField ℓ Kplus) (𝓞 (CyclotomicField ℓ Kplus)) g
        (ThaineAux.zetaInt Kplus (CyclotomicField ℓ Kplus) ℓ - 1)
        = (ThaineAux.zetaInt Kplus (CyclotomicField ℓ Kplus) ℓ - 1)
            * (∑ i ∈ Finset.range ((s : ZMod ℓ)).val, ThaineAux.zetaInt Kplus
                (CyclotomicField ℓ Kplus) ℓ ^ i) := by
      rw [map_sub, map_one, hgζ, ThaineDesk.sub_one_mul_geom_sum]
    have hus : (∑ i ∈ Finset.range ((s : ZMod ℓ)).val, ThaineAux.zetaInt Kplus
        (CyclotomicField ℓ Kplus) ℓ ^ i)
        - (((s : ZMod ℓ)).val : 𝓞 (CyclotomicField ℓ Kplus)) ∈ 𝔓 :=
      ThaineDesk.geom_sum_sub_natCast_mem 𝔓
          (ThaineAux.zetaInt Kplus (CyclotomicField ℓ Kplus) ℓ) hζ𝔓 _
    have hgtriv : ∀ x : 𝓞 (CyclotomicField ℓ Kplus), galRestrict (𝓞 Kplus) Kplus
        (CyclotomicField ℓ Kplus) (𝓞 (CyclotomicField ℓ Kplus)) g x - x ∈ 𝔓 :=
      fun x => ThaineAux.galRestrict_sub_self_mem (F := Kplus)
          (L := (CyclotomicField ℓ Kplus)) (ℓ := ℓ)
        𝔔 𝔓 hℓ𝔔 hℓ𝔔2 g x
    obtain ⟨ha, ha'⟩ :=
      ThaineDesk.span_le_pow_count 𝔓 h𝔓0 β hβ0
    have hC6 : (η : 𝓞 (CyclotomicField ℓ Kplus)) *
        ((((s : ZMod ℓ)).val : ℕ) : 𝓞 (CyclotomicField ℓ Kplus))
          ^ (Multiset.count 𝔓
              (normalizedFactors (Ideal.span {(β : 𝓞 (CyclotomicField ℓ Kplus))}))) - 1 ∈ 𝔓 :=
      ThaineDesk.eta_mul_pow_sub_one_mem (A := 𝓞 Kplus) (K := Kplus)
        (L := CyclotomicField ℓ Kplus) (B := 𝓞 (CyclotomicField ℓ Kplus)) 𝔓 h𝔓0
        (ThaineAux.zetaInt Kplus (CyclotomicField ℓ Kplus) ℓ - 1) hζ𝔓 hζ𝔓2
        g hgtriv _ hu ((s : ZMod ℓ)).val hus η β hβ0 hβrel _ ha ha'
    have hres𝔓 : (η : 𝓞 (CyclotomicField ℓ Kplus)) - algebraMap (𝓞 Kplus)
        (𝓞 (CyclotomicField ℓ Kplus)) (δ₁ : 𝓞 Kplus) ∈ 𝔓 :=
      hηres 𝔔 hℓ𝔔 𝔓 h𝔓Q
    have hA : (δ₁ : 𝓞 Kplus) * ((((s : ZMod ℓ)).val : ℕ) : 𝓞 Kplus)
          ^ (Multiset.count 𝔓
              (normalizedFactors (Ideal.span {(β : 𝓞 (CyclotomicField ℓ Kplus))}))) - 1 ∈ 𝔔 :=
      ThaineDesk.delta_mul_pow_sub_one_mem 𝔔 𝔓 (η : 𝓞 (CyclotomicField ℓ Kplus)) (δ₁ : 𝓞 Kplus)
        ((s : ZMod ℓ)).val _ hC6 hres𝔓
    obtain ⟨d₀, hd₀⟩ :=
      ThaineAux.exists_eq_map_of_natCast_mem (K := CyclotomicField p ℚ) (F := Kplus)
        (Δact := Δact)
        (σt := (IsCyclotomicExtension.Rat.galEquivZMod p (CyclotomicField p ℚ)).symm.toMonoidHom)
        hσtK hcommK ℓ 𝔏 𝔔 hℓ𝔏 hℓ𝔔
    have hψQker : ∀ x ∈ 𝔔, ψL.comp ((Δact d₀⁻¹ : 𝓞 Kplus ≃+* 𝓞 Kplus) :
        𝓞 Kplus →+* 𝓞 Kplus) x = 0 := by
      intro x hx
      rw [hd₀] at hx
      obtain ⟨y, hy, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (Δact d₀) (Δact d₀).surjective).mp hx
      have hyx : (Δact d₀⁻¹) ((Δact d₀) y) = y := by
        have h5 : (Δact d₀⁻¹) * (Δact d₀) = 1 := by
          rw [← map_mul, inv_mul_cancel, map_one]
        calc (Δact d₀⁻¹) ((Δact d₀) y) = ((Δact d₀⁻¹) * (Δact d₀)) y := rfl
          _ = y := by rw [h5]; rfl
      rw [RingHom.comp_apply]
      refine (hψLker _).mpr ?_
      change (Δact d₀⁻¹) ((Δact d₀) y) ∈ 𝔏
      rw [hyx]
      exact hy
    obtain ⟨xQ, hxQval, hxQrel⟩ :=
      ThaineDesk.exists_units_mul_pow_eq_one
        (ψL.comp ((Δact d₀⁻¹ : 𝓞 Kplus ≃+* 𝓞 Kplus) : 𝓞 Kplus →+* 𝓞 Kplus)) 𝔔 hψQker
        δ₁ s _ hA
    obtain ⟨v, hveig⟩ := hδ₁eig d₀⁻¹
    have hxQx₀ : xQ = hx₀u.unit ^ ((((d₀⁻¹ : (ZMod p)ˣ) : ZMod p)) ^ 2).val
        * ((v.isUnit.map ψL).unit) ^ p := by
      refine Units.ext ?_
      have h3 := congrArg Units.val hveig
      push_cast [Units.coe_mapEquiv, RingEquiv.coe_toMulEquiv] at h3 ⊢
      rw [hxQval, hx₀u.unit_spec, (v.isUnit.map ψL).unit_spec]
      rw [RingHom.comp_apply, RingHom.coe_coe]
      rw [show (Δact d₀⁻¹) (δ₁ : 𝓞 Kplus)
          = (δ₁ : 𝓞 Kplus) ^ ((((d₀ : ZMod p))⁻¹) ^ 2).val * (v : 𝓞 Kplus) ^ p from h3,
        map_mul, map_pow, map_pow]
    have hE5 := ThaineDesk.cast_eq_sum_pair_of_rep hp2 s hs hpℓ hx₀u.unit t₀ ht₀ d₀
      ((v.isUnit.map ψL).unit) xQ hxQx₀
      (Multiset.count 𝔓 (normalizedFactors (Ideal.span {(β : 𝓞 (CyclotomicField ℓ Kplus))}))) hxQrel
    have hstab : ∀ e : (ZMod p)ˣ,
        𝔏.map ((Δact e : 𝓞 Kplus ≃+* 𝓞 Kplus) : 𝓞 Kplus →+* 𝓞 Kplus) = 𝔏 →
        e = 1 ∨ e = -1 := by
      intro e he
      obtain ⟨ve, hveige⟩ := hδ₁eig e
      refine ThaineDesk.fix_eq_pm_one s hs hpℓ ψL 𝔏 (fun x hx => (hψLker x).mpr hx)
        δ₁ hx₀u.unit hx₀u.unit_spec t₀ ht₀0 ht₀ e (Δact e) ?_ ve ?_
      · intro x
        exact ThaineAux.ringEquiv_sub_self_mem_of_map_eq (F := Kplus) (Δact e) 𝔏
          hℓ h𝔏deg he x
      · have h3 := congrArg Units.val hveige
        push_cast at h3
        exact h3
    have hfilter : Finset.univ.filter
          (fun d : (ZMod p)ˣ => 𝔏.map (Δact d) = 𝔔) = ({d₀, -d₀} : Finset (ZMod p)ˣ) := by
      refine (Finset.filter_congr ?_).trans
        (ThaineDesk.filter_map_eq_pair Δact 𝔏 hstab hminus d₀)
      rintro d -
      rw [hd₀]
      exact Iff.rfl
    change ((Multiset.count 𝔔 (normalizedFactors (Ideal.span {α})) : ℕ) : ZMod p)
        = ∑ d ∈ Finset.univ.filter (fun d : (ZMod p)ˣ => 𝔏.map (Δact d) = 𝔔),
            -(2 : ZMod p)⁻¹ * t₀ * (((d : ZMod p)) ^ 2)⁻¹
    rw [hfilter, haQP]
    exact hE5

end ThaineAssembly
open scoped ThaineReduce

namespace Stickelberger

open ThaineAssembly in
/-- **Thaine's relation** in the totally real subfield of `ℚ(ζ_p)`, for a prime `p ≥ 5`: given a
degree-one prime `𝔏` of `K⁺` above `ℓ ≠ p` and a unit `δ` of `K⁺` in the `ω²`-eigenspace modulo
`p`-th powers whose residue modulo `𝔏` is not a `p`-th power, some nonzero `t : ZMod p` makes
`∏_d (d • 𝔏) ^ (t d⁻²)` principal up to a `p`-th power of an ideal. -/
public theorem thaine_relation_plusField (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p)
    (Kplus : Type*) [Field Kplus] [NumberField Kplus] [IsTotallyReal Kplus]
    [Algebra Kplus (CyclotomicField p ℚ)]
    (hKplus : Module.finrank Kplus (CyclotomicField p ℚ) = 2)
    (Δact : (ZMod p)ˣ →* (𝓞 Kplus) ≃+* (𝓞 Kplus))
    (hΔact : ∀ d, (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))).comp
      (Δact d).toRingHom = (clRingAction p (CyclotomicField p ℚ) d).toRingHom.comp
        (algebraMap (𝓞 Kplus) (𝓞 (CyclotomicField p ℚ))))
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p)
    (𝔏 : Ideal (𝓞 Kplus)) (h𝔏max : 𝔏.IsMaximal)
    (h𝔏deg : Ideal.absNorm 𝔏 = ℓ)
    (δ : (𝓞 Kplus)ˣ)
    (hδeig : ∀ d : (ZMod p)ˣ, ∃ v : (𝓞 Kplus)ˣ,
      Units.mapEquiv (Δact d).toMulEquiv δ = δ ^ ((d : ZMod p) ^ 2).val * v ^ p)
    (hδ𝔏 : (Ideal.Quotient.mk 𝔏 (δ : 𝓞 Kplus))
      ∉ {x : 𝓞 Kplus ⧸ 𝔏 | ∃ y, y ^ p = x}) :
    ∃ (α : Kplus) (_hα : α ≠ 0) (t : ZMod p) (_ht : t ≠ 0) (J : Ideal (𝓞 Kplus)),
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 Kplus)) α =
        (∏ d : (ZMod p)ˣ, (𝔏.map (Δact d).toRingHom :
          FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^
            (t * ((d : ZMod p) ^ 2)⁻¹).val) *
        (J : FractionalIdeal (nonZeroDivisors (𝓞 Kplus)) Kplus) ^ p := by
  classical
  have := h𝔏max
  have hℓF : Fact ℓ.Prime := ⟨hℓ⟩
  have hp := (Fact.out : p.Prime)
  have hℓ𝔏 : (ℓ : 𝓞 Kplus) ∈ 𝔏 := by
    have := Ideal.absNorm_mem 𝔏
    rw [h𝔏deg] at this
    exact_mod_cast this
  obtain ⟨a₀, W, av, t, ha₀, ht, hrel, hcong⟩ :=
    engine_out p hp5 Kplus hKplus Δact hΔact ℓ hℓ hℓp 𝔏 h𝔏max h𝔏deg δ hδeig hδ𝔏
  have hunram : ∀ (𝔔 : Ideal (𝓞 Kplus)) [𝔔.IsMaximal], (ℓ : 𝓞 Kplus) ∈ 𝔔 →
      (ℓ : 𝓞 Kplus) ∉ 𝔔 ^ 2 :=
    fun 𝔔 _ h => ThaineAux.natCast_not_mem_sq_of_algebra (F := Kplus) ℓ p hℓp
        (CyclotomicField p ℚ) 𝔔 h
  have hπ := ThaineAux.span_natCast_eq_prod_primesOver (F := Kplus) ℓ hunram
  have hpZbot : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hℓ.ne_zero
  have hpZprime : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsPrime := by
    rw [Ideal.span_singleton_prime (by exact_mod_cast hℓ.ne_zero)]
    exact Nat.prime_iff_prime_int.mp hℓ
  have hpZmax : (Ideal.span {(ℓ : ℤ)} : Ideal ℤ).IsMaximal :=
    Ring.DimensionLEOne.maximalOfPrime hpZbot hpZprime
  have hφS : ∀ d : (ZMod p)ˣ, 𝔏.map (Δact d) ∈
      IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)}) (𝓞 Kplus) := by
    intro d
    rw [IsDedekindDomain.mem_primesOverFinset_iff hpZbot]
    refine ⟨Ideal.map_isPrime_of_equiv _, ?_⟩
    have hℓd : (ℓ : 𝓞 Kplus) ∈ 𝔏.map (Δact d) := by
      simpa using Ideal.mem_map_of_mem (Δact d) hℓ𝔏
    have hle : Ideal.span {(ℓ : ℤ)} ≤ (𝔏.map (Δact d)).under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hℓd
    exact ⟨hpZmax.eq_of_le (Ideal.comap_ne_top _ (Ideal.IsMaximal.ne_top inferInstance)) hle⟩
  have hℓ0 : (ℓ : 𝓞 Kplus) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  obtain ⟨α, hα, J, hJ⟩ := ThaineAux.bookkeeping Kplus
    (IsDedekindDomain.primesOverFinset (Ideal.span {(ℓ : ℤ)}) (𝓞 Kplus))
    (fun d : (ZMod p)ˣ => 𝔏.map (Δact d)) hφS p hp.pos av
    (fun d : (ZMod p)ˣ => (t * ((d : ZMod p) ^ 2)⁻¹).val)
    (fun 𝔔 h𝔔 => by simpa only [ZMod.natCast_zmod_val] using hcong 𝔔 h𝔔)
    (ℓ : 𝓞 Kplus) a₀ hℓ0 ha₀ hπ W hrel
  exact ⟨α, hα, t, ht, J, hJ⟩

end Stickelberger
