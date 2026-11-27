/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.FractionalIdeal.Operations
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# An ideal of index `N` under the Heegner hypothesis

Let `K` be a quadratic field and `N ≥ 1` an integer such that every prime factor of `N` splits in
`K`. Then `𝓞 K` has an ideal `𝒩` with `𝓞 K ⧸ 𝒩 ≃+* ℤ ⧸ N ℤ`, so that `𝓞 K ⧸ 𝒩` is cyclic of
order `N`
(`NumberField.RingOfIntegers.exists_ideal_isAddCyclic_quotient_of_heegnerHypothesis`, stated for
an imaginary quadratic field as in the sources). This is the ideal used to construct Heegner points
on `X₀(N)` (Gross, *Kolyvagin's work on modular elliptic curves*, 1991, §1, p. 235; Miller,
*Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank
zero and one*, 2011, §4, p. 335).

For a nonzero ideal `I` of a Dedekind domain `R`, the quotient `I⁻¹ / R` is isomorphic to `R ⧸ I`
(`FractionalIdeal.invQuotientEquiv`, from Mathlib's `FractionalIdeal.quotientEquiv`); so `I⁻¹ / R`
is cyclic of order `N` whenever `R ⧸ I` is (`FractionalIdeal.isAddCyclic_inv_quotient_one`).

## Proof

For each prime `p ∣ N` write `p 𝓞 K = P_p Q_p` with `P_p ≠ Q_p`. Comparing absolute norms gives
`N(P_p) = p`, and `p ∉ P_p ^ 2` because `P_p ≠ Q_p`. Then a natural number `k` lies in `P_p ^ e`
exactly when `p ^ e ∣ k`. With `𝒩 = ∏_{p ∣ N} P_p ^ {v_p(N)}`, the Chinese remainder theorem
(`IsDedekindDomain.quotientEquivPiOfProdEq`) shows that `𝓞 K ⧸ 𝒩` has characteristic `N`; its
order is the absolute norm `∏ p ^ {v_p(N)} = N`, so `ZMod.ringEquiv` identifies it with `ZMod N`.
-/

@[expose] public section

open NumberField nonZeroDivisors

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K]

/-- If `P` is a prime of `𝓞 K` of absolute norm a prime `p` with `p ∉ P ^ 2`, then a natural number
`k` lies in `P ^ e` if and only if `p ^ e ∣ k`. -/
theorem natCast_mem_pow_iff_of_absNorm_eq {P : Ideal (𝓞 K)} [hP : P.IsPrime] {p : ℕ}
    (hp : p.Prime) (hPp : Ideal.absNorm P = p) (hP2 : (p : 𝓞 K) ∉ P ^ 2) (e k : ℕ) :
    (k : 𝓞 K) ∈ P ^ e ↔ p ^ e ∣ k := by
  have hpP : (p : 𝓞 K) ∈ P := hPp ▸ Ideal.absNorm_mem P
  have hPbot : P ≠ ⊥ := by
    rintro rfl
    simp only [Ideal.absNorm_bot] at hPp
    exact hp.ne_zero hPp.symm
  have hPprime : Prime P := Ideal.prime_of_isPrime hPbot hP
  -- `span {p} = P * A` with `P ∤ A`
  obtain ⟨A, hA⟩ : P ∣ Ideal.span {(p : 𝓞 K)} :=
    Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem P).mpr hpP)
  have hPA : ¬ P ∣ A := by
    rintro ⟨B, rfl⟩
    apply hP2
    rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le, hA, ← mul_assoc, ← pow_two]
    exact dvd_mul_right _ _
  constructor
  · induction e generalizing k with
    | zero => simp
    | succ e ih =>
      intro hk
      have hkP : (k : 𝓞 K) ∈ P := Ideal.pow_le_self (Nat.succ_ne_zero e) hk
      have hpk : p ∣ k := by
        by_contra h
        have hcop : IsCoprime (p : ℤ) (k : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)
        obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom (𝓞 K))
        apply hP.ne_top
        rw [Ideal.eq_top_iff_one, ← hab]
        simp only [eq_intCast, Int.cast_natCast]
        exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hkP)
      obtain ⟨m, rfl⟩ := hpk
      have hm : (m : 𝓞 K) ∈ P ^ e := by
        rw [← Ideal.span_singleton_le_iff_mem, ← Ideal.dvd_iff_le]
        have h1 : P ^ (e + 1) ∣ Ideal.span {(p : 𝓞 K)} * Ideal.span {(m : 𝓞 K)} := by
          rw [Ideal.span_singleton_mul_span_singleton, Ideal.dvd_iff_le,
            Ideal.span_singleton_le_iff_mem]
          exact_mod_cast hk
        rw [hA, pow_succ', mul_assoc] at h1
        exact hPprime.pow_dvd_of_dvd_mul_left e hPA
          ((mul_dvd_mul_iff_left hPprime.ne_zero).mp h1)
      rw [pow_succ']
      exact mul_dvd_mul_left p (ih m hm)
  · rintro ⟨m, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hpP e)

/-- **An ideal of index `N` with cyclic quotient.** Let `N ≠ 0` and suppose that for every prime
`p ∣ N` there is a prime `P` of `𝓞 K` of absolute norm `p` with `p ∉ P ^ 2`. Then there is an ideal
`𝒩` of `𝓞 K` with `𝓞 K ⧸ 𝒩 ≃+* ZMod N`. -/
theorem exists_ideal_quotient_ringEquiv_zmod {N : ℕ} (hN : N ≠ 0)
    (h : ∀ p ∈ N.primeFactors, ∃ P : Ideal (𝓞 K), P.IsPrime ∧ Ideal.absNorm P = p ∧
      (p : 𝓞 K) ∉ P ^ 2) :
    ∃ 𝒩 : Ideal (𝓞 K), Nonempty (𝓞 K ⧸ 𝒩 ≃+* ZMod N) := by
  choose! P hPprime hPnorm hP2 using h
  let ι := {p // p ∈ N.primeFactors}
  let Q : ι → Ideal (𝓞 K) := fun i => P i
  let e : ι → ℕ := fun i => N.factorization i
  let 𝒩 : Ideal (𝓞 K) := ∏ i, Q i ^ e i
  refine ⟨𝒩, ?_⟩
  have hQbot : ∀ i : ι, Q i ≠ ⊥ := fun i hi => by
    have := hPnorm i i.2
    simp only [Q] at hi
    rw [hi, Ideal.absNorm_bot] at this
    exact (Nat.prime_of_mem_primeFactors i.2).ne_zero this.symm
  have hQprime : ∀ i, Prime (Q i) := fun i => Ideal.prime_of_isPrime (hQbot i) (hPprime i i.2)
  have hQinj : Pairwise fun i j => Q i ≠ Q j := fun i j hij hQ => hij <| Subtype.ext <| by
    have := congrArg Ideal.absNorm hQ
    simpa [Q, hPnorm i i.2, hPnorm j j.2] using this
  let f := IsDedekindDomain.quotientEquivPiOfProdEq 𝒩 Q e hQprime hQinj rfl
  -- the characteristic of `𝓞 K ⧸ 𝒩` is `N`
  have hchar : CharP (𝓞 K ⧸ 𝒩) N := by
    refine ⟨fun k => ?_⟩
    rw [← map_eq_zero_iff f f.injective, map_natCast, funext_iff]
    simp only [Pi.natCast_apply, Pi.zero_apply]
    have : ∀ i : ι, ((k : 𝓞 K ⧸ Q i ^ e i) = 0 ↔ i.1 ^ e i ∣ k) := fun i => by
      rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem]
      have := hPprime i i.2
      exact natCast_mem_pow_iff_of_absNorm_eq (Nat.prime_of_mem_primeFactors i.2)
        (hPnorm i i.2) (hP2 i i.2) _ _
    simp only [this, ι, e]
    constructor
    · intro hk
      rcases eq_or_ne k 0 with rfl | hk0
      · exact dvd_zero N
      refine (Nat.factorization_le_iff_dvd hN hk0).mp fun p => ?_
      by_cases hp : p ∈ N.primeFactors
      · exact ((Nat.prime_of_mem_primeFactors hp).pow_dvd_iff_le_factorization hk0).mp
          (hk ⟨p, hp⟩)
      · rw [Finsupp.notMem_support_iff.mp (by simpa using hp)]
        exact Nat.zero_le _
    · intro hk i
      exact (Nat.ordProj_dvd N i).trans hk
  -- the order of `𝓞 K ⧸ 𝒩` is `N`
  have hcard : Nat.card (𝓞 K ⧸ 𝒩) = N := by
    rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply, map_prod]
    simp only [map_pow, Q, e]
    rw [Finset.prod_coe_sort N.primeFactors (fun p => Ideal.absNorm (P p) ^ N.factorization p)]
    rw [Finset.prod_congr rfl fun p hp => by rw [hPnorm p hp]]
    exact (Nat.prod_primeFactors_pow_factorization hN).symm
  have : Finite (𝓞 K ⧸ 𝒩) := Nat.finite_of_card_ne_zero (hcard ▸ hN)
  let _ := Fintype.ofFinite (𝓞 K ⧸ 𝒩)
  exact ⟨(ZMod.ringEquiv (𝓞 K ⧸ 𝒩) (Fintype.card_eq_nat_card.trans hcard)).symm⟩

/-- In a quadratic field, if `p 𝓞 K = P Q` for distinct primes `P ≠ Q`, then `P` has absolute norm
`p` and `p ∉ P ^ 2`. -/
theorem absNorm_eq_and_natCast_notMem_sq_of_span_eq_mul (hK : Module.finrank ℚ K = 2) {p : ℕ}
    (hp : p.Prime) {P Q : Ideal (𝓞 K)} (hP : P.IsPrime) (hQ : Q.IsPrime) (hPQ : P ≠ Q)
    (hspan : Ideal.span {(p : 𝓞 K)} = P * Q) : Ideal.absNorm P = p ∧ (p : 𝓞 K) ∉ P ^ 2 := by
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hPQbot : P * Q ≠ ⊥ := by
    rw [← hspan]
    exact fun h => hp0 (Ideal.span_singleton_eq_bot.mp h)
  have hPbot : P ≠ ⊥ := fun h => hPQbot (by simp [h])
  have hQbot : Q ≠ ⊥ := fun h => hPQbot (by simp [h])
  have hnorm : Ideal.absNorm P * Ideal.absNorm Q = p ^ 2 := by
    rw [← map_mul, ← hspan, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, hK]
  have hP1 : Ideal.absNorm P ≠ 1 := fun h => hP.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have hQ1 : Ideal.absNorm Q ≠ 1 := fun h => hQ.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow hp).mp (Dvd.intro _ hnorm)
    interval_cases k
    · exact absurd (by simpa using hk') hP1
    · simpa using hk'
    · rw [hk'] at hnorm
      exact absurd (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos 2) (hnorm.trans (mul_one _).symm))
        hQ1
  · intro h
    have h1 : P ^ 2 ∣ P * Q := by
      rw [← hspan, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact h
    rw [pow_two] at h1
    have h2 : P ∣ Q := (mul_dvd_mul_iff_left hPbot).mp h1
    exact hPQ ((hQ.isMaximal hQbot).eq_of_le hP.ne_top (Ideal.dvd_iff_le.mp h2)).symm

/-- **An ideal of index `N` in a quadratic field.** Let `K` be a quadratic field and `N ≥ 1` an
integer such that every prime `p ∣ N` splits in `K`, i.e. `p 𝓞 K = P Q` for distinct primes `P ≠ Q`
of `𝓞 K`. Then there is an ideal `𝒩` of `𝓞 K` with `𝓞 K ⧸ 𝒩 ≃+* ℤ ⧸ N ℤ`. -/
theorem exists_ideal_quotient_ringEquiv_zmod_of_finrank_eq_two (hK : Module.finrank ℚ K = 2)
    {N : ℕ} (hN : 1 ≤ N)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ N → ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) :
    ∃ 𝒩 : Ideal (𝓞 K), Nonempty (𝓞 K ⧸ 𝒩 ≃+* ZMod N) := by
  refine exists_ideal_quotient_ringEquiv_zmod (by omega) fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  obtain ⟨P, Q, hP, hQ, hPQ, hspan⟩ := hsplit p hpp (Nat.dvd_of_mem_primeFactors hp)
  exact ⟨P, hP, absNorm_eq_and_natCast_notMem_sq_of_span_eq_mul hK hpp hP hQ hPQ hspan⟩

/-- **An ideal of index `N` under the Heegner hypothesis.** Let `K` be an imaginary quadratic field
with ring of integers `𝓞 K` and let `N ≥ 1` be an integer such that every prime factor `p` of `N`
splits in `K`: `p 𝓞 K = P Q` with `P ≠ Q` prime ideals. Then there is an ideal `𝒩` of `𝓞 K` such
that the additive group `𝓞 K ⧸ 𝒩` is cyclic of order `N`.

The proof takes `𝒩 = ∏_{p ∣ N} P_p ^ {v_p(N)}`; it does not use that `K` is imaginary
(`exists_ideal_quotient_ringEquiv_zmod_of_finrank_eq_two`).

Sources: R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic
curves of analytic rank zero and one*, LMS J. Comput. Math. 14 (2011), 327–350, §4, p. 335 ("By
hypothesis, there is an ideal $\mathcal{N}$ of $\mathcal{O}_K$ such that
$\mathcal{O}_K/\mathcal{N}$ is cyclic of order $N$"); B. H. Gross, *Kolyvagin's work on modular
elliptic curves*, in *L-functions and arithmetic* (Durham, 1989), London Math. Soc. Lecture Note
Ser. 153, Cambridge Univ. Press, 1991, 235–256, §1, p. 235 ("Choose an ideal $\mathcal{N}$ of
$\mathcal{O}$ with $\mathcal{O}/\mathcal{N} \simeq \mathbb{Z}/N\mathbb{Z}$"). -/
theorem exists_ideal_isAddCyclic_quotient_of_heegnerHypothesis [IsTotallyComplex K]
    (hK : Module.finrank ℚ K = 2) {N : ℕ} (hN : 1 ≤ N)
    (hsplit : ∀ p : ℕ, p.Prime → p ∣ N → ∃ P Q : Ideal (𝓞 K), P.IsPrime ∧ Q.IsPrime ∧ P ≠ Q ∧
      Ideal.span {(p : 𝓞 K)} = P * Q) :
    ∃ 𝒩 : Ideal (𝓞 K), IsAddCyclic (𝓞 K ⧸ 𝒩) ∧ Nat.card (𝓞 K ⧸ 𝒩) = N := by
  obtain ⟨𝒩, ⟨f⟩⟩ := exists_ideal_quotient_ringEquiv_zmod_of_finrank_eq_two hK hN hsplit
  exact ⟨𝒩, isAddCyclic_of_surjective f.symm.toAddMonoidHom f.symm.surjective,
    (Nat.card_congr f.toEquiv).trans (Nat.card_zmod N)⟩

end NumberField.RingOfIntegers

namespace FractionalIdeal

open nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {L : Type*} [Field L] [Algebra R L]
  [IsFractionRing R L]

/-- For a nonzero ideal `I` of a Dedekind domain `R` with fraction field `L`, the fractional ideal
`I⁻¹ = {x ∈ L : x I ⊆ R}` contains `R`. -/
theorem one_le_inv_coeIdeal {I : Ideal R} (hI : I ≠ ⊥) :
    (1 : FractionalIdeal R⁰ L) ≤ (I : FractionalIdeal R⁰ L)⁻¹ := by
  simpa using inv_anti_mono (coeIdeal_eq_zero.not.mpr hI) (coeIdeal_le_one (S := R⁰) (P := L))

/-- The `R`-linear isomorphism `R ≃ 1` onto the unit fractional ideal `1 ⊆ L`. -/
noncomputable def oneLinearEquiv : R ≃ₗ[R] ((1 : FractionalIdeal R⁰ L) : Submodule R L) :=
  (LinearEquiv.ofInjective (Algebra.linearMap R L) (IsFractionRing.injective R L)).trans
    (LinearEquiv.ofEq _ _ (by rw [coeToSubmodule_one, Submodule.one_eq_range]))

/-- For a nonzero ideal `I` of a Dedekind domain `R` with fraction field `L`, the quotient
`I⁻¹ / R` of fractional ideals is isomorphic to `R ⧸ I` as an `R`-module. It comes from
`FractionalIdeal.quotientEquiv`, the isomorphism `I/J ≃ I'/J'` when `I J' = I' J`. -/
noncomputable def invQuotientEquiv (I : Ideal R) (hI : I ≠ ⊥) :
    (↥(((I : FractionalIdeal R⁰ L)⁻¹ : FractionalIdeal R⁰ L) : Submodule R L) ⧸
      Submodule.comap
        ((((I : FractionalIdeal R⁰ L)⁻¹ : FractionalIdeal R⁰ L) : Submodule R L).subtype)
        ((1 : FractionalIdeal R⁰ L) : Submodule R L)) ≃ₗ[R] R ⧸ I :=
  have hI0 : (I : FractionalIdeal R⁰ L) ≠ 0 := coeIdeal_eq_zero.not.mpr hI
  (quotientEquiv _ 1 1 (I : FractionalIdeal R⁰ L) (by rw [inv_mul_cancel₀ hI0, mul_one])
      (one_le_inv_coeIdeal hI) coeIdeal_le_one hI0 (inv_ne_zero hI0)).trans
    (Submodule.Quotient.equiv I _ oneLinearEquiv (by
      ext x
      simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (mem_coeIdeal R⁰).mpr ⟨y, hy, rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := (mem_coeIdeal R⁰).mp hx
        exact ⟨y, hy, Subtype.ext hyx⟩)).symm

/-- **`I⁻¹ / R` is cyclic of order `N` when `R ⧸ I` is.** For a nonzero ideal `I` of a Dedekind
domain `R` with fraction field `L` such that `R ⧸ I` is cyclic of order `N`, the fractional ideal
`I⁻¹ = {x ∈ L : x I ⊆ R}` contains `R` and the quotient `I⁻¹ / R` is cyclic of order `N`. -/
theorem isAddCyclic_inv_quotient_one {I : Ideal R} (hI : I ≠ ⊥) {N : ℕ}
    (hcyc : IsAddCyclic (R ⧸ I)) (hcard : Nat.card (R ⧸ I) = N) :
    IsAddCyclic (↥(((I : FractionalIdeal R⁰ L)⁻¹ : FractionalIdeal R⁰ L) : Submodule R L) ⧸
      Submodule.comap
        ((((I : FractionalIdeal R⁰ L)⁻¹ : FractionalIdeal R⁰ L) : Submodule R L).subtype)
        ((1 : FractionalIdeal R⁰ L) : Submodule R L)) ∧
    Nat.card (↥(((I : FractionalIdeal R⁰ L)⁻¹ : FractionalIdeal R⁰ L) : Submodule R L) ⧸
      Submodule.comap
        ((((I : FractionalIdeal R⁰ L)⁻¹ : FractionalIdeal R⁰ L) : Submodule R L).subtype)
        ((1 : FractionalIdeal R⁰ L) : Submodule R L)) = N := by
  let e := invQuotientEquiv (L := L) I hI
  exact ⟨isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective,
    (Nat.card_congr e.toEquiv).trans hcard⟩

end FractionalIdeal


end
