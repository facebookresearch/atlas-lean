/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Prime.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Elementary Macaulay unmixedness for pairs via UFD factorization

Let `R` be a commutative domain with unique factorization and let
`q : Fin 2 → R` be a successive-regular pair in the sense of
`RegularityBridge.SuccessiveSMulRegular`. This file develops the unconditional
setup for the length-two case of Macaulay unmixedness: it factors the
first generator into primes, shows the second generator avoids each
prime divisor (a zerodivisor-witness argument that has no analogue in
the `k = 1` colon computation), shows every prime over `(f, g)` contains
a prime factor of `f`, and proves that every associated prime of the
quotient is minimal over the pair ideal under one explicit residual
hypothesis (`unmixed_pair_of_prime_over_minimal`).

All results in this file are fully proved.

## Main results

* `pair_fst_ne_zero`: the first generator of a successive pair is nonzero.
* `pair_snd_regular_on_span_fst`: the second generator is regular on
  `R ⧸ span {f}` (successive data rewritten to principal-quotient shape).
* `snd_avoids_prime_dvd`: if `π` is prime with `π ∣ f` and `g` is regular
  on `R ⧸ (f)`, then `g ∉ (π)`. Proof: the cofactor `c = f / π` is the
  witness — `c ∉ (f)` (else `π` is a unit) while `g • c ∈ (f)` (since
  `g ∈ (π)` gives `g * c = h * f`), against regularity via
  `mem_of_isSMulRegular_quotient_of_smul_mem`.
* `exists_prime_factor_mem`: every prime containing nonzero `f` contains a
  prime factor `π ∣ f` (factorization + prime induction on the multiset).
* `isRelPrime_of_successive_pair`: `f, g` are coprime (any common divisor has
  a prime factor, against avoidance).
* `unmixed_pair_of_prime_over_minimal`: every `P ∈ Ass(R ⧸ J)` is minimal
  over `J`, under the explicit hypothesis that each such `P` is minimal
  over every `span {π, g}` it contains (`π ∣ f` prime). This hypothesis is
  the `k = 1` step inside `R ⧸ (π)` restated in `R`, so no
  quotient-prime correspondence is needed.

## Remarks on the residual hypothesis

The endgame above is conditional, and the hypothesis is the genuine
content: unmixedness does not propagate across quotients in general, so
the `k = 1` unique-factorization argument cannot simply be reapplied
inside `R ⧸ (π)` (see the discussion in `VariableInductionCM.lean` §4 (i), which
notes that minimality at `k ≥ 2` is genuine Cohen–Macaulay content, not
bookkeeping). Three natural routes to discharging the hypothesis fail,
each with recorded evidence (see the appendix in `MacaulayScoped`):

* (F1) Transferring `Ass` across the quotient map `R → R ⧸ (π)`: Mathlib
  provides no lemma moving associated primes across a ring quotient (stuck
  at `⊢ Q.comap (Ideal.Quotient.mk (Ideal.span {π})) ∈ associatedPrimes _ _`).
* (F2) Localizing at `(π)`: `g` avoids `(π)` by the result above, hence is
  a unit in `R_(π)`, so `(f, g)` localizes to `⊤` and the localized
  equation is vacuous.
* (F3) Replaying the `k = 1` colon computation: `(J : 1) = J` is
  two-generated, not principal, even for the regular pair `x, y` in
  `k[x, y]` — the `f / gcd` computation has no analogue at `k = 2`.

## Scope

Every unconditional result here uses the domain and unique-factorization
structure of `R` essentially (factorization, primality of `π`,
cancellation of a nonzero cofactor). In particular, none of these steps
applies over a base that is neither a domain nor a UFD, and the
conditional endgame takes the `R ⧸ (π)`-minimality as an explicit
hypothesis rather than assuming any quotient-propagation principle.

## Dependencies

This file depends only on the leaves `RegularityBridge`,
`LocalUnmixed`, and `RegularSequenceDimDrop` (no `Statement/Statement`, no `GradeDepthFragment`,
no `Geometry`/`Bridge`, no `TriangularRegularity`/`MkSystemRegular`). The Mathlib
imports are narrow; see References.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):
* `Regularity/Avoid/RegularityBridge.lean`: `RegularityBridge.SuccessiveSMulRegular`.
* `Dimension/LocalUnmixed.lean`: `LocalUnmixed.assPrime_contains_span`.
* `Dimension/RegularSequenceDimDrop.lean`: `RegularSequenceDimDrop.span_smul_top`.

Mathlib v4.34.0 (with source locations):
* `IsSMulRegular` (`Algebra/Regular/SMul.lean`, via `IsSMulRegular.lean`);
  `mem_of_isSMulRegular_quotient_of_smul_mem`,
  `isSMulRegular_quotient_iff_mem_of_smul_mem`
  (`RingTheory/Regular/IsSMulRegular.lean,92`).
* `Prime.ne_zero`, `Prime.not_isUnit`, `Prime.dvd_or_dvd`
  (`Algebra/Prime/Defs.lean,54,65`).
* `UniqueFactorizationMonoid.exists_prime_factors`
  (`RingTheory/UniqueFactorizationDomain/Defs.lean`).
* `Associated` (`Algebra/GroupWithZero/Associated.lean`).
* `isUnit_of_dvd_one`, `IsRelPrime`
  (`Algebra/Divisibility/Units.lean`).
* `Ideal.mul_mem_left`, `Ideal.unit_mul_mem_iff_mem`
  (`RingTheory/Ideal/Defs.lean,75`).
* `Ideal.mem_span_singleton`, `Ideal.mem_span_singleton_self`,
  `Ideal.span_empty`, `Ideal.span_le`, `Ideal.subset_span`
  (`RingTheory/Ideal/Span.lean,181`).
* `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.mk`
  (`RingTheory/Ideal/Quotient/Defs.lean`).
* `associatedPrimes`, `AssociatedPrimes.mem_iff`
  (`RingTheory/Ideal/AssociatedPrime/Basic.lean,108`).
* `Ideal.minimalPrimes`, `Ideal.IsMinimalPrime`
  (`RingTheory/Ideal/MinimalPrime/Basic.lean,57`).
* `smul_eq_mul` (`Algebra/Group/Action/Defs.lean`, core action API).
-/

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
namespace MacaulayTwo

variable {R : Type*} [CommRing R]

/-- The first generator of a successive pair is nonzero: the span before
index `0` is empty, so the successive data is regularity on `R ⧸ ⊥`, and
`f = 0` would identify `0` with `mk 1`. -/
theorem pair_fst_ne_zero [IsDomain R] {q : Fin 2 → R}
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) : q ⟨0, by omega⟩ ≠ 0 := by
  set i₀ : Fin 2 := ⟨0, by omega⟩ with hi₀
  have hf0raw := hsucc i₀
  have hempty : Set.image q { j : Fin 2 | j.val < i₀.val } = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨j, hj, rfl⟩
    have hlt : j.val < 0 := hj
    exact Nat.not_lt_zero _ hlt
  have hJ00 : Ideal.span (Set.image q { j : Fin 2 | j.val < i₀.val }) = ⊥ := by
    rw [hempty, Ideal.span_empty]
  rw [RegularSequenceDimDrop.span_smul_top, hJ00] at hf0raw
  intro hcon
  have h10 : q i₀ • (0 : R ⧸ ((⊥ : Ideal R) : Submodule R R)) =
      q i₀ • Ideal.Quotient.mk (⊥ : Ideal R) 1 := by
    rw [hcon, zero_smul, zero_smul]
  have hcon2 := hf0raw h10
  have hmem1 : (1 : R) ∈ (⊥ : Ideal R) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hcon2.symm
  exact one_ne_zero (Ideal.mem_bot.mp hmem1)

/-- Successive data at index `1` in principal-quotient form: `g` is regular
on `R ⧸ span {f}`. The span before index `1` is exactly `{f}`. -/
theorem pair_snd_regular_on_span_fst {q : Fin 2 → R}
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) :
    IsSMulRegular (R ⧸ Ideal.span {q ⟨0, by omega⟩}) (q ⟨1, by omega⟩) := by
  set i₀ : Fin 2 := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin 2 := ⟨1, by omega⟩ with hi₁
  have hreg := hsucc i₁
  have h01 : i₀.val < i₁.val := by
    rw [hi₀, hi₁]
    exact Nat.zero_lt_one
  have hspan : Ideal.span (Set.image q { j : Fin 2 | j.val < i₁.val }) =
      Ideal.span {q i₀} := by
    congr 1
    ext r
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨j, hj, rfl⟩
      have h1 : j.val < 1 := hj
      have hj0 : j.val = 0 := by omega
      have hje : j = i₀ := Fin.ext hj0
      rw [hje]
    · intro hr
      rw [hr]
      exact ⟨i₀, h01, rfl⟩
  rw [hspan, RegularSequenceDimDrop.span_smul_top] at hreg
  exact hreg

/-- Prime avoidance for successive pairs: if `π` is prime dividing `f` and
`g` is regular on `R ⧸ (f)`, then `g ∉ (π)`. The witness is the cofactor
`c = f / π`: `c ∉ (f)` (else `π` is a unit, by cancelling `c ≠ 0` in the
domain), while `g ∈ (π)` forces `g • c = h * f ∈ (f)`, against regularity.
Uses only the domain structure and primality of `π`. -/
theorem snd_avoids_prime_dvd [IsDomain R] {f g : R} (_hf : f ≠ 0)
    (hreg : IsSMulRegular (R ⧸ Ideal.span {f}) g)
    {π : R} (hprime : Prime π) (hdvd : π ∣ f) :
    g ∉ Ideal.span {π} := by
  have hπ0 : π ≠ 0 := hprime.ne_zero
  obtain ⟨c, hc⟩ := hdvd
  have hc0 : c ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hc
    exact _hf hc
  have hc_notmem : c ∉ Ideal.span {f} := by
    intro hmem
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨d, hd⟩ := hmem
    have heq' : c = c * (π * d) := by
      conv_lhs => rw [hd, hc]
      ring
    have heq : c * 1 = c * (π * d) := by rw [mul_one]; exact heq'
    have hunit_eq : (1 : R) = π * d := mul_left_cancel₀ hc0 heq
    have hunit : IsUnit π := isUnit_of_dvd_one ⟨d, hunit_eq⟩
    exact hprime.not_isUnit hunit
  intro hmem
  rw [Ideal.mem_span_singleton] at hmem
  obtain ⟨h, hh⟩ := hmem
  have hsmul_mem : g • c ∈ ((Ideal.span {f} : Ideal R) : Submodule R R) := by
    rw [smul_eq_mul]
    have hgc : g * c = h * f := by rw [hh, hc]; ring
    rw [hgc]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)
  have hcon := mem_of_isSMulRegular_quotient_of_smul_mem hreg hsmul_mem
  exact hc_notmem hcon

/-- Every prime ideal containing a nonzero `f` over a UFD contains a prime
factor `π ∣ f`. Proof: factor `f`, push the factor product into `Q` across
the associated unit, then induct on the multiset using primality. -/
theorem exists_prime_factor_mem [IsDomain R] [UniqueFactorizationMonoid R]
    {f : R} (hf : f ≠ 0) {Q : Ideal R} [Q.IsPrime] (hfQ : f ∈ Q) :
    ∃ π, Prime π ∧ π ∣ f ∧ π ∈ Q := by
  obtain ⟨S, hSprime, hSprod⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors f hf
  have hprodQ : S.prod ∈ Q := by
    obtain ⟨u, hu⟩ := hSprod
    have hmemU : S.prod * (↑u : R) ∈ Q := by
      rw [hu]
      exact hfQ
    rw [mul_comm] at hmemU
    exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit u)).mp hmemU
  have key : ∀ T : Multiset R, T.prod ∈ Q → ∃ π ∈ T, π ∈ Q := by
    intro T
    induction T using Multiset.induction with
    | empty =>
      intro h
      simp only [Multiset.prod_zero] at h
      have hQtop : Q = ⊤ := by
        have h1 : Ideal.span {(1 : R)} ≤ Q :=
          Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
        rw [Ideal.span_singleton_one] at h1
        exact top_le_iff.mp h1
      exact (‹Q.IsPrime›.ne_top hQtop).elim
    | cons b U ih =>
      intro h
      rw [Multiset.prod_cons] at h
      rcases ‹Q.IsPrime›.mem_or_mem h with hb | hU
      · exact ⟨b, Multiset.mem_cons_self _ _, hb⟩
      · obtain ⟨π, hπ, hπQ⟩ := ih hU
        exact ⟨π, Multiset.mem_cons_of_mem hπ, hπQ⟩
  obtain ⟨π₀, hπ₀S, hπ₀Q⟩ := key S hprodQ
  have hπ₀prime : Prime π₀ := hSprime π₀ hπ₀S
  have hπ₀dvd : π₀ ∣ f :=
    dvd_trans (Multiset.dvd_prod hπ₀S) hSprod.dvd_dvd.1
  exact ⟨π₀, hπ₀prime, hπ₀dvd, hπ₀Q⟩

/-- A successive pair is coprime: any common divisor has a prime factor
(using unique factorization), which would put `g` in `(π)`, contradicting
`snd_avoids_prime_dvd`. -/
theorem isRelPrime_of_successive_pair [IsDomain R]
    [UniqueFactorizationMonoid R] {q : Fin 2 → R}
    (hsucc : RegularityBridge.SuccessiveSMulRegular q) :
    IsRelPrime (q ⟨0, by omega⟩) (q ⟨1, by omega⟩) := by
  intro d hdvd0 hdvd1
  by_cases hunit : IsUnit d
  · exact hunit
  · have hf0 : q ⟨0, by omega⟩ ≠ 0 := pair_fst_ne_zero hsucc
    have hreg := pair_snd_regular_on_span_fst hsucc
    have hd0 : d ≠ 0 := by
      intro hcon
      rw [hcon] at hdvd0
      exact hf0 (zero_dvd_iff.mp hdvd0)
    obtain ⟨S, hSprime, hSprod⟩ :=
      UniqueFactorizationMonoid.exists_prime_factors d hd0
    have hSne : S ≠ 0 := by
      intro hSe
      rw [hSe] at hSprod
      simp only [Multiset.prod_zero] at hSprod
      exact hunit (isUnit_of_dvd_one hSprod.dvd')
    obtain ⟨π, hπS⟩ := Multiset.exists_mem_of_ne_zero hSne
    have hπprime : Prime π := hSprime π hπS
    have hπd : π ∣ d := dvd_trans (Multiset.dvd_prod hπS) hSprod.dvd_dvd.1
    have hπf : π ∣ q ⟨0, by omega⟩ := dvd_trans hπd hdvd0
    have hπg : π ∣ q ⟨1, by omega⟩ := dvd_trans hπd hdvd1
    have hgmem : q ⟨1, by omega⟩ ∈ Ideal.span {π} :=
      Ideal.mem_span_singleton.mpr hπg
    have havoid := snd_avoids_prime_dvd hf0 hreg hπprime hπf
    exact absurd hgmem havoid

/-- Conditional endgame for pairs: every `P ∈ Ass(R ⧸ J)` is minimal over
`J`, under the hypothesis that each such `P` is minimal over every
`span {π, g}` it contains (`π ∣ f` prime). Proof: any `Q` with `J ≤ Q ≤ P`
contains `f`, hence a prime factor `π ∈ Q` (which also lies in `P`), so
`span {π, g} ≤ Q ≤ P` and the hypothesis forces `P ≤ Q`. The hypothesis is
exactly the `k = 1` step inside `R ⧸ (π)` restated in `R`, so no
quotient-prime correspondence is needed. -/
theorem unmixed_pair_of_prime_over_minimal [IsDomain R]
    [UniqueFactorizationMonoid R] {q : Fin 2 → R}
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal R) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal R) [P.IsPrime]
    (hP : P ∈ associatedPrimes R (R ⧸ J))
    (hmin : ∀ π : R, Prime π → π ∣ q ⟨0, by omega⟩ → π ∈ P →
      P ∈ (Ideal.span ({π, q ⟨1, by omega⟩} : Set R)).minimalPrimes) :
    P ∈ J.minimalPrimes := by
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hJP : J ≤ P := LocalUnmixed.assPrime_contains_span J P hP
  have hf0 : q ⟨0, by omega⟩ ≠ 0 := pair_fst_ne_zero hsucc
  refine ⟨⟨hprime, hJP⟩, fun Q hQ hQP => ?_⟩
  obtain ⟨hQprime, hQJ⟩ := hQ
  have hfJ : q ⟨0, by omega⟩ ∈ J := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_range_self _)
  have hgJ : q ⟨1, by omega⟩ ∈ J := by
    rw [hJ]
    exact Ideal.subset_span (Set.mem_range_self _)
  have hfQ : q ⟨0, by omega⟩ ∈ Q := hQJ hfJ
  have hgQ : q ⟨1, by omega⟩ ∈ Q := hQJ hgJ
  obtain ⟨π, hπprime, hπdvd, hπQ⟩ := exists_prime_factor_mem hf0 hfQ
  have hπP : π ∈ P := hQP hπQ
  have hminP : P ∈ (Ideal.span ({π, q ⟨1, by omega⟩} : Set R)).minimalPrimes :=
    hmin π hπprime hπdvd hπP
  have hminP' : (Ideal.span ({π, q ⟨1, by omega⟩} : Set R)).IsMinimalPrime P :=
    hminP
  have hQspan : Ideal.span ({π, q ⟨1, by omega⟩} : Set R) ≤ Q := by
    apply Ideal.span_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hπQ
    · exact hgQ
  exact hminP'.2 ⟨hQprime, hQspan⟩ hQP

end MacaulayTwo
end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
