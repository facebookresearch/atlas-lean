/-
Copyright (c) 2026 Andres Barei. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andres Barei
-/
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.RegularityBridge
import Appendix_FixedPoint.BezoutChain.Regularity.Avoid.AssHeightBound
import Appendix_FixedPoint.BezoutChain.Dimension.LocalUnmixed
import Appendix_FixedPoint.BezoutChain.Dimension.PolynomialCatenary
import Appendix_FixedPoint.BezoutChain.Dimension.RegularSequenceDimDrop
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Prime.Defs
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Ideal.Colon
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Defs
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Unmixedness of complete-intersection quotients of polynomial rings

Let `R = MvPolynomial (Fin m) K` with `[Field K]`, let `q : Fin k → R` carry
successive SMul-regularity data (`RegularityBridge.SuccessiveSMulRegular`), and write
`J = Ideal.span (Set.range q)`. The unmixedness goal — the input left open by
the general-Noetherian analysis in `AssHeightBound.lean` (see its
`## Obstruction` section) — is:

> every `P ∈ associatedPrimes R (R ⧸ J)` satisfies `P ∈ J.minimalPrimes`.

## Main results

This file proves every step of that goal available in Mathlib v4.34.0:

* `mem_minimalPrimes_of_successive_zero`: the `k = 0` case (`J = ⊥`, and `R`
  is a domain, so the only associated prime of `R ⧸ ⊥` is `⊥` itself).
* `mem_minimalPrimes_of_successive_singleton`: the `k = 1` case, the new
  polynomial-ring-specific input of this file. Since `R` is a UFD, the
  annihilator of `ā : R ⧸ (f)` is the principal ideal `(f / gcd f a)`; a prime
  `Q` with `(f) ≤ Q ≤ P` contains a prime factor `π₀` of `f`, and `π₀ ∈ P`
  forces every prime factor of `f / gcd f a` to be associate to `π₀`, so
  `P = (π₀) ≤ Q`. This is the polynomial-ring analogue of the
  regular-element height-drop lemma that the general-Noetherian analysis shows
  is false for arbitrary Noetherian local rings.
* `assPrime_quotient_dim_eq_normalization_index`: every `P ∈ Ass(R ⧸ J)`
  satisfies `ringKrullDim (R ⧸ P) = s` for the Noether-normalization index
  `s ≤ m` (normalize `R ⧸ P` and use dimension preservation along integral
  extensions).
* `mem_minimalPrimes_of_localized_quotient_dim_zero`: the minimal-over-`J`
  reformulation — for `P ∈ Ass(R ⧸ J)` it suffices to show the localized
  quotient `R_P ⧸ J_P` has dimension zero (via
  `AssHeightBound.height_eq_add_of_span`, which turns `dim = 0` into
  `P.height = k`, forcing minimality against the global Ass lower bound).

The case `k ≥ 2` remains open; see the trailing `## Obstruction` section for
the precise gap and the route ledger.
-/

local infixl:50 " ~ᵤ " => Associated

namespace EvolutionAlgebras
namespace Appendix_FixedPoint.BezoutChain
/-- Empty regular family (`k = 0`): `J = ⊥`, and since `R` is a domain the only
associated prime of `R ⧸ ⊥` is `⊥` itself, which is minimal over `⊥`. -/
theorem mem_minimalPrimes_of_successive_zero (m : ℕ) (K : Type*) [Field K]
    (q : Fin 0 → MvPolynomial (Fin m) K)
    (_hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K))
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P ∈ J.minimalPrimes := by
  have hrange0 : Set.range q = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨i, rfl⟩
    exact Fin.elim0 i
  have hJbot : J = ⊥ := by rw [hJ, hrange0, Ideal.span_empty]
  subst hJbot
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hmem : IsAssociatedPrime P (_ ⧸ (⊥ : Ideal (MvPolynomial (Fin m) K))) :=
    AssociatedPrimes.mem_iff.mp hP
  have hsub : (⊥ : Submodule (MvPolynomial (Fin m) K)
      (_ ⧸ (⊥ : Ideal (MvPolynomial (Fin m) K)))).IsAssociatedPrime P := hmem
  obtain ⟨hprime, hx0⟩ := hsub
  obtain ⟨x, hx⟩ := hx0
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have haJ : a ∉ (⊥ : Ideal (MvPolynomial (Fin m) K)) := by
    intro hmemJ
    have hx0 : Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin m) K)) a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hmemJ
    have hcol : (⊥ : Submodule (MvPolynomial (Fin m) K)
        (_ ⧸ (⊥ : Ideal (MvPolynomial (Fin m) K)))).colon
        {Ideal.Quotient.mk ⊥ a} = ⊤ := by
      rw [hx0]
      exact Submodule.colon_singleton_zero
    have hPtop : P = ⊤ := by
      rw [hx, hcol]
      exact Ideal.radical_top _
    exact hprime.ne_top hPtop
  have ha0 : a ≠ 0 := fun h => haJ (Ideal.mem_bot.mpr h)
  have hPbot : P = ⊥ := by
    ext r
    rw [hx, Ideal.mem_radical_iff, Ideal.mem_bot]
    constructor
    · rintro ⟨n, hn⟩
      have hsmul : r ^ n • Ideal.Quotient.mk (⊥ : Ideal (MvPolynomial (Fin m) K)) a =
          Ideal.Quotient.mk ⊥ (r ^ n * a) := by
        rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
      rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hsmul,
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hn
      have key : ∀ t : ℕ, r ^ t * a = 0 → r = 0 := by
        intro t
        induction t with
        | zero => intro h; exact absurd (by simpa using h) ha0
        | succ t ih =>
          intro h
          rw [pow_succ'] at h
          rw [mul_assoc] at h
          rcases mul_eq_zero.mp h with h1 | h2
          · exact h1
          · exact ih h2
      have hr0 : r = 0 := key n hn
      exact Ideal.mem_bot.mpr hr0
    · intro hr
      have hr0 : r = 0 := Ideal.mem_bot.mp hr
      refine ⟨1, ?_⟩
      rw [Submodule.mem_colon_singleton, hr0, pow_one, zero_smul]
      exact Submodule.zero_mem _
  rw [hPbot]
  exact ⟨⟨Ideal.isPrime_bot, bot_le⟩, fun Q _ _ => bot_le⟩

/-- Length-one case: for `J = (f)` with `f ≠ 0` (from successive regularity),
every associated prime of `R ⧸ J` is minimal over `J`.

This is the polynomial-ring-specific step that has no general-Noetherian
analogue (see `LocalUnmixed.lean`): it uses that `R` is a UFD, so the
annihilator of `ā : R ⧸ (f)` is the principal ideal spanned by
`f / gcd f a`. A prime `Q` with `(f) ≤ Q ≤ P` contains a prime factor `π₀`
of `f`; since `π₀ ∈ P`, some power `π₀ⁿ` lies in the annihilator, forcing
every prime factor of `f / gcd f a` to be associate to `π₀`. Hence
`P = (π₀) ≤ Q`. -/
theorem mem_minimalPrimes_of_successive_singleton (m : ℕ) (K : Type*) [Field K]
    (q : Fin 1 → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K))
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    P ∈ J.minimalPrimes := by
  set i₀ : Fin 1 := ⟨0, by omega⟩
  have hf0raw := hsucc i₀
  set f : MvPolynomial (Fin m) K := q i₀
  have hrange : Set.range q = {f} := by
    ext r
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      have hii : i = i₀ := by rw [Fin.eq_zero i, Fin.eq_zero i₀]
      exact congrArg q hii
    · intro hr
      exact ⟨i₀, hr.symm⟩
  have hJspan : J = Ideal.span {f} := by rw [hJ, hrange]
  have hempty : Set.image q {j : Fin 1 | j.val < i₀.val} = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro r ⟨j, hj, rfl⟩
    have hlt : j.val < i₀.val := hj
    have hje : j = i₀ := by rw [Fin.eq_zero j, Fin.eq_zero i₀]
    rw [hje] at hlt
    exact lt_irrefl _ hlt
  have hJ00 : Ideal.span (Set.image q {j : Fin 1 | j.val < i₀.val}) = ⊥ := by
    rw [hempty, Ideal.span_empty]
  rw [RegularSequenceDimDrop.span_smul_top, hJ00] at hf0raw
  have hf_ne : f ≠ 0 := by
    intro hcon
    have h10 : f • (0 : MvPolynomial (Fin m) K ⧸
        ((⊥ : Ideal (MvPolynomial (Fin m) K)) : Submodule _ _)) =
        f • Ideal.Quotient.mk (⊥ : Ideal _) 1 := by
      rw [hcon, zero_smul, zero_smul]
    have hcon2 := hf0raw h10
    have hmem1 : (1 : MvPolynomial (Fin m) K) ∈ (⊥ : Ideal _) :=
      Ideal.Quotient.eq_zero_iff_mem.mp hcon2.symm
    exact one_ne_zero (Ideal.mem_bot.mp hmem1)
  have := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hmem : IsAssociatedPrime P (_ ⧸ J) := AssociatedPrimes.mem_iff.mp hP
  have hsub : (⊥ : Submodule _ (_ ⧸ J)).IsAssociatedPrime P := hmem
  obtain ⟨hprime, hx0⟩ := hsub
  obtain ⟨x, hx⟩ := hx0
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have : GCDMonoid (MvPolynomial (Fin m) K) :=
    UniqueFactorizationMonoid.toGCDMonoid _
  obtain ⟨f₁, hf₁⟩ := gcd_dvd_left f a
  obtain ⟨a₁, ha₁⟩ := gcd_dvd_right f a
  set g : MvPolynomial (Fin m) K := GCDMonoid.gcd f a with hg
  have hg0 : g ≠ 0 := by
    intro hcon
    rw [hcon, zero_mul] at hf₁
    exact hf_ne hf₁
  have hrel : IsRelPrime f₁ a₁ := by
    intro d hd1 hda1
    have hgdvd_f : g * d ∣ f := by
      rw [hf₁]
      exact mul_dvd_mul_left g hd1
    have hgdvd_a : g * d ∣ a := by
      rw [ha₁]
      exact mul_dvd_mul_left g hda1
    have hgdvd_g : g * d ∣ g := by
      rw [hg] at hgdvd_f hgdvd_a ⊢
      exact dvd_gcd hgdvd_f hgdvd_a
    obtain ⟨c, hc⟩ := hgdvd_g
    have hdc : d * c = 1 := by
      apply mul_left_cancel₀ hg0
      calc g * (d * c) = (g * d) * c := by ring
        _ = g := hc.symm
        _ = g * 1 := by ring
    exact isUnit_of_dvd_one ⟨c, hdc.symm⟩
  have hcolon : (⊥ : Submodule _ (_ ⧸ J)).colon {Ideal.Quotient.mk J a} =
      Ideal.span {f₁} := by
    have hsmul : ∀ c : MvPolynomial (Fin m) K, c • Ideal.Quotient.mk J a =
        Ideal.Quotient.mk J (c * a) := by
      intro c
      have e := Algebra.smul_def c (Ideal.Quotient.mk J a)
      rw [Ideal.Quotient.algebraMap_eq] at e
      rw [← map_mul] at e
      exact e
    ext r
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, hsmul,
      Ideal.Quotient.eq_zero_iff_mem, hJspan, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    constructor
    · intro hdiv
      obtain ⟨c, hc⟩ := hdiv
      have hcan : r * a₁ = f₁ * c := by
        apply mul_left_cancel₀ hg0
        calc g * (r * a₁) = r * (g * a₁) := by ring
          _ = r * a := by rw [← ha₁]
          _ = f * c := hc
          _ = (g * f₁) * c := by rw [hf₁]
          _ = g * (f₁ * c) := by ring
      have hdiv2 : f₁ ∣ r * a₁ := ⟨c, hcan⟩
      obtain ⟨r', a₁', hr'r, ha₁'a, hfa⟩ := exists_dvd_and_dvd_of_dvd_mul hdiv2
      have ha₁'f₁ : a₁' ∣ f₁ := by
        rw [hfa]
        exact dvd_mul_left a₁' r'
      have hunit : IsUnit a₁' := hrel ha₁'f₁ ha₁'a
      obtain ⟨s, hs⟩ := hr'r
      have hfr : f₁ ∣ r := by
        rw [hfa, hs]
        exact mul_dvd_mul_left r' ((isUnit_iff_forall_dvd.mp hunit) s)
      exact hfr
    · intro hdiv
      obtain ⟨c, hc⟩ := hdiv
      exact ⟨c * a₁, by rw [hc, ha₁, hf₁]; ring⟩
  have hf₁ne : f₁ ≠ 0 := by
    intro hcon
    rw [hcon, mul_zero] at hf₁
    exact hf_ne hf₁
  have hJP : J ≤ P := LocalUnmixed.assPrime_contains_span J P hP
  refine ⟨⟨hprime, hJP⟩, fun Q hQ hQP => ?_⟩
  obtain ⟨hQprime, hQJ⟩ := hQ
  have hfJ : f ∈ J := by
    rw [hJspan]
    exact Ideal.mem_span_singleton_self f
  have hfQ : f ∈ Q := hQJ hfJ
  obtain ⟨S, hSprime, hSprod⟩ := UniqueFactorizationMonoid.exists_prime_factors f hf_ne
  have hprodQ : S.prod ∈ Q := by
    obtain ⟨u, hu⟩ := hSprod
    have hmemU : S.prod * (↑u : MvPolynomial (Fin m) K) ∈ Q := by
      rw [hu]
      exact hfQ
    rw [mul_comm] at hmemU
    exact (Ideal.unit_mul_mem_iff_mem _ (Units.isUnit u)).mp hmemU
  have key : ∀ T : Multiset (MvPolynomial (Fin m) K), T.prod ∈ Q →
      ∃ π ∈ T, π ∈ Q := by
    intro T
    induction T using Multiset.induction with
    | empty =>
      intro h
      simp only [Multiset.prod_zero] at h
      have hQtop : Q = ⊤ := by
        have h1 : Ideal.span {(1 : MvPolynomial (Fin m) K)} ≤ Q :=
          Ideal.span_le.mpr (Set.singleton_subset_iff.mpr h)
        rw [Ideal.span_singleton_one] at h1
        exact top_le_iff.mp h1
      exact (hQprime.ne_top hQtop).elim
    | cons b U ih =>
      intro h
      rw [Multiset.prod_cons] at h
      rcases hQprime.mem_or_mem h with hb | hU
      · exact ⟨b, Multiset.mem_cons_self _ _, hb⟩
      · obtain ⟨π, hπ, hπQ⟩ := ih hU
        exact ⟨π, Multiset.mem_cons_of_mem hπ, hπQ⟩
  obtain ⟨π₀, hπ₀S, hπ₀Q⟩ := key S hprodQ
  have hπ₀prime : Prime π₀ := hSprime π₀ hπ₀S
  have hπ₀dvd : π₀ ∣ f :=
    dvd_trans (Multiset.dvd_prod hπ₀S) hSprod.dvd_dvd.1
  have hπ₀ne : π₀ ≠ 0 := by
    intro hcon
    rw [hcon] at hπ₀dvd
    exact hf_ne (zero_dvd_iff.mp hπ₀dvd)
  have hπ₀P : π₀ ∈ P := hQP hπ₀Q
  rw [hx, hcolon] at hπ₀P
  obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp hπ₀P
  rw [Ideal.mem_span_singleton] at hn
  obtain ⟨T, hTprime, hTprod⟩ :=
    UniqueFactorizationMonoid.exists_prime_factors f₁ hf₁ne
  have hTprime_all : ∀ τ ∈ T, τ ~ᵤ π₀ := by
    intro τ hτ
    have hτdvd : τ ∣ π₀ ^ n :=
      dvd_trans (dvd_trans (Multiset.dvd_prod hτ) hTprod.dvd_dvd.1) hn
    have hτπ : τ ∣ π₀ := (hTprime τ hτ).dvd_of_dvd_pow hτdvd
    have hτirr : Irreducible τ := (hTprime τ hτ).irreducible
    have hπirr : Irreducible π₀ := hπ₀prime.irreducible
    have hback : π₀ ∣ τ := hτirr.dvd_symm hπirr hτπ
    exact associated_of_dvd_dvd hτπ hback
  have hpassoc : ∀ U : Multiset (MvPolynomial (Fin m) K), (∀ τ ∈ U, τ ~ᵤ π₀) →
      U.prod ~ᵤ π₀ ^ U.card := by
    intro U
    induction U using Multiset.induction with
    | empty =>
      intro _
      rw [Multiset.prod_zero, Multiset.card_zero, pow_zero]
    | cons b U ih =>
      intro hall
      rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
      exact (hall b (Multiset.mem_cons_self _ _)).mul_mul
        (ih (fun τ hτ => hall τ (Multiset.mem_cons_of_mem hτ)))
  have hfall : f₁ ~ᵤ π₀ ^ T.card := hTprod.symm.trans (hpassoc T hTprime_all)
  have hspan : Ideal.span {f₁} = Ideal.span {π₀ ^ T.card} :=
    Ideal.span_singleton_eq_span_singleton.mpr hfall
  have htpos : 0 < T.card := by
    rcases Nat.eq_zero_or_pos T.card with h0 | hpos
    · have hTe : T = 0 := Multiset.card_eq_zero.mp h0
      rw [hTe] at hTprod
      simp only [Multiset.prod_zero] at hTprod
      have hunitf : IsUnit f₁ := isUnit_of_dvd_one hTprod.dvd'
      have htop : Ideal.span {f₁} = ⊤ := Ideal.span_singleton_eq_top.mpr hunitf
      have hPtop : P = ⊤ := by
        rw [hx, hcolon, htop]
        exact Ideal.radical_top _
      exact absurd hPtop hprime.ne_top
    · exact hpos
  have hle : Ideal.span {π₀ ^ T.card} ≤ Ideal.span {π₀} := by
    obtain ⟨s, hs⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : T.card ≠ 0)
    rw [Ideal.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rw [hs]
    exact Ideal.mem_span_singleton'.mpr ⟨π₀ ^ s, pow_succ π₀ s⟩
  have hπ₀span_prime : (Ideal.span {π₀}).IsPrime :=
    (Ideal.span_singleton_prime hπ₀ne).mpr hπ₀prime
  have hPeq : P = Ideal.span {π₀} := by
    rw [hx, hcolon, hspan]
    apply le_antisymm
    · calc (Ideal.span {π₀ ^ T.card}).radical
          ≤ (Ideal.span {π₀}).radical := Ideal.radical_mono hle
        _ = Ideal.span {π₀} := hπ₀span_prime.radical
    · rw [Ideal.span_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [SetLike.mem_coe, Ideal.mem_radical_iff]
      exact ⟨T.card, Ideal.mem_span_singleton_self _⟩
  have hPQ : P ≤ Q := by
    rw [hPeq]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hπ₀Q)
  exact hPQ

/-- Normalization-dimension description of associated primes: for
`P ∈ Ass(R ⧸ J)` — `J` any ideal, so in particular a complete
intersection — `P ≠ ⊤`, hence Noether normalization presents `R ⧸ P` as
integral over `MvPolynomial (Fin s) K` for some `s ≤ m`, and dimension
preservation along integral extensions gives `ringKrullDim (R ⧸ P) = s`.
This pins the remaining unmixedness goal to a height computation, which still
needs the catenary lower bound (see `## Obstruction`). -/
theorem assPrime_quotient_dim_eq_normalization_index (m : ℕ) (K : Type*) [Field K]
    (J : Ideal (MvPolynomial (Fin m) K))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J)) :
    ∃ s ≤ m, ringKrullDim (MvPolynomial (Fin m) K ⧸ P) = (s : WithBot ℕ∞) := by
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hPtop : P ≠ ⊤ := hprime.ne_top
  exact dim_quotient_eq_normalization_index K m P hPtop

/-- Minimal-over-`J` reformulation: for `P ∈ Ass(R ⧸ J)` with `J` spanned by a
successive-regular family, it suffices to show the localized quotient
`R_P ⧸ J_P` has Krull dimension zero. Indeed `AssHeightBound.height_eq_add_of_span`
then gives `P.height = k`, while every prime `Q` with `J ≤ Q ≤ P` has height
at least `k` (the global Ass lower bound) and at most `P.height`; a strict
`Q < P` would raise height by one, so `Q = P`. -/
theorem mem_minimalPrimes_of_localized_quotient_dim_zero (m k : ℕ) (K : Type*)
    [Field K]
    (q : Fin k → MvPolynomial (Fin m) K)
    (hsucc : RegularityBridge.SuccessiveSMulRegular q)
    (J : Ideal (MvPolynomial (Fin m) K)) (hJ : J = Ideal.span (Set.range q))
    (P : Ideal (MvPolynomial (Fin m) K)) [P.IsPrime]
    (hP : P ∈ associatedPrimes _ (_ ⧸ J))
    (hdim : ringKrullDim (Localization.AtPrime P ⧸
      Ideal.span (Set.range (algebraMap (MvPolynomial (Fin m) K)
        (Localization.AtPrime P) ∘ q))) = 0) :
    P ∈ J.minimalPrimes := by
  have hJP : J ≤ P := LocalUnmixed.assPrime_contains_span J P hP
  have hJPspan : Ideal.span (Set.range q) ≤ P := hJ ▸ hJP
  have hcount := AssHeightBound.height_eq_add_of_span q hsucc P hJPspan
  have hcast : (P.height : WithBot ℕ∞) = ((k : ℕ) : WithBot ℕ∞) := by
    rw [hcount, hdim, zero_add]
  have hPk : P.height = (k : ℕ∞) := by exact_mod_cast hcast
  have hprime : P.IsPrime := (AssociatedPrimes.mem_iff.mp hP).isPrime
  have hlow : ∀ Q : Ideal (MvPolynomial (Fin m) K), Q.IsPrime → J ≤ Q →
      (k : ℕ∞) ≤ Q.height := by
    intro Q hQi hJQ
    have := hQi
    have hJQspan : Ideal.span (Set.range q) ≤ Q := hJ ▸ hJQ
    exact AssHeightBound.le_height_of_span_of_successive q hsucc Q hJQspan
  refine ⟨⟨hprime, hJP⟩, fun Q hQ hQP => ?_⟩
  obtain ⟨hQprime, hQJ⟩ := hQ
  have := hQprime
  have hleQ : (k : ℕ∞) ≤ Q.height := hlow Q hQprime hQJ
  by_contra hne
  have hne' : Q ≠ P := by
    rintro rfl
    exact hne le_rfl
  have hlt : Q < P := lt_of_le_of_ne hQP hne'
  have hstep := Ideal.height_add_one_le_of_lt_of_isPrime hlt
  rw [hPk] at hstep
  have hcon : Q.height + 1 ≤ (k : ℕ∞) := hstep
  have hplus : (k : ℕ∞) + 1 ≤ Q.height + 1 := by gcongr
  have hcon2 : (k : ℕ∞) + 1 ≤ (k : ℕ∞) := le_trans hplus hcon
  rw [← Nat.cast_one, ← Nat.cast_add] at hcon2
  exact absurd (Nat.cast_le.mp hcon2) (by omega)

/-! ## Obstruction (the remaining gap: `k ≥ 2`)

The target interface theorem,
```
theorem unmixed_of_successive_regular (m k: ℕ) (K: Type*) [Field K]
    (q: Fin k → MvPolynomial (Fin m) K)
    (hsucc: RegularityBridge.SuccessiveSMulRegular q)
    (J: Ideal (MvPolynomial (Fin m) K))
    (hJ: J = Ideal.span (Set.range q))
    (P: Ideal (MvPolynomial (Fin m) K))
    (hP: P ∈ associatedPrimes _ (_ ⧸ J)):
    P ∈ J.minimalPrimes
```
is proved here for `k = 0` (`mem_minimalPrimes_of_successive_zero`) and
`k = 1` (`mem_minimalPrimes_of_successive_singleton`); the case `k ≥ 2`
remains open, for a structural reason rather than a missing trick.

Why the `k = 1` argument does not iterate: after quotienting by the first
generator, the ring `R ⧸ (q₀)` is no longer a polynomial ring (hence no
longer a UFD), so the annihilator-principal argument cannot be reapplied to
the images of the remaining generators. The standard induction instead goes
through Cohen–Macaulay theory (a quotient of a CM ring by a regular element
is CM; CM rings are unmixed), and Mathlib v4.34.0 has no Cohen–Macaulay /
unmixed / grade API (verified: the only `Unmixed` hits are the unrelated
`ComplexEmbedding.IsUnmixed` about number fields; the only grade-adjacent
hits are graded/filtered-algebra false positives). The regular/depth
fragments that do exist — `IsRegular`/`IsWeaklyRegular` in
`Mathlib/RingTheory/Regular/RegularSequence.lean` and the Rees theorem
(`ModuleCat.exists_isRegular_tfae`) in `Mathlib/RingTheory/Depth/Rees.lean`
— do not unblock this: there is no `CohenMacaulay` class and no
UFD-quotient CM fragment (CM-ness of `R ⧸ (q₀)`) to carry the induction.

Route ledger:

* (a) filter-regular/grade style: blocked, no grade API (as above).
* (b) Noether normalization + going-down: half-proved as
  `assPrime_quotient_dim_eq_normalization_index` (normalization presents
  `R ⧸ P` as integral over `MvPolynomial (Fin s) K`, so
  `ringKrullDim (R ⧸ P) = s ≤ m` by chunk B2). Going-down/lying-over only
  reproduces the `≤` direction of catenary (cf. `PolynomialCatenary.lean`); the
  `≥` direction — long chains below `P`, i.e. the catenary lower bound —
  is exactly what is still missing, now pinned to: for `P ∈ Ass(R ⧸ J)`,
  `(m : WithBot ℕ∞) ≤ P.height + s` where `s` is the normalization index.
* (c) induction on `k` via `isRegular_cons_iff` + annihilator-subset-Ass
  (`AssociatedPrime/Localization.lean`): the `k = 1` step is now supplied
  for polynomial rings by `mem_minimalPrimes_of_successive_singleton`
  (the regular-element height-drop for principal ideals via UFD structure),
  but the induction step needs the same statement in `R ⧸ (q₀)`, which is
  not available. The localization tools
  (`minimalPrimes_annihilator_subset_associatedPrimes`,
  `mem_associatedPrimes_atPrime_of_mem_associatedPrimes`) were deliberately
  not imported: they transport in the wrong direction for this (their
  content is the general-Noetherian part, which attempt 1 already
  exhausted).
* Minimal-over-`J` reformulation: proved as
  `mem_minimalPrimes_of_localized_quotient_dim_zero`, reducing the target to
  `ringKrullDim (R_P ⧸ J_P) = 0`. Closing that from `P ∈ Ass` is equivalent
  to minimality itself (attempt 1's equation), so this only repackages the
  goal for a consumer with dimension-zero input; it does not advance it.

Precise next target: either supply the catenary lower bound for
`P ∈ Ass(R ⧸ J)` (normalization-route endgame), or formalize "quotients of a
UFD by a prime element are …" style Cohen–Macaulay fragments sufficient to push
the induction past `k = 1`. Neither is available in Mathlib v4.34.0 as of this
writing.

## References

Project (`Formalization/Appendix_FixedPoint/BezoutChain/`):
* `RegularityBridge.lean`: `RegularityBridge.SuccessiveSMulRegular`,
  `RegularityBridge.isRegular_ofFn_of_successive` (not needed here),
  `RegularityBridge.span_range_eq_ofList_ofFn` (not needed here).
* `RegularSequenceDimDrop.lean`: `RegularSequenceDimDrop.span_smul_top`,
  `RegularSequenceDimDrop.ringKrullDim_atPrime_quotient_span_add_of_successive`
  (used via `AssHeightBound`).
* `LocalUnmixed.lean`: `LocalUnmixed.assPrime_contains_span` (every
  associated prime contains `J`).
* `AssHeightBound.lean`: `AssHeightBound.height_eq_add_of_span`,
  `AssHeightBound.le_height_of_span_of_successive`.
* `PolynomialCatenary.lean`: `dim_quotient_eq_normalization_index` (bare `BezoutChain`
  namespace, as here).

Mathlib (`Mathlib/RingTheory/Ideal/AssociatedPrime/Basic.lean`):
* `associatedPrimes`, `AssociatedPrimes.mem_iff`, `IsAssociatedPrime`,
  `IsAssociatedPrime.isPrime`, `Submodule.IsAssociatedPrime`
  (`eq_radical_colon`).

Mathlib (`Mathlib/RingTheory/Ideal/MinimalPrime/Basic.lean`):
* `Ideal.minimalPrimes`, `Ideal.IsMinimalPrime` (a `Minimal` predicate).

Mathlib (`Mathlib/RingTheory/Ideal/Colon.lean`):
* `Submodule.mem_colon_singleton`, `Submodule.colon_singleton_zero`.

Mathlib (`Mathlib/RingTheory/Ideal/Quotient/Basic.lean`):
* `Ideal.Quotient.mk_surjective`, `Ideal.Quotient.eq_zero_iff_mem`,
  `Ideal.Quotient.algebraMap_eq`.

Mathlib (`Mathlib/RingTheory/Ideal/Span.lean`):
* `Ideal.span_empty`, `Ideal.span_le`, `Ideal.mem_span_singleton`,
  `Ideal.mem_span_singleton'`, `Ideal.mem_span_singleton_self`,
  `Ideal.span_singleton_eq_top`, `Ideal.span_singleton_one`,
  `Ideal.span_singleton_eq_span_singleton`.

Mathlib (`Mathlib/RingTheory/Ideal/Operations.lean`):
* `Ideal.mem_radical_iff`, `Ideal.radical_top`, `Ideal.radical_mono`,
  `Ideal.IsPrime.radical`.

Mathlib (`Mathlib/RingTheory/Ideal/Prime.lean`):
* `Ideal.IsPrime.ne_top`, `Ideal.IsPrime.mem_or_mem`.

Mathlib (`Mathlib/RingTheory/Ideal/Maximal.lean`):
* `Ideal.span_singleton_prime`.

Mathlib (`Mathlib/RingTheory/Ideal/Height.lean`):
* `Ideal.height_add_one_le_of_lt_of_isPrime`.

Mathlib core / Batteries (no import needed):
* `Multiset.induction`, `Multiset.prod_zero`, `Multiset.prod_cons`,
  `Multiset.card_zero`, `Multiset.card_cons`, `Multiset.card_eq_zero`,
  `Multiset.dvd_prod`, `Multiset.mem_cons_self`, `Multiset.mem_cons_of_mem`,
  `SetLike.mem_coe`, `Set.mem_singleton_iff`, `Set.singleton_subset_iff`,
  `Set.eq_empty_iff_forall_notMem`, `top_le_iff`, `Fin.elim0`, `Fin.eq_zero`.

Mathlib (`Mathlib/RingTheory/Polynomial/UniqueFactorization.lean`):
* `MvPolynomial.uniqueFactorizationMonoid`.

Mathlib (`Mathlib/RingTheory/UniqueFactorizationDomain/Defs.lean`):
* `UniqueFactorizationMonoid.exists_prime_factors`.

Mathlib (`Mathlib/RingTheory/UniqueFactorizationDomain/GCDMonoid.lean`):
* `UniqueFactorizationMonoid.toGCDMonoid`, instance `IsGCDMonoid` of a UFD.

Mathlib (`Mathlib/Algebra/GCDMonoid/Basic.lean`):
* `gcd`, `gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`,
  instance `DecompositionMonoid` of `IsGCDMonoid`.

Mathlib (`Mathlib/Algebra/Divisibility/Basic.lean`):
* `exists_dvd_and_dvd_of_dvd_mul`, `mul_dvd_mul_left`.

Mathlib (`Mathlib/Algebra/Divisibility/Units.lean`):
* `IsRelPrime`, `isUnit_of_dvd_one`, `isUnit_iff_forall_dvd`.

Mathlib (`Mathlib/Algebra/GroupWithZero/Associated.lean`):
* `associated_of_dvd_dvd`, `Associated.mul_mul`, `Associated.refl`,
  `Associated.dvd_dvd` (`.dvd`, `.dvd'`), `Associated.symm/trans`.

Mathlib (`Mathlib/Algebra/Prime/Defs.lean`):
* `Prime.dvd_of_dvd_pow`, `Prime.irreducible`, `Irreducible.dvd_symm`.

Mathlib (`Mathlib/Algebra/Regular/SMul.lean`, via `RegularityBridge`):
* `IsSMulRegular` (injective smul; used through `hsucc i₀`).

Mathlib (`Mathlib/Algebra/EuclideanDomain/Field.lean`,
`Mathlib/RingTheory/PrincipalIdealDomain.lean`):
* `Field.toEuclideanDomain`, `EuclideanDomain.instIsPrincipalIdealRing`
  (instance chain `Field K → UniqueFactorizationMonoid K` feeding the
  `MvPolynomial` UFD instance).
-/

end Appendix_FixedPoint.BezoutChain
end EvolutionAlgebras
