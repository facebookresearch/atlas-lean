/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.Data.Nat.Nth
public import MathlibExt.NumberTheory.Schatunowsky
public import MathlibExt.NumberTheory.SchatunowskyImaginaryQuadratic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Norm.AbsNorm

/-!
# Decomposition of the Schatunowsky set

The Schatunowsky set `quadSchatunowskySet K ℓ` of an imaginary quadratic field of class
number one is the union, over `1 ≤ n ≤ n₀`, of the sets of algebraic integers whose norm
lies strictly above `quadPrimeNorm K (n - 1) ^ (ℓ + 1)` and at most
`quadPrimeNorm K n ^ (ℓ + 1)` and that lie in every nonzero prime ideal of norm at most
`quadPrimeNorm K (n - 1)`, when the prime norm powers eventually fall below the primorial
norms (`quadSchatunowskySet_eq_iUnion`).

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for
Imaginary Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110.
-/

open NumberField

namespace MetaMathlibExt

@[expose] public section

namespace quadSchatunowskySet_eq_iUnion

/-- The set of absolute norms of nonzero prime ideals of a number field is infinite:
above every rational prime there is a prime ideal whose norm is divisible by that prime. -/
private theorem primeNormSet_infinite {K : Type*} [Field K] [NumberField K] :
    (Set.ofPred (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧
      Ideal.absNorm P = x)).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨p, hpB, hp⟩ := Nat.exists_infinite_primes (B + 1)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨Q, hQmax, hQlies⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (R := ℤ) (S := 𝓞 K)
      (Ideal.span {(p : ℤ)})
  have hQunder : Ideal.span {(p : ℤ)} = Ideal.under ℤ Q := (Ideal.liesOver_iff Q _).mp hQlies
  have hQprime : Q.IsPrime := hQmax.isPrime
  have hspanbot : Ideal.span {(p : ℤ)} ≠ ⊥ := by
    rw [ne_eq, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have hQbot : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hspanbot Q
  have hnorm : Ideal.absNorm (Ideal.under ℤ Q) = p := by
    rw [← hQunder]
    simp [Ideal.absNorm_span_singleton]
  have hdvd : p ∣ Ideal.absNorm Q := hnorm ▸ Int.absNorm_under_dvd_absNorm Q
  have hpos : 0 < Ideal.absNorm Q := by
    rw [Nat.pos_iff_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff]
    exact hQbot
  have hle : p ≤ Ideal.absNorm Q := Nat.le_of_dvd hpos hdvd
  have hmem : Ideal.absNorm Q ∈ Set.ofPred
      (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) :=
    ⟨Q, hQprime, hQbot, rfl⟩
  have hle' := hB hmem
  omega

/-- For `m ≠ 0`, the prime norm `quadPrimeNorm K m` is the `(m - 1)`-st element of the
set of prime ideal norms. -/
private theorem primeNorm_eq_nth_of_ne_zero {K : Type*} [Field K] [NumberField K] {m : ℕ}
    (hm : m ≠ 0) : quadPrimeNorm K m =
      Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) (m - 1) := by
  simp [quadPrimeNorm, hm]

/-- Every prime norm is at least one: the zeroth prime norm is one, and the others are
absolute norms of nonzero prime ideals. -/
private theorem primeNorm_ge_one {K : Type*} [Field K] [NumberField K] (m : ℕ) :
    1 ≤ quadPrimeNorm K m := by
  by_cases hm : m = 0
  · rw [hm, quadPrimeNorm_zero]
  · rw [primeNorm_eq_nth_of_ne_zero hm]
    have hmem := Nat.nth_mem_of_infinite (primeNormSet_infinite (K := K)) (m - 1)
    obtain ⟨P, hPprime, hPne, hPeq⟩ := hmem
    have hne : Ideal.absNorm P ≠ 0 := fun h => hPne (Ideal.absNorm_eq_zero_iff.mp h)
    omega

/-- A prime ideal norm above `quadPrimeNorm K (n - 1)` is at least `quadPrimeNorm K n`. -/
private theorem primeNorm_le_of_mem_gt {K : Type*} [Field K] [NumberField K] (n : ℕ)
    (hn : 1 ≤ n) (Q : Ideal (𝓞 K)) (hQprime : Q.IsPrime) (hQne : Q ≠ ⊥)
    (hgt : quadPrimeNorm K (n - 1) < Ideal.absNorm Q) :
    quadPrimeNorm K n ≤ Ideal.absNorm Q := by
  have hQmem : ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = Ideal.absNorm Q :=
    ⟨Q, hQprime, hQne, rfl⟩
  have hmem : Ideal.absNorm Q ∈ Set.ofPred
      (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) := hQmem
  obtain ⟨k, hk⟩ := Nat.subset_range_nth hmem
  have hnth : quadPrimeNorm K n =
      Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) (n - 1) :=
    primeNorm_eq_nth_of_ne_zero (by omega)
  rw [hnth, ← hk]
  by_cases hle : n - 1 ≤ k
  · exact (Nat.nth_strictMono (primeNormSet_infinite (K := K))).monotone hle
  · have hkn : k < n - 1 := not_le.mp hle
    have hn2 : 2 ≤ n := by omega
    have hkle : k ≤ n - 2 := by omega
    have hmono := (Nat.nth_strictMono (primeNormSet_infinite (K := K))).monotone hkle
    have hsub : n - 1 - 1 = n - 2 := by omega
    have heq : quadPrimeNorm K (n - 1) =
        Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) (n - 2) := by
      rw [primeNorm_eq_nth_of_ne_zero (by omega), hsub]
    omega

/-- A power bound for a multiset of naturals bounded below. -/
private theorem pow_card_le_prod {b : ℕ} {s : Multiset ℕ} (h : ∀ a ∈ s, b ≤ a) :
    b ^ s.card ≤ s.prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    have h1 : b ≤ a := h a (Multiset.mem_cons_self a s)
    have h2 : b ^ s.card ≤ s.prod := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    rw [Multiset.card_cons, pow_succ', Multiset.prod_cons]
    exact mul_le_mul' h1 h2

/-- Coprime elements generate the whole ring as ideals. -/
private theorem isCoprime_span_sup {K : Type*} [Field K] [NumberField K] {α β : 𝓞 K}
    (h : IsCoprime α β) :
    Ideal.span ({α} : Set (𝓞 K)) ⊔ Ideal.span ({β} : Set (𝓞 K)) = ⊤ := by
  obtain ⟨a, b, hab⟩ := h
  rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_singleton_le_iff_mem, ← hab]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self α))
    (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self β))

/-- **Large elements of a Schatunowsky set lie in all small prime ideals.** If `K` has class
number `1` and `α` lies in the Schatunowsky set with
`quadPrimeNorm K n ^ (ℓ + 1) < N(α)`, then `α` lies in every nonzero prime ideal of norm at
most `quadPrimeNorm K n`: otherwise a power of a generator of such a prime ideal would be
coprime to `α`, have norm strictly between `1` and `N(α)`, and have `ℓ + 1` prime ideal
factors. -/
private theorem mem_prime_of_mem {K : Type*} [Field K] [NumberField K]
    (hK1 : classNumber K = 1) (ℓ n : ℕ) (α : 𝓞 K) (hα : α ∈ quadSchatunowskySet K ℓ)
    (hn : quadPrimeNorm K n ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α})) :
    ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → Ideal.absNorm P ≤ quadPrimeNorm K n → α ∈ P := by
  have : IsPrincipalIdealRing (𝓞 K) := NumberField.classNumber_eq_one_iff.mp hK1
  intro P hPprime hPbot hPle
  by_contra hmem
  obtain ⟨π, hπ⟩ := IsPrincipalIdealRing.principal P
  have hspan : Ideal.span {π} = P := hπ.symm
  have hπ0 : π ≠ 0 := by
    intro h0
    apply hPbot
    rw [← hspan, h0]
    simp
  have hspanprime : (Ideal.span {π}).IsPrime := by
    rw [hspan]
    exact hPprime
  have hprime : Prime π := (Ideal.span_singleton_prime hπ0).mp hspanprime
  have hnotdvd : ¬ π ∣ α := by
    intro hdvd
    apply hmem
    rw [← hspan]
    exact Ideal.mem_span_singleton.mpr hdvd
  have hcop : IsCoprime α π := ((Prime.coprime_iff_not_dvd hprime).mpr hnotdvd).symm
  have hcopβ : IsCoprime α (π ^ (ℓ + 1)) := hcop.pow_right
  have hβnorm : Ideal.absNorm (Ideal.span {π ^ (ℓ + 1)}) = Ideal.absNorm P ^ (ℓ + 1) := by
    rw [← Ideal.span_singleton_pow, hspan, map_pow]
  have hPge : 2 ≤ Ideal.absNorm P := by
    have hpos : 0 < Ideal.absNorm P := by
      rw [Nat.pos_iff_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff]
      exact hPbot
    have hne1 : Ideal.absNorm P ≠ 1 := by
      intro h1
      exact hPprime.ne_top (Ideal.absNorm_eq_one_iff.mp h1)
    omega
  have hβgt : 1 < Ideal.absNorm (Ideal.span {π ^ (ℓ + 1)}) := by
    rw [hβnorm]
    exact one_lt_pow₀ (by omega) (by omega)
  have hβlt : Ideal.absNorm (Ideal.span {π ^ (ℓ + 1)}) < Ideal.absNorm (Ideal.span {α}) := by
    rw [hβnorm]
    exact lt_of_le_of_lt (Nat.pow_le_pow_left hPle _) hn
  have hΩ : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {π ^ (ℓ + 1)})).card
      = ℓ + 1 := by
    have hirr : Irreducible P := (Ideal.prime_of_isPrime hPbot hPprime).irreducible
    rw [← Ideal.span_singleton_pow, hspan, hirr.normalizedFactors_pow,
      Multiset.card_replicate]
  obtain ⟨-, hα2⟩ := hα
  have hle := hα2 (π ^ (ℓ + 1)) hβgt hβlt hcopβ
  rw [hΩ] at hle
  omega

end quadSchatunowskySet_eq_iUnion

/-- **Decomposition of the Schatunowsky set.** Let $K$ be an imaginary quadratic field (a totally
complex number field of degree $2$ over $\mathbb{Q}$) with class number $1$ and ring of integers
$\mathcal{O}_K$, and let $\ell$ and $n_0$ be natural numbers such that
$N(\pi_{n+1})^{\ell+1} < N(\pi_n\#)$ for every $n \ge n_0$, where $N(\pi_n)$ and $N(\pi_n\#)$ are
the prime and primorial norms of $K$. Write $N(\alpha)$ for the absolute norm of the principal
ideal $(\alpha)$. Then the Schatunowsky set $Q_\ell(K)$ is the union, over $1 \le n \le n_0$, of
the sets of $\alpha \in \mathcal{O}_K$ with
$N(\pi_{n-1})^{\ell+1} < N(\alpha) \le N(\pi_n)^{\ell+1}$ that lie in every nonzero prime ideal
of $\mathcal{O}_K$ of norm at most $N(\pi_{n-1})$.

Since $K$ has class number $1$, lying in all these prime ideals means being divisible by the
paper's primorial $\pi_{n-1}\#$. The element of largest norm in $Q_\ell(K)$ need not be divisible
by $\pi_{n_0-1}\#$ unless $n_0$ is the least admissible value: for the Gaussian integers with
$\ell = 1$, both $n_0 = 3$ and $n_0 = 4$ are admissible, but the element of largest norm,
$5(1+i) = \pi_2\#$, is not divisible by $\pi_3\# = 15(1+i)$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 5
(`integers-2026-A110-thm-5`). -/
public theorem quadSchatunowskySet_eq_iUnion {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n) :
    quadSchatunowskySet K ℓ = ⋃ n ∈ Finset.Icc 1 n₀,
      {α : 𝓞 K | quadPrimeNorm K (n - 1) ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) ∧
        Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K n ^ (ℓ + 1) ∧
        ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → Ideal.absNorm P ≤ quadPrimeNorm K (n - 1) →
          α ∈ P} := by
  classical
  obtain ⟨hbound, -⟩ := quadSchatunowskySet_norm_bound_and_finite hK hK1 ℓ n₀ hn₀
  ext α
  constructor
  · intro hα
    have hN1 : 1 < Ideal.absNorm (Ideal.span {α}) := hα.1
    have hle : Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K n₀ ^ (ℓ + 1) := by
      by_contra hlt
      exact hbound α (not_le.mp hlt) hα
    have hex : ∃ n, Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K n ^ (ℓ + 1) := ⟨n₀, hle⟩
    set n := Nat.find hex
    have hspec : Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K n ^ (ℓ + 1) :=
      Nat.find_spec hex
    have hn_le : n ≤ n₀ := Nat.find_min' hex hle
    have hn_ne : n ≠ 0 := by
      intro h0
      rw [h0, quadPrimeNorm_zero, one_pow] at hspec
      omega
    have hn_ge : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn_ne
    have hlow : quadPrimeNorm K (n - 1) ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) := by
      have hmin : ¬ Ideal.absNorm (Ideal.span {α}) ≤ quadPrimeNorm K (n - 1) ^ (ℓ + 1) :=
        Nat.find_min hex (by omega)
      exact not_le.mp hmin
    have hsmall := quadSchatunowskySet_eq_iUnion.mem_prime_of_mem hK1 ℓ (n - 1) α hα hlow
    have hnmem : n ∈ Finset.Icc 1 n₀ := Finset.mem_Icc.mpr ⟨hn_ge, hn_le⟩
    exact Set.mem_iUnion₂_of_mem hnmem ⟨hlow, hspec, hsmall⟩
  · intro hα
    obtain ⟨n, hnmem, hαn⟩ := Set.mem_iUnion₂.mp hα
    obtain ⟨hlow, hup, hsmall⟩ := hαn
    rw [Finset.mem_Icc] at hnmem
    obtain ⟨hn1, -⟩ := hnmem
    have hN1 : 1 < Ideal.absNorm (Ideal.span {α}) :=
      lt_of_le_of_lt (one_le_pow₀ (quadSchatunowskySet_eq_iUnion.primeNorm_ge_one (n - 1))) hlow
    refine ⟨hN1, fun β hβ1 hβlt hcop => ?_⟩
    by_contra hle
    have hlt : ℓ < (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β})).card :=
      not_le.mp hle
    have hβne : Ideal.span ({β} : Set (𝓞 K)) ≠ ⊥ := by
      intro hz
      have h0 : Ideal.absNorm (Ideal.span {β}) = 0 := Ideal.absNorm_eq_zero_iff.mpr hz
      omega
    have hboundQ : ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β}),
        quadPrimeNorm K n ≤ Ideal.absNorm Q := by
      intro Q hQmem
      have hQprime : Q.IsPrime := Ideal.isPrime_of_prime
        (UniqueFactorizationMonoid.prime_of_normalized_factor Q hQmem)
      have hQne : Q ≠ ⊥ := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hQmem
      have hαnQ : α ∉ Q := by
        intro hmem
        have hdvd : Q ∣ Ideal.span {β} :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hQmem
        have hsup := quadSchatunowskySet_eq_iUnion.isCoprime_span_sup hcop
        have hleQ : Ideal.span ({α} : Set (𝓞 K)) ⊔ Ideal.span ({β} : Set (𝓞 K)) ≤ Q :=
          sup_le ((Ideal.span_singleton_le_iff_mem (I := Q)).mpr hmem)
            (Ideal.dvd_iff_le.mp hdvd)
        rw [hsup] at hleQ
        exact hQprime.ne_top (eq_top_iff.mpr hleQ)
      have hgt : quadPrimeNorm K (n - 1) < Ideal.absNorm Q := by
        by_contra hle'
        exact hαnQ (hsmall Q hQprime hQne (not_lt.mp hle'))
      exact quadSchatunowskySet_eq_iUnion.primeNorm_le_of_mem_gt n hn1 Q hQprime hQne hgt
    have h1 : quadPrimeNorm K n ^ (ℓ + 1) ≤
        quadPrimeNorm K n ^ (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β})).card :=
      pow_le_pow_right₀ (quadSchatunowskySet_eq_iUnion.primeNorm_ge_one n) (by omega)
    have hprod : (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β})).prod =
        Ideal.span {β} :=
      Ideal.prod_normalizedFactors_eq_self hβne
    have h2 : quadPrimeNorm K n ^ (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {β})).card ≤ Ideal.absNorm (Ideal.span {β}) := by
      have hmap := map_multiset_prod Ideal.absNorm
        (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β}))
      rw [hprod] at hmap
      rw [hmap]
      have hcard : ((UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β})).map
          Ideal.absNorm).card
          = (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β})).card :=
        Multiset.card_map _ _
      rw [← hcard]
      exact quadSchatunowskySet_eq_iUnion.pow_card_le_prod (fun a ha => by
        obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp ha
        exact hboundQ Q hQ)
    omega

end

end MetaMathlibExt
