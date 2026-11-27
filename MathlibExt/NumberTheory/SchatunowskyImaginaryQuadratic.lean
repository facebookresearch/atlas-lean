/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Nth
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Prime norms, primorial norms and Schatunowsky sets in imaginary quadratic fields

The prime norm $N(\pi_n)$, the primorial norm $N(\pi_n\#)$ and the Schatunowsky set
$Q_\ell(K)$ of a number field, and the norm bound and finiteness of $Q_\ell(K)$ for an
imaginary quadratic field of class number one when the prime norm powers eventually fall
below the primorial norms. Large elements of $Q_\ell(K)$ lie in every small nonzero prime ideal
(`mem_prime_of_mem_quadSchatunowskySet`), and under the same hypotheses $Q_\ell(K)$ is the union,
over $1 \le n \le n_0$, of the elements with
$N(\pi_{n-1})^{\ell+1} < N(\alpha) \le N(\pi_n)^{\ell+1}$ that lie in every nonzero prime ideal
of norm at most $N(\pi_{n-1})$ (`quadSchatunowskySet_eq_iUnion`).
-/

open NumberField

namespace MetaMathlibExt

/-- **Norm of the $n$-th prime.** Let $K$ be a number field with ring of integers $\mathcal{O}_K$.
For $n \ge 1$, $N(\pi_n)$ is the $n$-th smallest natural number that is the absolute norm of some
nonzero prime ideal of $\mathcal{O}_K$, each such norm counted once however many prime ideals
have it; and $N(\pi_0) = 1$.

For an imaginary quadratic field $K = \mathbb{Q}(\sqrt{m})$ of class number one the prime ideals
above distinct rational primes $p$ have distinct norms $p$ or $p^2$, so $N(\pi_n)$ is the norm of
the $n$-th prime $\pi_n$ of the paper's norm-ordered set $P_m^+$ (Definition 1), and
$N(\pi_0) = 1$ matches its convention $\pi_0 = 1$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 1 and
Section 4 (`N(π_n)`). -/
noncomputable def quadPrimeNorm (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  if n = 0 then 1
  else Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) (n - 1)

/-- **The zeroth prime norm is one.** For every number field $K$, the zeroth prime norm
$N(\pi_0)$ of $K$ equals $1$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 1
(convention `π_0 = 1`). -/
theorem quadPrimeNorm_zero (K : Type*) [Field K] [NumberField K] :
    quadPrimeNorm K 0 = 1 := by
  simp [quadPrimeNorm]

/-- **Norm of the $n$-th primorial.** Let $K$ be a number field with ring of integers
$\mathcal{O}_K$, and let $n$ be a natural number. The primorial norm $N(\pi_n\#)$ is the product of
the absolute norms of the nonzero prime ideals of $\mathcal{O}_K$ whose norm is at most $N(\pi_n)$,
where $N(\pi_n)$ is the $n$-th smallest norm of a nonzero prime ideal of $\mathcal{O}_K$ for
$n \ge 1$ and $N(\pi_0) = 1$.

There are finitely many such prime ideals. For an imaginary quadratic field of class number one,
$N(\pi_n\#)$ is the norm of the paper's quadratic primorial $\pi_n\#$ (Definition 2).

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 2
(`π_n#`). -/
noncomputable def quadPrimorialNorm (K : Type*) [Field K] [NumberField K] (n : ℕ) : ℕ :=
  ∏ᶠ P ∈ {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ quadPrimeNorm K n},
    Ideal.absNorm P

/-- **The zeroth primorial norm is one.** For every number field $K$ with ring of integers
$\mathcal{O}_K$, the primorial norm $N(\pi_0\#)$ of $K$ equals $1$: no nonzero prime ideal of
$\mathcal{O}_K$ has norm at most $1$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Definition 2
(`π_0# = 1`). -/
theorem quadPrimorialNorm_zero (K : Type*) [Field K] [NumberField K] :
    quadPrimorialNorm K 0 = 1 := by
  have hempty : {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ 1} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun P ⟨hP, hbot, hle⟩ => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact hbot (Ideal.absNorm_eq_zero_iff.mp h)
    · exact hP.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  rw [quadPrimorialNorm, quadPrimeNorm_zero, hempty, finprod_mem_empty]

/-- **Schatunowsky set of a number field.** Let $K$ be a number field with ring of integers
$\mathcal{O}_K$ and let $\ell$ be a natural number. For $\alpha \in \mathcal{O}_K$ write $N(\alpha)$
for the absolute norm of the principal ideal $(\alpha)$ and $\Omega(\alpha)$ for the number of
prime ideal factors of $(\alpha)$ counted with multiplicity. The Schatunowsky set $Q_\ell(K)$ is
the set of $\alpha \in \mathcal{O}_K$ with $N(\alpha) > 1$ such that every $\beta \in \mathcal{O}_K$
coprime to $\alpha$ (that is, $(\alpha) + (\beta) = \mathcal{O}_K$) with $1 < N(\beta) < N(\alpha)$
satisfies $\Omega(\beta) \le \ell$.

The set is closed under multiplication by units. For $K = \mathbb{Q}(\sqrt{m})$ imaginary quadratic
of class number one it is the paper's set $Q_{m,\ell}$ (Equation (4)).

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Section 5, Equation
(4). -/
def quadSchatunowskySet (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) : Set (𝓞 K) :=
  {α | 1 < Ideal.absNorm (Ideal.span {α}) ∧ ∀ β : 𝓞 K,
      1 < Ideal.absNorm (Ideal.span {β}) →
      Ideal.absNorm (Ideal.span {β}) < Ideal.absNorm (Ideal.span {α}) →
    IsCoprime α β → (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {β})).card ≤ ℓ}

/-- **One is not in the Schatunowsky set.** For every number field $K$ and every natural number
$\ell$, the element $1$ of the ring of integers $\mathcal{O}_K$ does not lie in the Schatunowsky
set $Q_\ell(K)$, because the ideal it generates has norm $1$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Section 5, Equation
(4). -/
theorem one_not_mem_quadSchatunowskySet (K : Type*) [Field K] [NumberField K] (ℓ : ℕ) :
    (1 : 𝓞 K) ∉ quadSchatunowskySet K ℓ := by
  simp [quadSchatunowskySet]

namespace quadSchatunowskySet_norm_bound_and_finite

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

/-- For `n ≥ 1`, the prime norm `quadPrimeNorm K n` is the `(n - 1)`-st element of the
set of prime ideal norms. -/
private theorem primeNorm_eq_nth {K : Type*} [Field K] [NumberField K] (n : ℕ) :
    quadPrimeNorm K (n + 1) =
      Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) n := by
  simp only [quadPrimeNorm, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]

/-- The prime norms `quadPrimeNorm K (n + 1)`, for `n` varying, are strictly increasing. -/
private theorem primeNorm_strictMono {K : Type*} [Field K] [NumberField K] :
    StrictMono (fun n => quadPrimeNorm K (n + 1)) := by
  intro a b hab
  change quadPrimeNorm K (a + 1) < quadPrimeNorm K (b + 1)
  rw [primeNorm_eq_nth, primeNorm_eq_nth]
  exact Nat.nth_strictMono (primeNormSet_infinite (K := K)) hab

/-- The `(n + 1)`-st prime norm is at least `n`. -/
private theorem primeNorm_ge {K : Type*} [Field K] [NumberField K] (n : ℕ) :
    n ≤ quadPrimeNorm K (n + 1) := by
  have hle := (primeNorm_strictMono (K := K)).id_le n
  exact hle

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

/-- The primorial norm divides the norm of every element lying in all the prime ideals
whose norms enter it: distinct nonzero prime ideals are pairwise coprime, so their
product divides the principal ideal. -/
private theorem primorialNorm_dvd_of_mem {K : Type*} [Field K] [NumberField K] (m : ℕ)
    (α : 𝓞 K)
    (hmem : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
      Ideal.absNorm P ≤ quadPrimeNorm K m → α ∈ P) :
    quadPrimorialNorm K m ∣ Ideal.absNorm (Ideal.span {α}) := by
  classical
  set S : Set (Ideal (𝓞 K)) :=
    {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ quadPrimeNorm K m} with hS
  have hSfin : S.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (quadPrimeNorm K m)).subset
      (fun P hP => hP.2.2)
  have hprim : quadPrimorialNorm K m = ∏ P ∈ hSfin.toFinset, Ideal.absNorm P := by
    rw [quadPrimorialNorm, finprod_mem_eq_finite_toFinset_prod _ hSfin]
  have hdvd : (∏ P ∈ hSfin.toFinset, P) ∣ Ideal.span {α} := by
    apply Finset.prod_dvd_of_coprime (s := id) (z := Ideal.span {α})
    · intro P hP Q hQ hne
      simp only [Function.onFun, id]
      have hP' : P ∈ S := hSfin.mem_toFinset.mp hP
      have hQ' : Q ∈ S := hSfin.mem_toFinset.mp hQ
      have hPmax : P.IsMaximal := hP'.1.isMaximal hP'.2.1
      have hQmax : Q.IsMaximal := hQ'.1.isMaximal hQ'.2.1
      exact Ideal.isCoprime_iff_sup_eq.mpr (hPmax.coprime_of_ne hQmax hne)
    · intro P hP
      have hP' : P ∈ S := hSfin.mem_toFinset.mp hP
      rw [Ideal.dvd_iff_le]
      exact (Ideal.span_singleton_le_iff_mem (I := P)).mpr (hmem P hP'.1 hP'.2.1 hP'.2.2)
  have hmap : Ideal.absNorm (∏ P ∈ hSfin.toFinset, P)
      = ∏ P ∈ hSfin.toFinset, Ideal.absNorm P := by
    rw [map_prod]
  rw [hprim, ← hmap]
  exact map_dvd Ideal.absNorm hdvd

/-- The primorial norm is positive: it is a product of positive prime ideal norms. -/
private theorem primorialNorm_pos {K : Type*} [Field K] [NumberField K] (n : ℕ) :
    0 < quadPrimorialNorm K n := by
  classical
  set S : Set (Ideal (𝓞 K)) :=
    {P : Ideal (𝓞 K) | P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P ≤ quadPrimeNorm K n} with hS
  have hSfin : S.Finite :=
    (Ring.HasFiniteQuotients.finite_absNorm_le (quadPrimeNorm K n)).subset
      (fun P hP => hP.2.2)
  rw [quadPrimorialNorm, finprod_mem_eq_finite_toFinset_prod _ hSfin]
  apply Finset.prod_pos
  intro P hP
  have hP' : P ∈ S := hSfin.mem_toFinset.mp hP
  rw [Nat.pos_iff_ne_zero, ne_eq, Ideal.absNorm_eq_zero_iff]
  exact hP'.2.1

/-- The unit group of the ring of integers of an imaginary quadratic field is finite,
by Dirichlet's unit theorem: the unit rank is the number of infinite places minus one,
and here there is a single infinite place. -/
private theorem finite_units {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] : Finite (𝓞 K)ˣ := by
  have hcard : Fintype.card (NumberField.InfinitePlace K) = 1 := by
    have h1 := IsTotallyComplex.nrRealPlaces_eq_zero K
    have h2 := NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces K
    have h3 := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank K
    rw [hK] at h3
    omega
  have hrank : NumberField.Units.rank K = 0 := by
    simp [NumberField.Units.rank, hcard]
  apply Finite.of_surjective (fun ζ : NumberField.Units.torsion K => (ζ : (𝓞 K)ˣ))
  intro x
  obtain ⟨ζe, h, -⟩ := NumberField.Units.exist_unique_eq_mul_prod K x
  refine ⟨ζe.1, ?_⟩
  change (ζe.1 : (𝓞 K)ˣ) = x
  rw [h]
  have huniv : (Finset.univ : Finset (Fin (NumberField.Units.rank K))) = ∅ := by
    rw [hrank]
    exact Finset.univ_eq_empty
  rw [huniv, Finset.prod_empty, mul_one]

/-- Only finitely many algebraic integers have absolute norm at most a given bound:
there are finitely many ideals of bounded norm, and the integers generating a given
ideal form finitely many associate classes, the unit group being finite. -/
private theorem boundedAbsNorm_finite {K : Type*} [Field K] [NumberField K]
    [Finite (𝓞 K)ˣ] (B : ℕ) :
    {α : 𝓞 K | Ideal.absNorm (Ideal.span {α}) ≤ B}.Finite := by
  have hfinI : {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ B}.Finite :=
    Ring.HasFiniteQuotients.finite_absNorm_le B
  have hfib : ∀ I : Ideal (𝓞 K), {α : 𝓞 K | Ideal.span {α} = I}.Finite := by
    intro I
    by_cases hI : ∃ β : 𝓞 K, Ideal.span {β} = I
    · obtain ⟨β, hβ⟩ := hI
      refine Set.Finite.subset (Set.finite_range (fun u : (𝓞 K)ˣ => β * (u : 𝓞 K))) ?_
      intro α hα
      have hassoc : Associated α β := by
        rw [← Ideal.span_singleton_eq_span_singleton]
        rw [hα, hβ]
      obtain ⟨u, hu⟩ := hassoc
      refine ⟨u⁻¹, ?_⟩
      have h1 : (u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = 1 := by simp
      have hu' : β * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) = α := by
        calc β * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)
            = (α * (u : 𝓞 K)) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K) := by rw [hu]
          _ = α * ((u : 𝓞 K) * ((u⁻¹ : (𝓞 K)ˣ) : 𝓞 K)) := by rw [mul_assoc]
          _ = α := by rw [h1, mul_one]
      exact hu'
    · have hempty : {α : 𝓞 K | Ideal.span {α} = I} = ∅ := by
        apply Set.eq_empty_of_forall_notMem
        intro α hα
        exact hI ⟨α, hα⟩
      rw [hempty]
      exact Set.finite_empty
  refine Set.Finite.subset (hfinI.biUnion (fun I _ => hfib I)) ?_
  intro α hα
  exact Set.mem_biUnion hα rfl

end quadSchatunowskySet_norm_bound_and_finite

/-- **Norm bound and finiteness of the Schatunowsky set.** Let $K$ be an imaginary quadratic field
(a totally complex number field of degree $2$ over $\mathbb{Q}$) with class number $1$ and ring of
integers $\mathcal{O}_K$, and let $\ell$ and $n_0$ be natural numbers such that
$N(\pi_{n+1})^{\ell+1} < N(\pi_n\#)$ for every $n \ge n_0$, where $N(\pi_n)$ and $N(\pi_n\#)$ are
the prime and primorial norms of $K$. Then no $\alpha \in \mathcal{O}_K$ whose principal ideal
$(\alpha)$ has absolute norm greater than $N(\pi_{n_0})^{\ell+1}$ lies in the Schatunowsky set
$Q_\ell(K)$, and $Q_\ell(K)$ is finite.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Theorem 4
(`integers-2026-A110-thm-4`). -/
theorem quadSchatunowskySet_norm_bound_and_finite {K : Type*} [Field K]
    [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n₀ : ℕ)
    (hn₀ : ∀ n ≥ n₀, quadPrimeNorm K (n + 1) ^ (ℓ + 1) < quadPrimorialNorm K n) :
    (∀ α : 𝓞 K, quadPrimeNorm K n₀ ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) →
        α ∉ quadSchatunowskySet K ℓ) ∧
      (quadSchatunowskySet K ℓ).Finite := by
  classical
  have hbound : ∀ α : 𝓞 K, quadPrimeNorm K n₀ ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α}) →
      α ∉ quadSchatunowskySet K ℓ := by
    intro α hαlt hαmem
    set B := Ideal.absNorm (Ideal.span {α}) with hBdef
    set N := B + n₀ + 2 with hNdef
    -- The prime norm powers are unbounded, so the defining property fails at `N`.
    have hPN : ¬ quadPrimeNorm K N ^ (ℓ + 1) < B := by
      have hge0 := quadSchatunowskySet_norm_bound_and_finite.primeNorm_ge (K := K) (B + n₀ + 1)
      rw [show B + n₀ + 1 + 1 = N from by omega] at hge0
      have hpow : quadPrimeNorm K N ≤ quadPrimeNorm K N ^ (ℓ + 1) :=
        Nat.le_self_pow (by omega) _
      omega
    -- Let `m` be the greatest index at most `N` with the defining property.
    have hmP : quadPrimeNorm K
        (Nat.findGreatest (fun n => quadPrimeNorm K n ^ (ℓ + 1) < B) N) ^ (ℓ + 1) < B :=
      Nat.findGreatest_spec (P := fun n => quadPrimeNorm K n ^ (ℓ + 1) < B)
        (by omega : n₀ ≤ N) hαlt
    have hmle : Nat.findGreatest (fun n => quadPrimeNorm K n ^ (ℓ + 1) < B) N ≤ N :=
      Nat.findGreatest_le (P := fun n => quadPrimeNorm K n ^ (ℓ + 1) < B) N
    have hmge : n₀ ≤ Nat.findGreatest (fun n => quadPrimeNorm K n ^ (ℓ + 1) < B) N :=
      Nat.le_findGreatest (P := fun n => quadPrimeNorm K n ^ (ℓ + 1) < B)
        (by omega : n₀ ≤ N) hαlt
    set m := Nat.findGreatest (fun n => quadPrimeNorm K n ^ (ℓ + 1) < B) N with hmdef
    have hmax : ∀ k, m < k → k ≤ N → ¬ quadPrimeNorm K k ^ (ℓ + 1) < B := by
      intro k hk1 hk2 hPk
      exact absurd (Nat.le_findGreatest
        (P := fun n => quadPrimeNorm K n ^ (ℓ + 1) < B) hk2 hPk) (by omega)
    have hmN : m < N := by
      refine lt_of_le_of_ne hmle ?_
      intro hEq
      apply hPN
      rw [← hEq]
      exact hmP
    have hsucc : B ≤ quadPrimeNorm K (m + 1) ^ (ℓ + 1) :=
      Nat.le_of_not_gt (hmax (m + 1) (by omega) (by omega))
    -- By the auxiliary lemma, `α` lies in every prime ideal counted by the primorial.
    have hmem : ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ →
        Ideal.absNorm P ≤ quadPrimeNorm K m → α ∈ P :=
      quadSchatunowskySet_norm_bound_and_finite.mem_prime_of_mem hK1 ℓ m α hαmem hmP
    have hdvd := quadSchatunowskySet_norm_bound_and_finite.primorialNorm_dvd_of_mem m α hmem
    have hpos := quadSchatunowskySet_norm_bound_and_finite.primorialNorm_pos (K := K) m
    have hle : quadPrimorialNorm K m ≤ B := Nat.le_of_dvd (by omega) hdvd
    have hlt := hn₀ m hmge
    omega
  refine ⟨hbound, ?_⟩
  have : Finite (𝓞 K)ˣ :=
    quadSchatunowskySet_norm_bound_and_finite.finite_units hK
  refine Set.Finite.subset
    (quadSchatunowskySet_norm_bound_and_finite.boundedAbsNorm_finite
      (K := K) (quadPrimeNorm K n₀ ^ (ℓ + 1))) (fun α hα => ?_)
  by_contra hle
  exact hbound α (Nat.lt_of_not_le hle) hα

-- The degree and total-complexity hypotheses belong to the source statement; the proof uses
-- only class number one.
set_option linter.unusedVariables false in
/-- **Large elements of a Schatunowsky set lie in all small prime ideals.** Let $K$ be an
imaginary quadratic field of class number $1$. For $\alpha \in \mathcal{O}_K$ let $N(\alpha)$ be
the absolute norm of the ideal $(\alpha)$. Put $N(\pi_0) = 1$ and, for $n \ge 1$, let $N(\pi_n)$
be the $n$-th smallest number that is the norm of a nonzero prime ideal of $\mathcal{O}_K$. For
a natural number $\ell$, let $Q_\ell$ be the set of $\alpha \in \mathcal{O}_K$ with
$N(\alpha) > 1$ such that every $\beta \in \mathcal{O}_K$ coprime to $\alpha$ with
$1 < N(\beta) < N(\alpha)$ has at most $\ell$ prime ideal factors, counted with multiplicity.
For natural numbers $\ell$ and $n$, if $\alpha \in Q_\ell$ and $N(\pi_n)^{\ell+1} < N(\alpha)$,
then $\alpha$ lies in every nonzero prime ideal of $\mathcal{O}_K$ of norm at most $N(\pi_n)$.

Source: Hirofumi Nakai, Ken Sasaki and Konoka Yoshida, *Schatunowsky-type Theorems for Imaginary
Quadratic Integer Rings of Class Number One*, INTEGERS 26 (2026), Article A110, Lemma 4
(`integers-2026-A110-lem-4`). -/
theorem mem_prime_of_mem_quadSchatunowskySet {K : Type*} [Field K] [NumberField K]
    (hK : Module.finrank ℚ K = 2) [IsTotallyComplex K] (hK1 : classNumber K = 1) (ℓ n : ℕ)
    (α : 𝓞 K) (hα : α ∈ quadSchatunowskySet K ℓ)
    (hn : quadPrimeNorm K n ^ (ℓ + 1) < Ideal.absNorm (Ideal.span {α})) :
    ∀ P : Ideal (𝓞 K), P.IsPrime → P ≠ ⊥ → Ideal.absNorm P ≤ quadPrimeNorm K n → α ∈ P :=
  quadSchatunowskySet_norm_bound_and_finite.mem_prime_of_mem hK1 ℓ n α hα hn

namespace quadSchatunowskySet_eq_iUnion

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
    have hmem := Nat.nth_mem_of_infinite
      (quadSchatunowskySet_norm_bound_and_finite.primeNormSet_infinite (K := K)) (m - 1)
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
  · exact (Nat.nth_strictMono
      (quadSchatunowskySet_norm_bound_and_finite.primeNormSet_infinite (K := K))).monotone hle
  · have hkn : k < n - 1 := not_le.mp hle
    have hn2 : 2 ≤ n := by omega
    have hkle : k ≤ n - 2 := by omega
    have hmono := (Nat.nth_strictMono
      (quadSchatunowskySet_norm_bound_and_finite.primeNormSet_infinite (K := K))).monotone hkle
    have hsub : n - 1 - 1 = n - 2 := by omega
    have heq : quadPrimeNorm K (n - 1) =
        Nat.nth (fun x => ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P ≠ ⊥ ∧ Ideal.absNorm P = x) (n - 2) := by
      rw [primeNorm_eq_nth_of_ne_zero (by omega), hsub]
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
theorem quadSchatunowskySet_eq_iUnion {K : Type*} [Field K] [NumberField K]
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
    have hsmall := mem_prime_of_mem_quadSchatunowskySet hK hK1 ℓ (n - 1) α hα hlow
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
        have hsup := (Ideal.sup_eq_top_iff_isCoprime α β).2 hcop
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
      exact Multiset.pow_card_le_prod (fun a ha => by
        obtain ⟨Q, hQ, rfl⟩ := Multiset.mem_map.mp ha
        exact hboundQ Q hQ)
    omega


end MetaMathlibExt
