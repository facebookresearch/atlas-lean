/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Image
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Sets of remainders and unbounded drops in their size

For a natural number `n`, the remainder set is `S(n) = {n mod k : 1 ≤ k ≤ ⌊n/2⌋}` and the
remainder count is `s(n) = |S(n)|` (OEIS A283190). The main result,
`remainderCount_drops_unbounded`, shows that the differences `s(n+1) - s(n)` are unbounded
below: for every natural number `M` there are infinitely many `n` with `s(n+1) + M ≤ s(n)`.
This is Proposition 4 of Omkar Baraskar and Ingrid Vukusic, *Bounds for sets of remainders*,
arXiv:2508.20853v1 (2025), Section 4, the preprint of the journal article that the docstrings
below cite.

The proof follows the preprint. Every nonzero element of `S(n+1)` is `r + 1` for some
`r ∈ S(n)` (Lemma 6 of the preprint), so `s(n+1) + |T| ≤ s(n) + 1` for every set `T ⊆ S(n)` of
elements `r` with `r + 1 ∉ S(n+1)`. If `n + 1 = d (p + 1)` with `p` prime and `d` free of
primes below `p`, then `d - 1` is such an element (Lemma 9 of the preprint characterizes all of
them). Given a prime `p`, Dirichlet's theorem on primes in arithmetic progressions gives a
larger prime `p'` with `p' ≡ p (mod (p + 1) (p - 1)!)`. Then `(p' + 1)/(p + 1)` has no prime
factor below `p`, so every such factorization of `p + 1` gives one of `p' + 1`, and
`p' + 1 = 1 · (p' + 1)` is one more. Iterating from any prime gives `n` with arbitrarily many
such factorizations of `n + 1`. The preprint chooses the arithmetic progression with the
Chinese remainder theorem instead.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Remainder set.** For a natural number $n$, the remainder set is
$S(n) = \{\, n \bmod k : 1 \le k \le \lfloor n/2 \rfloor \,\}$, the set of remainders of $n$
modulo the integers from $1$ to $\lfloor n/2 \rfloor$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `S(n)`). -/
public def remainderSet (n : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (n / 2)).image (n % ·)

/-- **Remainder count.** For a natural number $n$, $s(n)$ is the number of elements of the
remainder set $S(n)$, that is, the number of distinct values of $n \bmod k$ for
$1 \le k \le \lfloor n/2 \rfloor$ (OEIS A283190).

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Section 1 (definition of `s(n)`). -/
public def remainderCount (n : ℕ) : ℕ :=
  (remainderSet n).card

/-- Membership in the remainder set, unfolded. -/
private theorem mem_remainderSet_iff {n r : ℕ} :
    r ∈ remainderSet n ↔ ∃ k, 1 ≤ k ∧ k ≤ n / 2 ∧ n % k = r := by
  simp only [remainderSet, Finset.mem_image, Finset.mem_Icc, and_assoc]

/-- If `n + 1 = (p + 1) d` with `p` prime, then `d - 1 = n mod d` lies in `S(n)`. -/
private theorem div_sub_one_mem_remainderSet {n p : ℕ} (hp : p.Prime) (hdvd : p + 1 ∣ n + 1) :
    (n + 1) / (p + 1) - 1 ∈ remainderSet n := by
  obtain ⟨d, hd⟩ := hdvd
  have hp2 := hp.two_le
  rw [hd, Nat.mul_div_cancel_left d (by omega), mem_remainderSet_iff]
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hd; omega
  have h1 : n + 1 = d * p + d := by rw [hd]; ring
  have h2 : d * 2 ≤ d * p := Nat.mul_le_mul_left d hp2
  have hn : n = d - 1 + d * p := by omega
  refine ⟨d, hd0, by omega, ?_⟩
  rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

/-- If `n + 1 = (p + 1) d` with `p` prime and `d` free of primes below `p`, then `d ∉ S(n + 1)`:
a modulus `k` with `(n + 1) mod k = d` would divide `n + 1 - d = d p` and exceed `d`, so it
would be `d p`, which is larger than `(n + 1)/2`. -/
private theorem div_notMem_remainderSet_succ {n p : ℕ} (hp : p.Prime) (hdvd : p + 1 ∣ n + 1)
    (hfac : ∀ q, q.Prime → q ∣ (n + 1) / (p + 1) → p ≤ q) :
    (n + 1) / (p + 1) ∉ remainderSet (n + 1) := by
  obtain ⟨d, hd⟩ := hdvd
  have hp2 := hp.two_le
  have hdiv : (n + 1) / (p + 1) = d := by rw [hd, Nat.mul_div_cancel_left d (by omega)]
  rw [hdiv] at hfac ⊢
  rw [mem_remainderSet_iff]
  rintro ⟨k, hk1, hk2, hmod⟩
  have hd0 : 0 < d := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hd; omega
  have h1 : n + 1 = d * p + d := by rw [hd]; ring
  have hdk : d < k := hmod ▸ Nat.mod_lt _ (by omega)
  have hkdvd : k ∣ d * p := by
    have h2 : k ∣ n + 1 - (n + 1) % k := Nat.dvd_sub_mod (n + 1)
    rwa [hmod, show n + 1 - d = d * p by omega] at h2
  obtain ⟨c, hc⟩ := hkdvd
  have hdp : 0 < d * p := Nat.mul_pos hd0 (by omega)
  have hcp : c < p := by
    by_contra h
    have h3 : d * p < k * p := Nat.mul_lt_mul_of_pos_right hdk (by omega)
    have h4 : k * p ≤ k * c := Nat.mul_le_mul_left k (not_lt.1 h)
    omega
  have hc1 : c = 1 := by
    by_contra hne
    obtain ⟨q, hq, hqc⟩ := Nat.exists_prime_and_dvd hne
    have hc0 : 0 < c := Nat.pos_of_ne_zero fun h => by rw [h, Nat.mul_zero] at hc; omega
    have hqle : q ≤ c := Nat.le_of_dvd hc0 hqc
    have hqdp : q ∣ d * p := by rw [hc]; exact hqc.mul_left k
    rcases hq.dvd_mul.1 hqdp with hqd | hqp
    · have := hfac q hq hqd
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hq hp).1 hqp
      omega
  rw [hc1, Nat.mul_one] at hc
  omega

/-- Every nonzero element of `S(n + 1)` is `r + 1` for some `r ∈ S(n)`. So if `r + 1 ∉ S(n + 1)`
for every `r ∈ T`, then `S(n + 1) ⊆ {0} ∪ {r + 1 : r ∈ S(n) \ T}`. -/
private theorem remainderSet_succ_subset (n : ℕ) (T : Finset ℕ)
    (hT : ∀ r ∈ T, r + 1 ∉ remainderSet (n + 1)) :
    remainderSet (n + 1) ⊆ insert 0 ((remainderSet n \ T).image (· + 1)) := by
  intro j hj
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · exact Finset.mem_insert_self _ _
  apply Finset.mem_insert_of_mem
  rw [Finset.mem_image]
  refine ⟨j - 1, Finset.mem_sdiff.2 ⟨?_, fun hmem => hT _ hmem ?_⟩, by omega⟩
  · obtain ⟨k, hk1, hk2, hmod⟩ := mem_remainderSet_iff.1 hj
    have hjk : j < k := hmod ▸ Nat.mod_lt _ (by omega)
    rw [mem_remainderSet_iff]
    refine ⟨k, hk1, ?_, ?_⟩
    · by_contra hk
      have h2 : n + 1 = k * 2 := by omega
      have h3 : (n + 1) % k = 0 := by rw [h2]; simp
      omega
    · have key := Nat.div_add_mod (n + 1) k
      rw [hmod] at key
      have hn : n = j - 1 + k * ((n + 1) / k) := by omega
      rw [hn, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · rwa [Nat.sub_add_cancel hj0]

/-- **The drop criterion.** If `P` is a finite set of primes `p` with `p + 1 ∣ n + 1` such that
`(n + 1)/(p + 1)` has no prime factor below `p`, then `s(n + 1) + |P| ≤ s(n) + 1`. -/
private theorem remainderCount_succ_add_card_le {n : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p + 1 ∣ n + 1 ∧ ∀ q, q.Prime → q ∣ (n + 1) / (p + 1) → p ≤ q) :
    remainderCount (n + 1) + P.card ≤ remainderCount n + 1 := by
  have hpos : ∀ p ∈ P, 0 < (n + 1) / (p + 1) := fun p hp =>
    Nat.div_pos (Nat.le_of_dvd (by omega) (hP p hp).2.1) (by omega)
  obtain ⟨T, hT⟩ : ∃ T, T = P.image (fun p => (n + 1) / (p + 1) - 1) := ⟨_, rfl⟩
  have hTcard : T.card = P.card := by
    rw [hT]
    refine Finset.card_image_of_injOn fun p hp p' hp' h => ?_
    have h' : (n + 1) / (p + 1) = (n + 1) / (p' + 1) := by
      have := hpos p hp
      have := hpos p' hp'
      omega
    have e1 := Nat.div_div_self (hP p hp).2.1 (by omega)
    have e2 := Nat.div_div_self (hP p' hp').2.1 (by omega)
    rw [h', e2] at e1
    omega
  have hTsub : T ⊆ remainderSet n := by
    intro r hr
    rw [hT] at hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hr
    exact div_sub_one_mem_remainderSet (hP p hp).1 (hP p hp).2.1
  have hTnot : ∀ r ∈ T, r + 1 ∉ remainderSet (n + 1) := by
    intro r hr
    rw [hT] at hr
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hr
    rw [Nat.sub_add_cancel (hpos p hp)]
    exact div_notMem_remainderSet_succ (hP p hp).1 (hP p hp).2.1 (hP p hp).2.2
  have h1 := Finset.card_le_card (remainderSet_succ_subset n T hTnot)
  have h2 := Finset.card_insert_le 0 ((remainderSet n \ T).image (· + 1))
  have h3 := Finset.card_image_le (s := remainderSet n \ T) (f := (· + 1))
  have h4 := Finset.card_sdiff_add_card_eq_card hTsub
  unfold remainderCount
  omega

/-- **Long chains.** For all `J` and `B` there are a prime `p > B` and a set of `J` primes `q`
with `q + 1 ∣ p + 1` such that `(p + 1)/(q + 1)` has no prime factor below `q`. Each step
applies Dirichlet's theorem to the progression `p' ≡ p (mod (p + 1) (p - 1)!)`. -/
private theorem exists_prime_chain (J B : ℕ) : ∃ p, B < p ∧ p.Prime ∧ ∃ P : Finset ℕ,
    P.card = J ∧ ∀ q ∈ P, q.Prime ∧ q + 1 ∣ p + 1 ∧
      ∀ r, r.Prime → r ∣ (p + 1) / (q + 1) → q ≤ r := by
  induction J generalizing B with
  | zero =>
    obtain ⟨p, hp1, hp2⟩ := Nat.exists_infinite_primes (B + 1)
    exact ⟨p, by omega, hp2, ∅, rfl, by simp⟩
  | succ J ih =>
    obtain ⟨p, hBp, hp, P, hcard, hP⟩ := ih B
    have hp2 := hp.two_le
    obtain ⟨F, hF⟩ : ∃ F, F = Nat.factorial (p - 1) := ⟨_, rfl⟩
    have hN0 : (p + 1) * F ≠ 0 := by
      rw [hF]
      exact Nat.mul_ne_zero (by omega) (Nat.factorial_ne_zero _)
    have hcop : p.Coprime ((p + 1) * F) := by
      refine Nat.Coprime.mul_right (Nat.coprime_self_add_right.2 (Nat.coprime_one_right p)) ?_
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_
      rw [hF] at h
      have := (Nat.Prime.dvd_factorial hp).1 h
      omega
    obtain ⟨p', hpp', hp', hmod⟩ := Nat.forall_exists_prime_gt_and_modEq p hN0 hcop
    obtain ⟨x, hx⟩ := (Nat.modEq_iff_dvd' hpp'.le).1 hmod.symm
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 + F * x := ⟨_, rfl⟩
    have hp'eq : p' + 1 = (p + 1) * Q := by
      have h1 : p' = p + (p + 1) * F * x := by omega
      rw [h1, hQ]
      ring
    have hQfac : ∀ r, r.Prime → r ∣ Q → p ≤ r := by
      intro r hr hrQ
      by_contra hlt
      have hrF : r ∣ F * x := by
        rw [hF]
        exact (Nat.dvd_factorial hr.pos (by omega)).mul_right x
      have hr1 : r ∣ Q - F * x := Nat.dvd_sub hrQ hrF
      rw [show Q - F * x = 1 by omega] at hr1
      exact hr.one_lt.ne' (Nat.dvd_one.1 hr1)
    have hPle : ∀ q ∈ P, q ≤ p := fun q hq => by
      have := Nat.le_of_dvd (by omega) (hP q hq).2.1
      omega
    have hnot : p' ∉ P := fun h => by
      have := hPle p' h
      omega
    refine ⟨p', by omega, hp', insert p' P, by rw [Finset.card_insert_of_notMem hnot, hcard],
      fun q hqP => ?_⟩
    rcases Finset.mem_insert.1 hqP with rfl | hqP
    · refine ⟨hp', dvd_rfl, fun r hr hrdvd => ?_⟩
      rw [Nat.div_self (by omega)] at hrdvd
      exact absurd (Nat.dvd_one.1 hrdvd) hr.one_lt.ne'
    · obtain ⟨hq, ⟨e, he⟩, hqfac⟩ := hP q hqP
      have hq1 : 0 < q + 1 := by omega
      have hp'q : p' + 1 = (q + 1) * (e * Q) := by rw [hp'eq, he, mul_assoc]
      refine ⟨hq, ⟨e * Q, hp'q⟩, fun r hr hrdvd => ?_⟩
      rw [hp'q, Nat.mul_div_cancel_left _ hq1] at hrdvd
      rcases hr.dvd_mul.1 hrdvd with hre | hrQ
      · refine hqfac r hr ?_
        rwa [he, Nat.mul_div_cancel_left _ hq1]
      · have := hQfac r hr hrQ
        have := hPle q hqP
        omega

/-- **Unbounded drops in the number of remainders.** Let $s(n)$ be the number of distinct
remainders $n \bmod k$ with $1 \le k \le \lfloor n/2 \rfloor$. For every natural number $M$
there are infinitely many $n$ with $s(n+1) + M \le s(n)$; equivalently,
$\liminf_{n \to \infty} (s(n+1) - s(n)) = -\infty$.

Source: Omkar Baraskar and Ingrid Vukusic, *Bounds for Sets of Remainders*, Journal of
Integer Sequences 29 (2026), Article 26.1.4, Proposition 17 (`prop:diffs_unbounded`). -/
public theorem remainderCount_drops_unbounded (M : ℕ) :
    ∃ᶠ n in Filter.atTop, remainderCount (n + 1) + M ≤ remainderCount n := by
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨p, hap, -, P, hcard, hP⟩ := exists_prime_chain (M + 1) a
  refine ⟨p, hap.le, ?_⟩
  have := remainderCount_succ_add_card_le P hP
  omega

end

end MetaMathlibExt
